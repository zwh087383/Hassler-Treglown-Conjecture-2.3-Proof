import Audit.StripFormula

namespace Audit.Strip.NoZero
open Sumfree.Counter

/-- The three-seed no-zero model with P={(0,0)}, Q={(0,1),(1,1)}. -/
def seed : Strip.Seed := {(1,0,0),(4,0,4),(4,4,4)}

def vertex (right : Bool) (i : ℕ) : P :=
  let clone := i%10 ≥ 5
  let positive := right == decide clone
  let x : Fin 5 := (i%5:ℕ)
  let y : Fin 5 := (i/10:ℕ)
  (if clone then 3 else 2,(if positive then x else -x,if positive then y else -y),
    if positive then 1 else 4)

def inPlane (p : P) := p.2.2 == 0 && decide ((p.1,p.2.1) ∈ seed)
def adj (p q : P) := p != q && (inPlane (p+q) || inPlane (p-q) || inPlane (q-p))

abbrev Clause (n : ℕ) := Fin n × List (Fin n)

/-- A bit denotes a candidate right vertex that can block a witness. Every mask
    below is checked against the original graph; horizontal translations give the other columns. -/
def templates : ℕ → List ℕ
  | 0 => [50,1042,2066]
  | 1 => [1025,2049,32769,65537,1042,1104,1538,1600,2066,2128,2562,2624]
  | 2 => [32785,32816,33281,33312,34832,35328,49153,49184,51200]
  | _ => []

def adjacentRows (n offset : ℕ) : List (Clause n) :=
  (List.finRange n).flatMap fun i =>
    if offset ≤ i.val ∧ i.val < offset+20 then
      (templates ((i.val-offset)/5)).map fun mask =>
        let blockers := (List.finRange n).filter fun j =>
          decide (offset ≤ j.val ∧ j.val < offset+20) &&
            mask.testBit (5*((j.val-offset)/5) + ((j.val%5+5-i.val%5)%5))
        (i,blockers)
    else []

def pairClauses := adjacentRows 20 0
def tripleClauses := adjacentRows 30 0 ++ adjacentRows 30 10

def formula {n : ℕ} (clauses : List (Clause n)) : Formula := clauses.map fun (i,blockers) =>
  (i.val,true)::blockers.map fun j => (j.val,false)

def checked {n : ℕ} (start : ℕ) (arg : Clause n) : Bool :=
  (List.finRange 50).all fun j =>
    !adj (vertex true (start+arg.1.val)) (vertex false j.val) ||
    arg.2.any fun z => adj (vertex false j.val) (vertex true (start+z.val))

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem pair_sound : pairClauses.all (checked 0)=true := by native_decide
theorem triple_sound : tripleClauses.all (checked 20)=true := by native_decide
theorem pair_count : cached 20 (formula pairClauses)=56551 := by native_decide
theorem triple_count : cached 30 (formula tripleClauses)=6613551 := by native_decide

end Audit.Strip.NoZero
