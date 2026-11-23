import Audit.StripFormula

namespace Audit.SmallMixed.ZeroTriple
open Finset Sumfree Sumfree.Counter Generic Strip

def seed : Seed := {(0,1,0),(0,0,1),(0,4,4)}

def vertex (h : Bool) (i : Fin 50) : P :=
  let k : K := ((i.val/2%5 : ℕ),(i.val/10 : ℕ))
  let t : Fin 5 := if h then 4 else 1
  if i.val%2=0 then (2,k,t) else (3,-k,-t)

def isIn (p : P) : Bool := p.2.2==0 && decide ((p.1,p.2.1) ∈ seed)
def adj (p q : P) : Bool := p != q && (isIn (p+q) || isIn (p-q) || isIn (q-p))

def condition (h : Bool) : Formula :=
  (List.finRange 50).flatMap fun i =>
    let row := (List.finRange 50).filter fun j => adj (vertex h i) (vertex h j)
    let edges := (row.filter fun j => i<j).map fun j => [(i.val,false),(j.val,false)]
    ((i.val,true)::row.map fun j => (j.val,true))::edges

def parts (left final : ℕ) (f : Formula) : ℕ :=
  match left with
  | 0 => cached final f
  | i+1 => if []∈f then 0 else parts i final (assign false f) + parts i final (assign true f)

theorem parts_correct (left final : ℕ) (f : Formula) : parts left final f=solve (final+left) f := by
  induction left generalizing f with
  | zero => exact cached_correct .. 
  | succ i ih =>
    rw [Nat.add_succ]
    change (if []∈f then 0 else _ + _) = (if []∈f then 0 else _ + _)
    split <;> simp only [ih] <;> rfl

theorem formulas : condition false=condition true := by native_decide

end Audit.SmallMixed.ZeroTriple


