import Audit.Generic
import Sumfree.CountMemo

namespace Audit.Strip
open Finset Sumfree Sumfree.Counter Generic

abbrev K := Fin 5 × Fin 5
abbrev P := Raw.Point K
abbrev Seed := Finset (Lower.Pt K)

inductive Model
  | sameTriple | oppositeTriple | nestedFour | triangleFour | twoZeroFour | triangleFive
  deriving DecidableEq, Repr

def seed : Model → Seed
  | .sameTriple => {(0,1,0), (1,0,0), (1,0,1)}
  | .oppositeTriple => {(0,1,0), (1,0,0), (4,0,1)}
  | .nestedFour => {(0,1,0), (1,0,0), (1,0,1), (4,0,0)}
  | .triangleFour => {(0,1,0), (1,0,0), (1,0,1), (4,4,0)}
  | .twoZeroFour => {(0,1,0), (0,4,0), (1,0,0), (1,0,1)}
  | .triangleFive => {(0,1,0), (1,0,0), (1,0,1), (4,0,0), (4,4,4)}

def vertex (c : Model) (side : Bool) (i : Fin 50) : P :=
  let slice := (if side then 5 else 0)+i.val/10
  let positive := i.val%10 < 5
  let evenRow := (slice%2 = 0) == (c == .oppositeTriple)
  let h : Fin 5 := if positive == evenRow then 2 else 3
  let y : Fin 5 := (slice/2 : ℕ)
  (h,((i.val%5:ℕ),if positive then y else -y),if positive then 1 else 4)

def inside (i : Fin 50) : Bool := decide (10 ≤ i.val ∧ i.val < 40)
def inPlane (c : Model) (p : P) : Bool := p.2.2==0 && decide ((p.1,p.2.1) ∈ seed c)
def adj (c : Model) (p q : P) : Bool :=
  p != q && (inPlane c (p+q) || inPlane c (p-q) || inPlane c (q-p))

/-- A window enforces independence everywhere and domination at its three inner slices. -/
def windowFormula (c : Model) (side : Bool) : Formula :=
  (List.finRange 50).flatMap fun x =>
    let neigh := (List.finRange 50).filter fun y => adj c (vertex c side x) (vertex c side y)
    let edges := (neigh.filter fun y => x<y).map fun y => [(x.val,false),(y.val,false)]
    if inside x then ((x.val,true)::neigh.map fun y => (y.val,true))::edges else edges

def count (c : Model) (side : Bool) := cached 50 (windowFormula c side)

end Audit.Strip
