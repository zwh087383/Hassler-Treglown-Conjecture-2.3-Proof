import Sumfree.Counter
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Fin.Basic

namespace Sumfree.Blocks
open Counter

/-- (layer, first tail coordinate, second tail coordinate, quotient coordinate). -/
abbrev Point := Fin 5 × Fin 5 × Fin 5 × Fin 5

inductive Kind
  | same | opposite | different | mixed | zeroOpposite | zeroIndependent | oneNonzero | oneZero
  deriving DecidableEq

def q : Kind → Nat
  | .opposite | .oneNonzero => 1
  | .zeroIndependent => 25
  | _ => 5

def seeds : Kind → List Point
  | .same => [(1,0,0,0),(1,1,0,0)]
  | .opposite => [(1,0,0,0),(4,0,0,0)]
  | .different => [(1,0,0,0),(4,4,0,0)]
  | .mixed => [(0,1,0,0),(1,0,0,0)]
  | .zeroOpposite => [(0,1,0,0),(0,4,0,0)]
  | .zeroIndependent => [(0,1,0,0),(0,0,1,0)]
  | .oneNonzero => [(1,0,0,0)]
  | .oneZero => [(0,1,0,0)]

def size (k : Kind) (generic : Bool) := (if generic then 4 else 2) * q k
def point (k : Kind) (generic : Bool) (i : Fin (size k generic)) : Point :=
  let offset := i.val / 2 % q k
  let sign := i.val % 2 == 1
  let x : Fin 5 := Fin.ofNat' 5 (offset % 5)
  let y : Fin 5 := Fin.ofNat' 5 (offset / 5)
  let z : Fin 5 := if generic then (if i.val < 2*q k then 1 else 4) else 0
  if sign then (3,-x,-y,-z) else (2,x,y,z)

def sf (s : List Point) := s.all fun x => s.all fun y => !(s.contains (x+y))
def edge (k : Kind) (generic : Bool) (i j : Fin (size k generic)) :=
  let x := point k generic i
  let y := point k generic j
  let s := seeds k
  i != j && (s.contains (x+y) || s.contains (x-y) || s.contains (y-x))
def legal (k : Kind) (generic : Bool) (i : Fin (size k generic)) := sf (point k generic i :: seeds k)
def count (k : Kind) (generic : Bool) :=
  solve (size k generic) (graphFormula _ (edge k generic) (legal k generic))

theorem counts_actual_MIS (k : Kind) (generic : Bool) :
    count k generic = mis (fun i j => edge k generic i j = true) (domain (legal k generic)) :=
  solve_mis .. 

def prismEdge (r : Nat) (i j : Fin (2*r)) : Bool :=
  let x := i.val/2
  let y := j.val/2
  (x == y && i != j) || (i.val%2 == j.val%2 && ((x+1)%r == y || (y+1)%r == x))

def prism (r : Nat) (m : Bool) :=
  solve (2*r) (graphFormula _ (prismEdge r) (fun _ => true) m)

end Sumfree.Blocks
