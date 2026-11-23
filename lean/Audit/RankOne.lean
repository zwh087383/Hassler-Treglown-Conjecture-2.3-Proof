import Sumfree.CountMemo
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Prod

namespace Audit.RankOne
open Sumfree Sumfree.Counter

abbrev Point := Fin 5 × Fin 5 × Fin 5

/-- The 14 possible nonzero seed elements in layers 0, 1, and 4;
    the last coordinate is zero on the seed span. -/
def label (i : Nat) : Point :=
  if i < 4 then (0, ((i+1 : ℕ) : Fin 5), 0)
  else if i < 9 then (1, ((i-4 : ℕ) : Fin 5), 0)
  else (4, ((i-9 : ℕ) : Fin 5), 0)

def seed (mask : Nat) : List Point :=
  ((List.range 14).filter fun i => mask.testBit i).map label

def sumFree (s : List Point) : Bool :=
  s.all fun x => s.all fun y => !(s.contains (x+y))

/-- Complete four-layer generic component on the two nonzero opposite
    quotient cosets. Every vertex has tail 1 or 4; neither it nor its
    double is in the seed plane. -/
def vertex (i : Fin 20) : Point :=
  (if i.val < 10 then 2 else 3, ((i.val/2 : ℕ) : Fin 5), if i.val%2=0 then 1 else 4)

def edge (s : List Point) (i j : Fin 20) : Bool :=
  let x := vertex i
  let y := vertex j
  i != j && (s.contains (x+y) || s.contains (x-y) || s.contains (y-x))

def count (s : List Point) : Nat :=
  cached 20 (graphFormula 20 (edge s) (fun _ => true) true)

theorem count_spec (s : List Point) :
    count s = mis (fun x y => edge s x y = true) Finset.univ := by
  rw [count,cached_correct,solve_mis]
  congr 1

def passes (m : Nat) := !sumFree (seed m) || decide (count (seed m) ≤ 243)

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem exhaustive : (List.range 16384).all passes = true := by native_decide

theorem every_seed (m : Nat) (range : m < 16384) (legal : sumFree (seed m)=true) :
    mis (fun x y => edge (seed m) x y = true) Finset.univ ≤ 3^5 := by
  have h := List.all_eq_true.mp exhaustive m (List.mem_range.mpr range)
  simpa [passes,legal,count_spec] using h

end Audit.RankOne
