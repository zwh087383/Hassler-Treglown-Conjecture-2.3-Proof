import Audit.StripSemantics
import Audit.StripCounts
import Audit.Reduction

namespace Audit.Strip
open Finset Generic Reduction

/-- The six 100-vertex models, measured on the original four-layer domain. -/
theorem model_bound (c : Model) : rankCount (seed c) < 3^25 := by
  have h := window_product c
  rw [count_checked,count_checked] at h
  exact h.trans_lt (by cases c <;> decide)

def coordinates : K ≃+ Blocks.Space 2 where
  toFun p := ![p.1,p.2]
  invFun v := (v 0,v 1)
  left_inv _ := rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' p q := by funext i; fin_cases i <;> rfl

/-- Direct entry point for the `Fin 2 → ZMod 5` convention of the global reduction. -/
theorem model_bound_space (c : Model) :
    rankCount ((seed c).image (relabel coordinates)) < 3^(5^2) := by
  rw [←rankCount_relabel]; exact model_bound c

end Audit.Strip
