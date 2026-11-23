import Audit.Remaining
import Audit.SmallMixedFour
import Audit.ManuscriptForm
import Audit.GenericTheorem
import Audit.Main

namespace Audit.Sharp
open Finset Generic Band Link Lower Blocks Assembly Filter
open scoped Topology
noncomputable section

/-- This discharges the last bounded classification in the global argument. -/
theorem local_counts : Remaining.LocalCounts := by
  intro k s _ _ sf out zero _ _ size
  exact SmallMixed.four sf out zero size

theorem standard_band : StandardBand := Remaining.standard_of_local local_counts

/-- The global upper bound at every positive accuracy. -/
theorem upper {η : ℝ} (positive : 0<η) (small : η≤1) :
    ∀ᶠ k : ℕ in atTop, (Asymptotic.fmax (k+1):ℝ) ≤
      (2:ℝ)^((2*η)*order k)*(3:ℝ)^(order k/10+errorConstant) :=
  upper_with_band Sparse.sparseCovers Structure.largeSetStructure standard_band positive small

/-- Normalized logarithm of the number of inclusion-maximal sum-free subsets. -/
theorem limit : Tendsto Limit.normalized atTop (𝓝 (1/10:ℝ)) :=
  Remaining.main_of_local_counts local_counts

/-- A second assembly of the limit through the generic block theorem for all seeds. -/
theorem limit_via_generic_blocks : Tendsto Limit.normalized atTop (𝓝 (1/10:ℝ)) :=
  Main.main_of_generic_blocks GenericTheorem.original_blocks

theorem log_limit : Tendsto
    (fun k : ℕ => Real.logb 3 ((Link.maximalSets (univ : Finset (Fin k → ZMod 5))).card)/(5:ℝ)^k)
    atTop (𝓝 (1/10:ℝ)) := by
  change Tendsto (fun k : ℕ => Real.logb 3 (Manuscript.count k)/(5:ℝ)^k) atTop _
  simpa only [Manuscript.log_form] using limit

/-- The literal exponential formulation in standard F₅^k coordinates, with an explicit
    real-valued error that is little-o of 5^k. -/
theorem main_theorem :
    ∃ e : ℕ → ℝ, e =o[atTop] (fun k : ℕ => (5:ℝ)^k) ∧
      ∀ k : ℕ, ((Link.maximalSets (univ : Finset (Fin k → ZMod 5))).card:ℝ) =
        (3:ℝ)^((5:ℝ)^k/10+e k) :=
  ⟨Manuscript.errorTerm,Manuscript.error_iff_limit.mpr limit,Manuscript.exact_power⟩

end
end Audit.Sharp
