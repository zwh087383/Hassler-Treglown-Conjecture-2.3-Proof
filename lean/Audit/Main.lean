import Audit.Sparse
import Audit.Structure
import Audit.Limit

namespace Audit.Main
open Filter Blocks
open scoped Topology

/-- Apply the generic block estimate to the proved container and density theorems. -/
theorem main_of_generic_blocks (blocks : BlockBound) :
    Tendsto Limit.normalized atTop (𝓝 (1/10:ℝ)) :=
  Limit.limit_of_inputs Sparse.sparseCovers Structure.largeSetStructure blocks

theorem upper_of_generic_blocks (blocks : BlockBound) {η : ℝ} (positive : 0<η) (small : η≤1) :
    ∀ᶠ k : ℕ in atTop, (Asymptotic.fmax (k+1):ℝ) ≤
      (2:ℝ)^((2*η)*Assembly.order k)*(3:ℝ)^(Assembly.order k/10+errorConstant) :=
  Assembly.upper_at_accuracy Sparse.sparseCovers Structure.largeSetStructure blocks positive small

end Audit.Main
