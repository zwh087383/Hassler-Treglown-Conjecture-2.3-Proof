import Sumfree.Graph
import Mathlib.Data.Finset.Max

namespace Sumfree
open Finset
variable {V : Type*} [DecidableEq V] {R : V → V → Prop}

/-- Fact 1. Extend inside the larger graph, then restrict back to the original vertices. -/
theorem induced_mono (sym : Symmetric R) {a b : Finset V} (sub : a ⊆ b)
    (irr : ∀ x ∈ b, ¬ R x x) : mis R a ≤ mis R b := by
  classical
  apply card_le_card_of_surjOn (fun J => J ∩ a)
  intro I hi
  have h := mem_family.mp hi
  let F := b.powerset.filter fun J => I ⊆ J ∧ Independent R J
  have nonempty : F.Nonempty := ⟨I,mem_filter.mpr
    ⟨mem_powerset.mpr (h.1.trans sub),Finset.Subset.refl _,h.2.1⟩⟩
  obtain ⟨J,hj,maximal⟩ := F.exists_max_image Finset.card nonempty
  obtain ⟨jb,ij,ind⟩ := mem_filter.mp hj
  have maxJ : IsMIS R b J := (isMIS_iff_maximal sym irr).2 ⟨mem_powerset.mp jb,ind,by
    intro L lb li jl
    exact (eq_of_subset_of_card_le jl
      (maximal L (mem_filter.mpr ⟨mem_powerset.mpr lb,ij.trans jl,li⟩))).symm⟩
  refine ⟨J,mem_family.mpr maxJ,Finset.Subset.antisymm ?_ (subset_inter ij h.1)⟩
  intro x hx
  obtain ⟨xj,xa⟩ := mem_inter.mp hx
  by_contra xn
  obtain ⟨y,yi,e⟩ := h.2.2 x xa xn
  exact ind x xj y (ij yi) e

end Sumfree
