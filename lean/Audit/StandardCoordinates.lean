import Audit.Limit

namespace Audit.StandardCoordinates
open Finset Link Blocks
open scoped Classical
noncomputable section

variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
  [AddCommGroup H] [DecidableEq H] [Fintype H]

private theorem image_maximal (e : G ≃+ H) {s : Finset G} (maximal : MaxIn univ s) :
    MaxIn univ (s.image e) := by
  refine ⟨subset_univ _,(Assembly.free_image e s).mpr maximal.2.1,?_⟩
  intro t _ tf sub
  have back : s⊆t.image e.symm := by
    intro x hx
    exact mem_image.mpr ⟨e x,sub (mem_image_of_mem _ hx),e.symm_apply_apply _⟩
  have eq := maximal.2.2 (t.image e.symm) (subset_univ _) ((Assembly.free_image e.symm t).mpr tf) back
  rw [←eq]
  simp [image_image,Function.comp_def]

theorem maximal_count_equiv (e : G ≃+ H) :
    (maximalSets (univ : Finset G)).card=(maximalSets (univ : Finset H)).card := by
  let f (s : Finset G) := s.image e
  have inj : Function.Injective f := by
    intro a b h
    have t := congrArg (fun s : Finset H => s.image e.symm) h
    simpa [f,image_image,Function.comp_def] using t
  have bij : (maximalSets univ).image f=maximalSets (univ : Finset H) := by
    ext t
    constructor
    · intro h; obtain ⟨s,hs,rfl⟩ := mem_image.mp h
      exact mem_maximalSets.mpr (image_maximal e (mem_maximalSets.mp hs))
    · intro h
      refine mem_image.mpr ⟨t.image e.symm,mem_maximalSets.mpr (image_maximal e.symm (mem_maximalSets.mp h)),?_⟩
      simp [f,image_image,Function.comp_def]
  rw [←bij,card_image_of_injective _ inj]

def split (k : ℕ) : (Fin (k+1) → Field5) ≃+ Lower.Pt (Space k) where
  toFun v := (v 0,fun i => v i.succ)
  invFun v := Fin.cons v.1 v.2
  left_inv v := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv v := by cases v; simp
  map_add' _ _ := rfl

/-- The count is over all inclusion-maximal sum-free subsets of the usual coordinate space. -/
theorem fmax_eq (k : ℕ) :
    Asymptotic.fmax k=(maximalSets (univ : Finset (Fin k → ZMod 5))).card := by
  cases k with
  | zero => rfl
  | succ j => exact (maximal_count_equiv (split j)).symm

end
end Audit.StandardCoordinates
