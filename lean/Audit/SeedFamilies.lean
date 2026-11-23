import Audit.Blocks
import Sumfree.TheoremA

namespace Audit.SeedFamilies
open Finset Lower Band Blocks
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
theorem free_set (s : Finset (Pt H)) : Link.Free s ↔ Sumfree.SumFree (s : Set (Pt H)) := by
  constructor
  · intro f x hx y hy h; exact f _ hx _ hy _ h rfl
  · intro f x hx y hy z hz eq; exact f _ hx _ hy (eq.symm ▸ hz)

variable [Module Field5 H]

theorem old_link (s : Finset (Pt H)) :
    Sumfree.mis (Link.clash s) (Link.legal s (full H)) =
    Sumfree.mis (Sumfree.Link (s : Set (Pt H))) (Sumfree.legal (s : Set (Pt H))) := by
  symm
  let u := Sumfree.legal (s : Set (Pt H))
  have imageEq : u.image Sumfree.vertex=Link.legal s (full H) := by
    have layers : (Finset.univ : Finset (Bool × H)).image Sumfree.vertex=full H := by
      rw [Sumfree.Pair.vertex_image]; ext x
      simp only [Sumfree.Pair.layers,mem_filter,mem_univ,true_and]
      exact (mem_full (u:=x)).symm
    have compatible (p : Bool × H) : p∈u ↔ Link.Free (insert (Sumfree.vertex p) s) := by
      simp only [u,Sumfree.legal,mem_filter,mem_univ,true_and,free_set,coe_insert]
    ext x; constructor
    · intro h; obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      exact Link.mem_legal.mpr ⟨layers ▸ mem_image_of_mem _ (mem_univ p), (compatible _).mp hp⟩
    · intro h; obtain ⟨hb,f⟩ := Link.mem_legal.mp h
      obtain ⟨p,_,rfl⟩ := mem_image.mp (layers.symm ▸ hb)
      exact mem_image.mpr ⟨p,(compatible _).mpr f,rfl⟩
  rw [←imageEq]
  apply Sumfree.mis_image _ _ _ _ Sumfree.Pair.vertex_injection.injOn
  intro x hx y hy
  have lx : Sumfree.vertex x∈Link.legal s (full H) := imageEq ▸ mem_image_of_mem _ hx
  have ly : Sumfree.vertex y∈Link.legal s (full H) := imageEq ▸ mem_image_of_mem _ hy
  rw [legal_edge (band_free _) lx ly]
  simp only [Sumfree.Link,Sumfree.raw,edge,Sumfree.Pair.vertex_injection.ne_iff,mem_coe]
  tauto

theorem symmetric {s : Finset (Pt H)} (sym : ∀ x,x∈s ↔ -x∈s) :
    (Sumfree.mis (Link.clash s) (Link.legal s (full H)):ℝ) ≤ (3:ℝ)^((Fintype.card H:ℝ)/2) := by
  rw [old_link]
  exact (Sumfree.theorem_B (S:=(s : Set (Pt H))) sym).trans (Real.rpow_le_rpow_of_exponent_le
    (by norm_num) (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card H); linarith))

theorem at_most_two {s : Finset (Pt H)} (sf : Link.Free s)
    (dis : Disjoint s (full H)) (two : s.card≤2) :
    (Sumfree.mis (Link.clash s) (Link.legal s (full H)):ℝ) ≤ (3:ℝ)^((Fintype.card H:ℝ)/2) := by
  rw [old_link]
  exact Sumfree.Pair.at_most_two s two (fun _ hx h => disjoint_left.mp dis hx (mem_full.mpr h)) ((free_set _).mp sf)

end
end Audit.SeedFamilies
