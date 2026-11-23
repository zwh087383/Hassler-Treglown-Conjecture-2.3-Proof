import Sumfree.Folding
namespace Sumfree
noncomputable section
open Finset

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem mis_image (s : Finset V) (f : V → W) (r : V → V → Prop) (t : W → W → Prop)
    (inj : (s : Set V).InjOn f) (edges : ∀ x ∈ s, ∀ y ∈ s, r x y ↔ t (f x) (f y)) :
    mis r s = mis t (s.image f) := by
  classical
  have translated {I : Finset V} (sub : I ⊆ s) :
      IsMIS r s I ↔ IsMIS t (s.image f) (I.image f) := by
    constructor
    · rintro ⟨_,ind,dom⟩
      refine ⟨image_subset_image sub,?_,?_⟩
      · intro a ha b hb e
        obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
        exact ind _ hx _ hy ((edges _ (sub hx) _ (sub hy)).2 e)
      · intro a ha hn
        obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
        obtain ⟨y,hy,e⟩ := dom x hx (fun xi => hn (mem_image_of_mem _ xi))
        exact ⟨f y,mem_image_of_mem _ hy,(edges _ hx _ (sub hy)).1 e⟩
    · rintro ⟨_,ind,dom⟩
      refine ⟨sub,fun x hx y hy e => ind _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
        ((edges _ (sub hx) _ (sub hy)).1 e),?_⟩
      intro x hx hn
      have no : f x ∉ I.image f := by
        rintro h
        obtain ⟨y,hy,eq⟩ := mem_image.mp h
        exact hn (inj (sub hy) hx eq ▸ hy)
      obtain ⟨b,hb,e⟩ := dom _ (mem_image_of_mem _ hx) no
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
      exact ⟨y,hy,(edges _ hx _ (sub hy)).2 e⟩
  apply card_bij (fun I _ => I.image f)
  · intro I hi
    exact mem_family.mpr ((translated (mem_family.mp hi).1).1 (mem_family.mp hi))
  · intro I hi J hj eq
    have direction {a b : Finset V} (sa : a ⊆ s) (sb : b ⊆ s) (e : a.image f = b.image f) : a ⊆ b := by
      intro x hx
      obtain ⟨y,hy,same⟩ := mem_image.mp (e ▸ mem_image_of_mem f hx : f x ∈ b.image f)
      exact inj (sb hy) (sa hx) same ▸ hy
    exact Finset.Subset.antisymm (direction (mem_family.mp hi).1 (mem_family.mp hj).1 eq)
      (direction (mem_family.mp hj).1 (mem_family.mp hi).1 eq.symm)
  · intro J hj
    let I := s.filter fun x => f x ∈ J
    have eq : I.image f = J := by
      ext y
      constructor
      · rintro h
        obtain ⟨x,hx,rfl⟩ := mem_image.mp h
        exact (mem_filter.mp hx).2
      · intro hy
        obtain ⟨x,hx,rfl⟩ := mem_image.mp ((mem_family.mp hj).1 hy)
        exact mem_image_of_mem _ (mem_filter.mpr ⟨hx,hy⟩)
    exact ⟨I,mem_family.mpr ((translated (filter_subset _ _)).2 (eq.symm ▸ mem_family.mp hj)),eq⟩

end
end Sumfree
