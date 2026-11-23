import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Push
import Mathlib.SetTheory.Cardinal.Finite

namespace Sumfree

noncomputable section
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]

/-- Independent sets of the relation, with loops treated as forbidden vertices. -/
def Independent (R : V → V → Prop) (I : Finset V) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, ¬ R x y

/-- Independent and dominating on the set of legal vertices. -/
def IsMIS (R : V → V → Prop) (s I : Finset V) : Prop :=
  I ⊆ s ∧ Independent R I ∧ ∀ x ∈ s, x ∉ I → ∃ y ∈ I, R x y

noncomputable def family (R : V → V → Prop) (s : Finset V) : Finset (Finset V) := by
  classical exact s.powerset.filter (IsMIS R s)

@[simp] theorem mem_family {R : V → V → Prop} {s I : Finset V} :
    I ∈ family R s ↔ IsMIS R s I := by
  classical
  simp only [family, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  exact fun h => h.1

abbrev mis (R : V → V → Prop) (s : Finset V) := (family R s).card

theorem isMIS_iff_maximal {R : V → V → Prop} (sym : Symmetric R)
    {s I : Finset V} (simple : ∀ x ∈ s, ¬ R x x) :
    IsMIS R s I ↔ I ⊆ s ∧ Independent R I ∧
      ∀ J ⊆ s, Independent R J → I ⊆ J → J = I := by
  constructor
  · rintro ⟨hs, hi, hd⟩
    refine ⟨hs, hi, ?_⟩
    intro J hJ ind sub
    apply Finset.Subset.antisymm _ sub
    intro x hx
    by_contra hn
    obtain ⟨y, hy, e⟩ := hd x (hJ hx) hn
    exact ind x hx y (sub hy) e
  · rintro ⟨hs, hi, hm⟩
    refine ⟨hs, hi, ?_⟩
    intro x hx hn
    by_contra! h
    have ind : Independent R (insert x I) := by
      intro a ha b hb
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact simple _ hx
        · exact h _ hb
      · rcases hb with rfl | hb
        · exact fun e => h _ ha (sym e)
        · exact hi _ ha _ hb
    have eq := hm (insert x I) (Finset.insert_subset hx hs) ind (Finset.subset_insert _ _)
    exact hn (eq ▸ Finset.mem_insert_self x I)

theorem member_iff {R : V → V → Prop} {s I : Finset V} (h : IsMIS R s I) (x : V) :
    x ∈ I ↔ x ∈ s ∧ ∀ y ∈ I, ¬ R x y := by
  constructor
  · exact fun hx => ⟨h.1 hx, h.2.1 x hx⟩
  · rintro ⟨hx, hn⟩
    by_contra ha
    obtain ⟨y, hy, e⟩ := h.2.2 x hx ha
    exact hn y hy e

theorem isMIS_of_iff {R : V → V → Prop} {s I : Finset V}
    (h : ∀ x, x ∈ I ↔ x ∈ s ∧ ∀ y ∈ I, ¬ R x y) : IsMIS R s I := by
  refine ⟨fun x hx => ((h x).1 hx).1, fun x hx => ((h x).1 hx).2, ?_⟩
  intro x hx hn
  by_contra! hnone
  exact hn ((h x).2 ⟨hx, hnone⟩)

/-- Maximal independent sets restrict to components when there are no crossing edges. -/
theorem disjoint_count {R : V → V → Prop} (sym : Symmetric R)
    (a b : Finset V) (dis : Disjoint a b) (sep : ∀ x ∈ a, ∀ y ∈ b, ¬ R x y) :
    mis R (a ∪ b) = mis R a * mis R b := by
  classical
  have restrict {u v I : Finset V} (h : IsMIS R (u ∪ v) I)
      (cross : ∀ x ∈ u, ∀ y ∈ v, ¬ R x y) : IsMIS R u (I ∩ u) := by
    refine ⟨Finset.inter_subset_right, fun x hx y hy =>
      h.2.1 x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1, ?_⟩
    intro x hx xn
    obtain ⟨y, hy, e⟩ := h.2.2 x (Finset.mem_union_left _ hx)
      (fun hxi => xn (Finset.mem_inter.mpr ⟨hxi, hx⟩))
    have yu : y ∈ u := (Finset.mem_union.mp (h.1 hy)).resolve_right (fun yv => cross x hx y yv e)
    exact ⟨y, Finset.mem_inter.mpr ⟨hy, yu⟩, e⟩
  have reverseSep : ∀ x ∈ b, ∀ y ∈ a, ¬ R x y := fun x hx y hy e => sep y hy x hx (sym e)
  have combine {I J : Finset V} (hI : IsMIS R a I) (hJ : IsMIS R b J) :
      IsMIS R (a ∪ b) (I ∪ J) := by
    refine ⟨Finset.union_subset_union hI.1 hJ.1, ?_, ?_⟩
    · intro x hx y hy
      rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
      · exact hI.2.1 _ hx _ hy
      · exact sep _ (hI.1 hx) _ (hJ.1 hy)
      · exact reverseSep _ (hJ.1 hx) _ (hI.1 hy)
      · exact hJ.2.1 _ hx _ hy
    · intro x hx xn
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨y, hy, e⟩ := hI.2.2 _ hx (fun h => xn (Finset.mem_union_left _ h))
        exact ⟨y, Finset.mem_union_left _ hy, e⟩
      · obtain ⟨y, hy, e⟩ := hJ.2.2 _ hx (fun h => xn (Finset.mem_union_right _ h))
        exact ⟨y, Finset.mem_union_right _ hy, e⟩
  rw [← Finset.card_product]
  apply Finset.card_bij (fun I _ => (I ∩ a, I ∩ b))
  · intro I hi
    have h := mem_family.mp hi
    exact Finset.mem_product.mpr ⟨mem_family.mpr (restrict h sep),
      mem_family.mpr (restrict (by simpa [Finset.union_comm] using h) reverseSep)⟩
  · intro I hI J hJ eq
    have h1 := congrArg Prod.fst eq
    have h2 := congrArg Prod.snd eq
    have subI := (mem_family.mp hI).1
    have subJ := (mem_family.mp hJ).1
    change I ∩ a = J ∩ a at h1
    change I ∩ b = J ∩ b at h2
    have recover (S : Finset V) (hs : S ⊆ a ∪ b) : S ∩ a ∪ S ∩ b = S := by
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hs]
    rw [← recover I subI, h1, h2, recover J subJ]
  · rintro ⟨I,J⟩ h
    obtain ⟨hI,hJ⟩ := Finset.mem_product.mp h
    have i := mem_family.mp hI
    have j := mem_family.mp hJ
    refine ⟨I ∪ J, mem_family.mpr (combine i j), ?_⟩
    have hdis := Finset.disjoint_left.mp dis
    apply Prod.ext
    · ext x
      change x ∈ (I ∪ J) ∩ a ↔ x ∈ I
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hx, ha⟩ => hx.resolve_right (fun hj => hdis ha (j.1 hj)),
        fun hx => ⟨Or.inl hx, i.1 hx⟩⟩
    · ext x
      change x ∈ (I ∪ J) ∩ b ↔ x ∈ J
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hx, hb⟩ => hx.resolve_left (fun hi => hdis (i.1 hi) hb),
        fun hx => ⟨Or.inr hx, j.1 hx⟩⟩

end
end Sumfree
