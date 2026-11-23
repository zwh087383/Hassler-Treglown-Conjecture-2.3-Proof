import Audit.Colored

namespace Audit.Defects
open Finset Sumfree
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Blue edges join all four pairs. A red edge leaves just the prescribed pair compatible. -/
def lifted (blue red : V → V → Prop) (color : V → V → Bool) (p q : V × Bool) : Prop :=
  blue p.1 q.1 ∨ (red p.1 q.1 ∧ (p.2≠color p.1 q.1 ∨ q.2≠color q.1 p.1))

theorem support_injection (blue red : V → V → Prop) (color : V → V → Bool)
    (unique : ∀ x y z, red x y → red x z → color x y=color x z → y=z) :
    mis (lifted blue red color) univ ≤ (Colored.family blue red univ).card := by
  classical
  let r := lifted blue red color
  let support (I : Finset (V × Bool)) := I.image Prod.fst
  have member {x : V} {I : Finset (V × Bool)} : x∈support I ↔ ∃ b,(x,b)∈I := by
    constructor
    · intro h; obtain ⟨⟨u,b⟩,hb,rfl⟩ := mem_image.mp h; exact ⟨b,hb⟩
    · rintro ⟨b,hb⟩; exact mem_image_of_mem Prod.fst hb
  have color_forced {I : Finset (V × Bool)} (ind : Independent r I) {x y : V} {a b : Bool}
      (xi : (x,a)∈I) (yi : (y,b)∈I) (hit : red x y) : a=color x y ∧ b=color y x := by
    by_contra! h
    exact ind _ xi _ yi (Or.inr ⟨hit,by tauto⟩)
  have valid {I : Finset (V × Bool)} (h : IsMIS r univ I) : Colored.Valid blue red univ (support I) := by
    refine ⟨subset_univ _,?_,?_,?_⟩
    · intro x hx y hy blueEdge
      obtain ⟨a,ha⟩ := member.mp hx; obtain ⟨b,hb⟩ := member.mp hy
      exact h.2.1 _ ha _ hb (Or.inl blueEdge)
    · intro x hx y hy z hz xy xz
      obtain ⟨a,ha⟩ := member.mp hx
      obtain ⟨b,hb⟩ := member.mp hy
      obtain ⟨c,hc⟩ := member.mp hz
      exact unique x y z xy xz ((color_forced h.2.1 ha hb xy).1.symm.trans (color_forced h.2.1 ha hc xz).1)
    · intro x _ miss
      have no : (x,false)∉I := fun h => miss (member.mpr ⟨_,h⟩)
      obtain ⟨⟨y,b⟩,inc,edge⟩ := h.2.2 (x,false) (mem_univ _) no
      exact ⟨y,member.mpr ⟨b,inc⟩,edge.imp id And.left⟩
  apply card_le_card_of_injOn support
  · intro I hi; exact (Colored.mem_family ..).mpr (valid (mem_family.mp hi))
  · intro I hi J hj same
    have sub {A B : Finset (V × Bool)} (a : IsMIS r univ A) (b : IsMIS r univ B)
        (eq : support A=support B) : A⊆B := by
      rintro ⟨x,c⟩ xc
      apply (member_iff b (x,c)).mpr ⟨mem_univ _,?_⟩
      rintro ⟨y,d⟩ yd clash
      obtain ⟨j,xj⟩ := member.mp (eq ▸ member.mpr ⟨c,xc⟩ : x∈support B)
      obtain ⟨i,yi⟩ := member.mp (eq.symm ▸ member.mpr ⟨d,yd⟩ : y∈support A)
      rcases clash with blueEdge|⟨redEdge,ne|ne⟩
      · exact a.2.1 _ xc _ yi (Or.inl blueEdge)
      · exact ne (color_forced a.2.1 xc yi redEdge).1
      · exact ne (color_forced b.2.1 xj yd redEdge).2
    exact Subset.antisymm (sub (mem_family.mp hi) (mem_family.mp hj) same)
      (sub (mem_family.mp hj) (mem_family.mp hi) same.symm)

end
end Audit.Defects
