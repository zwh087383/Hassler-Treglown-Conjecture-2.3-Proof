import Sumfree.CellCertificate
import Sumfree.Charts
import Sumfree.Exponents

namespace Sumfree.Pair
open Finset
variable {H : Type*} [AddCommGroup H] [Module F H] [DecidableEq H] [Fintype H]
set_option linter.unusedSectionVars false

theorem root_bound (s t g : Ambient H) (os : ¬band s) (ot : ¬band t)
    (sf : SumFree (seedSet s t)) (bg : band g) :
    (mis (edges s t) (allowed s t (cell s t g))) ^ powerFor s t ≤
      (baseFor s t)^(cell s t g).card := by
  classical
  obtain ⟨c⟩ := chart_exists s t g bg
  let src : Ambient Plane := (s.1,c.uv.1)
  let tgt : Ambient Plane := (t.1,c.uv.2)
  let root : Ambient Plane := (g.1,0)
  obtain ⟨fs,ft,fg⟩ := c.maps
  have tr := cell_transport c.f c.head c.inj c.sourceS c.sourceT c.sourceG
  rw [fs,ft,fg] at tr
  have admissible (a : F) (h : ¬(a=2 ∨ a=3)) : a ∈ ([0,1,4] : List F) := by
    have finite : ∀ b : F, ¬(b=2 ∨ b=3) → b ∈ ([0,1,4] : List F) := by decide
    exact finite a h
  have roots : g.1 ∈ ([2,3] : List F) := by simpa [band] using bg
  have ok := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp checked_cells g.1 roots) s.1 (admissible _ os)) t.1 (admissible _ ot)) c.uv c.shape
  have safe : freeB [src,tgt] := by
    apply (freeB_iff [src,tgt]).2
    intro a ha b hb ab
    have imageMem {x : Ambient Plane} (h : x ∈ [src,tgt]) : c.f x ∈ seedSet s t := by
      rcases List.mem_cons.mp h with rfl | tail
      · exact Or.inl fs
      · have e := List.mem_singleton.mp tail
        subst x
        exact Or.inr ft
    apply sf _ (imageMem ha) _ (imageMem hb)
    rw [← map_add]
    exact imageMem ab
  change (if freeB [src,tgt] then decide (_ ≤ _) else true) = true at ok
  rw [if_pos safe,decide_eq_true_eq] at ok
  have eq : src=tgt ↔ s=t := ⟨fun e => fs.symm.trans ((congrArg c.f e).trans ft),
    fun e => c.inj c.sourceS c.sourceT (fs.trans (e.trans ft.symm))⟩
  have pc : powerFor src tgt = powerFor s t := by simp [powerFor,eq]
  have bc : baseFor src tgt = baseFor s t := by simp [baseFor,eq]
  have length : (rooted src tgt root).length = (cell src tgt root).card := by
    change (points src tgt root).dedup.length = (points src tgt root).toFinset.card
    exact (List.card_toFinset (points src tgt root)).symm
  change localCount src tgt root ^ powerFor src tgt ≤ baseFor src tgt ^ (rooted src tgt root).length at ok
  rw [pc,bc,local_correct,length] at ok
  rwa [tr.1,tr.2]

theorem vertex_injection : Function.Injective (vertex (H := H)) := by
  rintro ⟨c,x⟩ ⟨d,y⟩ eq
  cases c <;> cases d
  · exact Prod.ext (by rfl) (congrArg (fun z : Ambient H => z.2) eq)
  · exact False.elim ((by decide : (2:F) ≠ -2) (congrArg Prod.fst eq))
  · exact False.elim ((by decide : (-2:F) ≠ 2) (congrArg Prod.fst eq))
  · refine Prod.ext (by rfl) ?_
    exact neg_injective (congrArg (fun z : Ambient H => z.2) eq)

theorem vertex_image : (univ : Finset (Bool × H)).image vertex = layers := by
  classical
  ext ⟨a,u⟩
  simp only [mem_image,mem_univ,true_and,layers,mem_filter,band]
  constructor
  · rintro ⟨⟨c,v⟩,eq⟩
    cases c
    · exact Or.inl (congrArg Prod.fst eq).symm
    · exact Or.inr ((congrArg Prod.fst eq).symm.trans (by decide : (-2:F)=3))
  · rintro (rfl|rfl)
    · exact ⟨(false,u),rfl⟩
    · exact ⟨(true,-u),Prod.ext (by decide : (-2:F)=3) (neg_neg u)⟩

theorem band_card : (layers (H := H)).card = 2*Fintype.card H := by
  rw [← vertex_image,Finset.card_image_of_injective _ vertex_injection]
  simp

theorem link_equals (s t : Ambient H) :
    mis (Link (seedSet s t)) (legal (seedSet s t)) =
    mis (edges s t) (allowed s t layers) := by
  classical
  have eq : (legal (seedSet s t)).image vertex = allowed s t layers := by
    ext v
    rw [mem_image,mem_allowed,← vertex_image,mem_image]
    simp only [legal,mem_filter,mem_univ,true_and,legalAt]
    constructor
    · rintro ⟨p,h,rfl⟩
      exact ⟨⟨p,rfl⟩,h⟩
    · rintro ⟨⟨p,rfl⟩,h⟩
      exact ⟨p,h,rfl⟩
  rw [← eq]
  apply mis_image _ _ _ _ vertex_injection.injOn
  intro p _ q _
  exact and_congr_left fun _ => not_congr ⟨congrArg vertex,fun e => vertex_injection e⟩

/-- Stronger integer bound; for two distinct seeds the power is 50, for a
    repeated seed (a singleton set) it is 4. -/
theorem pair_integer (s t : Ambient H) (os : ¬band s) (ot : ¬band t)
    (sf : SumFree (seedSet s t)) : (mis (Link (seedSet s t)) (legal (seedSet s t))) ^ powerFor s t
    ≤ (baseFor s t)^(2*Fintype.card H) := by
  rw [link_equals,← band_card]
  exact assemble s t _ _ (root_bound s t · os ot sf ·)

theorem from_power (m b p k : ℕ) (p0 : 0<p) (b0 : 0<b) (h : m^p ≤ b^k) :
    (m:ℝ) ≤ (b:ℝ)^((k:ℝ)/p) := by
  by_contra! gt
  have h' : (m:ℝ)^p ≤ (b:ℝ)^k := by exact_mod_cast h
  have bad := pow_lt_pow_left₀ gt (n := p) (by positivity) p0.ne'
  rw [← Real.rpow_natCast ((b:ℝ)^_), ← Real.rpow_mul (by positivity : (0:ℝ) ≤ b),
    div_mul_cancel₀ _ (by exact_mod_cast p0.ne'),Real.rpow_natCast] at bad
  linarith

/-- Theorem A from its original two-element seed hypothesis, with C=1. -/
theorem theorem_A_strong (S : Finset (Ambient H)) (two : S.card = 2)
    (outside : ∀ s ∈ S, ¬band s) (sf : SumFree (S : Set (Ambient H))) :
    (mis (Link (S : Set (Ambient H))) (legal (S : Set (Ambient H))) : ℝ) ≤
        (820694:ℝ)^((5*(Fintype.card H : ℝ))/125) := by
  classical
  obtain ⟨s,t,ne,rfl⟩ := card_eq_two.mp two
  have enc : (({s,t} : Finset (Ambient H)) : Set (Ambient H)) = seedSet s t := by ext z; simp [seedSet]
  rw [enc] at sf ⊢
  have h := pair_integer s t (outside s (by simp)) (outside t (by simp)) sf
  simp only [powerFor,baseFor,if_neg ne] at h
  have result := from_power (mis (Link (seedSet s t)) (legal (seedSet s t))) 820694 50
    (2*Fintype.card H) (by decide) (by decide) h
  have ex : ((2*Fintype.card H : ℕ) : ℝ)/(50:ℕ) = 5*(Fintype.card H : ℝ)/125 := by push_cast; ring
  rwa [ex] at result

theorem theorem_A (S : Finset (Ambient H)) (two : S.card = 2) (outside : ∀ s ∈ S, ¬band s)
    (sf : SumFree (S : Set (Ambient H))) : (mis (Link (S : Set (Ambient H))) (legal (S : Set (Ambient H))) : ℝ) ≤
      ((3:ℝ)^((50:ℝ)/3)/820694) * (820694:ℝ)^((5*(Fintype.card H : ℝ))/125) := by
  apply (theorem_A_strong S two outside sf).trans
  apply le_mul_of_one_le_left (by positivity)
  have h := from_power 820694 3 3 50 (by decide) (by decide) (by decide)
  norm_num at h ⊢
  linarith

/-- The common bound for zero, one or two seeds, without an additive constant. -/
theorem at_most_two (S : Finset (Ambient H)) (small : S.card ≤ 2) (outside : ∀ s ∈ S, ¬band s)
    (sf : SumFree (S : Set (Ambient H))) :
    (mis (Link (S : Set (Ambient H))) (legal (S : Set (Ambient H))) : ℝ) ≤
        (3:ℝ)^((Fintype.card H : ℝ)/2) := by
  classical
  have cases : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases cases with zero | one | two
  · have se := Finset.card_eq_zero.mp zero
    subst S
    let d := legal (∅ : Set (Ambient H))
    have only : family (Link (∅ : Set (Ambient H))) d ⊆ {d} := by
      intro I hi
      have h := mem_family.mp hi
      apply mem_singleton.mpr
      apply Finset.Subset.antisymm h.1
      intro x hx
      apply (member_iff h _).2 ⟨hx,?_⟩
      simp [Link,raw]
    have a : mis (Link (∅ : Set (Ambient H))) d ≤ 1 := by simpa [mis] using card_le_card only
    simp only [Finset.coe_empty]
    exact (show (mis (Link (∅ : Set (Ambient H))) d : ℝ) ≤ 1 by exact_mod_cast a).trans
      (Real.one_le_rpow (by norm_num) (by positivity))
  · obtain ⟨s,rfl⟩ := Finset.card_eq_one.mp one
    have os := outside s (by simp)
    have enc : (({s} : Finset (Ambient H)) : Set (Ambient H)) = seedSet s s := by ext z; simp [seedSet]
    rw [enc] at sf ⊢
    have h := pair_integer s s os os sf
    simp only [powerFor,baseFor,if_pos rfl] at h
    have result := from_power (mis (Link (seedSet s s)) (legal (seedSet s s))) 3 4
      (2*Fintype.card H) (by decide) (by decide) h
    have ex : ((2*Fintype.card H : ℕ) : ℝ)/(4:ℕ) = (Fintype.card H : ℝ)/2 := by push_cast; ring
    rwa [ex] at result
  · apply (theorem_A_strong S two outside sf).trans
    have base := from_power 820694 3 2 25 (by decide) (by decide) numerical_margin.1.le
    change (820694:ℝ) ≤ (3:ℝ)^((25:ℝ)/2) at base
    have b := Real.rpow_le_rpow (show (0:ℝ) ≤ 820694 by norm_num) base
      (show 0 ≤ 5*(Fintype.card H:ℝ)/125 by positivity)
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)] at b
    convert b using 1
    congr 1
    ring

theorem common_paper_bound (S : Finset (Ambient H)) (small : S.card ≤ 2)
    (outside : ∀ s ∈ S, ¬band s) (sf : SumFree (S : Set (Ambient H))) :
    (mis (Link (S : Set (Ambient H))) (legal (S : Set (Ambient H))) : ℝ) ≤
        (3:ℝ)^(5*(Fintype.card H : ℝ)/10+25/6) := by
  exact (at_most_two S small outside sf).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

end Sumfree.Pair
