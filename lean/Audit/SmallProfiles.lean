import Audit.CrossProfiles

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

theorem even_zero (sf : Free s) : Even (seedLayer (forward s) 0).card := by
  let T := seedLayer (forward s) 0
  have mem (x : Pt (Space k)) : x∈T ↔ x∈signed s ∧ x.1=0 := by
    simp only [T,seedLayer,forward,mem_filter]
    tauto
  have closed {x : Pt (Space k)} (h : x∈T) : -x∈T := by
    obtain ⟨hs,hx⟩ := (mem _).mp h
    exact (mem _).mpr ⟨by simpa only [mem_signed,neg_neg,or_comm] using hs,by change -x.1=0; rw [hx,neg_zero]⟩
  have diff {x : Pt (Space k)} (h : x∈T) : x≠ -x := by
    intro e
    have f : ∀ b : Field5, b= -b → b=0 := by decide
    have eq : x=0 := Prod.ext (mem _ |>.mp h).2 (funext fun i => f _ (congrArg (fun v : Pt (Space k) => v.2 i) e))
    have nx : (0:Pt (Space k))∉s := fun a => sf 0 a 0 a 0 a (zero_add _)
    simpa [eq,nx] using (mem _ |>.mp h).1
  let index := Fintype.equivFin (Pt (Space k))
  let half := T.filter fun x => index x < index (-x)
  have split : half ∪ half.image Neg.neg=T := by
    ext x
    constructor
    · intro h
      rcases mem_union.mp h with z|z
      · exact (mem_filter.mp z).1
      · obtain ⟨v,hv,rfl⟩ := mem_image.mp z
        exact closed (mem_filter.mp hv).1
    · intro h
      rcases lt_or_gt_of_ne (fun e => diff h (index.injective e)) with lt|gt
      · exact mem_union_left _ (mem_filter.mpr ⟨h,lt⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨-x,mem_filter.mpr ⟨closed h,by simpa using gt⟩,neg_neg _⟩)
  have apart : Disjoint half (half.image Neg.neg) := by
    apply disjoint_left.mpr
    intro x hx hu
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hu
    have l : index y < index (-y) := (mem_filter.mp hy).2
    have r : index (-y) < index (- -y) := (mem_filter.mp hx).2
    rw [neg_neg] at r; exact (lt_asymm l r)
  exact ⟨half.card,by change T.card=_; rw [←split,card_union_of_disjoint apart,card_image_of_injective _ neg_injective]⟩

theorem signed_one (s : Finset (Pt (Space k))) :
    seedLayer (forward s) 1 = seedLayer s 1 ∪ (seedLayer s 4).image Neg.neg := by
  ext x
  constructor
  · intro h
    obtain ⟨hf,head⟩ := mem_filter.mp h
    rcases mem_signed.mp (mem_filter.mp hf).1 with a|a
    · exact mem_union_left _ (mem_filter.mpr ⟨a,head⟩)
    · have h4 : (-x).1=4 := by change -x.1=4; rw [head]; decide
      exact mem_union_right _ (mem_image.mpr ⟨-x,mem_filter.mpr ⟨a,h4⟩,neg_neg _⟩)
  · intro h
    have add {u : Pt (Space k)} (m : u∈signed s) (hd : u.1=1) : u∈seedLayer (forward s) 1 :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨m,Or.inr hd⟩,hd⟩
    rcases mem_union.mp h with a|a
    · exact add (mem_signed.mpr (Or.inl (mem_filter.mp a).1)) (mem_filter.mp a).2
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp a
      exact add (mem_signed.mpr (Or.inr (by simpa using (mem_filter.mp hu).1)))
        (by change -u.1=1; rw [(mem_filter.mp hu).2]; decide)

private def options (n z p q Z U : ℕ) : Prop :=
  let hi := max (Z+U+z+q) (Z+U+z+p)
  let lo := min (Z+U+z+q) (Z+U+z+p)
  (z=1 ∧ Z=2 ∧
    ((n=6 ∧ lo=9 ∧ ((hi=12 ∧ 6≤U+z) ∨ (hi=10 ∧ 5≤U+z))) ∨
     (n=5 ∧ ((p=2 ∧ q=2 ∧ U=3 ∧ hi=8 ∧ lo=8) ∨
             (p=2 ∧ q=2 ∧ U=4 ∧ hi=9 ∧ lo=9) ∨
             (((p=3 ∧ q=1) ∨ (p=1 ∧ q=3)) ∧ U=4 ∧ hi=10 ∧ lo=8)))))

private instance (n z p q Z U : ℕ) : Decidable (options n z p q Z U) := by unfold options; infer_instance

private def allowed (z p q m U : ℕ) : Prop :=
  (z+p+q=5 ∨ z+p+q=6) ∧ 0<z ∧ 0<p ∧ 0<q ∧ z<m+m ∧ p<U ∧ q<U ∧ U≤p+q ∧
  min (m+m+U+z+q) (m+m+U+z+p)<10

private instance (z p q m U : ℕ) : Decidable (allowed z p q m U) := by unfold allowed; infer_instance

private def validCell (z p q m U : ℕ) : Bool :=
  !decide (allowed z p q m U) || decide (options (z+p+q) z p q (m+m) U)

private theorem values : ∀ z p q : Fin 7, ∀ m : Fin 5, ∀ U : Fin 7,
    validCell z p q m U=true := by native_decide

/-- Actual crossing geometry and all remaining size-five and size-six degree pairs. -/
theorem small_bad (sf : Free s) (out : Disjoint s (full _)) (size : s.card=5 ∨ s.card=6)
    (bad : ¬NoZeroSum s) (low : minimumDegree s<10) :
    let z := (seedLayer s 0).card
    let p := (seedLayer s 1).card
    let q := (seedLayer s 4).card
    let U := (seedLayer (forward s) 1).card
    Crossing s ∧ z=1 ∧ (seedLayer (forward s) 0).card=2 ∧
      ((s.card=6 ∧ minimumDegree s=9 ∧
        ((maximumDegree s=12 ∧ 6≤U+z) ∨ (maximumDegree s=10 ∧ 5≤U+z))) ∨
       (s.card=5 ∧ ((p=2 ∧ q=2 ∧ U=3 ∧ maximumDegree s=8 ∧ minimumDegree s=8) ∨
                    (p=2 ∧ q=2 ∧ U=4 ∧ maximumDegree s=9 ∧ minimumDegree s=9) ∨
                    (((p=3 ∧ q=1) ∨ (p=1 ∧ q=3)) ∧ U=4 ∧ maximumDegree s=10 ∧ minimumDegree s=8)))) := by
  dsimp only
  obtain ⟨cnt,pu,qu,h2,h3⟩ := profiles s out
  have g := bad_cases sf out bad
  rcases g with many|cross
  · unfold minimumDegree at low
    omega
  have gains := crossing_gains sf cross
  obtain ⟨a,v,na,az,pv,qv⟩ := cross
  have pos0 := card_pos.mpr (show (seedLayer s 0).Nonempty from ⟨_,mem_filter.mpr ⟨az,rfl⟩⟩)
  have pos1 := card_pos.mpr (show (seedLayer s 1).Nonempty from ⟨_,mem_filter.mpr ⟨pv,rfl⟩⟩)
  have pos4 := card_pos.mpr (show (seedLayer s 4).Nonempty from ⟨_,mem_filter.mpr ⟨qv,rfl⟩⟩)
  have uBound : (seedLayer (forward s) 1).card ≤ (seedLayer s 1).card+(seedLayer s 4).card := by
    rw [signed_one]
    simpa only [card_image_of_injective _ neg_injective] using (card_union_le (seedLayer s 1) ((seedLayer s 4).image Neg.neg))
  obtain ⟨m,even⟩ := even_zero sf
  let z := (seedLayer s 0).card
  let p := (seedLayer s 1).card
  let q := (seedLayer s 4).card
  let U := (seedLayer (forward s) 1).card
  let Z := (seedLayer (forward s) 0).card
  change s.card=z+p+q at cnt
  change z<Z ∧ p<U ∧ q<U at gains
  change Z=m+m at even
  change U≤p+q at uBound
  change 0<z at pos0
  change 0<p at pos1
  change 0<q at pos4
  have d : min (m+m+U+z+q) (m+m+U+z+p)<10 := by
    change min (headDegree s 2) (headDegree s 3)<10 at low
    change headDegree s 2=Z+U+z+q at h2
    change headDegree s 3=Z+U+z+p at h3
    rwa [h2,h3,even] at low
  have ok : allowed z p q m U := ⟨cnt ▸ size,pos0,pos1,pos4,by omega,gains.2.1,gains.2.2,uBound,d⟩
  have valid := values ⟨z,by omega⟩ ⟨p,by omega⟩ ⟨q,by omega⟩ ⟨m,by omega⟩ ⟨U,by omega⟩
  change validCell z p q m U=true at valid
  have t : options (z+p+q) z p q (m+m) U := by
    simpa only [validCell,decide_eq_true ok,Bool.not_true,Bool.false_or,decide_eq_true_eq] using valid
  refine ⟨⟨a,v,na,az,pv,qv⟩,?_⟩
  change options (z+p+q) z p q (m+m) U at t
  unfold options at t
  rw [←even,←cnt] at t
  unfold minimumDegree maximumDegree
  rw [h2,h3]
  exact t

end
end Audit.Mixed
