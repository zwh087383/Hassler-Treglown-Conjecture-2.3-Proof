import Audit.MixedNeighbors
import Audit.Defects

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

theorem signed_card (s : Finset (Pt (Space k))) (out : Disjoint s (full _)) :
    (signed s).card=(seedLayer (forward s) 0).card+2*(seedLayer (forward s) 1).card := by
  have stable (x : Pt (Space k)) : x∈signed s ↔ -x∈signed s := by simp [or_comm]
  have excl : Disjoint (signed s) (full _) := by
    apply disjoint_left.mpr
    intro x hx band
    rcases mem_signed.mp hx with h|h
    · exact disjoint_left.mp out h band
    · have ar : ∀ a : Fin 5, (a=2 ∨ a=3) → -a=2 ∨ -a=3 := by decide
      exact disjoint_left.mp out h (mem_full.mpr (ar _ (mem_full.mp band)))
  have eq (j : Fin 5) (hj : j=0 ∨ j=1) : seedLayer (forward s) j=seedLayer (signed s) j := by
    ext x
    simp only [seedLayer,forward,mem_filter]
    aesop
  have flip : (seedLayer (signed s) 1).image Neg.neg=seedLayer (signed s) 4 := by
    ext x
    constructor
    · intro h; obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      obtain ⟨ys,yh⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨(stable _).mp ys,by change -y.1=4; rw [yh]; decide⟩
    · intro h; obtain ⟨xs,xh⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨-x,mem_filter.mpr ⟨(stable _).mp xs,by change -x.1=1; rw [xh]; decide⟩,neg_neg _⟩
  have count := congrArg Finset.card flip
  rw [card_image_of_injective _ neg_injective] at count
  rw [eq 0 (Or.inl rfl),eq 1 (Or.inr rfl)]
  have size := (profiles (signed s) excl).1
  omega

theorem at_most_one_unpaired (sf : Free s) (out : Disjoint s (full _))
    (small : (signed s).card≤s.card+1) : rankCount s≤3^Fintype.card (Space k) := by
  let core := s.filter fun x => -x∈s
  have sub : core⊆s := filter_subset ..
  have stable (x : Pt (Space k)) : x∈core ↔ -x∈core := by simp [core,and_comm]
  have flip : (s\core).image Neg.neg = signed s\s := by
    ext x
    constructor
    · intro h; obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      obtain ⟨ys,unpaired⟩ := mem_sdiff.mp hy
      exact mem_sdiff.mpr ⟨(mem_signed.mpr (Or.inr (by simpa using ys))),fun hn => unpaired (mem_filter.mpr ⟨ys,hn⟩)⟩
    · intro h; obtain ⟨xs,n⟩ := mem_sdiff.mp h
      have ns := (mem_signed.mp xs).resolve_left n
      exact mem_image.mpr ⟨-x,mem_sdiff.mpr ⟨ns,fun t => n (by simpa using (mem_filter.mp t).2)⟩,neg_neg _⟩
  have flipc := congrArg Finset.card flip
  rw [card_image_of_injective _ neg_injective] at flipc
  have size := card_sdiff_add_card_eq_card (show s⊆signed s from fun _ h => mem_signed.mpr (Or.inl h))
  have delta : (s\core).card≤1 := by omega
  by_cases empty : s\core=∅
  · have same : s=core := Subset.antisymm (sdiff_eq_empty_iff_subset.mp empty) sub
    have nz : 0∉core := by rw [←same]; exact fun h => sf 0 h 0 h 0 h (zero_add _)
    simpa only [same,Defects.signedSeed,Bool.false_eq_true,if_false] using
      Defects.nonzero core stable nz false false 0 0 (by simp)
  · obtain ⟨z,hz⟩ := card_eq_one.mp (show (s\core).card=1 by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega)
    have same : insert z core=s := by
      have eq := sdiff_union_of_subset sub
      rw [hz] at eq
      simpa using eq
    rw [←same] at sf out ⊢
    exact Defects.one_defect core stable z sf out

private def goodDegrees (z p q Z U : ℕ) : Prop :=
  let D := Z+U+z+max p q
  let l := Z+U+z+min p q
  10≤l ∨ (D≤8 ∧ 15≤D+l) ∨ (D≤10 ∧ 17≤D+l) ∨ (D≤12 ∧ 18≤D+l) ∨
    (12≤D ∧ D≤2*l) ∨ (D=9 ∧ 15≤D+l ∧ 8≤(U+z)*(D-l)) ∨ Z+2*U≤6

private instance (z p q Z U : ℕ) : Decidable (goodDegrees z p q Z U) := by
  unfold goodDegrees; infer_instance

private theorem table : ∀ z p q : Fin 6, ∀ Z U : Fin 10,
    (z:ℕ)+p+q=5 → 1≤(z:ℕ) → 2≤(Z:ℕ) → (p:ℕ)≤U → (q:ℕ)≤U →
    goodDegrees z p q Z U := by native_decide

theorem clean_five (sf : Free s) (out : Disjoint s (full _)) (size : s.card=5)
    (mixed : (seedLayer s 0).Nonempty) (clean : NoZeroSum s) : rankCount s≤3^(5^k) := by
  let z := (seedLayer s 0).card
  let p := (seedLayer s 1).card
  let q := (seedLayer s 4).card
  let Z := (seedLayer (forward s) 0).card
  let U := (seedLayer (forward s) 1).card
  obtain ⟨sc,pu,qu,h2,h3⟩ := profiles s out
  change s.card=z+p+q at sc
  change p≤U at pu
  change q≤U at qu
  change headDegree s 2=Z+U+z+q at h2
  change headDegree s 3=Z+U+z+p at h3
  have low : minimumDegree s=Z+U+z+min p q := by unfold minimumDegree; omega
  have high : maximumDegree s=Z+U+z+max p q := by unfold maximumDegree; omega
  have sum : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 := max_add_min ..
  suffices h : rankCount s≤3^Fintype.card (Space k) by simpa [Space,Field5] using h
  have general (h : 10≤minimumDegree s) := MasterTable.two_degree s sf out h (mixed_profile s sf out mixed).2
  by_cases large : 10≤minimumDegree s
  · exact general large
  obtain ⟨x,hx⟩ := mixed
  have zpos : 0<z := card_pos.mpr ⟨x,hx⟩
  have zTwo : 2≤Z := zero_gain sf (mem_filter.mp hx).1 (mem_filter.mp hx).2
  have choice := table ⟨z,by omega⟩ ⟨p,by omega⟩ ⟨q,by omega⟩ ⟨Z,by omega⟩ ⟨U,by omega⟩
    (show z+p+q=5 from sc.symm.trans size) zpos zTwo pu qu
  change goodDegrees z p q Z U at choice
  unfold goodDegrees at choice
  rw [←low,←high] at choice
  have tf := triangle_free sf clean
  rcases choice with h|⟨c,av⟩|h|h|h|⟨c,av,ns⟩|small
  · exact general h
  · exact within_quarter _ sf (TriangleEight.dense (within_sym _) (within_irr _) tf _
      (fun y hy => (within_cap sf y hy).trans c) (two_degree_sum s sf 15 (by omega)))
  · exact neither_high sf tf (Or.inl ⟨h.1,by omega⟩)
  · exact neither_high sf tf (Or.inr (Or.inl ⟨h.1,by omega⟩))
  · exact neither_high sf tf (Or.inr (Or.inr h))
  · apply within_quarter _ sf
    apply TriangleEight.capNine (within_sym _) (within_irr _) tf _ (fun y hy => (within_cap sf y hy).trans c.le) _
      (two_degree_sum s sf 15 (by omega))
    intro y hy d
    have hd := (within_degree sf hy).symm.trans (d.trans c.symm)
    have total := high_sum sf hy hd
    change _ + (U+z)*_ ≤ _ at total
    rw [c] at total ns
    change (∑ w∈Fingerprint.neighbors (within s) Raw.domain y, (Fingerprint.neighbors (within s) Raw.domain w).card)≤73
    omega
  · apply at_most_one_unpaired sf out
    rw [signed_card s out,size]
    exact small

end
end Audit.Mixed
