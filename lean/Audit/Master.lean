import Audit.CubeCases

namespace Audit.Master
open Finset Sumfree Fingerprint Potential GraphMeasure Subcubic CubeCases
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop)

def factor (b : ℝ) (d : ℕ) :=
  (3:ℝ)^(-(1/3+b*(1-d)))+
  (3:ℝ)^(-(((d:ℝ)+1)/3+b*(d+1-(d:ℝ)^2)))

theorem master (sym : Symmetric r) (irr : Irreflexive r) {D : ℕ} {b : ℝ}
    (b0 : 0≤b) (b1 : b≤1/36) (scalar : ∀ d,4≤d → d≤D → factor b d ≤ 1)
    (s : Finset V) (cap : ∀ x∈s,(neighbors r s x).card≤D) :
    (mis r s:ℝ) ≤ (3:ℝ)^(mu r b s) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    have inductionStep : Induction r b s := by
      intro t ts
      have sub := (Finset.ssubset_iff_subset_ne.mp ts).1
      exact ih _ ts (fun x hx => (degree_mono r sub x).trans (cap x (sub hx)))
    by_cases low : ∀ x∈s,(neighbors r s x).card≤3
    · exact step r sym irr inductionStep b0 b1 low
    push_neg at low
    obtain ⟨y,ys,ylarge⟩ := low
    obtain ⟨x,xs,top⟩ := s.exists_max_image (fun u => (neighbors r s u).card) ⟨y,ys⟩
    let d := (neighbors r s x).card
    let t := closed r s x
    have closedSet : t=insert x (neighbors r s x) := by
      ext u; simp only [t,mem_closed,mem_insert,neighbors,mem_filter]
      constructor
      · rintro ⟨us,h|h⟩
        · exact Or.inl h
        · exact Or.inr ⟨us,sym h⟩
      · rintro (rfl|⟨us,h⟩)
        · exact ⟨xs,Or.inl rfl⟩
        · exact ⟨us,Or.inr (sym h)⟩
    have nonloop : x∉neighbors r s x := fun h => irr x (mem_filter.mp h).2
    have size : t.card=d+1 := closed_card r sym irr xs
    have adj : neighbors r (neighbors r s x) x=neighbors r s x := by
      ext z; simp only [neighbors,mem_filter,and_assoc,and_self]
    have v : 2*d ≤ volume r t := by
      rw [closedSet,volume_insert r sym irr nonloop,adj]
      omega
    have subset : t⊆s := fun _ h => (mem_closed.mp h).1
    have inside : x∈t := mem_closed.mpr ⟨xs,Or.inl rfl⟩
    have strict (u : Finset V) (hit : x∈u) : s\u⊂s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun eq => (mem_sdiff.mp (eq.symm ▸ xs)).2 hit⟩
    have cl : Clique r {x} := by
      intro a ha z hz ne; exact (ne ((mem_singleton.mp ha).trans (mem_singleton.mp hz).symm)).elim
    have single : volume r {x}=0 := by simpa using clique_volume r irr cl
    have skip : (mis r (s\{x}):ℝ) ≤ (3:ℝ)^(-(1/3+b*(1-d)))*(3:ℝ)^(mu r b s) := by
      apply ratio r (inductionStep _ (strict _ (mem_singleton_self x))) _ le_rfl
      have c := drop r sym (singleton_subset_iff.mpr xs) (fun u hu => top u ((singleton_subset_iff.mpr xs) hu)) b0
      simpa only [single,card_singleton,Nat.cast_one,Nat.cast_zero,zero_div,mul_one,sub_zero] using c
    have sel : (mis r (s\t):ℝ) ≤ (3:ℝ)^(-(((d:ℝ)+1)/3+b*(d+1-(d:ℝ)^2)))*(3:ℝ)^(mu r b s) := by
      apply ratio r (inductionStep _ (strict _ inside)) _ le_rfl
      have c := drop r sym subset (fun u hu => top u (subset hu)) b0
      rw [size,Nat.cast_add,Nat.cast_one] at c
      have vr : (2:ℝ)*d ≤ volume r t := by exact_mod_cast v
      apply le_trans _ c
      apply add_le_add_left (mul_le_mul_of_nonneg_left _ b0)
      nlinarith
    have num := scalar d (ylarge.trans_le (top y ys)) (cap x xs)
    have br : (mis r s:ℝ) ≤ (mis r (s\{x}):ℝ)+mis r (s\t) := by exact_mod_cast branch r s x
    apply br.trans ((add_le_add skip sel).trans _)
    rw [←add_mul]
    exact (mul_le_mul_of_nonneg_right num (Real.rpow_nonneg (by norm_num) _)).trans_eq (one_mul _)

end
end Audit.Master
