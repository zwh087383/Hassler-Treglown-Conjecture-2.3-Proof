import Audit.Entropy
import Mathlib.Tactic.NormNum

open Finset
namespace Audit.Entropy
noncomputable section
variable {O K X : Type*} [Fintype O] [Fintype K] [AddCommGroup K] [DecidableEq K] [Fintype X]

/-- Shearer's cover and the local weighted estimate, on actual translates
    of a list of distinct offsets. The weight is zero off the allowed support. -/
theorem translated_estimate {d : ℕ}
    (t : Fin d → K) (ht : Function.Injective t) (z : O → K → X) (inj : Function.Injective z)
    (w : (Fin d → X) → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hw : ∀ a, 0 ≤ w a) (total : ∑ a, w a ≤ Z)
    (hit : ∀ y o, 0 < w (fun i => z o (y+t i)))
    (balance : ∀ y, ∑ o, Real.log (w (fun i => z o (y+t i))) = 0) :
    d * (Fintype.card O * Real.log (Fintype.card O)) ≤
      Fintype.card K * (Fintype.card O * Real.log Z) := by
  classical
  let D (y : K) := univ.image fun i => y+t i
  have regular (x : K) : (univ.filter fun y => x∈D y).card=d := by
    have eq : (univ.filter fun y => x∈D y) = univ.image (fun i => x-t i) := by
      ext y
      simp only [mem_filter,mem_univ,true_and,D,mem_image]
      constructor
      · rintro ⟨i,h⟩; exact ⟨i,sub_eq_iff_eq_add.mpr h.symm⟩
      · rintro ⟨i,h⟩; exact ⟨i,(sub_eq_iff_eq_add.mp h).symm⟩
    rw [eq,card_image_of_injective]
    · simp
    · intro a b e; apply ht; exact sub_right_injective e
  have localBound (y : K) : info (obs z (D y)) ≤ Fintype.card O * Real.log Z := by
    let read (o : O) (i : Fin d) := z o (y+t i)
    have same : info (obs z (D y)) = info read := by
      apply info_congr
      intro a b; rw [obs_eq,funext_iff]
      simp [D,read]
    rw [same]
    exact weighted_bound read w Z hZ hw (hit y) total (balance y)
  have whole : info (obs z univ) = Fintype.card O * Real.log (Fintype.card O) := by
    apply info_inj
    intro a b h
    apply inj; funext x; exact (obs_eq z _ _ _).mp h x (mem_univ _)
  have cover := shearer z D d regular univ
  simp only [whole,univ_inter] at cover
  have sumBound := sum_le_sum (s:=univ) (fun y _ => localBound y)
  simp only [sum_const,card_univ,nsmul_eq_mul] at sumBound
  exact cover.trans sumBound

theorem translated_power {d : ℕ} (hd : 0 < d)
    (t : Fin d → K) (ht : Function.Injective t) (z : O → K → X) (inj : Function.Injective z)
    (w : (Fin d → X) → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hw : ∀ a, 0 ≤ w a) (total : ∑ a, w a ≤ Z)
    (hit : ∀ y o, 0 < w (fun i => z o (y+t i)))
    (balance : ∀ y, ∑ o, Real.log (w (fun i => z o (y+t i))) = 0) :
    (Fintype.card O : ℝ)^d ≤ Z^(Fintype.card K) := by
  by_cases empty : Fintype.card O=0
  · simp [empty,hd.ne',pow_nonneg hZ.le]
  have co : (0:ℝ) < Fintype.card O := by exact_mod_cast Nat.pos_of_ne_zero empty
  have estimate := translated_estimate t ht z inj w Z hZ hw total hit balance
  apply (Real.log_le_log_iff (pow_pos co _) (pow_pos hZ _)).mp
  rw [Real.log_pow,Real.log_pow]
  apply le_of_mul_le_mul_left _ co
  linarith only [estimate]

theorem below_target {m d q : ℕ} (_hd : 0 < d) (hq : 0 < q) {Z : ℝ}
    (pos : 0 < Z) (limit : Z < 3^d) (witness : (m:ℝ)^d ≤ Z^q) : m < 3^q := by
  by_contra! bad
  have hx : ((3:ℝ)^q)^d ≤ (m:ℝ)^d := pow_le_pow_left₀ (by positivity) (by exact_mod_cast bad) _
  have hy := pow_lt_pow_left₀ limit pos.le hq.ne'
  rw [← pow_mul] at hx hy
  rw [Nat.mul_comm q d] at hx
  linarith

end
end Audit.Entropy
