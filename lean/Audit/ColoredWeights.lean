import Audit.Colored

namespace Audit.Colored
noncomputable section

def base := Real.sqrt 3
theorem base_pos : 0<base := Real.sqrt_pos.mpr (by norm_num)
theorem base_sq : base^2=3 := Real.sq_sqrt (by norm_num)
theorem base_ge : 3/2≤base := by apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr; norm_num
theorem base_upper : base≤7/4 := by apply (Real.sqrt_le_left (by norm_num)).mpr; norm_num
theorem base_one : (1:ℝ)≤base := by linarith [base_ge]

theorem exponent_decay (k c q n : ℕ) (start : 2≤q+k) (h : q≤n) :
    ((n:ℝ)+k)/base^(n+c) ≤ ((q:ℝ)+k)/base^(q+c) := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    apply le_trans _ ih
    have le : (2:ℝ)≤(n:ℝ)+k := by exact_mod_cast (by omega : 2≤n+k)
    have p : 0<base^(n+c) := pow_pos base_pos _
    rw [show n+1+c=(n+c)+1 by omega,pow_succ,Nat.cast_succ]
    apply (div_le_div_iff₀ (mul_pos p base_pos) p).mpr
    calc
      ((n:ℝ)+1+k)*base^(n+c) ≤ (((n:ℝ)+k)*base)*base^(n+c) := by
        apply mul_le_mul_of_nonneg_right _ p.le
        nlinarith only [mul_le_mul_of_nonneg_left base_ge (show (0:ℝ)≤n+k by positivity),le]
      _ = _ := by ring

theorem pow_le_div {M X : ℝ} (nonneg : 0≤M) {N t j : ℕ}
    (budget : t+j≤N) (h : X≤base^t) (amount : M=base^N) : X≤M/base^j := by
  apply (le_div_iff₀ (pow_pos base_pos j)).mpr
  apply (mul_le_mul_of_nonneg_right h (pow_nonneg base_pos.le _)).trans
  rw [←pow_add,amount]
  exact pow_le_pow_right₀ base_one budget

theorem leaf_weight {d : ℕ} (lo : 1≤d) :
    1/base^2+((d:ℝ)+1)/base^(d+1) ≤ 1 := by
  have h := exponent_decay 1 1 1 d (by decide) lo
  norm_num only [Nat.cast_one,Nat.reduceAdd] at h
  rw [base_sq] at h ⊢
  linarith

theorem missing_weight {d : ℕ} (lo : 2≤d) :
    1/base+(d:ℝ)/base^(d+1) ≤ 1 := by
  have h := exponent_decay 0 1 2 d (by decide) lo
  norm_num only [Nat.cast_zero,add_zero,Nat.cast_ofNat,Nat.reduceAdd] at h
  apply le_trans (add_le_add_left h _)
  rw [show base^3=3*base by rw [pow_succ,base_sq]]
  have p := base_pos
  have b : 1/base=base/3 := (div_eq_div_iff p.ne' (by norm_num)).mpr (by nlinarith only [base_sq])
  have c : 2/(3*base)=2*base/9 := (div_eq_div_iff (by positivity) (by norm_num)).mpr (by nlinarith only [base_sq])
  rw [b,c]
  linarith only [base_upper]

theorem red_weight {d : ℕ} (lo : 2≤d) :
    1/base+1/base^(d+1)+(d:ℝ)/base^(d+2) ≤ 1 := by
  have h := exponent_decay 0 2 2 d (by decide) lo
  norm_num only [Nat.cast_zero,add_zero,Nat.cast_ofNat,Nat.reduceAdd] at h
  have g : 1/base^(d+1)≤1/base^3 := one_div_le_one_div_of_le (pow_pos base_pos _)
    (pow_le_pow_right₀ base_one (by omega))
  apply le_trans (add_le_add (add_le_add_left g _) h)
  rw [show base^3=3*base by rw [pow_succ,base_sq],show base^4=9 by nlinarith only [base_sq,congrArg (·^2) base_sq]]
  have p := base_pos
  have b : 1/base=base/3 := (div_eq_div_iff (by positivity) (by norm_num)).mpr (by nlinarith only [base_sq])
  have c : 1/(3*base)=base/9 := (div_eq_div_iff (by positivity) (by norm_num)).mpr (by nlinarith only [base_sq])
  rw [b,c]
  linarith only [base_upper]

end
end Audit.Colored
