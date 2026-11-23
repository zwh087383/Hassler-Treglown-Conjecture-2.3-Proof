import Sumfree.Bounds

namespace Sumfree
open Real

/-- The last step of Theorem A, with every dependency in the hypotheses.
    t counts the opposite pairs of nonzero cosets, so h = q(2t+1). -/
theorem two_seed_exponent (q t c g : ℕ) (qle : q ≤ 25)
    (core : (c : ℝ) ≤ (3 : ℝ)^((2:ℝ)*q/3))
    (generic : (g : ℝ)^25 ≤ (820694 : ℝ)^(2*q)) :
    (c : ℝ)*g^t ≤ ((3:ℝ)^((50:ℝ)/3)/820694) * (820694:ℝ)^(((q:ℝ)*(2*t+1))/25) := by
  have gbound : (g : ℝ) ≤ (820694 : ℝ)^((2:ℝ)*q/25) := by
    apply le_of_not_gt
    intro h
    have bad := pow_lt_pow_left₀ h (n := 25) (by positivity) (by decide)
    rw [← Real.rpow_natCast ((820694 : ℝ)^_), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 820694)] at bad
    have e : ((2:ℝ)*q/25)*(25:ℕ) = (↑(2*q : ℕ) : ℝ) := by push_cast; ring
    rw [e,Real.rpow_natCast] at bad
    linarith
  have base : (820694 : ℝ)^((1:ℝ)/25) ≤ (3:ℝ)^((2:ℝ)/3) := by
    by_contra! bad
    have b := pow_lt_pow_left₀ bad (n := 75) (by positivity) (by decide)
    rw [← Real.rpow_natCast ((3:ℝ)^_), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
        ← Real.rpow_natCast ((820694:ℝ)^_), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 820694)] at b
    norm_num at b
  have adjust := Real.rpow_le_rpow (by positivity) base
      (show (0:ℝ) ≤ 25-q by exact sub_nonneg.mpr (by exact_mod_cast qle))
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 820694),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)] at adjust
  have combined := mul_le_mul core (pow_le_pow_left₀ (by positivity) gbound t) (by positivity) (by positivity)
  apply combined.trans
  rw [← Real.rpow_natCast ((820694:ℝ)^_), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 820694)]
  have eq3 : (50:ℝ)/3 = 2*q/3 + (2/3)*(25-q) := by ring
  have eqA : ((q:ℝ)*(2*t+1))/25 = (2*q/25)*t + 1 - (1/25)*(25-q) := by ring
  rw [eq3,eqA,Real.rpow_add (by norm_num : (0:ℝ) < 3),Real.rpow_sub (by norm_num : (0:ℝ) < 820694),
      Real.rpow_add (by norm_num : (0:ℝ) < 820694),Real.rpow_one]
  let X := (3:ℝ)^(2*(q:ℝ)/3)
  let Y := (820694:ℝ)^((2*(q:ℝ)/25)*(t:ℝ))
  let A := (820694:ℝ)^((1/25 : ℝ)*(25-(q:ℝ)))
  let B := (3:ℝ)^((2/3 : ℝ)*(25-(q:ℝ)))
  change X*Y ≤ (X*B/820694)*(Y*820694/A)
  have ha : 0 < A := by dsimp [A]; positivity
  have hxy : 0 ≤ X*Y := by dsimp [X,Y]; positivity
  calc
    X*Y = X*Y*A/A := (mul_div_cancel_right₀ _ ha.ne').symm
    _ ≤ X*Y*B/A := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left adjust hxy) ha.le
    _ = _ := by ring

theorem numerical_margin : (820694:ℕ)^2 < 3^25 ∧ (220:ℕ)^5 < 820694^2 ∧
    (2:ℕ)^25 < 820694^2 ∧ (6727:ℕ)*122 = 820694 := by decide

theorem strict_log_margin : Real.log 820694 / Real.log 3 / 125 < (1:ℝ)/10 := by
  have g : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have n : (820694:ℝ)^2 < (3:ℝ)^25 := by norm_num
  have h := Real.log_lt_log (by positivity) n
  rw [Real.log_pow,Real.log_pow] at h
  norm_num at h
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 125)).2
  apply (div_lt_iff₀ g).2
  linarith
end Sumfree
