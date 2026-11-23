import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Audit.Global
open Filter
open scoped Topology

theorem fingerprint_remainder {δ Δ U N : ℝ} (hδ : 4096 ≤ δ) (hΔ : Δ ≤ 2*δ)
    (u0 : 0 ≤ U) (un : U ≤ N) (edges : (δ-511)*U ≤ Δ*(N-U)) :
    U ≤ (8192/11777)*N := by
  have combined := edges.trans (mul_le_mul_of_nonneg_right hΔ (sub_nonneg.mpr un))
  have den : 0 < 3*δ-511 := by linarith
  have res : U ≤ (2*δ*N)/(3*δ-511) := (le_div_iff₀ den).mpr (by linarith only [combined])
  have coeff : 2*δ/(3*δ-511) ≤ 8192/11777 := (div_le_iff₀ den).mpr (by linarith)
  calc
    U ≤ _ := res
    _ = 2*δ/(3*δ-511)*N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff (u0.trans un)

theorem large_strict_margin : (8192/35331 : ℚ)+8/513 = 1/4-61409/24166404 ∧
    (8192/35331 : ℚ)+8/513 < 1/4 := by norm_num

theorem core_exponent {h q : ℝ} (pos : 0 < q) :
    2*q/3 + q*((h/q-1)/2) = h/2+q/6 := by field_simp; ring

/-- The final analytic implication for n=5^k. Its two inequalities are
    explicit hypotheses so the theorem does not certify the global upper bound. -/
theorem main_squeeze (f : ℕ → ℕ) (err : ℕ → ℝ) (C : ℝ) (small : Tendsto err atTop (𝓝 0))
    (lower : ∀ᶠ k in atTop, (3:ℝ)^((5:ℝ)^k/10-1/2) ≤ f k)
    (upper : ∀ᶠ k in atTop, (f k:ℝ) ≤ (2:ℝ)^(err k*(5:ℝ)^k) * (3:ℝ)^((5:ℝ)^k/10+C)) :
    Tendsto (fun k => Real.log (f k)/((5:ℝ)^k*Real.log 3)) atTop (𝓝 (1/10)) := by
  let n (k : ℕ) := (5:ℝ)^k
  have np (k) : 0 < n k := pow_pos (by norm_num) _
  have lp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ni : Tendsto (fun k => (n k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<5))
  have base : Tendsto (fun _ : ℕ => (1/10:ℝ)) atTop (𝓝 (1/10)) := tendsto_const_nhds
  have tLo : Tendsto (fun k => 1/10-(1/2)*(n k)⁻¹) atTop (𝓝 (1/10 : ℝ)) := by
    simpa only [mul_zero,sub_zero] using base.sub (ni.const_mul (1/2 : ℝ))
  have tHi : Tendsto (fun k => 1/10+err k*(Real.log 2/Real.log 3)+C*(n k)⁻¹) atTop (𝓝 (1/10:ℝ)) := by
    simpa using (base.add
      (small.mul_const (Real.log 2/Real.log 3))).add (ni.const_mul C)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tLo tHi
  · filter_upwards [lower] with k hk
    have hl := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : 0<(3:ℝ)) _) hk
    rw [Real.log_rpow (by norm_num)] at hl
    change 1/10-1/2*(n k)⁻¹ ≤ Real.log (f k)/(n k*Real.log 3)
    apply (le_div_iff₀ (mul_pos (np k) lp)).mpr
    calc
      _ = (n k/10-1/2)*Real.log 3 := by field_simp [(np k).ne']; ring
      _ ≤ _ := hl
  · filter_upwards [lower,upper] with k hk hi
    have fp := (Real.rpow_pos_of_pos (by norm_num : 0<(3:ℝ)) _).trans_le hk
    have hl := Real.log_le_log fp hi
    rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : 0<(2:ℝ)) _).ne'
      (Real.rpow_pos_of_pos (by norm_num : 0<(3:ℝ)) _).ne',
      Real.log_rpow (by norm_num),Real.log_rpow (by norm_num)] at hl
    change Real.log (f k)/(n k*Real.log 3) ≤ 1/10+err k*(Real.log 2/Real.log 3)+C*(n k)⁻¹
    apply (div_le_iff₀ (mul_pos (np k) lp)).mpr
    calc
      _ ≤ _ := hl
      _ = _ := by change err k*n k*Real.log 2+(n k/10+C)*Real.log 3=_
                  field_simp [lp.ne',(np k).ne']; ring

end Audit.Global
