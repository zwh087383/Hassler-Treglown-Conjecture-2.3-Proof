import Audit.Assembly

namespace Audit.Limit
open Assembly Blocks Filter
open scoped Topology

/-- The normalized logarithm in the manuscript is written with natural logarithms.
    Division by log 3 changes the base to three. -/
noncomputable def normalized (k : ℕ) :=
  Real.log (Asymptotic.fmax k)/((5:ℝ)^k*Real.log 3)

private theorem inv_order : Tendsto (fun k => (order k)⁻¹) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat (f:=fun k : ℕ => ((5:ℝ)^k)⁻¹) 1).mpr
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<5))

theorem limit_of_band (covers : SparseCovers) (structural : LargeSetStructure) (bandBound : StandardBand) :
    Tendsto normalized atTop (𝓝 (1/10:ℝ)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have np (k : ℕ) : 0<order k := by dsimp [order]; positivity
  have lp : 0<Real.log 3 := Real.log_pos (by norm_num)
  have l2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have lo (k : ℕ) := Asymptotic.lower (k+1) (by omega)
  have lbound (k : ℕ) : 1/10-1/2*(order k)⁻¹ ≤ normalized (k+1) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _) (lo k)
    rw [Real.log_rpow (by norm_num)] at h
    change _ ≤ Real.log (Asymptotic.fmax (k+1))/(order k*Real.log 3)
    apply (le_div_iff₀ (mul_pos (np k) lp)).mpr
    calc
      _ = (order k/10-1/2)*Real.log 3 := by field_simp [(np k).ne']; ring
      _ ≤ _ := h
  let β := 2*Real.log 2/Real.log 3
  have bp : 0<β := by dsimp [β]; positivity
  have hi (a : ℝ) (ap : 0<a) (unit : a≤1) :
      ∀ᶠ k in atTop, normalized (k+1) ≤ 1/10+a*β+errorConstant*(order k)⁻¹ := by
    filter_upwards [upper_with_band covers structural bandBound ap unit] with k h
    have fp := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _).trans_le (lo k)
    have l := Real.log_le_log fp h
    rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne'
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _).ne',
        Real.log_rpow (by norm_num),Real.log_rpow (by norm_num)] at l
    change Real.log (Asymptotic.fmax (k+1))/(order k*Real.log 3) ≤ _
    apply (div_le_iff₀ (mul_pos (np k) lp)).mpr
    apply le_trans l
    apply le_of_eq
    dsimp only [β]
    field_simp [(np k).ne',lp.ne']
    ring
  apply tendsto_order.mpr
  constructor
  · intro x below
    have t : Tendsto (fun k => (1/10:ℝ)-1/2*(order k)⁻¹) atTop (𝓝 (1/10)) := by
      simpa using (tendsto_const_nhds (x:=(1/10:ℝ))).sub (inv_order.const_mul (1/2:ℝ))
    filter_upwards [t.eventually_const_lt below] with k h using h.trans_le (lbound k)
  · intro x above
    let a := min 1 ((x-1/10)/(2*β))
    have ap : 0<a := lt_min (by norm_num) (div_pos (sub_pos.mpr above) (by positivity))
    have a1 : a≤1 := min_le_left .. 
    have small := (le_div_iff₀ (show 0<2*β by positivity)).mp (min_le_right 1 ((x-1/10)/(2*β)))
    change a*(2*β)≤x-1/10 at small
    have margin : 1/10+a*β<x := by linarith
    have t : Tendsto (fun k => 1/10+a*β+errorConstant*(order k)⁻¹) atTop (𝓝 (1/10+a*β)) := by
      simpa using (tendsto_const_nhds (x:=1/10+a*β)).add (inv_order.const_mul errorConstant)
    filter_upwards [hi a ap a1,t.eventually_lt_const margin] with k h j using h.trans_lt j

theorem limit_of_inputs (covers : SparseCovers) (structural : LargeSetStructure) (gb : BlockBound) :
    Tendsto normalized atTop (𝓝 (1/10:ℝ)) :=
  limit_of_band covers structural (fun _ _ => all_seeds gb)

end Audit.Limit
