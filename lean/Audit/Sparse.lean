import Audit.ContainerCover
import Audit.Assembly

namespace Audit.Sparse
open Finset ContainerStep ContainerCover Assembly Filter
open scoped Classical Topology
noncomputable section

/-- The same fingerprint threshold works in every dimension at a given accuracy. -/
theorem sparse_codes (γ : ℝ) (gp : 0<γ) :
    ∃ d : ℕ, 0<d ∧ ∀ (G : Type) [Fintype G],
      ((codes G d).card:ℝ) ≤ (2:ℝ)^(γ*Fintype.card G) := by
  let a := (2:ℝ)^(γ/2)
  have a1 : 1<a := Real.one_lt_rpow (by norm_num) (by positivity)
  let b := a-1
  have bp : 0<b := sub_pos.mpr a1
  obtain ⟨d,hd,hda⟩ := ((eventually_gt_atTop (0:ℕ)).and
    ((tendsto_pow_atTop_atTop_of_one_lt a1).eventually_ge_atTop b⁻¹)).exists
  refine ⟨d,hd,?_⟩
  intro G inst
  classical
  let n := Fintype.card G
  have room : 1≤a^d*b := (div_le_iff₀ bp).mp (by simpa only [one_div] using hda)
  have each (s : Finset G) (hs : s∈codes G d) : 1≤a^n*b^s.card := by
    have h := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) room s.card
    rw [one_pow,mul_pow,←pow_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ a1.le (mem_filter.mp hs).2) (pow_nonneg bp.le _))
  calc
    _ = ∑ _s ∈ codes G d, (1:ℝ) := by simp
    _ ≤ ∑ s ∈ codes G d, a^n*b^s.card := sum_le_sum each
    _ = a^n*∑ s∈codes G d,b^s.card := (mul_sum ..).symm
    _ ≤ a^n*∑ s ∈ (univ : Finset G).powerset,b^s.card := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans a1.le) _)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => pow_nonneg bp.le _)
    _ = a^n*a^n := by
      have h := sum_pow_mul_eq_add_pow b 1 (univ : Finset G)
      simp only [one_pow,mul_one,card_univ] at h
      rw [h,show b+1=a by dsimp [b]; ring]
    _ = _ := by
      rw [←mul_pow]
      have eq : a*a=(2:ℝ)^γ := by
        dsimp only [a]; rw [←Real.rpow_add (by norm_num)]; congr 1; ring
      rw [eq,←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]

theorem increasing_order : Tendsto order atTop atTop := by
  exact (tendsto_add_atTop_iff_nat 1).mpr
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<5))

/-- A direct qualitative container theorem for the groups of the manuscript. -/
theorem sparseCovers : SparseCovers := by
  intro η ηp δ δp
  obtain ⟨l,large⟩ := exists_nat_gt (1/δ)
  have lp : 0<l := by exact_mod_cast ((one_div_pos.mpr δp).trans large)
  have denom : 1 < (l:ℝ)*δ := (div_lt_iff₀ δp).mp large
  let m := 8*l
  have mp : 0<m := Nat.mul_pos (by decide) lp
  let γ := η/(4*m)
  have gp : 0<γ := div_pos ηp (by positivity)
  obtain ⟨d,dp,code⟩ := sparse_codes γ gp
  have factors : ∀ᶠ k : ℕ in atTop, (3:ℝ)^m ≤ (2:ℝ)^(η*order k/2) := by
    have inc : Tendsto (fun k => η*order k/2) atTop atTop := by
      simpa only [div_eq_mul_inv] using (increasing_order.const_mul_atTop ηp).atTop_mul_const
        (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    filter_upwards [inc.eventually_ge_atTop ((2*m:ℕ):ℝ)] with k hk
    apply le_trans _ (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hk)
    calc
      (3:ℝ)^m ≤ ((2:ℝ)^(2:ℕ))^m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
      _ = (2:ℝ)^((2*m:ℕ):ℝ) := by rw [Real.rpow_natCast,←pow_mul]
  filter_upwards [increasing_order.eventually_ge_atTop ((4*l*(4*l*d):ℕ):ℝ),
    increasing_order.eventually_ge_atTop ((d*(4*l*d):ℕ):ℝ), factors] with k h₁ h₂ constant
  rw [←total_order] at h₁ h₂
  obtain ⟨F,count,cover,light⟩ := finite_covers l d lp dp (by exact_mod_cast h₁ : 4*l*(4*l*d)≤Fintype.card (group k))
    (by exact_mod_cast h₂)
  refine ⟨F,?_,fun i hi => cover i (Link.mem_maximalSets.mp hi).2.1,?_⟩
  · let n := order k
    let h := ((codes (group k) d).card:ℝ)
    let U := (2:ℝ)^(γ*n)
    have h_le : h ≤ U := by simpa only [total_order] using code (group k)
    have up : 1 ≤ U := Real.one_le_rpow (by norm_num) (mul_nonneg gp.le (by dsimp [n,order]; positivity))
    have rate_le : (rate (group k) d:ℝ) ≤ 3*(U*U) := by
      dsimp only [rate]; push_cast
      change 1+h+h^2 ≤ 3*(U*U)
      have h0 : 0≤h := Nat.cast_nonneg _
      nlinarith only [h_le,up,mul_self_le_mul_self h0 h_le,mul_le_mul_of_nonneg_left up (zero_le_one.trans up)]
    have realCount : (F.card:ℝ) ≤ (rate (group k) d:ℝ)^m := by exact_mod_cast count
    apply realCount.trans
    calc
      _ ≤ (3*(U*U))^m := pow_le_pow_left₀ (Nat.cast_nonneg _) rate_le _
      _ = (3:ℝ)^m*(U*U)^m := mul_pow .. 
      _ ≤ (2:ℝ)^(η*n/2)*(U*U)^m := mul_le_mul_of_nonneg_right constant (by positivity)
      _ = _ := by
        dsimp only [U]
        rw [←Real.rpow_add (by norm_num),←Real.rpow_natCast,←Real.rpow_mul (by norm_num),
          ←Real.rpow_add (by norm_num)]
        congr 1
        change η*n/2+(γ*n+γ*n)*m=η*n
        dsimp only [γ]; field_simp [Nat.cast_ne_zero.mpr mp.ne']; ring
  · intro c hc
    have bound : (l:ℝ)*(Removal.triples c).card < (order k)^2 := by
      rw [←total_order]; exact_mod_cast light c hc
    have nonneg : (0:ℝ) ≤ (Removal.triples c).card := Nat.cast_nonneg _
    have extra := mul_le_mul_of_nonneg_right denom.le nonneg
    nlinarith only [extra,mul_lt_mul_of_pos_left bound δp]

end
end Audit.Sparse
