import Audit.Sparse
import Audit.Structure
import Audit.Limit

namespace Audit.Unconditional
open Finset Link Band Blocks Lower Assembly Filter
open scoped Classical Topology
noncomputable section

theorem maximal_card {k : ℕ} {m : Finset (group k)} (mx : MaxIn univ m) :
    (m.card:ℝ) ≤ 2*order k/5 := by
  by_cases h : (m.card:ℝ) ≤ 3*order k/10
  · have pos : 0 ≤ order k := by dsimp [order]; positivity
    linarith
  · obtain ⟨e,sub⟩ := Structure.largeSetStructure k m mx.2.1 (lt_of_not_ge h)
    have eq := full_of_maximal mx e sub
    have card : m.card=2*Fintype.card (Space k) := by
      rw [←card_image_of_injective m e.injective,eq]
      simp [full,band]
    have tail := tail_order k
    rw [card]; push_cast; linarith

theorem links (k : ℕ) : LocalBound k ((3:ℝ)^(2*order k/15)) := by
  intro m s mx _ _
  apply (Sumfree.moon_moser (clash_sym s) (fun _ h => h.1 rfl) _).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have sub : legal s m ⊆ m := fun _ h => (mem_legal.mp h).1
  have card : ((legal s m).card:ℝ) ≤ m.card := by exact_mod_cast card_le_card sub
  linarith [maximal_card mx]

theorem upper {η : ℝ} (pos : 0<η) (unit : η≤1) :
    ∀ᶠ k : ℕ in atTop, (Asymptotic.fmax (k+1):ℝ) ≤
      (2:ℝ)^((2*η)*order k)*(3:ℝ)^(2*order k/15) :=
  upper_with Sparse.sparseCovers _ (fun _ => Real.rpow_nonneg (by norm_num) _) links pos unit

/-- The unconditioned interval for the exponent in every sufficiently large dimension. -/
theorem exponent_window (ε : ℝ) (pos : 0<ε) :
    ∀ᶠ k : ℕ in atTop, 1/10-ε < Limit.normalized k ∧ Limit.normalized k < 2/15+ε := by
  suffices shifted : ∀ᶠ k : ℕ in atTop,
      1/10-ε < Limit.normalized (k+1) ∧ Limit.normalized (k+1) < 2/15+ε by
    obtain ⟨n,hn⟩ := eventually_atTop.mp shifted
    apply eventually_atTop.mpr
    refine ⟨n+1,?_⟩
    rintro (_|j) hj
    · omega
    · exact hn j (by omega)
  have lp : 0<Real.log 3 := Real.log_pos (by norm_num)
  have lp2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let β := 2*Real.log 2/Real.log 3
  have bp : 0<β := by dsimp [β]; positivity
  let η := min 1 (ε/(2*β))
  have hp : 0<η := lt_min (by norm_num) (div_pos pos (by positivity))
  have eps := (le_div_iff₀ (show 0<2*β by positivity)).mp (min_le_right 1 (ε/(2*β)))
  change η*(2*β)≤ε at eps
  have small : η*β < ε := by linarith
  have inv : Tendsto (fun k : ℕ => (order k)⁻¹) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat (f:=fun k : ℕ => ((5:ℝ)^k)⁻¹) 1).mpr
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<5))
  filter_upwards [upper hp (min_le_left ..),inv.eventually_lt_const (show 0<2*ε by linarith)] with k up hi
  have np : 0<order k := by dsimp [order]; positivity
  have low := Asymptotic.lower (k+1) (by omega)
  have flo := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _) low
  rw [Real.log_rpow (by norm_num)] at flo
  have fhi := Real.log_le_log ((Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _).trans_le low) up
  rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne'
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _).ne',
    Real.log_rpow (by norm_num),Real.log_rpow (by norm_num)] at fhi
  change (order k/10-1/2)*Real.log 3 ≤ _ at flo
  change 1/10-ε < Real.log (Asymptotic.fmax (k+1))/(order k*Real.log 3) ∧ _ < 2/15+ε
  constructor
  · apply (lt_div_iff₀ (mul_pos np lp)).mpr
    have gap : 1/2 < ε*order k := by
      rw [inv_lt_comm₀ np (by positivity : 0<2*ε)] at hi
      have hh := (div_lt_iff₀ (by positivity : 0<2*ε)).mp (show 1/(2*ε)<order k by simpa using hi)
      linarith
    apply lt_of_lt_of_le _ flo
    calc
      _ = ((1/10-ε)*order k)*Real.log 3 := by ring
      _ < _ := mul_lt_mul_of_pos_right (by linarith) lp
  · change Real.log (Asymptotic.fmax (k+1))/(order k*Real.log 3) < 2/15+ε
    apply (div_lt_iff₀ (mul_pos np lp)).mpr
    apply lt_of_le_of_lt fhi
    calc
      _ = (2/15+η*β)*(order k*Real.log 3) := by dsimp only [β]; field_simp [lp.ne']; ring
      _ < _ := mul_lt_mul_of_pos_right (by linarith) (mul_pos np lp)

end
end Audit.Unconditional
