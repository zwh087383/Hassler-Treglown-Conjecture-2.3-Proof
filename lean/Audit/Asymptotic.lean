import Audit.Lower
import Audit.Global

namespace Audit.Asymptotic
open Filter Finset
open scoped Topology

/-- The actual number of inclusion-maximal sum-free sets in dimension k.
    For positive dimension we display its first coordinate separately. -/
noncomputable def fmax : ℕ → ℕ
  | 0 => (Link.maximalSets (univ : Finset (Fin 0 → Fin 5))).card
  | k+1 => (Link.maximalSets (univ : Finset (Lower.Pt (Fin k → Fin 5)))).card

theorem lower (k : ℕ) (hk : 0<k) : (3:ℝ)^((5:ℝ)^k/10-1/2) ≤ fmax k := by
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨m,hm⟩ := (show Odd (5:ℕ) from ⟨2,rfl⟩).pow (n:=k)
    have count : (5^k-1)/2=m := by omega
    have linear : (5:ℝ)^k=2*(m:ℝ)+1 := by exact_mod_cast hm
    have expEq : (5:ℝ)^(k+1)/10-1/2=(m:ℝ) := by rw [pow_succ,linear]; ring
    rw [expEq,Real.rpow_natCast]
    have term := Lower.singleton_lower k
    rw [count] at term
    exact_mod_cast term

/-- A squeeze lemma for the actual count from a variable-error upper bound. -/
theorem limit_of_upper (err : ℕ → ℝ) (C : ℝ) (small : Tendsto err atTop (𝓝 0))
    (upper : ∀ᶠ k in atTop, (fmax k : ℝ) ≤
      (2:ℝ)^(err k*(5:ℝ)^k) * (3:ℝ)^((5:ℝ)^k/10+C)) :
    Tendsto (fun k => Real.log (fmax k)/((5:ℝ)^k*Real.log 3)) atTop (𝓝 (1/10)) := by
  apply Global.main_squeeze fmax err C small _ upper
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk using lower k hk

end Audit.Asymptotic
