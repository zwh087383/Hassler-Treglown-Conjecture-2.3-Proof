import Audit.Bipartite
import Audit.Windows

namespace Audit.Bipartite
open Finset
variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K] {r : Rule K}

/-- The log of a ratio of products has zero uniform mean whenever every
    input and output has the same marginal and the weights balance in each state. -/
theorem balance {m n : ℕ} (symm : ∀ a i j, r a i j ↔ r a j i)
    (x : Fin m → K) (y : Fin n → K) (a : Fin m → State → ℝ) (g : Fin n → State → ℝ)
    (ha : ∀ i s, 0 < a i s) (hg : ∀ j s, 0 < g j s)
    (h : ∀ s, (∏ i, a i s) = ∏ j, g j s) :
    ∑ b : Sample r, Real.log ((∏ i, a i (left b (x i))) / ∏ j, g j (right b (y j))) = 0 := by
  classical
  have logRatio (b : Sample r) : Real.log ((∏ i, a i (left b (x i))) / ∏ j, g j (right b (y j))) =
      (∑ i, Real.log (a i (left b (x i)))) - ∑ j, Real.log (g j (right b (y j))) := by
    rw [Real.log_div (prod_pos (fun i _ => ha i _)).ne' (prod_pos (fun j _ => hg j _)).ne',
      Real.log_prod _ _ (fun i _ => (ha i _).ne'),Real.log_prod _ _ (fun j _ => (hg j _).ne')]
  have per (s : State) : (∑ i, Real.log (a i s)) = ∑ j, Real.log (g j s) := by
    rw [← Real.log_prod _ _ (fun i _ => (ha i _).ne'),← Real.log_prod _ _ (fun j _ => (hg j _).ne'),h]
  simp_rw [logRatio]
  rw [sum_sub_distrib,sub_eq_zero]
  calc
    _ = ∑ i, ∑ b : Sample r, Real.log (a i (left b (x i))) := sum_comm
    _ = ∑ i, ∑ b : Sample r, Real.log (a i (right b 0)) := by
      apply sum_congr rfl; intro i _; exact marginal symm _ _ (fun s => Real.log (a i s))
    _ = ∑ b : Sample r, ∑ i, Real.log (a i (right b 0)) := sum_comm
    _ = ∑ b : Sample r, ∑ j, Real.log (g j (right b 0)) := sum_congr rfl (fun b _ => per _)
    _ = ∑ j, ∑ b : Sample r, Real.log (g j (right b 0)) := sum_comm
    _ = ∑ j, ∑ b : Sample r, Real.log (g j (right b (y j))) := by
      apply sum_congr rfl; intro j _
      let w (s : State) := Real.log (g j s)
      exact (marginal symm 0 0 w).symm.trans (marginal symm 0 (y j) w)
    _ = _ := sum_comm

end Audit.Bipartite
