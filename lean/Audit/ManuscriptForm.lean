import Audit.StandardCoordinates
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Audit.Manuscript
open Finset Filter Asymptotics
open scoped Topology
noncomputable section

def count (k : ℕ) : ℕ := (Link.maximalSets (univ : Finset (Fin k → ZMod 5))).card

theorem count_eq_fmax (k : ℕ) : count k=Asymptotic.fmax k := (StandardCoordinates.fmax_eq k).symm

theorem count_pos (k : ℕ) : 0<count k := by
  classical
  have empty : Link.Free (∅ : Finset (Fin k → ZMod 5)) := by intro x hx; simp at hx
  obtain ⟨m,hm,_⟩ := Link.extend empty (empty_subset (univ : Finset (Fin k → ZMod 5)))
  exact card_pos.mpr ⟨m,hm⟩

def errorTerm (k : ℕ) : ℝ := Real.logb 3 (count k) - (5:ℝ)^k/10

theorem exact_power (k : ℕ) :
    (count k:ℝ)=(3:ℝ)^((5:ℝ)^k/10+errorTerm k) := by
  unfold errorTerm
  rw [add_sub_cancel]
  exact (Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.mpr (count_pos k))).symm

theorem log_form (k : ℕ) : Real.logb 3 (count k)/(5:ℝ)^k=Limit.normalized k := by
  rw [count_eq_fmax]
  unfold Limit.normalized Real.logb
  ring

theorem error_iff_limit : errorTerm =o[atTop] (fun k : ℕ => (5:ℝ)^k) ↔
    Tendsto Limit.normalized atTop (𝓝 (1/10:ℝ)) := by
  have nz (k : ℕ) : (5:ℝ)^k≠0 := by positivity
  rw [isLittleO_iff_tendsto (fun k h => (nz k h).elim)]
  have identity : (fun k => errorTerm k/(5:ℝ)^k)=(fun k => Limit.normalized k-1/10) := by
    funext k
    rw [←log_form,errorTerm,sub_div]
    field_simp [nz k]
    ring
  rw [identity]
  constructor
  · intro h
    have r := h.add (tendsto_const_nhds (x:=(1/10:ℝ)))
    simpa only [Pi.add_apply,sub_add_cancel,zero_add] using r
  · intro h
    simpa only [Pi.sub_apply,sub_self] using h.sub (tendsto_const_nhds (x:=(1/10:ℝ)))

end
end Audit.Manuscript
