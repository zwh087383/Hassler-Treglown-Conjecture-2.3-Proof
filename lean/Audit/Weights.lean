import Audit.Stars
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Lemmas

namespace Audit.Weights
open Bipartite Stars Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def ac (c : Bool) (i : Fin 4) (s : State) : ℚ :=
  if i=3 then (if c then four 1 (1/2) 1 (1/2) s else four 1 1 1 (1/2) s)
  else if c && i==0 then 1 else if s=0 then 1 else 1/2

def acW (c : Bool) (z : Fin 4 → State) : ℚ :=
  if good z then (∏ i, ac c i (z i)) / ∏ i, ac c i (out (acTag c) z) else 0
def acZ (c : Bool) : ℚ := if c then 279/4 else 1259/16

theorem ac_pos : ∀ c i s, 0 < ac c i s := by native_decide
theorem ac_total : ∀ c, (∑ z, acW c z) = acZ c := by native_decide
theorem ac_limit : ∀ c, 0 < acZ c ∧ acZ c < 3^4 := by native_decide
theorem support_size : (univ.filter good).card=193 := by native_decide

def inputB (i : Fin 7) (s : State) : ℚ :=
  if i=0 then four 1 (1/4) 1 1 s
  else if i.val≤2 then four 1 (1/3) (2/3) (1/2) s else four 1 (2/3) (1/3) (1/2) s
def outputB (_ : Fin 2) (s : State) : ℚ := four 1 (2/27) (2/27) (1/8) s
def rootB (z : Fin 7 → State) (j : Fin 2) := if j=0 then out bTag (first z) else out bTag (second z)
def bW (z : Fin 7 → State) : ℚ := (∏ i, inputB i (z i)) / ∏ j, outputB j (rootB z j)
def bZ : ℚ := 43177189/20736
theorem b_input_pos : ∀ i s, 0 < inputB i s := by native_decide
theorem b_output_pos : ∀ j s, 0 < outputB j s := by native_decide
theorem b_balance : ∀ s, (∏ i, inputB i s) = ∏ j, outputB j s := by native_decide
theorem b_total : (∑ z, bW z) = bZ := by native_decide
theorem b_limit : 0 < bZ ∧ bZ < 3^7 := by native_decide

end Audit.Weights
