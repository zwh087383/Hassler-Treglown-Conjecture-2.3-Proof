import Audit.Balance
import Audit.Weights

namespace Audit.FinalTypes
open Bipartite Stars Weights Entropy Finset
variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- A has three P-only translations and one Q-only translation.
    C has one common, two P-only and one Q-only translation. -/
theorem ac_power (c : Bool) (t : Fin 4 → K) (distinct : Function.Injective t) :
    (Sumfree.mis (adj (rule t (acTag c))) univ : ℝ)^4 ≤ (acZ c : ℝ)^(Fintype.card K) := by
  classical
  let r := rule t (acTag c)
  let a (i : Fin 4) (s : State) : ℝ := ac c i s
  have pa (i s) : 0 < a i s := by dsimp [a]; exact_mod_cast ac_pos c i s
  have pw (z : Fin 4 → State) (h : good z) : 0 < acW c z := by
    rw [acW,if_pos h]; exact div_pos (prod_pos fun i _ => ac_pos ..) (prod_pos fun i _ => ac_pos ..)
  have support (y : K) (b : Sample r) : good (fun i => left b (y+ -t i)) :=
    by simpa only [←sub_eq_add_neg] using ac_support c t b y
  rw [← card_graph]
  apply translated_power (by decide : 0 < 4) (fun i => -t i) (fun _ _ e => distinct (neg_inj.mp e))
    (@left K _ r) (left_injective r) (fun z => (acW c z : ℝ)) _ (by exact_mod_cast (ac_limit c).1)
  · intro z
    by_cases h : good z
    · exact_mod_cast (pw z h).le
    · simp [acW,h]
  · exact_mod_cast (ac_total c).le
  · intro y b; exact_mod_cast pw _ (support y b)
  · intro y
    have bound := balance (symmetric t (acTag c)) (fun i => y+ -t i) (fun _ : Fin 4 => y)
      a a pa pa (fun _ => rfl)
    convert bound using 1
    apply sum_congr rfl; intro b _
    apply congrArg Real.log
    rw [acW,if_pos (support y b)]
    push_cast
    have eq := star t (acTag c) b y
    simp only [sub_eq_add_neg] at eq
    simp only [a,eq]

theorem type_A (t : Fin 4 → K) (distinct : Function.Injective t) :
    Sumfree.mis (adj (rule t (acTag false))) univ < 3^(Fintype.card K) :=
  below_target (by decide) Fintype.card_pos (by exact_mod_cast (ac_limit false).1)
    (by exact_mod_cast (ac_limit false).2) (ac_power false t distinct)

theorem type_C (t : Fin 4 → K) (distinct : Function.Injective t) :
    Sumfree.mis (adj (rule t (acTag true))) univ < 3^(Fintype.card K) :=
  below_target (by decide) Fintype.card_pos (by exact_mod_cast (ac_limit true).1)
    (by exact_mod_cast (ac_limit true).2) (ac_power true t distinct)

/-- B with seven distinct offsets; this includes all independent u,v,w. -/
theorem b_power (u v w : K) (distinct : Function.Injective (offsets u v w)) :
    (Sumfree.mis (adj (rule (bSeed u v w) bTag)) univ : ℝ)^7 ≤ (bZ : ℝ)^(Fintype.card K) := by
  classical
  let r := rule (bSeed u v w) bTag
  let a (i : Fin 7) (s : State) : ℝ := inputB i s
  let g (j : Fin 2) (s : State) : ℝ := outputB j s
  have pa (i s) : 0 < a i s := by dsimp [a]; exact_mod_cast b_input_pos i s
  have pg (j s) : 0 < g j s := by dsimp [g]; exact_mod_cast b_output_pos j s
  have pw (z : Fin 7 → State) : 0 < bW z :=
    div_pos (prod_pos fun i _ => b_input_pos ..) (prod_pos fun j _ => b_output_pos ..)
  rw [← card_graph]
  apply translated_power (by decide : 0 < 7) (offsets u v w) distinct
    (@left K _ r) (left_injective r) (fun z => (bW z : ℝ)) _ (by exact_mod_cast b_limit.1)
  · intro z; exact_mod_cast (pw z).le
  · exact_mod_cast b_total.le
  · intro y b; exact_mod_cast pw _
  · intro y
    let centers (j : Fin 2) := if j=0 then y else y+u
    have same (s : State) : (∏ i, a i s) = ∏ j, g j s := by dsimp [a,g]; exact_mod_cast b_balance s
    have bound := balance (symmetric (bSeed u v w) bTag) (fun i => y+offsets u v w i) centers a g pa pg same
    convert bound using 1
    apply sum_congr rfl; intro b _
    apply congrArg Real.log
    have pair := b_outputs u v w b y
    have eq (j : Fin 2) : rootB (fun i => left b (y+offsets u v w i)) j = right b (centers j) := by
      by_cases h : j=0
      · simpa [rootB,centers,h] using pair.1.symm
      · simpa [rootB,centers,h] using pair.2.symm
    simp [bW,a,g,eq]

theorem type_B_seven (u v w : K) (distinct : Function.Injective (offsets u v w)) :
    Sumfree.mis (adj (rule (bSeed u v w) bTag)) univ < 3^(Fintype.card K) :=
  below_target (by decide) Fintype.card_pos (by exact_mod_cast b_limit.1)
    (by exact_mod_cast b_limit.2) (b_power u v w distinct)

end Audit.FinalTypes
