import Audit.Matrix

namespace Audit.Coverage
open Finset Bipartite Matrix
variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- A nested pair of rows removes one of the four states at every position. -/
theorem nested_rows {r : Rule K} (i j : Bool) (bad : State)
    (absent : bit bad i=false) (present : bit bad j=true)
    (incl : ∀ t b, r t i b → r t j b) :
    Sumfree.mis (adj r) univ ≤ 3^(Fintype.card K) := by
  classical
  have skip (s : Sample r) (x : K) : left s x≠bad := by
    intro eq
    have large : bit (left s x) j=true := eq ▸ present
    have small : bit (left s x) i=true := (s.2.1 x i).mpr
      (fun y b hb e => (s.2.1 x j).mp large y b hb (incl _ _ e))
    rw [eq,absent] at small; contradiction
  let enc (s : Sample r) (x : K) : {z : State // z≠bad} := ⟨left s x,skip s x⟩
  have inj : Function.Injective enc := by
    intro s t e; apply left_injective r; funext x; exact congrArg Subtype.val (congrFun e x)
  have count : Fintype.card {z : State // z≠bad} = 3 := by fin_cases bad <;> decide
  rw [← card_graph]
  simpa [Fintype.card_fun,count] using Fintype.card_le_of_injective enc inj

theorem nested_colors (p q : Finset K) (incl : p⊆q ∨ q⊆p) :
    Sumfree.mis (adj (matrix p q)) univ ≤ 3^(Fintype.card K) := by
  rcases incl with sub|sub
  · apply nested_rows true false 1 (by decide) (by decide)
    intro t b; cases b <;> simp [matrix] <;> aesop
  · apply nested_rows false true 2 (by decide) (by decide)
    intro t b; cases b <;> simp [matrix] <;> aesop

/-- Degree regimes in the no-zero table for all seed sizes ≥7. -/
theorem nozero_large (p r d : ℕ) (order : r≤p) (unionSize : p≤d) (size : 7≤p+r) :
    d=p ∨ (d+p≤10 ∧ 17≤2*d+p+r) ∨ (d+p≤12 ∧ 18≤2*d+p+r) ∨
    (12≤d+p ∧ d+p≤2*(d+r)) := by omega

/-- When a zero-layer seed is present, the hypotheses of the two-degree
    theorem apply as soon as the seed size reaches eight. -/
theorem mixed_large (z p r a₀ d : ℕ) (zeroSeed : 1≤z) (opposites : 2≤a₀)
    (order : r≤p) (unionSize : p≤d) (size : 8≤z+p+r) :
    let a:=a₀+z+d+p
    let b:=a₀+z+d+r
    10≤b ∧ b≤a ∧ a≤2*b-3 := by dsimp; omega

end Audit.Coverage
