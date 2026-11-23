import Sumfree.HardBlock

namespace Sumfree.Pair

private def small (s t g : Ambient Plane) :=
  if s=hardS ∧ t=hardT then decide ((rooted s t g).length = 50) else localOK s t g

/-- The largest graph is discharged by folding. The remaining rooted cells
    have at most 20 vertices; this closed computation checks their counts. -/
private theorem small_checked : allCases small = true := by native_decide

theorem checked_cells : finiteCases = true := by
  have lift (s t g : Ambient Plane) (h : small s t g = true) : localOK s t g = true := by
    unfold small at h
    split at h
    · rename_i hi
      obtain ⟨rfl,rfl⟩ := hi
      rw [decide_eq_true_eq] at h
      have bound := hard_cell g
      unfold localOK
      rw [decide_eq_true_eq,local_correct,h]
      change _^50 ≤ 820694^50
      exact Nat.pow_le_pow_left bound _
    · exact h
  unfold finiteCases allCases
  apply List.all_eq_true.mpr
  intro c hc
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  apply List.all_eq_true.mpr
  intro uv hu
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp small_checked c hc) a ha) b hb) uv hu
  dsimp only at h ⊢
  split <;> rename_i hs
  · exact lift _ _ _ (by simpa [hs] using h)
  · rfl

end Sumfree.Pair
