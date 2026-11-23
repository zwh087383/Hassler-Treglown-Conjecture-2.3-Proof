import Audit.TinyGeneric
import Audit.NoZero
import Audit.SmallMixedFour
import Audit.SharpFive
import Audit.MixedSix
import Audit.BlockTransport

namespace Audit.GenericTheorem
open Finset Blocks Lower Link Generic Band Degrees
noncomputable section

/-- Every possible exterior seed is covered, in every coordinate rank. -/
theorem all_coordinates : BlockTransport.Counts := by
  intro k s sf out
  by_cases small : s.card≤2
  · exact TinyGeneric.all s sf out small
  by_cases zero : (seedLayer s 0).Nonempty
  · by_cases many : 7≤s.card
    · exact Mixed.seven sf out zero many
    have cases : s.card=3 ∨ s.card=4 ∨ s.card=5 ∨ s.card=6 := by omega
    rcases cases with n|n|n|n
    · exact SmallMixed.three sf out zero n
    · exact SmallMixed.four sf out zero n
    · exact Mixed.five sf out zero n
    · exact Mixed.six sf out zero n
  · exact NoZero.all s out zero

/-- The paper's generic block theorem, with its original seed and field hypotheses. -/
theorem generic_block {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K] [Module Field5 K]
    (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K)) :
    rankCount s≤3^Fintype.card K :=
  BlockTransport.arbitrary all_coordinates s sf out

theorem original_blocks : BlockBound := BlockTransport.blocks all_coordinates

end
end Audit.GenericTheorem
