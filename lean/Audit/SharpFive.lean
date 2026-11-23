import Audit.FiveCases
import Audit.TenEight

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees

theorem five {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (zero : (seedLayer s 0).Nonempty) (size : s.card=5) : rankCount s≤3^(5^k) := by
  rcases five_cases sf out zero size with h|⟨cross,_,layers,_,_,_⟩
  · exact h
  · exact TenEight.crossing sf size cross (layers.imp And.left And.right)

end Audit.Mixed
