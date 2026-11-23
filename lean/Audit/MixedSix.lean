import Audit.SmallProfiles
import Audit.CrossTriangle
import Audit.TriangleRaw

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

theorem six (sf : Free s) (out : Disjoint s (full _)) (mixed : (seedLayer s 0).Nonempty)
    (size : s.card=6) : rankCount s≤3^(5^k) := by
  by_cases clean : NoZeroSum s
  · exact six_no_zero_sum sf out mixed size.ge clean
  suffices h : rankCount s≤3^Fintype.card (Space k) by simpa [Space,Field5] using h
  by_cases lo : 10≤minimumDegree s
  · exact MasterTable.two_degree s sf out lo (mixed_profile s sf out mixed).2
  obtain ⟨cross,_,_,cases⟩ := small_bad sf out (Or.inr size) clean (by omega)
  have total : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 := max_add_min ..
  obtain ⟨_,low,ab⟩ := cases.resolve_right (fun h => by omega)
  rcases ab with ⟨hi,across⟩|⟨hi,across⟩
  · exact TriangleRaw.twelve_nine sf hi.le low.le (by omega) across
  · apply TriangleRaw.ten_nine sf hi.le low.le (by omega) across
    obtain ⟨a,p,na,az,ps,qs⟩ := cross
    intro x hx _
    exact (by decide : 4≤6).trans (crossing_edges a p na az ps qs x hx)

end
end Audit.Mixed
