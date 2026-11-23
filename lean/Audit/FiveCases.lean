import Audit.MixedEightEight
import Audit.TriangleWitness

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

def TenEight (s : Finset (Pt (Space k))) : Prop :=
  Crossing s ∧ (seedLayer s 0).card=1 ∧
    (((seedLayer s 1).card=3 ∧ (seedLayer s 4).card=1) ∨ ((seedLayer s 1).card=1 ∧ (seedLayer s 4).card=3)) ∧
    (seedLayer (forward s) 1).card=4 ∧ maximumDegree s=10 ∧ minimumDegree s=8

theorem five_cases (sf : Free s) (out : Disjoint s (full _)) (zero : (seedLayer s 0).Nonempty)
    (size : s.card=5) : rankCount s≤3^(5^k) ∨ TenEight s := by
  by_cases clean : NoZeroSum s
  · exact Or.inl (clean_five sf out size zero clean)
  have use_bound (h : rankCount s≤3^Fintype.card (Space k)) : rankCount s≤3^(5^k) ∨ TenEight s :=
    Or.inl (by simpa [Space,Field5] using h)
  by_cases big : 10≤minimumDegree s
  · exact use_bound (MasterTable.two_degree _ sf out big (mixed_profile _ sf out zero).2)
  obtain ⟨cross,z,_,cases⟩ := small_bad sf out (Or.inl size) clean (by omega)
  obtain ⟨_,opts⟩ := cases.resolve_left (fun h => by omega)
  rcases opts with ⟨p,q,u,_,_⟩|⟨_,_,_,hi,lo⟩|⟨dist,u,hi,lo⟩
  · exact use_bound (eight_eight sf out size cross p q u)
  · obtain ⟨a,v,_,az,vs,qs⟩ := cross
    have total : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 := max_add_min ..
    exact use_bound (TriangleCoordinates.nine_cross sf out hi.le (by omega) (by omega) a v az vs qs)
  · exact Or.inr ⟨cross,z,dist,u,hi,lo⟩

end
end Audit.Mixed
