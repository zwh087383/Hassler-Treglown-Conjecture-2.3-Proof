import Audit.MixedNeighbors
import Audit.TriangleMixedCaps
import Audit.TrianglePartner

namespace Audit.TriangleRaw
open Finset Sumfree Generic Band Link Lower Blocks Degrees Fingerprint TriangleBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

theorem high_neighbors {s : Finset (Pt K)} (sf : Free s) (lo : minimumDegree s≤9) {k : ℕ}
    (counts : maximumDegree s≤k+(seedLayer (forward s) 1).card+(seedLayer s 0).card) :
    TriangleMixedCaps.HighNeighbors (within s) Raw.domain k := by
  intro x hx high
  let n := neighbors (within s) Raw.domain x
  let a := Mixed.across s x
  have highHead : 9<headDegree s x.1 := (within_degree sf hx) ▸ high
  have sub : n.filter (fun y => 9<deg (within s) Raw.domain y) ⊆ n\a := by
    intro y hy
    obtain ⟨yn,hd⟩ := mem_filter.mp hy
    refine mem_sdiff.mpr ⟨yn,fun ya => ?_⟩
    have other := (mem_filter.mp ya).2
    have yd := (mem_filter.mp yn).1
    change 9<(neighbors (within s) Raw.domain y).card at hd
    rw [within_degree sf yd] at hd
    have h1 := (mem_filter.mp hx).2.1
    have h2 := (mem_filter.mp yd).2.1
    unfold minimumDegree at lo
    rcases h1 with he|he <;> rcases h2 with ye|ye <;> rw [he,ye] at other <;> rw [he] at highHead <;> rw [ye] at hd <;> omega
  have bound := card_le_card sub
  have partition := card_sdiff_add_card_eq_card (show a⊆n from filter_subset ..)
  have across := Mixed.across_lower s hx
  change _≤a.card at across
  have size := within_cap sf x hx
  change n.card≤_ at size
  change (n.filter (fun y => 9<deg (within s) Raw.domain y)).card≤k
  omega

theorem twelve_nine {s : Finset (Pt K)} (sf : Free s) (hi : maximumDegree s≤12)
    (lo : minimumDegree s≤9) (total : 21≤headDegree s 2+headDegree s 3)
    (across : 6≤(seedLayer (forward s) 1).card+(seedLayer s 0).card) :
    rankCount s≤3^Fintype.card K :=
  within_quarter s sf (TriangleMixedCaps.twelve_nine (within_sym s) (within_irr s) _
    (fun x hx => (within_cap sf x hx).trans hi) (high_neighbors sf lo (by omega))
    (two_degree_sum s sf 21 total))

theorem ten_nine {s : Finset (Pt K)} (sf : Free s) (hi : maximumDegree s≤10)
    (lo : minimumDegree s≤9) (total : 19≤headDegree s 2+headDegree s 3)
    (across : 5≤(seedLayer (forward s) 1).card+(seedLayer s 0).card)
    (internal : TriangleMixedCaps.Inner (within s) Raw.domain 10 4) : rankCount s≤3^Fintype.card K :=
  within_quarter s sf (TriangleMixedCaps.ten_nine (within_sym s) (within_irr s) _
    (fun x hx => (within_cap sf x hx).trans hi) (high_neighbors sf lo (by omega)) internal
    (two_degree_sum s sf 19 total))

theorem nine {s : Finset (Pt K)} (sf : Free s) (hi : maximumDegree s≤9)
    (total : 18≤headDegree s 2+headDegree s 3)
    (cert : TrianglePartner.Certificate (within s) Raw.domain) : rankCount s≤3^Fintype.card K :=
  within_quarter s sf (TrianglePartner.bound (within_sym s) (within_irr s) _
    (fun x hx => (within_cap sf x hx).trans hi) cert (two_degree_sum s sf 18 total))

end
end Audit.TriangleRaw
