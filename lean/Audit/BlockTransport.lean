import Audit.Reduction

namespace Audit.BlockTransport
open Finset Blocks Lower Band Link Generic Reduction
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def Counts : Prop := ∀ k (s : Finset (Pt (Space k))), Free s → Disjoint s (full _) →
  rankCount s≤3^(5^k)

/-- Transport the coordinate-space assertion to any finite vector space over F₅. -/
theorem arbitrary (counts : Counts) {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
    [Module Field5 K] (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K)) :
    rankCount s≤3^Fintype.card K := by
  let r := Module.finrank Field5 K
  let iso := LinearEquiv.ofFinrankEq (R:=Field5) K (Space r) (by rw [Module.finrank_fin_fun])
  let e := relabel iso.toAddEquiv
  have f := (Assembly.free_image e s).mpr sf
  have o : Disjoint (s.image e) (full (Space r)) := by
    apply disjoint_left.mpr
    intro v h band; obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact disjoint_left.mp out hx ((mem_full (u:=x)).mpr ((mem_full (u:=e x)).mp band))
  have c : Fintype.card K=5^r := by
    rw [Fintype.card_congr iso.toEquiv]
    simp [Space,Field5]
  rw [rankCount_relabel iso.toAddEquiv,c]
  exact counts r _ f o

theorem original_cell (counts : Counts) {k : ℕ} (s : Finset (Pt (Space k)))
    (sf : Free s) (out : Disjoint s (full _)) (w : Space k ⧸ spanTails s) (nz : w≠0) :
    Sumfree.mis (edge s) (genericCell s w)≤3^(Nat.card (spanTails s)) := by
  rw [generic_count s w nz,Nat.card_eq_fintype_card]
  have d := roots_data sf out
  exact arbitrary counts _ d.1 d.2.1

theorem blocks (counts : Counts) : BlockBound := fun _ s sf out _ w nz => original_cell counts s sf out w nz

end
end Audit.BlockTransport
