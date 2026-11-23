import Audit.TriangleCoordinates

namespace Audit.TriangleCoordinates
open Finset Sumfree Generic Band Link Lower Blocks Degrees Fingerprint TriangleBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
variable {s : Finset (Pt K)} {v : Raw.Point K}

def common (s : Finset (Pt K)) (v : Raw.Point K) : Finset (Raw.Point K) :=
  ((s.filter (allows v)).image (point v)) ∪ ((s.filter (allows (-v))).image (point (-v)))

theorem common_sub (sf : Free s) (hv : v∈Raw.domain) : common s v ⊆
    neighbors (within s) Raw.domain v ∩ neighbors (within s) Raw.domain (-v) := by
  have one {x : Raw.Point K} (hx : x∈Raw.domain) {d : Pt K} (hd : d∈s) (ha : allows x d) :
      point x d∈neighbors (within s) Raw.domain x ∩ neighbors (within s) Raw.domain (-x) := by
    have yd := point_dom hx ha
    have ed := same sf x (a:=0) (by simpa using hx) yd (by simpa using mem_signed.mpr (Or.inl hd))
    have op := opposite hx yd (b:=0) (by simpa using opposite_domain hx) (by simpa using hd)
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨yd,by simpa using ed⟩,
      mem_filter.mpr ⟨yd,within_sym _ (by simpa using op)⟩⟩
  intro y hy
  rcases mem_union.mp hy with a|b
  · obtain ⟨d,hd,rfl⟩:=mem_image.mp a
    exact one hv (mem_filter.mp hd).1 (mem_filter.mp hd).2
  · obtain ⟨d,hd,rfl⟩:=mem_image.mp b
    simpa only [neg_neg,inter_comm] using one (opposite_domain hv) (mem_filter.mp hd).1 (mem_filter.mp hd).2

theorem common_count (out : Disjoint s (full K)) (hv : v∈Raw.domain) :
    (common s v).card=s.card+(seedLayer s 0).card := by
  let l := s.filter (allows v)
  let r := s.filter (allows (-v))
  have dis : Disjoint (l.image (point v)) (r.image (point (-v))) := by
    apply disjoint_left.mpr
    intro y hy hz
    obtain ⟨a,_,rfl⟩:=mem_image.mp hy
    obtain ⟨b,_,eq⟩:=mem_image.mp hz
    exact different_sides hv a b eq.symm
  have head := (mem_filter.mp hv).2.1
  have union : l∪r=s := by
    ext d
    constructor
    · intro h; rcases mem_union.mp h with k|k <;> exact (mem_filter.mp k).1
    · intro hs
      have no : ¬(d.1=2 ∨ d.1=3) := fun h => disjoint_left.mp out hs (mem_full.mpr h)
      have tt : (allows v d ∨ allows (-v) d) :=
        (show ∀ h i : Fin 5, (h=2 ∨ h=3) → ¬(i=2 ∨ i=3) →
          (i+h=2 ∨ i+h=3) ∨ (i+(-h)=2 ∨ i+(-h)=3) by decide) _ _ head no
      rcases tt with t|t
      · exact mem_union_left _ (mem_filter.mpr ⟨hs,t⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hs,t⟩)
  have inter : l∩r=seedLayer s 0 := by
    ext d
    have tt : (allows v d ∧ allows (-v) d) ↔ d.1=0 :=
      (show ∀ h i : Fin 5, (h=2 ∨ h=3) →
        ((i+h=2 ∨ i+h=3) ∧ (i+(-h)=2 ∨ i+(-h)=3) ↔ i=0) by decide) _ _ head
    simp only [l,r,seedLayer,mem_inter,mem_filter]
    tauto
  change (l.image (point v)∪r.image (point (-v))).card=_
  rw [card_union_of_disjoint dis,card_image_of_injective _ (inject_point _),
    card_image_of_injective _ (inject_point _),←card_union_add_card_inter l r,union,inter]

theorem outside_common (hv : v∈Raw.domain) {d : Pt K} (hd : d∉s) :
    point (-v) d ∉ common s v := by
  intro h
  rcases mem_union.mp h with a|b
  · obtain ⟨e,_,eq⟩:=mem_image.mp a
    exact different_sides hv e d eq
  · obtain ⟨e,he,eq⟩:=mem_image.mp b
    exact hd ((inject_point _ eq) ▸ (mem_filter.mp he).1)

theorem common_right {d : Pt K} (hd : d∈s) (good : allows (-v) d) :
    point (-v) d ∈ common s v :=
  mem_union_right _ (mem_image.mpr ⟨d,mem_filter.mpr ⟨hd,good⟩,rfl⟩)
end
end Audit.TriangleCoordinates
