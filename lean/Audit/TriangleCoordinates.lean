import Audit.TriangleRaw

namespace Audit.TriangleCoordinates
open Finset Sumfree Generic Band Link Lower Blocks Degrees Fingerprint TriangleBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
section Graph
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop} {f : Finset V}
variable {x a b c d : V}

theorem two_neighbors (ha : a∈f) (hb : b∈f) (ra : r x a) (rb : r x b) (ne : a≠b) :
    2≤deg r f x := by
  have sub : ({a,b} : Finset V)⊆neighbors r f x :=
    insert_subset (mem_filter.mpr ⟨ha,ra⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨hb,rb⟩))
  simpa only [card_pair ne] using card_le_card sub

theorem path_volume (sym : Symmetric r) (irr : Irreflexive r)
    (ha : a∈f) (hb : b∈f) (hc : c∈f) (hd : d∈f)
    (ab : r a b) (bc : r b c) (cd : r c d) (ac : a≠c) (ad : a≠d) (bd : b≠d) :
    6≤vol r f := by
  have b0 : 0<deg r f a := card_pos.mpr ⟨b,mem_filter.mpr ⟨hb,ab⟩⟩
  have c0 : 0<deg r f d := card_pos.mpr ⟨c,mem_filter.mpr ⟨hc,sym cd⟩⟩
  have b2 := two_neighbors ha hc (sym ab) bc ac
  have c2 := two_neighbors hb hd (sym bc) cd bd
  have abn : a≠b := fun eq => irr _ (eq ▸ ab)
  have bcn : b≠c := fun eq => irr _ (eq ▸ bc)
  have cdn : c≠d := fun eq => irr _ (eq ▸ cd)
  have sub : ({a,b,c,d} : Finset V) ⊆ f := by
    simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨ha,hb,hc,hd⟩
  calc
    6 ≤ deg r f a+(deg r f b+(deg r f c+deg r f d)) := by omega
    _ = ∑ z∈({a,b,c,d}:Finset V),deg r f z := by
      simp [abn,ac,ad,bcn,bd,cdn]
    _ ≤ ∑ z∈f,deg r f z := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)

end Graph
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

def lift : Pt K →+ Raw.Point K where
  toFun d := (d.1,d.2,0)
  map_zero' := rfl
  map_add' _ _ := Prod.ext rfl (Prod.ext rfl (zero_add _).symm)

def point (v : Raw.Point K) (d : Pt K) := lift d+v

theorem inject_point (v : Raw.Point K) : Function.Injective (point v) := by
  intro a b eq
  exact congrArg Degrees.project (add_right_cancel eq : lift a=lift b)

@[simp] theorem point_zero (v : Raw.Point K) : point v 0=v := by simp [point]
@[simp] theorem last (v : Raw.Point K) (a : Pt K) : (point v a).2.2=v.2.2 := zero_add _
@[simp] theorem first (v : Raw.Point K) (a : Pt K) : (point v a).1=a.1+v.1 := rfl

theorem opposite_domain {v : Raw.Point K} (h : v∈Raw.domain) : -v∈Raw.domain := by
  obtain ⟨head,sign⟩ := (mem_filter.mp h).2
  exact mem_filter.mpr ⟨mem_univ _,(show ∀ i : Fin 5,i=2 ∨ i=3 → -i=2 ∨ -i=3 by decide) _ head,
    (valid_sign _ sign).1⟩

theorem different_sides {v : Raw.Point K} (h : v∈Raw.domain) (a b : Pt K) : point v a ≠ point (-v) b := by
  intro eq
  have tail := congrArg (fun y : Raw.Point K => y.2.2) eq
  change (point v a).2.2=(point (-v) b).2.2 at tail
  rw [last,last] at tail
  exact (valid_sign _ (mem_filter.mp h).2.2).2 tail

def allows (v : Raw.Point K) (a : Pt K) : Prop := a.1+v.1=2 ∨ a.1+v.1=3

theorem point_dom {v : Raw.Point K} (h : v∈Raw.domain) {a : Pt K} (ah : allows v a) :
    point v a∈Raw.domain := mem_filter.mpr ⟨mem_univ _,ah,by rw [last]; exact (mem_filter.mp h).2.2⟩

theorem plane_lift {d : Pt K} {s : Finset (Pt K)} (h : d∈s) : lift d∈plane s :=
  (in_plane ..).mpr ⟨h,rfl⟩

theorem same {s : Finset (Pt K)} (sf : Free s) (v : Raw.Point K) {a b : Pt K}
    (ad : point v a∈Raw.domain) (bd : point v b∈Raw.domain) (h : b-a∈signed s) :
    within s (point v a) (point v b) := by
  have nz : (0:Pt K)∉signed s := by
    have no : (0:Pt K)∉s := fun k => sf 0 k 0 k 0 k (zero_add _)
    simpa using no
  have ne : a≠b := fun eq => nz (by simpa [eq] using h)
  refine ⟨ad,bd,(inject_point v).ne ne,Or.inr ?_⟩
  rcases mem_signed.mp h with k|k
  · exact Or.inl (by simpa [point,map_sub] using plane_lift k)
  · exact Or.inr (by simpa [point,map_sub] using plane_lift k)

theorem opposite {s : Finset (Pt K)} {v : Raw.Point K} (hv : v∈Raw.domain) {a b : Pt K}
    (ad : point v a∈Raw.domain) (bd : point (-v) b∈Raw.domain) (h : a+b∈s) :
    within s (point v a) (point (-v) b) := by
  refine ⟨ad,bd,different_sides hv a b,Or.inl ?_⟩
  rw [show point v a+point (-v) b = lift (a+b) by simp [point,map_add]; abel]
  exact plane_lift h

theorem no_partner_edge {s : Finset (Pt K)} (sf : Free s) {v : Raw.Point K} (hv : v∈Raw.domain) :
    ¬within s (-v) v := by
  have nz : (0:Pt K)∉s := fun k => sf 0 k 0 k 0 k (zero_add _)
  have signs := (mem_filter.mp hv).2.2
  have diff : v.2.2≠ -v.2.2 := (valid_sign _ signs).2
  intro e
  rcases e.2.2.2 with plus|diff1|diff2
  · have h := ((in_plane ..).mp plus).1
    exact nz (by simpa using h)
  · exact diff (sub_eq_zero.mp ((in_plane ..).mp diff1).2)
  · exact diff (sub_eq_zero.mp ((in_plane ..).mp diff2).2).symm

end
end Audit.TriangleCoordinates
