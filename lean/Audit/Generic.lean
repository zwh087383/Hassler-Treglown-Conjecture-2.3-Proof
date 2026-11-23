import Audit.Blocks
import Audit.Raw
import Audit.Assembly

namespace Audit.Generic
open Finset Lower Band Link Blocks Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {H K : Type} [AddCommGroup H] [Module Field5 H] [Fintype H] [DecidableEq H]
variable [AddCommGroup K] [Fintype K] [DecidableEq K]

def plane (s : Finset (Pt K)) : Finset (Raw.Point K) := s.image fun x => (x.1,x.2,0)
@[simp] theorem in_plane (s : Finset (Pt K)) (x : Raw.Point K) :
    x∈plane s ↔ (x.1,x.2.1)∈s ∧ x.2.2=0 := by
  rcases x with ⟨a,x,t⟩
  simp [plane,eq_comm]

def rankCount (s : Finset (Pt K)) := mis (edge (plane s)) Raw.domain

def shift (g : H) (t : Field5) : H := t • g
def chart (U : Submodule Field5 H) (g : H) : Raw.Point U →+ Pt H where
  toFun x := (x.1,x.2.1.val + shift g x.2.2)
  map_zero' := by simp [shift]
  map_add' := by
    rintro ⟨a,x,t⟩ ⟨b,y,u⟩
    refine Prod.ext rfl ?_
    have addAlong (v w : Field5) : shift g (v+w)=shift g v+shift g w := add_smul .. 
    change (x.val+y.val)+shift g (t+u)=(x.val+shift g t)+(y.val+shift g u)
    rw [addAlong]; abel

theorem projection_chart (U : Submodule Field5 H) (g : H) (v : Raw.Point U) :
    U.mkQ (chart U g v).2 = shift (U.mkQ g) v.2.2 := by
  change U.mkQ (v.2.1.val+shift g v.2.2)=_
  rw [map_add,show U.mkQ v.2.1.val=0 from (Submodule.Quotient.mk_eq_zero _).mpr v.2.1.property]
  simp only [zero_add,shift,map_smul]

theorem chart_inj (U : Submodule Field5 H) (g : H) (out : U.mkQ g ≠ 0) :
    Function.Injective (chart U g) := by
  rintro ⟨a,x,t⟩ ⟨b,y,u⟩ eq
  have head : a=b := congrArg Prod.fst eq
  have qe := congrArg (fun z : Pt H => U.mkQ z.2) eq
  simp only [projection_chart,shift] at qe
  have cancel (v w : Field5) (e : v • U.mkQ g = w • U.mkQ g) : v=w := by
    have q : (v-w) • U.mkQ g=0 := by rw [sub_smul,e,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp q).resolve_right out)
  obtain rfl : t=u := cancel t u qe
  have tails : x.val+shift g t=y.val+shift g t := congrArg Prod.snd eq
  exact Prod.ext head (Prod.ext (Subtype.ext (add_right_cancel tails)) rfl)

def roots {k : ℕ} (s : Finset (Pt (Space k))) : Finset (Pt (spanTails s)) :=
  univ.filter fun x => (x.1,x.2.val)∈s

theorem all_tails {k : ℕ} {s : Finset (Pt (Space k))} {x : Pt (Space k)} (h : x∈s) :
    x.2∈spanTails s := Submodule.subset_span (mem_image_of_mem Prod.snd h)

theorem seed_image {k : ℕ} (s : Finset (Pt (Space k))) (g : Space k) :
    (plane (roots s)).image (chart (spanTails s) g)=s := by
  ext p
  constructor
  · intro h; obtain ⟨⟨i,x,t⟩,hv,rfl⟩ := mem_image.mp h
    obtain ⟨seed, (ht : t=0)⟩ := (in_plane ..).mp hv
    subst t; simpa [chart,shift] using (mem_filter.mp seed).2
  · rintro h
    let x : spanTails s := ⟨p.2,all_tails h⟩
    refine mem_image.mpr ⟨(p.1,x,0),(in_plane ..).mpr ⟨mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩,?_⟩
    simp [chart,shift,x]

theorem roots_data {k : ℕ} {s : Finset (Pt (Space k))} (free : Free s)
    (out : Disjoint s (full (Space k))) :
    Free (roots s) ∧ Disjoint (roots s) (full (spanTails s)) ∧ (roots s).card=s.card := by
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy z hz eq
    exact free _ (mem_filter.mp hx).2 _ (mem_filter.mp hy).2 _ (mem_filter.mp hz).2
      (congrArg (fun v : Pt (spanTails s) => (v.1,v.2.val)) eq)
  · apply disjoint_left.mpr
    intro x hx hb
    have hs : (x.1,x.2.val)∈s := (mem_filter.mp hx).2
    have head : x.1=2 ∨ x.1=3 := (mem_full (u:=x)).mp hb
    exact disjoint_left.mp out hs ((mem_full (u:=(x.1,x.2.val))).mpr head)
  · apply card_bij (fun x _ => (x.1,x.2.val))
    · exact fun _ h => (mem_filter.mp h).2
    · intro x _ y _ h
      obtain ⟨a,b⟩ := Prod.mk.inj h
      exact Prod.ext a (Subtype.ext b)
    · intro y hy
      exact ⟨(y.1,⟨y.2,all_tails hy⟩), mem_filter.mpr ⟨mem_univ _,hy⟩,rfl⟩

theorem generic_image {k : ℕ} (s : Finset (Pt (Space k))) (g : Space k) :
    Raw.domain.image (chart (spanTails s) g) = genericCell s ((spanTails s).mkQ g) := by
  let U := spanTails s
  ext y
  constructor
  · intro h; obtain ⟨p,hp,rfl⟩ := mem_image.mp h
    obtain ⟨head,t⟩ := (mem_filter.mp hp).2
    apply mem_filter.mpr
    refine ⟨(mem_full (u:=chart U g p)).mpr head,?_⟩
    change U.mkQ (chart U g p).2∈{U.mkQ g,-U.mkQ g}
    rw [projection_chart]
    have four : (4:Field5) = -1 := by decide
    rcases t with h|h
    · simp only [h,shift,one_smul,mem_insert_self]
    · simp only [h,shift,four,neg_one_smul,mem_insert,mem_singleton,or_true]
  · intro h
    obtain ⟨head,sign⟩ := mem_filter.mp h
    have lift (t : Field5) (ht : t=1 ∨ t=4) (eq : U.mkQ y.2 = t • U.mkQ g) :
        y∈Raw.domain.image (chart U g) := by
      have sub : y.2 - t • g ∈ U := (Submodule.Quotient.mk_eq_zero U).mp
        (show U.mkQ (y.2-t • g)=0 by rw [map_sub,map_smul,eq,sub_self])
      let p : Raw.Point U := (y.1,⟨_,sub⟩,t)
      have dom : p∈Raw.domain := mem_filter.mpr ⟨mem_univ _,(mem_full (u:=y)).mp head,ht⟩
      exact mem_image.mpr ⟨p, dom, Prod.ext rfl (sub_add_cancel _ _)⟩
    rcases mem_insert.mp sign with pos|neg
    · apply lift 1 (Or.inl rfl); simpa using pos
    · apply lift 4 (Or.inr rfl)
      rw [show (4:Field5) = -1 by decide,neg_one_smul]
      exact mem_singleton.mp neg

theorem faithful_edges {G J : Type*} [AddCommGroup G] [AddCommGroup J] [DecidableEq G] [DecidableEq J]
    (f : G →+ J) (inj : Function.Injective f) (s : Finset G) (x y : G) :
    edge s x y ↔ edge (s.image f) (f x) (f y) := by
  have mem (z : G) : f z∈s.image f ↔ z∈s := by simp only [mem_image,inj.eq_iff,exists_eq_right]
  simp only [edge,←map_add,←map_sub,inj.ne_iff,mem]

theorem generic_count {k : ℕ} (s : Finset (Pt (Space k)))
    (w : Space k ⧸ spanTails s) (nz : w≠0) :
    mis (edge s) (genericCell s w) = rankCount (roots s) := by
  let U := spanTails s
  obtain ⟨g,rfl⟩ := U.mkQ_surjective w
  rw [←generic_image]
  symm
  apply mis_image _ _ _ _ (chart_inj U g nz).injOn
  intro x _ y _
  simpa only [U,seed_image] using faithful_edges (chart U g) (chart_inj U g nz) (plane (roots s)) x y

end
end Audit.Generic
