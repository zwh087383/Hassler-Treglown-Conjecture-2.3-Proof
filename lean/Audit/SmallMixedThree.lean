import Audit.SmallMixedNormalize

namespace Audit.SmallMixed
open Finset Lower Link Band Blocks Generic Degrees
set_option maxRecDepth 12000
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] [Module Field5 V]

def triple (j : Fin 5) : Strip.Seed := {(0,1,0),(1,0,0),(j,0,1)}

private theorem two_zero_bound : rankCount (triple 0)≤3^25 := by
  have free : Free (triple 0) := by simp only [Free,triple,forall_mem_insert,mem_singleton,forall_eq]; repeat' apply And.intro <;> decide
  have nz : Mixed.NoZeroSum (triple 0) := by simp only [Mixed.NoZeroSum,triple,forall_mem_insert,mem_singleton,forall_eq]; repeat' apply And.intro <;> decide
  have d : headDegree (triple 0) 2=7 ∧ headDegree (triple 0) 3=8 := by native_decide
  apply within_quarter (triple 0) free
  apply TriangleEight.dense (within_sym _) (within_irr _) (Mixed.triangle_free free nz)
  · intro x hx
    exact (within_cap free x hx).trans (by unfold maximumDegree; omega)
  · exact two_degree_sum _ free 15 (by omega)

theorem triple_bound {j : Fin 5} (legal : j=0 ∨ j=1 ∨ j=4) : rankCount (triple j)≤3^25 := by
  rcases legal with rfl|rfl|rfl
  · exact two_zero_bound
  · exact (Strip.model_bound .sameTriple).le
  · exact (Strip.model_bound .oppositeTriple).le

open scoped Classical

theorem external_head {s : Finset (Pt V)} (out : Disjoint s (full V)) {x : Pt V} (hx : x∈s) :
    x.1=0 ∨ x.1=1 ∨ x.1=4 := by
  have allow : ∀ i : Fin 5, ¬(i=2 ∨ i=3) → i=0 ∨ i=1 ∨ i=4 := by decide
  exact allow _ fun h => disjoint_left.mp out hx ((mem_full (u:=x)).mpr h)

theorem outside_image {s : Finset (Pt V)} (out : Disjoint s (full V)) (e : Pt V ≃+ Pt V)
    (bands : ∀x, x∈full V ↔ e x∈full V) : Disjoint (s.image e) (full V) := by
  apply disjoint_left.mpr
  intro x hx h
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  exact disjoint_left.mp out ha ((bands a).mpr h)

theorem positive_triple (u w t : V) (j : Fin 5)
    (sf : Free ({(0,u),(1,w),(j,t)} : Finset (Pt V))) (out : Disjoint ({(0,u),(1,w),(j,t)} : Finset (Pt V)) (full V)) :
    rankCount ({(0,u),(1,w),(j,t)} : Finset (Pt V))≤3^(Fintype.card V) := by
  let s : Finset (Pt V) := {(0,u),(1,w),(j,t)}
  let v := t+scalar j • (-w)
  let e := StripFamily.shear (-w)
  have first : e (0,u)=(0,u) := by change (0,u+(0:Field5) • (-w))=_; simp
  have anchor : e (1,w)=(1,0) := by change (1,w+(1:Field5) • (-w))=_; simp
  have last : e (j,t)=(j,v) := rfl
  have normal : s.image e=StripFamily.embedded (pairMap u v) (triple j) := by
    simp only [s,image_insert,image_singleton,first,anchor,last,StripFamily.embedded,triple]
    change _=insert (0,(1:Field5) • u+(0:Field5) • v) (insert (1,(0:Field5) • u+(0:Field5) • v) {(j,(0:Field5) • u+(1:Field5) • v)})
    simp
  have nz : u≠0 := by
    rintro rfl
    have h : (0:Pt V)∈s := mem_insert_self _ _
    exact sf _ h _ h _ h (zero_add _)
  have legal := external_head out (show (j,t)∈s by simp [s])
  have f := (Assembly.free_image e s).mpr sf
  have o := outside_image out e (fun x => (mem_full (u:=x)).trans (mem_full (u:=e x)).symm)
  rw [normal] at f o
  rw [show rankCount s=rankCount (s.image e) from StripFamily.shear_count (-w) s,normal]
  exact pair_bound _ (triple_bound legal) u v nz f o

theorem triple_from_members {s : Finset (Pt V)} (size : s.card=3) {x y : Pt V}
    (hx : x∈s) (hy : y∈s) (ne : x≠y) : ∃ z, s={x,y,z} := by
  have sub : {x,y}⊆s := insert_subset hx (singleton_subset_iff.mpr hy)
  have num : (s\{x,y}).card=1 := by have eq := card_sdiff_add_card_eq_card sub; rw [card_pair ne,size] at eq; omega
  obtain ⟨z,eq⟩ := card_eq_one.mp num
  have orig := sdiff_union_of_subset sub
  rw [eq] at orig
  exact ⟨z,by rw [←orig]; ext a; simp only [mem_union,mem_singleton,mem_insert]; tauto⟩

theorem mixed_three {s : Finset (Pt V)} (sf : Free s) (out : Disjoint s (full V)) (size : s.card=3)
    {x y : Pt V} (hx : x∈s) (hy : y∈s) (xzero : x.1=0) (ynon : y.1≠0) :
    rankCount s≤3^(Fintype.card V) := by
  have ne : x≠y := fun h => ynon (h ▸ xzero)
  obtain ⟨z,eq⟩ := triple_from_members size hx hy ne
  obtain ⟨i,u⟩ := x
  obtain ⟨j,w⟩ := y
  obtain ⟨l,t⟩ := z
  change i=0 at xzero
  subst i
  have heads := external_head out hy
  change j=0 ∨ j=1 ∨ j=4 at heads
  rcases heads with bad|rfl|rfl
  · exact (ynon bad).elim
  · rw [eq] at sf out ⊢
    exact positive_triple u w t l sf out
  · let e := AddEquiv.neg (Pt V)
    have negSeed : s.image e={(0,-u),(1,-w),(-l,-t)} := by
      rw [eq]; simp only [image_insert,image_singleton]; change {(-0,-u),(-(4:Fin 5),-w),(-l,-t)} = _; rw [neg_zero,show -(4:Fin 5)=1 from by decide]
    have bands (p : Pt V) : p∈full V ↔ e p∈full V := by
      simp only [mem_full]
      exact (show ∀h : Fin 5,(h=2 ∨ h=3) ↔ (-h=2 ∨ -h=3) by decide) _
    have f := (Assembly.free_image e s).mpr sf
    have o := outside_image out e bands
    rw [negSeed] at f o
    rw [StripFamily.transport e bands s,negSeed]
    exact positive_triple (-u) (-w) (-t) (-l) f o

end
end Audit.SmallMixed




