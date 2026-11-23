import Audit.SmallMixedFourReduce

namespace Audit.SmallMixed
open Finset Lower Link Band Blocks Generic Degrees
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] [Module Field5 V]

theorem positive_four (table : FourTables) (u anchor v w : V) (j l : Fin 5)
    (s : Finset (Pt V)) (form : s={(0,u),(1,anchor),(j,v),(l,w)})
    (sf : Free s) (out : Disjoint s (full V)) (size : s.card=4) : rankCount s≤3^Fintype.card V := by
  let e := StripFamily.shear (-anchor)
  let v' := v+scalar j • (-anchor)
  let w' := w+scalar l • (-anchor)
  have first : e (0,u)=(0,u) := by change (0,u+(0:Field5) • (-anchor))=_; simp
  have pivot : e (1,anchor)=(1,0) := by change (1,anchor+(1:Field5) • (-anchor))=_; simp
  have third : e (j,v)=(j,v') := rfl
  have fourth : e (l,w)=(l,w') := rfl
  have eq : s.image e=marked u v' w' j l := by rw [form]; simp only [image_insert,image_singleton,first,pivot,third,fourth,marked]
  have f := (Assembly.free_image e s).mpr sf
  have o := outside_image out e (fun x => (mem_full (u:=x)).trans (mem_full (u:=e x)).symm)
  have sz : (s.image e).card=4 := (card_image_of_injective _ e.injective).trans size
  rw [eq] at f o sz
  rw [StripFamily.shear_count (-anchor) s,eq]
  exact marked_four table u v' w' j l sz f o

theorem four_from_members {s : Finset (Pt V)} (size : s.card=4) {x y : Pt V}
    (hx : x∈s) (hy : y∈s) (ne : x≠y) : ∃ z t, s={x,y,z,t} := by
  have sub : {x,y}⊆s := insert_subset hx (singleton_subset_iff.mpr hy)
  have num : (s\{x,y}).card=2 := by have e := card_sdiff_add_card_eq_card sub; rw [card_pair ne,size] at e; omega
  obtain ⟨z,t,_,eq⟩ := card_eq_two.mp num
  have orig := sdiff_union_of_subset sub
  rw [eq] at orig
  exact ⟨z,t,by rw [←orig]; ext a; simp only [mem_union,mem_singleton,mem_insert]; tauto⟩

theorem mixed_four (table : FourTables) {s : Finset (Pt V)} (sf : Free s) (out : Disjoint s (full V))
    (size : s.card=4) {x y : Pt V} (hx : x∈s) (hy : y∈s) (xzero : x.1=0) (ynon : y.1≠0) :
    rankCount s≤3^Fintype.card V := by
  have ne : x≠y := fun e => ynon (e ▸ xzero)
  obtain ⟨z,t,eq⟩ := four_from_members size hx hy ne
  obtain ⟨i,u⟩ := x
  obtain ⟨h,anchor⟩ := y
  obtain ⟨j,v⟩ := z
  obtain ⟨l,w⟩ := t
  change i=0 at xzero
  subst i
  have heads := external_head out hy
  change h=0 ∨ h=1 ∨ h=4 at heads
  rcases heads with bad|rfl|rfl
  · exact (ynon bad).elim
  · exact positive_four table u anchor v w j l s eq sf out size
  · let e := AddEquiv.neg (Pt V)
    have negSeed : s.image e={(0,-u),(1,-anchor),(-j,-v),(-l,-w)} := by
      rw [eq]; simp only [image_insert,image_singleton]
      change {(-0,-u),(-(4:Fin 5),-anchor),(-j,-v),(-l,-w)}=_
      rw [neg_zero,show -(4:Fin 5)=1 from by decide]
    have bands (p : Pt V) : p∈full V ↔ e p∈full V := by
      simp only [mem_full]
      exact (show ∀h : Fin 5,(h=2 ∨ h=3) ↔ (-h=2 ∨ -h=3) by decide) _
    rw [StripFamily.transport e bands s]
    exact positive_four table (-u) (-anchor) (-v) (-w) (-j) (-l) (s.image e) negSeed
      ((Assembly.free_image e s).mpr sf) (outside_image out e bands) ((card_image_of_injective _ e.injective).trans size)

theorem pure_four {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (size : s.card=4) (zero : ∀p∈s,p.1=0) : rankCount s≤3^Fintype.card (Space k) := by
  by_cases low : (signed s).card≤s.card+1
  · exact Mixed.at_most_one_unpaired sf out low
  · have ⟨d2,d3⟩ := pure_profile out zero
    apply MasterTable.two_degree s sf out <;> simp only [minimumDegree,maximumDegree] <;> omega

theorem four_of_tables (table : FourTables) {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s)
    (out : Disjoint s (full _)) (zero : (seedLayer s 0).Nonempty) (size : s.card=4) : rankCount s≤3^(5^k) := by
  obtain ⟨x,hx⟩ := zero
  by_cases all : ∀p∈s,p.1=0
  · simpa [Space,Field5] using pure_four sf out size all
  · push_neg at all
    obtain ⟨y,hy,hn⟩ := all
    simpa [Space,Field5] using mixed_four table sf out size (mem_filter.mp hx).1 hy (mem_filter.mp hx).2 hn

end
end Audit.SmallMixed

