import Audit.CrossProfiles
import Audit.StripTransport

namespace Audit.MixedTenEight
open Finset Generic Band Link Lower Blocks Degrees StripFamily
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

def pat (a r t : Space k) : Finset (Pt (Space k)) := {(0,a),(1,0),(1,r),(1,t),(4,-a)}

private theorem plus_three
    (model : ∀ a r t : Space k, Free (pat a r t) → (pat a r t).card=5 → rankCount (pat a r t)≤3^(5^k))
    (sf : Free s) (size : s.card=5) (a p : Space k)
    (ha : (0,a)∈s) (hp : (1,p)∈s) (hq : (4,-(p+a))∈s) (three : (seedLayer s 1).card=3) :
    rankCount s≤3^(5^k) := by
  let P:=seedLayer s 1
  have pin : ((1:Fin 5),p)∈P := mem_filter.mpr ⟨hp,rfl⟩
  have zeros : (0,a)∉P := fun h => (by decide : (0:Fin 5)≠1) (mem_filter.mp h).2
  have four : (4,-(p+a))∉P := fun h => (by decide : (4:Fin 5)≠1) (mem_filter.mp h).2
  have f0 : (0,a)∉insert (4,-(p+a)) P := by simp (config:={decide:=true}) [zeros]
  have five : (insert (0,a) (insert (4,-(p+a)) P)).card=5 := by
    rw [card_insert_of_not_mem f0,card_insert_of_not_mem four]
    change (seedLayer s 1).card+1+1=5
    omega
  have shape : s=insert (0,a) (insert (4,-(p+a)) P) := by
    symm
    exact eq_of_subset_of_card_le (insert_subset ha (insert_subset hq (filter_subset ..))) (size.trans five.symm).le
  have two := card_erase_add_one pin
  change (P.erase (1,p)).card+1=(seedLayer s 1).card at two
  obtain ⟨⟨i,r⟩,⟨j,t⟩,_,pair⟩ := card_eq_two.mp (show (P.erase (1,p)).card=2 by omega)
  have rem : P=insert (1,p) {(i,r),(j,t)} := by rw [←pair,insert_erase pin]
  have ri : i=1 := (mem_filter.mp (show (i,r)∈P by rw [rem]; simp)).2
  have tj : j=1 := (mem_filter.mp (show (j,t)∈P by rw [rem]; simp)).2
  subst i; subst j
  let e:=shear (-p)
  have e0 : e (0,a)=(0,a) := Prod.ext rfl (by change a+(0:Field5) • (-p)=a; simp)
  have e1 (u : Space k) : e (1,u)=(1,u-p) :=
    Prod.ext rfl (by change u+(1:Field5) • (-p)=_; rw [one_smul,sub_eq_add_neg])
  have e4 : e (4,-(p+a))=(4,-a) := Prod.ext rfl (by
    change -(p+a)+(4:Field5) • (-p)= -a
    rw [show (4:Field5)= -1 by decide,neg_one_smul,neg_neg]; abel)
  have normal : s.image e=pat a (r-p) (t-p) := by
    rw [shape,rem]
    simp only [image_insert,image_singleton,e0,e1,e4,sub_self,pat]
    ext x; simp only [mem_insert,mem_singleton]; tauto
  have f := (Assembly.free_image e s).mpr sf
  have cs : (s.image e).card=5 := (card_image_of_injective _ e.injective).trans size
  rw [normal] at f cs
  rw [show rankCount s=rankCount (s.image e) from shear_count (-p) s,normal]
  exact model _ _ _ f cs

theorem classify
    (model : ∀ a r t : Space k, Free (pat a r t) → (pat a r t).card=5 → rankCount (pat a r t)≤3^(5^k))
    (sf : Free s) (size : s.card=5) (cross : Mixed.Crossing s)
    (layers : (seedLayer s 1).card=3 ∨ (seedLayer s 4).card=3) :
    rankCount s≤3^(5^k) := by
  obtain ⟨a,p,_,ha,hp,hq⟩:=cross
  rcases layers with three|three
  · exact plus_three model sf size a p ha hp hq three
  rw [negate_count s]
  let n:=s.image Neg.neg
  have nf : Free n := (Assembly.free_image (AddEquiv.neg _) s).mpr sf
  have ns : n.card=5 := (card_image_of_injective _ neg_injective).trans size
  have flip : seedLayer n 1=(seedLayer s 4).image Neg.neg := by
    ext y
    constructor
    · intro h; obtain ⟨ys,y1⟩:=mem_filter.mp h
      obtain ⟨x,xs,rfl⟩:=mem_image.mp ys
      have h4 : x.1=4 := (show ∀ i : Fin 5,-i=1 → i=4 by decide) _ y1
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨xs,h4⟩,rfl⟩
    · intro h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h
      obtain ⟨xs,x4⟩:=mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_image_of_mem _ xs,by change -x.1=1; rw [x4]; decide⟩
  have th : (seedLayer n 1).card=3 := by rw [flip,card_image_of_injective _ neg_injective,three]
  apply plus_three model nf ns (-a) (p+a) _ _ _ th
  · exact mem_image.mpr ⟨_,ha,Prod.ext (by decide : -(0:Fin 5)=0) rfl⟩
  · exact mem_image.mpr ⟨_,hq,Prod.ext (by decide : -(4:Fin 5)=1) (neg_neg _)⟩
  · exact mem_image.mpr ⟨_,hp,Prod.ext (by decide : -(1:Fin 5)=4) (show -p= -(p+a+-a) by abel)⟩

end
end Audit.MixedTenEight
