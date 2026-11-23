import Audit.SmallProfiles
import Audit.SmallMixedNormalize

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees StripFamily
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

/-- Recover the common translation of the two colors, then place the actual five points
    in the certified model or in its rank-one collapse. -/
theorem eight_eight (sf : Free s) (out : Disjoint s (full _)) (size : s.card=5)
    (cross : Crossing s) (hp : (seedLayer s 1).card=2) (hq : (seedLayer s 4).card=2)
    (hu : (seedLayer (forward s) 1).card=3) : rankCount s≤3^Fintype.card (Space k) := by
  obtain ⟨a,p,na,az,plus,minus⟩ := cross
  let P := seedLayer s 1
  let Q := (seedLayer s 4).image Neg.neg
  have qc : Q.card=2 := by simpa only [Q,card_image_of_injective _ neg_injective] using hq
  have union : (P∪Q).card=3 := by rwa [signed_one] at hu
  have overlap := card_union_add_card_inter P Q
  change P.card=2 at hp
  obtain ⟨⟨j,c⟩,hc⟩ := card_pos.mp (show 0<(P∩Q).card by omega)
  obtain ⟨cp,cq⟩ := mem_inter.mp hc
  have head : j=1 := (mem_filter.mp cp).2
  subst j
  have one : ((1:Fin 5),c)∈s := (mem_filter.mp cp).1
  have four : ((4:Fin 5),-c)∈s := by
    obtain ⟨v,hv,e⟩ := mem_image.mp cq
    have f := congrArg Neg.neg e
    rw [neg_neg] at f
    exact (show v=(4,-c) from f) ▸ (mem_filter.mp hv).1
  have pc : p≠c := by
    rintro rfl
    exact sf (0,a) az (4,-(p+a)) minus (4,-p) four (Prod.ext (by rfl) (by change a+ -(p+a)= -p; abel))
  have ca : c≠p+a := by
    rintro rfl
    exact sf (0,a) az (1,p) plus (1,p+a) one (Prod.ext rfl (add_comm ..))
  have shape : s={(0,a),(1,c),(1,p),(4,-c),(4,-(p+a))} := by
    symm
    apply eq_of_subset_of_card_le (insert_subset az (insert_subset one (insert_subset plus
      (insert_subset four (singleton_subset_iff.mpr minus)))))
    rw [size]
    have ne : ((4:Fin 5),-c)≠(4,-a+ -p) := by
      intro e; apply ca; apply neg_injective; rw [neg_add_rev]; exact congrArg Prod.snd e
    simp (config:={decide:=true}) [Ne.symm pc,ca,card_pair ne]
  let r := p-c
  let e := shear (-c)
  have t0 : e (0,a)=(0,a) := Prod.ext rfl (by change a+(0:Field5) • (-c)=a; simp)
  have t1 (u : Space k) : e (1,u)=(1,u-c) := Prod.ext rfl (by change u+(1:Field5) • (-c)=_; rw [one_smul,sub_eq_add_neg])
  have t4 (u : Space k) : e (4,-u)=(4,-(u-c)) := Prod.ext rfl (by
    change -u+(4:Field5) • (-c)=_
    rw [show (4:Field5)= -1 by decide,neg_one_smul,neg_neg]; abel)
  let model := embedded (SmallMixed.pairMap a r) (Strip.seed .triangleFive)
  have eq : s.image e=model := by
    rw [shape]
    simp only [image_insert,image_singleton,t0,t1,t4,sub_self,neg_zero]
    unfold model embedded Strip.seed
    simp only [image_insert,image_singleton]
    change {(0,a),(1,0),(1,p-c),(4,0),(4,-(p+a-c))}=
      {(0,(1:Field5) • a+(0:Field5) • r),(1,(0:Field5) • a+(0:Field5) • r),
       (1,(0:Field5) • a+(1:Field5) • r),(4,(0:Field5) • a+(0:Field5) • r),
       (4,(4:Field5) • a+(4:Field5) • r)}
    simp only [one_smul,zero_smul,add_zero,zero_add,show (4:Field5)= -1 by decide,neg_one_smul]
    rw [show -(p+a-c)= -a+ -r by dsimp [r]; abel]
  have f := (Assembly.free_image e s).mpr sf
  have outside : Disjoint (s.image e) (full _) := by
    apply disjoint_left.mpr
    intro y hy b; obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact disjoint_left.mp out hx ((mem_full (u:=x)).mpr ((mem_full (u:=e x)).mp b))
  rw [eq] at f outside
  rw [show rankCount s=rankCount (s.image e) from shear_count (-c) s,eq]
  exact SmallMixed.pair_bound _ (Strip.model_bound .triangleFive).le a r na f outside

end
end Audit.Mixed
