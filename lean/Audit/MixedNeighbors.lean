import Audit.MixedCounts

namespace Audit.Mixed
open Finset Sumfree Fingerprint Degrees Generic Band Link Lower Blocks
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

def across (s : Finset (Pt K)) (x : Raw.Point K) :=
  (neighbors (within s) Raw.domain x).filter (fun y => y.1≠x.1)

theorem across_lower (s : Finset (Pt K)) {x : Raw.Point K} (hx : x∈Raw.domain) :
    (seedLayer (forward s) 1).card+(seedLayer s 0).card ≤ (across s x).card := by
  let up := seedLayer (forward s) 1
  let zero := seedLayer s 0
  let lift (u : Pt K) : Raw.Point K := (u.1,u.2,0)
  have inj : Function.Injective lift := fun _ _ h => congrArg projection h
  let sign : Raw.Point K → Raw.Point K := if x.1=2 then id else Neg.neg
  have si : Function.Injective sign := by
    by_cases h : x.1=2
    · simpa only [sign,if_pos h] using (@Function.injective_id (Raw.Point K))
    · simpa only [sign,if_neg h] using (@neg_injective (Raw.Point K) _)
  let f (u : Pt K) := x+sign (lift u)
  let g (a : Pt K) := lift a-x
  have fi : Function.Injective f := (add_right_injective _).comp (si.comp inj)
  have gi : Function.Injective g := by
    intro u v h; apply inj
    simpa [g] using congrArg (fun w => w+x) h
  have xd := (mem_filter.mp hx).2
  have f0 (u : Pt K) : (f u).2.2=x.2.2 := by
    by_cases b : x.1=2 <;> simp [f,sign,lift,b,Prod.mk_add_mk]
  have g0 (u : Pt K) : (g u).2.2= -x.2.2 := by simp [g,lift]
  have zc : x.2.2 ≠ -x.2.2 := (valid_sign _ xd.2).2
  have aUnion : Disjoint (up.image f) (zero.image g) := by
    apply disjoint_left.mpr
    intro v ha hb; obtain ⟨u,_,rfl⟩ := mem_image.mp ha; obtain ⟨w,_,eq⟩ := mem_image.mp hb
    exact zc ((f0 u).symm.trans ((congrArg (fun p : Raw.Point K => p.2.2) eq).symm.trans (g0 w)))
  have one (u : Pt K) (hu : u∈up) : f u∈across s x := by
    obtain ⟨uf,uh⟩ := mem_filter.mp hu
    have un := (mem_filter.mp uf).1
    have hs : ((f u).1=2 ∨ (f u).1=3) ∧ (f u).1≠x.1 := by
      rcases xd.1 with b|b <;> simp [f,sign,lift,b,uh] <;> decide
    have mem : f u∈Raw.domain := mem_filter.mpr ⟨mem_univ _,hs.1,(f0 u).symm ▸ xd.2⟩
    have e : x≠f u := fun eq => hs.2 ((congrArg Prod.fst eq).symm)
    have plus {u : Pt K} (h : u∈s) : lift u∈plane s := (in_plane ..).mpr ⟨h,rfl⟩
    have minus {u : Pt K} (h : -u∈s) : -lift u∈plane s := (in_plane ..).mpr ⟨h,neg_zero⟩
    have hit : edge (plane s) x (f u) := by
      refine ⟨e,Or.inr ?_⟩
      by_cases b : x.1=2
      · rcases mem_signed.mp un with h|h
        · exact Or.inl (by simpa [f,sign,b] using plus h)
        · exact Or.inr (by simpa [f,sign,b] using minus h)
      · rcases mem_signed.mp un with h|h
        · exact Or.inr (by simpa [f,sign,b] using plus h)
        · exact Or.inl (by simpa [f,sign,b] using minus h)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem,hx,mem,hit⟩,hs.2⟩
  have two (a : Pt K) (ha : a∈zero) : g a∈across s x := by
    obtain ⟨az,as0⟩ := mem_filter.mp ha
    have hs : ((g a).1=2 ∨ (g a).1=3) ∧ (g a).1≠x.1 := by
      rcases xd.1 with b|b <;> simp [g,lift,b,as0] <;> decide
    have mem : g a∈Raw.domain := mem_filter.mpr ⟨mem_univ _,hs.1,(g0 _).symm ▸ (valid_sign _ xd.2).1⟩
    have hit : edge (plane s) x (g a) := by
      refine ⟨fun e => hs.2 ((congrArg Prod.fst e).symm),Or.inl ?_⟩
      rw [show x+g a=lift a by dsimp [g]; abel]; exact (in_plane ..).mpr ⟨az,rfl⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem,hx,mem,hit⟩,hs.2⟩
  have sub : up.image f ∪ zero.image g ⊆ across s x :=
    union_subset (image_subset_iff.mpr one) (image_subset_iff.mpr two)
  have bound := card_le_card sub
  rwa [card_union_of_disjoint aUnion,card_image_of_injective _ fi,card_image_of_injective _ gi] at bound

theorem high_sum {s : Finset (Pt K)} (sf : Free s) {x : Raw.Point K} (hx : x∈Raw.domain)
    (high : headDegree s x.1=maximumDegree s) :
    (∑ y∈neighbors (within s) Raw.domain x,(neighbors (within s) Raw.domain y).card)+
      ((seedLayer (forward s) 1).card+(seedLayer s 0).card)*(maximumDegree s-minimumDegree s)
      ≤ maximumDegree s ^ 2 := by
  let g := within s
  let n := neighbors g Raw.domain x
  let others := across s x
  have sub : others⊆n := filter_subset ..
  have d := (within_degree sf hx).trans high
  have partition : others.card+(n\others).card=maximumDegree s := by rw [add_comm,card_sdiff_add_card_eq_card sub]; exact d
  have low (y : Raw.Point K) (hy : y∈others) : (neighbors g Raw.domain y).card=minimumDegree s := by
    obtain ⟨yn,diff⟩ := mem_filter.mp hy
    have yd := (mem_filter.mp yn).1
    rw [within_degree sf yd]
    have yg := (mem_filter.mp yd).2.1; have xg := (mem_filter.mp hx).2.1
    unfold maximumDegree at high; unfold minimumDegree
    rcases xg with xx|xx <;> rcases yg with yy|yy <;> rw [xx] at high <;> rw [xx,yy] at diff <;> rw [yy] <;> omega
  have spl : (∑ y∈n,(neighbors g Raw.domain y).card) = (∑ y∈others,(neighbors g Raw.domain y).card)+
      ∑ y∈n\others,(neighbors g Raw.domain y).card := by
    have eq := sum_union (f:=fun y => (neighbors g Raw.domain y).card)
      (disjoint_left.mpr (fun _ ha hb => (mem_sdiff.mp hb).2 ha) : Disjoint others (n\others))
    rwa [union_sdiff_of_subset sub] at eq
  have sl : (∑ y∈others,(neighbors g Raw.domain y).card)=others.card*minimumDegree s :=
    (sum_congr rfl low).trans (by simp)
  have su : (∑ y∈n\others,(neighbors g Raw.domain y).card)≤(n\others).card*maximumDegree s := by
    have le (y : Raw.Point K) (hy : y∈n\others) : (neighbors g Raw.domain y).card≤maximumDegree s :=
      within_cap sf y (mem_filter.mp (mem_sdiff.mp hy).1).1
    exact (sum_le_sum le).trans_eq (by simp)
  have rate := Nat.mul_le_mul_right (maximumDegree s-minimumDegree s) (across_lower s hx)
  have ord : minimumDegree s≤maximumDegree s := min_le_max
  have delta := Nat.sub_add_cancel ord
  change _ + _ ≤ _
  rw [show (∑ y∈neighbors (within s) Raw.domain x,(neighbors (within s) Raw.domain y).card)=_ from spl,sl]
  calc
    _ ≤ others.card*minimumDegree s+(n\others).card*maximumDegree s+others.card*(maximumDegree s-minimumDegree s) :=
      Nat.add_le_add (Nat.add_le_add_left su _) rate
    _ = _ := by
      nlinarith only [congrArg (fun v : ℕ => v*maximumDegree s) partition,
        congrArg (fun v : ℕ => others.card*v) delta]

end
end Audit.Mixed
