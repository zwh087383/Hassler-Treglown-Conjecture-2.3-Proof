import Audit.Subcubic

namespace Audit.CubeCases
open Finset Sumfree Fingerprint Potential GraphMeasure Subcubic
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop)

def Induction (b : ℝ) (s : Finset V) :=
  ∀ t, t⊂s → (mis r t:ℝ) ≤ (3:ℝ)^(mu r b t)

private theorem strict {s t : Finset V} (non : t.Nonempty) (sub : t⊆s) : s\t⊂s :=
  Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun eq => by
    obtain ⟨x,xt⟩ := non
    exact (mem_sdiff.mp (eq.symm ▸ sub xt)).2 xt⟩

theorem weighted (sym : Symmetric r) {s t : Finset V} {b u : ℝ} (ih : Induction r b s)
    (b0 : 0≤b) (b1 : b≤1/36) (cap : ∀ x∈s,(neighbors r s x).card≤3)
    (non : t.Nonempty) (sub : t⊆s) (edges : 2*t.card≤volume r t)
    (weight : (3:ℝ)^(-((t.card:ℝ)*(11/36)))≤u) :
    (mis r (s\t):ℝ) ≤ u*(3:ℝ)^(mu r b s) := by
  apply ratio r (ih _ (strict non sub)) _ weight
  apply le_trans _ (drop r sym sub (fun x h => cap x (sub h)) b0)
  have e : (2:ℝ)*t.card ≤ volume r t := by exact_mod_cast edges
  nlinarith only [mul_le_mul_of_nonneg_left e b0,mul_le_mul_of_nonneg_right b1 (Nat.cast_nonneg (α:=ℝ) t.card)]

private theorem weight3 : (3:ℝ)^(-((3:ℝ)*(11/36)))≤11/30 := by
  convert neg_weight 11 12 (11/30) (by decide) (by norm_num) (by norm_num) using 2 <;> norm_num
private theorem weight4 : (3:ℝ)^(-((4:ℝ)*(11/36)))≤4/15 := by
  convert neg_weight 11 9 (4/15) (by decide) (by norm_num) (by norm_num) using 2 <;> norm_num
private theorem weight5 : (3:ℝ)^(-((5:ℝ)*(11/36)))≤1/5 := by
  convert neg_weight 55 36 (1/5) (by decide) (by norm_num) (by norm_num) using 2 <;> norm_num

private theorem clique4 (sym : Symmetric r) (irr : Irreflexive r) {s t : Finset V} {b : ℝ}
    (ih : Induction r b s) (b0 : 0≤b) (b1 : b≤1/36) (cap : ∀ x∈s,(neighbors r s x).card≤3)
    (sub : t⊆s) (cl : Clique r t) (size : t.card=4) :
    (mis r s:ℝ) ≤ (3:ℝ)^(mu r b s) := by
  obtain ⟨x,xt⟩ := card_pos.mp (show 0<t.card by omega)
  have eq := eq_of_subset_of_card_le (clique_closed r sub cl xt) (show (closed r s x).card≤t.card by
    rw [closed_card r sym irr (sub xt),size]; have h := cap x (sub xt); omega)
  have zero := avoid_zero r sym (sub xt) eq.ge
  have weight : (mis r (s\t):ℝ) ≤ (1/4:ℝ)*(3:ℝ)^(mu r b s) := by
    apply ratio r (ih _ (strict ⟨x,xt⟩ sub)) (p:=23/18)
    · apply le_trans _ (drop r sym sub (fun x hx => cap x (sub hx)) b0)
      rw [clique_volume r irr cl,size]; push_cast; norm_num; linarith
    · simpa only [Nat.cast_ofNat,neg_div] using neg_weight 23 18 (1/4) (by decide) (by norm_num) (by norm_num)
  have bound (x : V) (xt : x∈t) : (picked r s x ∅).card≤mis r (s\t) :=
    chosen_le r sym irr (clique_closed r sub cl xt)
  have cov := count_cover r s t
  rw [zero,add_zero] at cov
  have ct := cov.trans (sum_le_sum bound)
  simp only [sum_const,nsmul_eq_mul,size] at ct
  have h : (mis r s:ℝ)≤4*(mis r (s\t):ℝ) := by exact_mod_cast ct
  linarith

theorem step (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V} {b : ℝ}
    (ih : Induction r b s) (b0 : 0≤b) (b1 : b≤1/36) (cap : ∀ x∈s,(neighbors r s x).card≤3) :
    (mis r s:ℝ) ≤ (3:ℝ)^(mu r b s) := by
  classical
  by_cases existsT : ∃ t,Triangle r s t
  case neg => exact (trianglefree_count r sym irr existsT).trans (cutoff r b0 b1 cap)
  obtain ⟨t,sub,ts,cl⟩ := existsT
  have tn : t.Nonempty := card_pos.mp (by omega)
  let M : ℝ := (3:ℝ)^(mu r b s)
  have Mp : 0≤M := Real.rpow_nonneg (by norm_num) _
  let ext (x z : V) := z∈s ∧ z∉t ∧ r x z
  have edges3 : volume r t=6 := by rw [clique_volume r irr cl,ts]
  have triBound : (mis r (s\t):ℝ) ≤ (11/30)*M :=
    weighted r sym ih b0 b1 cap tn sub (by omega) (by rw [ts]; exact weight3)
  have one3 (x : V) (xt : x∈t) : ((picked r s x ∅).card:ℝ)≤(11/30)*M :=
    (Nat.cast_le.mpr (chosen_le r sym irr (clique_closed r sub cl xt))).trans triBound
  have boxed {x z : V} (xt : x∈t) (other : ext x z) : closed r s x=insert z t := by
    apply Eq.symm
    apply eq_of_subset_of_card_le (insert_subset (mem_closed.mpr ⟨other.1,Or.inr (sym other.2.2)⟩) (clique_closed r sub cl xt))
    rw [closed_card r sym irr (sub xt),card_insert_of_not_mem other.2.1,ts]
    have h := cap _ (sub xt); omega
  have noOut {x : V} (xt : x∈t) (none : ¬∃z,ext x z) : closed r s x⊆t := by
    intro z hz
    obtain ⟨zs,eq|e⟩ := mem_closed.mp hz
    · simpa only [eq] using xt
    · exact Classical.byContradiction (fun absent => none ⟨z,zs,absent,sym e⟩)
  have one4 {x z : V} (xt : x∈t) (other : ext x z) : ((picked r s x ∅).card:ℝ)≤(4/15)*M := by
    have ct : (insert z t).card=4 := by rw [card_insert_of_not_mem other.2.1,ts]
    have v := inside_degree r other.2.1 xt (sym other.2.2) sym irr
    have w := weighted r sym ih b0 b1 cap (insert_nonempty ..) (insert_subset other.1 sub)
      (by rw [ct]; omega) (u:=4/15) (by rw [ct]; exact weight4)
    exact (Nat.cast_le.mpr (chosen_le r sym irr (boxed xt other).ge)).trans w
  have cov : (mis r s:ℝ) ≤ (∑ x∈t,((picked r s x ∅).card:ℝ))+(avoid r s t).card := by exact_mod_cast count_cover r s t
  by_cases witness : ∃ x∈t,∃ z,ext x z
  case neg =>
    have none (x) (hx : x∈t) : ¬∃ z,ext x z := fun h => witness ⟨x,hx,h⟩
    obtain ⟨x,xt⟩ := tn
    have zero := avoid_zero r sym (sub xt) (noOut xt (none x xt))
    have noCross : cross r t (s\t)=0 := by
      apply sum_eq_zero
      intro u hu; apply card_eq_zero.mpr; apply eq_empty_iff_forall_not_mem.mpr
      intro z hz
      obtain ⟨h,e⟩ := mem_filter.mp hz
      exact none u hu ⟨z,(mem_sdiff.mp h).1,(mem_sdiff.mp h).2,e⟩
    have decomp := split_volume r sym (a:=t) (b:=s\t) (disjoint_left.mpr (fun _ ht hb => (mem_sdiff.mp hb).2 ht))
    rw [union_sdiff_of_subset sub,noCross,edges3] at decomp
    have exactWeight : (mis r (s\t):ℝ)≤(1/3)*M := by
      apply ratio r (ih _ (strict ⟨x,xt⟩ sub)) (p:=1)
      · rw [difference r b sub,ts]; have casted : (volume r s:ℝ)=6+volume r (s\t) := by exact_mod_cast (by omega : volume r s=6+volume r (s\t))
        rw [casted]; push_cast; linarith [b0]
      · norm_num
    have bound (y) (hy : y∈t) : ((picked r s y ∅).card:ℝ)≤(1/3)*M :=
      (Nat.cast_le.mpr (chosen_le r sym irr (clique_closed r sub cl hy))).trans exactWeight
    have sum := sum_le_sum bound
    rw [sum_const,ts] at sum; rw [zero,Nat.cast_zero,add_zero] at cov
    change _ ≤ M
    apply cov.trans; apply sum.trans; norm_num; ring_nf; exact le_rfl
  obtain ⟨x,xt,u,ux⟩ := witness
  by_cases all : ∀ y∈t,∃ z,ext y z
  case neg =>
    push_neg at all
    obtain ⟨y,yt,empty⟩ := all
    have zero := avoid_zero r sym (sub yt) (noOut yt (by simpa only [not_exists] using empty))
    have sum2 := sum_le_sum (s:=t.erase x) (fun z hz => one3 z (mem_of_mem_erase hz))
    rw [sum_const,card_erase_of_mem xt,ts] at sum2
    have split := sum_erase_add t (fun z => ((picked r s z ∅).card:ℝ)) xt
    rw [zero,Nat.cast_zero,add_zero,←split] at cov
    have w := one4 xt ux
    change _ ≤ M
    norm_num at sum2; linarith
  by_cases same : ∀ y∈t,r y u
  case pos =>
    apply clique4 r sym irr ih b0 b1 cap (insert_subset ux.1 sub) (t:=insert u t)
    · intro y hy z hz ne
      rcases mem_insert.mp hy with rfl|yt <;> rcases mem_insert.mp hz with rfl|zt
      · exact (ne rfl).elim
      · exact sym (same z zt)
      · exact same y yt
      · exact cl y yt z zt ne
    · rw [card_insert_of_not_mem ux.2.1,ts]
  push_neg at same
  obtain ⟨y,yt,yu⟩ := same
  obtain ⟨v,vy⟩ := all y yt
  have vu : v≠u := fun eq => yu (eq ▸ vy.2.2)
  have forced {p z : V} (pt : p∈t) (ex : ext p z) {i : Finset V} (hi : i∈avoid r s t) : z∈i := by
    obtain ⟨member,clear⟩ := mem_filter.mp hi
    obtain ⟨a,box,ai⟩ := hit_closed sym (mem_family.mp member) (sub pt)
    rw [boxed pt ex] at box
    rcases mem_insert.mp box with rfl|inside
    · exact ai
    · exact (disjoint_left.mp clear ai inside).elim
  have avoidSub : avoid r s t ⊆ (family r s).filter (fun i => {v,u}⊆i ∧ Disjoint i t) := by
    intro i hi
    have h := mem_filter.mp hi
    exact mem_filter.mpr ⟨h.1,insert_subset (forced yt vy hi) (singleton_subset_iff.mpr (forced xt ux hi)),h.2⟩
  have ac := (card_le_card avoidSub).trans (prescribed r sym irr s {v,u} t)
  have vn : v∉insert u t := fun h => (mem_insert.mp h).elim vu vy.2.1
  let t5 := insert v (insert u t)
  have v1 := inside_degree r ux.2.1 xt (sym ux.2.2) sym irr
  have v2 := inside_degree r vn (Finset.mem_insert_of_mem yt) (sym vy.2.2) sym irr
  have ct5 : t5.card=5 := by dsimp only [t5]; rw [card_insert_of_not_mem vn,card_insert_of_not_mem ux.2.1,ts]
  have edges5 : 2*t5.card≤volume r t5 := by rw [ct5]; dsimp only [t5]; omega
  have w5 := weighted r sym ih b0 b1 cap (t:=t5) (insert_nonempty ..) (insert_subset vy.1 (insert_subset ux.1 sub))
    edges5 (u:=1/5) (by rw [ct5]; exact weight5)
  have aset : {v,u}∪t=t5 := by ext z; simp [t5,or_assoc]
  rw [aset] at ac
  have avoidBound := (Nat.cast_le (α:=ℝ)).mpr ac |>.trans w5
  have sum := sum_le_sum (s:=t) (fun z hz => by obtain ⟨q,hq⟩ := all z hz; exact one4 hz hq)
  rw [sum_const,ts] at sum
  change _ ≤ M
  norm_num at sum; linarith

end
end Audit.CubeCases
