import Audit.TriangleCommon

namespace Audit.TriangleCoordinates
open Finset Sumfree Generic Band Link Lower Blocks Degrees Fingerprint TriangleBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
variable {s : Finset (Pt K)} {v : Raw.Point K} {t p q : Pt K}

private theorem unpaired (sf : Free s) (tp : t∈s) (pp : p∈s) (qp : q∈s) (rel : t+p+q=0) :
    -t∉s ∧ -p∉s ∧ -q∉s := by
  have t' : p+q= -t := eq_neg_of_add_eq_zero_left (by rw [←rel]; abel)
  have p' : t+q= -p := eq_neg_of_add_eq_zero_left (by rw [←rel]; abel)
  have q' : t+p= -q := eq_neg_of_add_eq_zero_left rel
  exact ⟨fun h => sf _ pp _ qp _ h t',fun h => sf _ tp _ qp _ h p',fun h => sf _ tp _ pp _ h q'⟩

structure Walk {V : Type*} (r : V → V → Prop) (a b c d : V) : Prop where
  ab : r a b
  bc : r b c
  cd : r c d
  ac : a≠c
  ad : a≠d
  bd : b≠d

theorem Walk.volume {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop} {a b c d : V}
    (w : Walk r a b c d) (sym : Symmetric r) (irr : Irreflexive r) {f : Finset V}
    (ha : a∈f) (hb : b∈f) (hc : c∈f) (hd : d∈f) : 6≤vol r f :=
  path_volume sym irr ha hb hc hd w.ab w.bc w.cd w.ac w.ad w.bd

private def StepOK (v : Raw.Point K) (t p q : Pt K) : Prop :=
  allows v (-t) ∧ allows v p ∧ allows v (-q) ∧ allows v t

private theorem same_member (sf : Free s) (hv : v∈Raw.domain) {d : Pt K} (gd : allows v d)
    (sd : d∈signed s) : point v d ∈ neighbors (within s) Raw.domain v := by
  have dom:=point_dom hv gd
  exact mem_filter.mpr ⟨dom,by simpa using same sf v (a:=0) (by simpa using hv) dom (by simpa using sd)⟩

private theorem step_data (sf : Free s) (hv : v∈Raw.domain) (tp : t∈s) (pp : p∈s) (qp : q∈s)
    (rel : t+p+q=0) (permitted : StepOK v t p q) (pt : p≠t) (tq : t≠q) :
    let a:=point v (-t); let b:=point v p; let c:=point v (-q); let d:=point v t
    let n:=neighbors (within s) Raw.domain v
    Walk (within s) a b c d ∧ a∈n ∧ b∈n ∧ c∈n ∧ d∈n := by
  dsimp only
  obtain ⟨oa,ob,oc,od⟩ := permitted
  have aa := same_member sf hv oa (mem_signed.mpr (Or.inr (by simpa using tp)))
  have bb := same_member sf hv ob (mem_signed.mpr (Or.inl pp))
  have cc := same_member sf hv oc (mem_signed.mpr (Or.inr (by simpa using qp)))
  have dd := same_member sf hv od (mem_signed.mpr (Or.inl tp))
  have g1 : p-(-t)= -q := by rw [←eq_neg_of_add_eq_zero_left rel]; abel
  have g2 : (-q)-p=t := by rw [←eq_neg_of_add_eq_zero_left rel]; abel
  have g3 : t-(-q)= -p := eq_neg_of_add_eq_zero_left (by rw [←rel]; abel)
  have ab := same sf v (mem_filter.mp aa).1 (mem_filter.mp bb).1
    (by rw [g1]; exact mem_signed.mpr (Or.inr (by simpa using qp)))
  have bc := same sf v (mem_filter.mp bb).1 (mem_filter.mp cc).1 (by rw [g2]; exact mem_signed.mpr (Or.inl tp))
  have cd := same sf v (mem_filter.mp cc).1 (mem_filter.mp dd).1
    (by rw [g3]; exact mem_signed.mpr (Or.inr (by simpa using pp)))
  have neg : -t≠t := fun h => (unpaired sf tp pp qp rel).1 (by rw [h]; exact tp)
  exact ⟨⟨ab,bc,cd,(inject_point v).ne (neg_injective.ne tq),(inject_point v).ne neg,
     (inject_point v).ne pt⟩,aa,bb,cc,dd⟩

private theorem cert_at (sf : Free s) (out : Disjoint s (full K)) (count : 6≤s.card+(seedLayer s 0).card)
    (hv : v∈Raw.domain) (tp : t∈s) (pp : p∈s) (qp : q∈s) (rel : t+p+q=0)
    (perm : StepOK v t p q) (rev : StepOK (-v) t q p) (pt : p≠t) (tq : t≠q) :
    let n:=neighbors (within s) Raw.domain v
    let m:=neighbors (within s) Raw.domain (-v)
    let safe:=m∩TrianglePartner.protectedZone (within s) Raw.domain v
    6≤vol (within s) n ∧ 6≤(n∩m).card ∧ 8≤safe.card ∧ 6≤vol (within s) safe := by
  dsimp only
  let n:=neighbors (within s) Raw.domain v
  let m:=neighbors (within s) Raw.domain (-v)
  let safe:=m∩TrianglePartner.protectedZone (within s) Raw.domain v
  let a:=point (-v) (-t)
  let b:=point (-v) q
  let c:=point (-v) (-p)
  let d:=point (-v) t
  have sym:=within_sym s
  have irr:=within_irr s
  obtain ⟨walk,f1,f2,f3,f4⟩ := step_data sf hv tp pp qp rel perm pt tq
  have rel' : t+q+p=0 := by simpa only [add_right_comm] using rel
  obtain ⟨walk',an,_,cn,_⟩ := step_data sf (opposite_domain hv) tp qp pp rel' rev tq.symm pt.symm
  have bs : b∈common s v := common_right qp rev.2.1
  have ds : d∈common s v := common_right tp rev.2.2.2
  have csub:=common_sub sf hv
  have bsN := (mem_inter.mp (csub bs)).1
  have dsN := (mem_inter.mp (csub ds)).1
  have cross1 : -q+(-t)=p := by rw [←eq_neg_of_add_eq_zero_left rel]; abel
  have cross2 : -t+(-p)=q := by
    have := eq_neg_of_add_eq_zero_left rel
    calc _ = -(t+p) := by abel
         _ = q := by rw [this,neg_neg]
  have e1 := opposite hv (mem_filter.mp f3).1 (mem_filter.mp an).1 (by rw [cross1]; exact pp)
  have e2 := opposite hv (mem_filter.mp f1).1 (mem_filter.mp cn).1 (by rw [cross2]; exact qp)
  have asafe : a∈safe := mem_inter.mpr ⟨an,mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp an).1,
    two_neighbors f3 bsN (sym e1) walk'.ab (different_sides hv _ _)⟩)⟩
  have csafe : c∈safe := mem_inter.mpr ⟨cn,mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp cn).1,
    two_neighbors f1 dsN (sym e2) walk'.cd (different_sides hv _ _)⟩)⟩
  have core : common s v⊆safe := fun _ h => mem_inter.mpr ⟨(mem_inter.mp (csub h)).2,
    mem_union_left _ (mem_inter.mp (csub h)).1⟩
  have unpair := unpaired sf tp pp qp rel
  have ae : a∉common s v := outside_common hv unpair.1
  have ce : c∉common s v := outside_common hv unpair.2.1
  have ne : a≠c := (inject_point _).ne (neg_injective.ne pt.symm)
  have large := card_le_card (insert_subset asafe (insert_subset csafe core))
  rw [card_insert_of_not_mem (show a∉insert c (common s v) by simp [ne,ae]),
    card_insert_of_not_mem ce,common_count out hv] at large
  have sh := card_le_card csub
  rw [common_count out hv] at sh
  have sz : 8≤safe.card := by omega
  exact ⟨walk.volume sym irr f1 f2 f3 f4,count.trans sh,sz,
    walk'.volume sym irr asafe (core bs) csafe (core ds)⟩

theorem partner_certificate (sf : Free s) (out : Disjoint s (full K)) (count : 6≤s.card+(seedLayer s 0).card)
    (tp : t∈s) (pp : p∈s) (qp : q∈s) (th : t.1=0) (ph : p.1=1) (qh : q.1=4) (rel : t+p+q=0) :
    TrianglePartner.Certificate (within s) Raw.domain := by
  intro v hv
  have solve {a b : Pt K} (aa : a∈s) (bb : b∈s) (rel' : t+a+b=0)
      (h : v.1=2 ∧ a.1=1 ∧ b.1=4 ∨ v.1=3 ∧ a.1=4 ∧ b.1=1) :
      let n:=neighbors (within s) Raw.domain v
      let m:=neighbors (within s) Raw.domain (-v)
      let safe:=m∩TrianglePartner.protectedZone (within s) Raw.domain v
      6≤vol (within s) n ∧ 6≤(n∩m).card ∧ 8≤safe.card ∧ 6≤vol (within s) safe := by
    have permitted : StepOK v t a b ∧ StepOK (-v) t b a := by
      change ((-t.1+v.1=2 ∨ -t.1+v.1=3) ∧ (a.1+v.1=2 ∨ a.1+v.1=3) ∧
        (-b.1+v.1=2 ∨ -b.1+v.1=3) ∧ (t.1+v.1=2 ∨ t.1+v.1=3)) ∧
        ((-t.1+-v.1=2 ∨ -t.1+-v.1=3) ∧ (b.1+-v.1=2 ∨ b.1+-v.1=3) ∧
        (-a.1+-v.1=2 ∨ -a.1+-v.1=3) ∧ (t.1+-v.1=2 ∨ t.1+-v.1=3))
      rcases h with ⟨va,af,bf⟩|⟨va,af,bf⟩ <;> rw [th,va,af,bf] <;> decide
    have at' : a≠t := by
      intro e; have eh := congrArg Prod.fst e
      rcases h with ⟨_,ha,_⟩|⟨_,ha,_⟩ <;> rw [th,ha] at eh <;> contradiction
    have tb' : t≠b := by
      intro e; have eh := congrArg Prod.fst e
      rcases h with ⟨_,_,hb⟩|⟨_,_,hb⟩ <;> rw [th,hb] at eh <;> contradiction
    exact cert_at sf out count hv tp aa bb rel' permitted.1 permitted.2 at' tb'
  right
  have data :
      let n:=neighbors (within s) Raw.domain v
      let m:=neighbors (within s) Raw.domain (-v)
      let safe:=m∩TrianglePartner.protectedZone (within s) Raw.domain v
      6≤vol (within s) n ∧ 6≤(n∩m).card ∧ 8≤safe.card ∧ 6≤vol (within s) safe := by
    rcases (mem_filter.mp hv).2.1 with h|h
    · exact solve pp qp rel (Or.inl ⟨h,ph,qh⟩)
    · exact solve qp pp (by simpa only [add_right_comm] using rel) (Or.inr ⟨h,qh,ph⟩)
  have ne : -v≠v := by
    have d := different_sides hv (0:Pt K) 0
    simpa only [point_zero,ne_comm] using d
  exact ⟨data.1,-v,opposite_domain hv,ne,no_partner_edge sf hv,data.2⟩

theorem nine_cross {s : Finset (Pt K)} (sf : Free s) (out : Disjoint s (full K))
    (cap : maximumDegree s≤9) (total : 18≤headDegree s 2+headDegree s 3)
    (count : 6≤s.card+(seedLayer s 0).card) (a p : K)
    (ha : (0,a)∈s) (hp : (1,p)∈s) (hq : (4,-(p+a))∈s) :
    rankCount s≤3^Fintype.card K := by
  apply TriangleRaw.nine sf cap total
  apply partner_certificate sf out count ha hp hq rfl rfl rfl
  exact Prod.ext (show (0:Fin 5)+1+4=0 by decide) (show a+p+(-(p+a))=0 by abel)

end
end Audit.TriangleCoordinates
