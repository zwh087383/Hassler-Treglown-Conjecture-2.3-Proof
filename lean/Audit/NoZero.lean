import Audit.Degrees
import Audit.StripFamily
import Audit.TriangleEight
import Audit.DefectsNonzero
import Mathlib.Data.Finset.Card

namespace Audit.NoZero
open Finset Lower Link Band Blocks Generic Reduction Degrees StripFamily
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Module Field5 Strip.K := inferInstanceAs (Module Field5 (Field5 × Field5))

private def rows {K : Type} [AddCommGroup K] [DecidableEq K]
    (p q : Finset K) : Finset (Pt K) :=
  p.image (fun x => (1,x)) ∪ q.image (fun x => (4,-x))

private theorem in_rows {K : Type} [AddCommGroup K] [DecidableEq K] {p q : Finset K} {v : Pt K} :
    v∈rows p q ↔ (v.1=1 ∧ v.2∈p) ∨ (v.1=4 ∧ -v.2∈q) := by
  rcases v with ⟨i,x⟩
  simp only [rows,mem_union,mem_image,Prod.mk.injEq]
  constructor
  · rintro (⟨u,hu,rfl,rfl⟩|⟨u,hu,rfl,rfl⟩)
    · exact Or.inl ⟨rfl,hu⟩
    · exact Or.inr ⟨rfl,by simpa using hu⟩
  · rintro (⟨rfl,h⟩|⟨rfl,h⟩)
    · exact Or.inl ⟨_,h,rfl,rfl⟩
    · exact Or.inr ⟨_,h,rfl,neg_neg _⟩

private theorem rows_free {K : Type} [AddCommGroup K] [DecidableEq K] (p q : Finset K) :
    Free (rows p q) := by
  have no : ∀ a b c : Fin 5, (a=1 ∨ a=4) → (b=1 ∨ b=4) → (c=1 ∨ c=4) → a+b≠c := by decide
  intro x hx y hy z hz eq
  exact no _ _ _ ((in_rows.mp hx).imp And.left And.left) ((in_rows.mp hy).imp And.left And.left)
    ((in_rows.mp hz).imp And.left And.left) (congrArg Prod.fst eq)

private theorem rows_outside {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K] (p q : Finset K) :
    Disjoint (rows p q) (full K) := by
  apply disjoint_left.mpr
  intro x hx hb
  exact (show ∀ h : Fin 5, (h=1 ∨ h=4) → ¬(h=2 ∨ h=3) by decide) x.1
    ((in_rows.mp hx).imp And.left And.left) (mem_full.mp hb)

private theorem rows_nozero {K : Type} [AddCommGroup K] [DecidableEq K] (p q : Finset K) :
    ¬(seedLayer (rows p q) 0).Nonempty := by
  rintro ⟨x,h⟩
  obtain ⟨hx,z⟩ := mem_filter.mp h
  have head := (in_rows.mp hx).imp And.left And.left
  rw [z] at head; exact (by decide : ¬((0:Fin 5)=1 ∨ (0:Fin 5)=4)) head

private theorem colors_rows {k : ℕ} (p q : Finset (Space k)) : TwoColors p q=rows p q := by
  ext x; simp [TwoColors,in_rows]

theorem swap_count {k : ℕ} (p q : Finset (Space k)) :
    rankCount (TwoColors p q)=rankCount (TwoColors q p) := by
  have eq : (TwoColors p q).image Neg.neg=TwoColors q p := by
    ext ⟨i,x⟩
    have neg (a : Pt (Space k)) : a∈(TwoColors p q).image Neg.neg ↔ -a∈TwoColors p q := by
      constructor
      · rintro h; obtain ⟨u,hu,rfl⟩ := mem_image.mp h; simpa using hu
      · intro h; exact mem_image.mpr ⟨-a,h,neg_neg _⟩
    rw [neg]
    fin_cases i <;> simp (config:={decide:=true}) [TwoColors]
  rw [negate_count (TwoColors p q),eq]

private theorem row_shear {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K] [Module Field5 K]
    (p q : Finset K) (u : K) :
    (rows p q).image (shear u)=rows (p.image (·+u)) (q.image (·+u)) := by
  have h1 (x : K) : shear u (1,x)=(1,x+u) := by
    refine Prod.ext ?_ ?_
    · rfl
    · change x+(1:Field5) • u=x+u; rw [one_smul]
  have h4 (x : K) : shear u (4,-x)=(4,-(x+u)) := by
    refine Prod.ext (by rfl) ?_
    change -x+(4:Field5) • u= -(x+u)
    rw [show (4:Field5)= -1 by decide,neg_one_smul]; abel
  simp only [rows,image_union,image_image,Function.comp_def,h1,h4]

private theorem rows_embedding {K L : Type} [AddCommGroup K] [DecidableEq K] [Module Field5 K]
    [AddCommGroup L] [DecidableEq L] [Module Field5 L] (f : K →ₗ[Field5] L) (p q : Finset K) :
    embedded f (rows p q)=rows (p.image f) (q.image f) := by
  simp only [embedded,rows,image_union,image_image,Function.comp_def,map_neg]

theorem triple_base {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K] [Module Field5 K]
    (v w : K) (nv : v≠0) : rankCount (rows {0} {v,w})≤3^Fintype.card K := by
  by_cases line : ∃ c : Field5, w=c • v
  · obtain ⟨c,rfl⟩ := line
    let f : Field5 →ₗ[Field5] K := (LinearMap.id : Field5 →ₗ[Field5] Field5).smulRight v
    have inj : Function.Injective f := by
      intro a b h
      have q : (a-b) • v=0 := by rw [sub_smul]; exact sub_eq_zero.mpr h
      exact sub_eq_zero.mp ((smul_eq_zero.mp q).resolve_right nv)
    have base : rankCount (rows ({0}:Finset (Fin 5)) {1,c}) ≤ 3^Fintype.card Field5 := by
      exact RankOneBridge.all _ (rows_free _ _) (rows_outside _ _)
    have h := bound_embedding f inj base
    rw [rows_embedding] at h
    simpa [f,LinearMap.smulRight_apply] using h
  · let f : Strip.K →ₗ[Field5] K := (LinearMap.fst Field5 Field5 Field5).smulRight (w-v) +
      (LinearMap.snd Field5 Field5 Field5).smulRight v
    have applyF (a b : Field5) : f (a,b)=a • (w-v)+b • v := rfl
    have kernel (a b : Field5) (h : f (a,b)=0) : a=0 ∧ b=0 := by
      rw [applyF,smul_sub] at h
      have form : a • w= (a-b) • v := by
        rw [sub_smul]
        apply eq_sub_iff_add_eq.mpr
        exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using h)
      have az : a=0 := by
        by_contra ne
        apply line
        refine ⟨a⁻¹*(a-b),?_⟩
        rw [mul_smul,←form,←mul_smul,inv_mul_cancel₀ ne,one_smul]
      rw [az,zero_smul,zero_smul,sub_zero,zero_add] at h
      exact ⟨az,(smul_eq_zero.mp h).resolve_right nv⟩
    have inj : Function.Injective f := by
      intro a b eq
      have diff : f (a-b)=0 := by rw [map_sub,eq,sub_self]
      obtain ⟨u,z⟩ := kernel (a-b).1 (a-b).2 diff
      exact sub_eq_zero.mp (Prod.ext u z)
    have model : Strip.NoZero.seed=rows ({0}:Finset Strip.K) {(0,1),(1,1)} := by decide
    have base : rankCount (rows ({0}:Finset Strip.K) {(0,1),(1,1)}) ≤ 3^Fintype.card Strip.K := by
      rw [←model]
      exact Strip.NoZero.model_bound.le
    have h := bound_embedding f inj base
    rw [rows_embedding] at h
    simpa [applyF] using h

theorem triple {k : ℕ} (u v w : Space k) (different : v≠u) :
    rankCount (TwoColors {u} {v,w})≤3^Fintype.card (Space k) := by
  rw [colors_rows,shear_count (-u),row_shear]
  simpa only [image_singleton,image_insert,add_neg_cancel] using
    triple_base (v+ -u) (w+ -u) (by simpa only [←sub_eq_add_neg,sub_ne_zero] using different)

theorem eight {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s) (out : Disjoint s (full _))
    (nz : ¬(seedLayer s 0).Nonempty) (c : maximumDegree s≤8)
    (sum : 15≤headDegree s 2+headDegree s 3) : rankCount s≤3^Fintype.card (Space k) :=
  within_quarter s sf (TriangleEight.dense (within_sym s) (within_irr s) (nozero_triangleFree s out nz)
    Raw.domain (fun x hx => (within_cap sf x hx).trans c) (two_degree_sum s sf 15 sum))

theorem nine_rule {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s)
    (nz : ¬(seedLayer s 0).Nonempty) (c : maximumDegree s≤9) (l : minimumDegree s≤7) :
    TriangleEight.NineRule (within s) Raw.domain := by
  classical
  intro x hx high
  let N := Fingerprint.neighbors (within s) Raw.domain x
  let L := N.filter fun y => y.1≠x.1
  have xn : N.card=9 := high
  have xh : headDegree s x.1=9 := (within_degree sf hx).symm.trans high
  have b := head_bounds s ((mem_filter.mp hx).2.1)
  have floor := opposite_neighbors s sf nz hx
  change (forward s).card≤L.card at floor
  have atLeast : 4≤L.card := by omega
  have sub : L⊆N := filter_subset .. 
  have split := sdiff_union_of_subset sub
  have apart : Disjoint (N\L) L := disjoint_left.mpr (fun _ h => (mem_sdiff.mp h).2)
  have other (y : Raw.Point (Space k)) (hy : y∈L) : TriangleBase.deg (within s) Raw.domain y ≤7 := by
    obtain ⟨hn,neq⟩ := mem_filter.mp hy
    have yd : y∈Raw.domain := (mem_filter.mp hn).1
    rw [show TriangleBase.deg (within s) Raw.domain y=headDegree s y.1 from within_degree sf yd]
    unfold minimumDegree at l
    rcases (mem_filter.mp hx).2.1 with h|h <;> rcases (mem_filter.mp yd).2.1 with u|u <;>
      rw [h] at xh <;> rw [u] <;> rw [u,h] at neq <;> omega
  have hi (y : Raw.Point (Space k)) (hy : y∈N\L) : TriangleBase.deg (within s) Raw.domain y≤9 :=
    (within_cap sf y (mem_filter.mp (mem_sdiff.mp hy).1).1).trans c
  let deg := TriangleBase.deg (within s) Raw.domain
  have small : (∑ y∈L,deg y) ≤ L.card*7 := (sum_le_sum other).trans_eq (by simp)
  have big : (∑ y∈N\L,deg y) ≤ (N\L).card*9 := (sum_le_sum hi).trans_eq (by simp)
  have count := card_sdiff_add_card_eq_card sub
  change (∑ y∈N,deg y)≤73
  rw [←split,sum_union apart]
  omega

theorem nine {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s) (out : Disjoint s (full _))
    (nz : ¬(seedLayer s 0).Nonempty) (c : maximumDegree s≤9) (l : minimumDegree s≤7)
    (sum : 15≤headDegree s 2+headDegree s 3) : rankCount s≤3^Fintype.card (Space k) :=
  within_quarter s sf (TriangleEight.capNine (within_sym s) (within_irr s) (nozero_triangleFree s out nz)
    Raw.domain (fun x hx => (within_cap sf x hx).trans c) (nine_rule s sf nz c l) (two_degree_sum s sf 15 sum))

private theorem four_injective {A : Type*} {a b c d : A}
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d) :
    Function.Injective (![a,b,c,d] : Fin 4 → A) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem A {k : ℕ} (p q : Finset (Space k)) (cp : p.card=3) (cq : q.card=1) (dis : Disjoint p q) :
    MatrixCovered (TwoColors p q) := by
  obtain ⟨a,b,c,ab,ac,bc,rfl⟩ := card_eq_three.mp cp
  obtain ⟨d,rfl⟩ := card_eq_one.mp cq
  have ex := disjoint_singleton_right.mp dis
  simp only [mem_insert,mem_singleton,not_or] at ex
  exact .typeA ![a,b,c,d] (four_injective ab ac (Ne.symm ex.1) bc (Ne.symm ex.2.1) (Ne.symm ex.2.2))

theorem B {k : ℕ} (p q : Finset (Space k)) (cp : p.card=2) (cq : q.card=2) (dis : Disjoint p q) :
    MatrixCovered (TwoColors p q) := by
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp cp
  obtain ⟨c,d,cd,rfl⟩ := card_eq_two.mp cq
  have apart (x : Space k) (hx : x∈({a,b}:Finset _)) : x≠c ∧ x≠d :=
    ⟨fun e => disjoint_left.mp dis hx (by simp [e]),fun e => disjoint_left.mp dis hx (by simp [e])⟩
  have x := apart a (by simp)
  have y := apart b (by simp)
  exact .typeB ![a,b,c,d] (four_injective ab x.1 x.2 y.1 y.2 cd)

theorem C {k : ℕ} (p q : Finset (Space k)) (cp : p.card=3) (cq : q.card=2) (cu : (p∪q).card=4) :
    MatrixCovered (TwoColors p q) := by
  have both := card_union_add_card_inter p q
  have left := card_sdiff_add_card p q
  have right := card_sdiff_add_card q p
  rw [union_comm q p] at right
  obtain ⟨a,ha⟩ := card_eq_one.mp (show (p∩q).card=1 by omega)
  obtain ⟨b,c,bc,hbc⟩ := card_eq_two.mp (show (p\q).card=2 by omega)
  obtain ⟨d,hd⟩ := card_eq_one.mp (show (q\p).card=1 by omega)
  have ma : a∈p∩q := ha.symm ▸ mem_singleton_self a
  have mb : b∈p\q := hbc.symm ▸ mem_insert_self b {c}
  have mc : c∈p\q := hbc.symm ▸ (by simp : c∈({b,c}:Finset _))
  have md : d∈q\p := hd.symm ▸ mem_singleton_self d
  obtain ⟨ap,aq⟩ := mem_inter.mp ma
  obtain ⟨bp,bq⟩ := mem_sdiff.mp mb
  obtain ⟨cp',cq'⟩ := mem_sdiff.mp mc
  obtain ⟨dq,dp⟩ := mem_sdiff.mp md
  have endsP : p={a,b,c} := by rw [←sdiff_union_inter p q,hbc,ha]; ext x; simp; tauto
  have endsQ : q={a,d} := by rw [←sdiff_union_inter q p,inter_comm q p,hd,ha]; ext x; simp; tauto
  rw [endsP,endsQ]
  exact .typeC ![a,b,c,d] (four_injective (fun e => bq (e ▸ aq)) (fun e => cq' (e ▸ aq))
    (fun e => dp (e ▸ ap)) bc (fun e => dp (e ▸ bp)) (fun e => dp (e ▸ cp')))

def DefectBound {k : ℕ} (p q : Finset (Space k)) : Prop :=
  (p\q).card=1 → (q\p).card=1 → rankCount (TwoColors p q)≤3^Fintype.card (Space k)

private def tableInput (p q u : ℕ) : Prop :=
  q≤p ∧ p<u ∧ u≤p+q ∧ u+p<12 ∧
  ¬(u+p≤12 ∧ 18≤(u+q)+(u+p)) ∧ ¬(u+p≤10 ∧ 17≤(u+q)+(u+p)) ∧
  ¬(u+p≤8 ∧ 15≤(u+q)+(u+p)) ∧ ¬(u+p≤9 ∧ u+q≤7 ∧ 15≤(u+q)+(u+p)) ∧
  ¬(u=q+1 ∧ u=p+1)
private instance (p q u : ℕ) : Decidable (tableInput p q u) := by unfold tableInput; infer_instance

private def tableOutput (p q u : ℕ) : Prop := (p=2 ∧ q=1) ∨
  (p=3 ∧ q=1 ∧ u=p+q) ∨ (p=2 ∧ q=2 ∧ u=p+q) ∨ (p=3 ∧ q=2 ∧ u=4)
private instance (p q u : ℕ) : Decidable (tableOutput p q u) := by unfold tableOutput; infer_instance

private def tableCell (p q u : ℕ) : Bool := !decide (tableInput p q u) || decide (tableOutput p q u)
private theorem allCells : (List.range 12).all (fun p =>
    (List.range 12).all fun q => (List.range 12).all (tableCell p q))=true := by native_decide

private theorem entry {p q u : ℕ} (hp : p<12) (hq : q<12) (hu : u<12) (h : tableInput p q u) :
    tableOutput p q u := by
  have a := List.all_eq_true.mp allCells p (List.mem_range.mpr hp)
  have b := List.all_eq_true.mp a q (List.mem_range.mpr hq)
  have c := List.all_eq_true.mp b u (List.mem_range.mpr hu)
  simpa only [tableCell,decide_eq_true h,Bool.not_true,Bool.false_or,decide_eq_true_eq] using c

private theorem ordered {k : ℕ} (p q : Finset (Space k)) (order : q.card≤p.card)
    (defect : DefectBound p q) : rankCount (TwoColors p q)≤3^Fintype.card (Space k) := by
  let s := TwoColors p q
  have sf : Free s := by unfold s; rw [colors_rows]; exact rows_free p q
  have outside : Disjoint s (full _) := by unfold s; rw [colors_rows]; exact rows_outside p q
  have nz : ¬(seedLayer s 0).Nonempty := by unfold s; rw [colors_rows]; exact rows_nozero p q
  obtain ⟨sz,d2,d3⟩ := two_color_profile p q
  change s.card=p.card+q.card at sz
  change headDegree s 2=(p∪q).card+q.card at d2
  change headDegree s 3=(p∪q).card+p.card at d3
  by_cases nested : p⊆q ∨ q⊆p
  · exact covered_count (.nested _ _ nested)
  have up := card_le_card (subset_union_left (s₁:=p) (s₂:=q))
  have uq := card_le_card (subset_union_right (s₁:=p) (s₂:=q))
  have more : p.card<(p∪q).card := by
    apply lt_of_le_of_ne up
    intro same
    have equal : p=p∪q := eq_of_subset_of_card_le subset_union_left same.ge
    exact nested (Or.inr (show q⊆p by rw [equal]; exact subset_union_right))
  have cpq := card_union_le p q
  have inter := card_union_add_card_inter p q
  have diffP := card_sdiff_add_card p q
  have diffQ := card_sdiff_add_card q p
  rw [union_comm q p] at diffQ
  have maxeq : maximumDegree s=(p∪q).card+p.card := by unfold maximumDegree; omega
  have mineq : minimumDegree s=(p∪q).card+q.card := by unfold minimumDegree; omega
  by_cases high : 12≤maximumDegree s
  · exact nozero_large_degree s sf outside nz high
  by_cases large : maximumDegree s≤12 ∧ 18≤headDegree s 2+headDegree s 3
  · exact nozero_TF12 s sf outside nz large.1 large.2
  by_cases ten : maximumDegree s≤10 ∧ 17≤headDegree s 2+headDegree s 3
  · exact nozero_TF10 s sf outside nz ten.1 ten.2
  by_cases e : maximumDegree s≤8 ∧ 15≤headDegree s 2+headDegree s 3
  · exact eight s sf outside nz e.1 e.2
  by_cases n : maximumDegree s≤9 ∧ minimumDegree s≤7 ∧ 15≤headDegree s 2+headDegree s 3
  · exact nine s sf outside nz n.1 n.2.1 n.2.2
  by_cases ex : (p\q).card=1 ∧ (q\p).card=1
  · exact defect ex.1 ex.2
  rw [maxeq] at high
  simp only [maxeq,mineq,d2,d3] at large ten e n
  have one (z a b : ℕ) (h : z+a=b) (bump : b=a+1) : z=1 := by omega
  have noEx : ¬((p∪q).card=q.card+1 ∧ (p∪q).card=p.card+1) :=
    fun ⟨a,b⟩ => ex ⟨one _ _ _ diffP a,one _ _ _ diffQ b⟩
  have limit : (p∪q).card+p.card<12 := lt_of_not_ge high
  have lowP := (Nat.le_add_left p.card (p∪q).card).trans_lt limit
  have lowU := (Nat.le_add_right (p∪q).card p.card).trans_lt limit
  have zeroI (i n sum : ℕ) (count : n+i=sum) (all : n=sum) : i=0 := by omega
  have cases := entry (p:=p.card) (q:=q.card) (u:=(p∪q).card) lowP (order.trans_lt lowP) lowU
    ⟨order,more,cpq,lt_of_not_ge high,large,ten,e,n,noEx⟩
  rcases cases with ⟨cp,cq⟩|⟨cp,cq,ci⟩|⟨cp,cq,ci⟩|⟨cp,cq,cu⟩
  · obtain ⟨v,w,vw,rfl⟩ := card_eq_two.mp cp
    obtain ⟨u,rfl⟩ := card_eq_one.mp cq
    have vu : v≠u := fun e => nested (Or.inr (by simp [e]))
    rw [swap_count]; exact triple u v w vu
  · exact covered_count (A p q cp cq (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (zeroI _ _ _ inter ci))))
  · exact covered_count (B p q cp cq (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (zeroI _ _ _ inter ci))))
  · exact covered_count (C p q cp cq cu)

theorem of_defects {k : ℕ} (s : Finset (Pt (Space k))) (out : Disjoint s (full _))
    (nz : ¬(seedLayer s 0).Nonempty) (defect : ∀ p q : Finset (Space k), DefectBound p q) :
    rankCount s≤3^(5^k) := by
  obtain ⟨p,q,rfl⟩ := two_colors s out nz
  have result : rankCount (TwoColors p q)≤3^Fintype.card (Space k) := by
    by_cases h : q.card≤p.card
    · exact ordered p q h (defect p q)
    · rw [swap_count]; exact ordered q p (by omega) (defect q p)
  simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using result

theorem defects {k : ℕ} (p q : Finset (Space k)) : DefectBound p q := by
  intro first second
  obtain ⟨a,ea⟩ := card_eq_one.mp first
  obtain ⟨b,eb⟩ := card_eq_one.mp second
  let u := p∩q
  let T := rows u u
  have ap := mem_sdiff.mp (ea.symm ▸ mem_singleton_self a : a∈p\q)
  have bp := mem_sdiff.mp (eb.symm ▸ mem_singleton_self b : b∈q\p)
  have dist : -b ≠ -a := fun h => bp.2 (neg_inj.mp h ▸ ap.1)
  have ep : p=insert a u := by rw [←sdiff_union_inter p q,ea]; ext x; simp [u]
  have eq : q=insert b u := by rw [←sdiff_union_inter q p,eb,inter_comm q p]; ext x; simp [u]
  have target : TwoColors p q=Defects.signedSeed T true true a (-b) := by
    rw [colors_rows,ep,eq]
    ext x; simp only [Defects.signedSeed,if_true,rows,image_insert,mem_insert,mem_union,T]
    tauto
  have stable (x : Pt (Space k)) : x∈T ↔ -x∈T := by
    rcases x with ⟨i,v⟩
    simp only [T,in_rows,Prod.neg_mk,neg_neg]
    fin_cases i <;> simp (config:={decide:=true})
  have zero : (0:Pt (Space k))∉T := by
    intro h
    have impossible := (in_rows.mp h).imp And.left And.left
    exact (by decide : ¬((0:Fin 5)=1 ∨ (0:Fin 5)=4)) impossible
  rw [target]
  exact Defects.nonzero T stable zero true true a (-b) (fun _ _ => dist)

/-- The whole four-layer theorem for seeds outside the band that avoid the zero head. -/
theorem all {k : ℕ} (s : Finset (Pt (Space k))) (out : Disjoint s (full _))
    (nz : ¬(seedLayer s 0).Nonempty) : rankCount s≤3^(5^k) :=
  of_defects s out nz defects

end
end Audit.NoZero
