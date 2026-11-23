import Audit.Generic
import Audit.Potential
import Audit.Reduction
import Audit.TriangleTen
import Audit.TriangleTwelve
import Audit.GraphMeasure

namespace Audit.Degrees
open Finset Lower Link Band Generic Fingerprint Blocks
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

def project (x : Raw.Point K) : Pt K := (x.1,x.2.1)

def liftSign (t : Fin 5) (v : Vtx K) : Raw.Point K := (v.val.1,v.val.2,t)

theorem inject_sign (t : Fin 5) : Function.Injective (liftSign (K:=K) t) := by
  intro u v h
  exact Subtype.ext (congrArg project h)

theorem valid_sign (t : Fin 5) (allow : t=1 ∨ t=4) :
    (-t=1 ∨ -t=4) ∧ t≠-t := by
  rcases allow with rfl|rfl <;> decide

private theorem lifted_domain {t : Fin 5} (good : t=1 ∨ t=4) (v : Vtx K) :
    liftSign t v∈Raw.domain := mem_filter.mpr ⟨mem_univ _,(mem_full (u:=v.val)).mp v.2,good⟩

theorem split_neighbors (s : Finset (Pt K)) (sf : Free s)
    (v : Vtx K) {t : Fin 5} (good : t=1 ∨ t=4) :
    neighbors (edge (plane s)) Raw.domain (liftSign t v) =
    (difference s v).image (liftSign t) ∪ (sumNeighbors s v).image (liftSign (-t)) := by
  ext y
  have sign := valid_sign t good
  have hz : (0:Pt K)∉s := fun h => sf _ h _ h _ h (zero_add _)
  constructor
  · intro hy
    obtain ⟨dom,ed⟩ := mem_filter.mp hy
    let w : Vtx K := ⟨project y,mem_full.mpr (mem_filter.mp dom).2.1⟩
    rcases ed.2 with add|sub|sub
    · obtain ⟨hit,eq⟩ := (in_plane ..).mp add
      have l : t+y.2.2=0 := eq
      have oy : -t=y.2.2 := neg_eq_iff_add_eq_zero.mpr l
      exact mem_union_right _ (mem_image.mpr ⟨w,mem_filter.mpr ⟨mem_univ _,hit⟩,
        Prod.ext rfl (Prod.ext rfl oy)⟩)
    · obtain ⟨hit,eq⟩ := (in_plane ..).mp sub
      have l : y.2.2-t=0 := eq
      exact mem_union_left _ (mem_image.mpr ⟨w,
        mem_filter.mpr ⟨mem_univ _,mem_signed.mpr (Or.inl hit)⟩,
        Prod.ext rfl (Prod.ext rfl (sub_eq_zero.mp l).symm)⟩)
    · obtain ⟨hit,eq⟩ := (in_plane ..).mp sub
      have l : t-y.2.2=0 := eq
      have h : v.val-w.val∈s := hit
      have neg : -(w.val-v.val)∈s := by simpa only [neg_sub] using h
      exact mem_union_left _ (mem_image.mpr ⟨w,
        mem_filter.mpr ⟨mem_univ _,mem_signed.mpr (Or.inr neg)⟩,
        Prod.ext rfl (Prod.ext rfl (sub_eq_zero.mp l))⟩)
  · intro hy
    rcases mem_union.mp hy with hd|ha
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hd
      have signMem := mem_signed.mp (mem_filter.mp hw).2
      have ne : liftSign t v ≠ liftSign t w := by
        intro eq; obtain rfl := inject_sign t eq
        rcases signMem with h|h <;> simp [hz] at h
      refine mem_filter.mpr ⟨lifted_domain good _,ne,Or.inr ?_⟩
      rcases signMem with diff|diff
      · exact Or.inl ((in_plane ..).mpr ⟨diff,sub_self _⟩)
      · have h : v.val-w.val∈s := by simpa only [neg_sub] using diff
        exact Or.inr ((in_plane ..).mpr ⟨h,sub_self _⟩)
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp ha
      have ne : liftSign t v ≠ liftSign (-t) w := fun h => sign.2 (congrArg (fun x : Raw.Point K => x.2.2) h)
      exact mem_filter.mpr ⟨lifted_domain sign.1 _,ne,Or.inl ((in_plane ..).mpr
        ⟨(mem_filter.mp hw).2,add_neg_cancel _⟩)⟩

private def sumPart (s : Finset (Pt K)) (h : Fin 5) :=
  s.filter fun p => p.1-h=2 ∨ p.1-h=3

private theorem sum_count (s : Finset (Pt K)) (v : Vtx K) :
    (sumNeighbors s v).card=(sumPart s v.val.1).card := by
  apply card_bij (fun w _ => v.val+w.val)
  · intro w hw
    refine mem_filter.mpr ⟨(mem_filter.mp hw).2,?_⟩
    have ok := (mem_full (u:=w.val)).mp w.2
    change v.val.1+w.val.1-v.val.1=2 ∨ v.val.1+w.val.1-v.val.1=3
    simpa using ok
  · intro a _ b _ h
    exact Subtype.ext (add_left_cancel h)
  · intro p hp
    let w : Vtx K := ⟨p-v.val,mem_full.mpr (mem_filter.mp hp).2⟩
    have eq : v.val+w.val=p := add_sub_cancel _ _
    exact ⟨w,mem_filter.mpr ⟨mem_univ _,eq.symm ▸ (mem_filter.mp hp).1⟩,eq⟩

def headDegree (s : Finset (Pt K)) (h : Fin 5) := (forward s).card+(sumPart s h).card

theorem degree_on_head (s : Finset (Pt K)) (sf : Free s) {x : Raw.Point K} (hx : x∈Raw.domain) :
    (neighbors (edge (plane s)) Raw.domain x).card = headDegree s x.1 := by
  let v : Vtx K := ⟨project x,mem_full.mpr (mem_filter.mp hx).2.1⟩
  let t := x.2.2
  have good : t=1 ∨ t=4 := (mem_filter.mp hx).2.2
  have dis : Disjoint ((difference s v).image (liftSign t)) ((sumNeighbors s v).image (liftSign (-t))) := by
    apply disjoint_left.mpr
    intro y hy ha
    obtain ⟨u,_,rfl⟩ := mem_image.mp hy
    obtain ⟨w,_,eq⟩ := mem_image.mp ha
    exact (valid_sign t good).2 (congrArg (fun z : Raw.Point K => z.2.2) eq.symm)
  change (neighbors (edge (plane s)) Raw.domain (liftSign t v)).card=_
  rw [split_neighbors s sf v good,card_union_of_disjoint dis,card_image_of_injective _ (inject_sign _),
    card_image_of_injective _ (inject_sign _),difference_card,sum_count]
  rfl

theorem head_bounds (s : Finset (Pt K)) {h : Fin 5} (head : h=2 ∨ h=3) :
    (forward s).card ≤ headDegree s h ∧ headDegree s h ≤ 2*(forward s).card := by
  let v : Vtx K := ⟨(h,0),mem_full.mpr head⟩
  have b := sum_card s v
  rw [sum_count,difference_card] at b
  change (sumPart s h).card≤(forward s).card at b
  unfold headDegree
  omega

theorem seed_le_degree (s : Finset (Pt K)) (out : Disjoint s (full K)) :
    s.card ≤ headDegree s 2 := by
  have split : s⊆forward s ∪ sumPart s 2 := by
    intro x hx
    have no : ¬(x.1=2 ∨ x.1=3) := fun h => disjoint_left.mp out hx (mem_full.mpr h)
    have kinds : ∀ i : Fin 5, ¬(i=2 ∨ i=3) → (i=0 ∨ i=1) ∨ (i-2=2 ∨ i-2=3) := by decide
    rcases kinds _ no with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_signed.mpr (Or.inl hx),h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,h⟩)
  exact (card_le_card split).trans (card_union_le ..)

theorem seed_le_degree_three (s : Finset (Pt K)) (out : Disjoint s (full K)) :
    s.card ≤ headDegree s 3 := by
  let covered := sumPart s 3
  have contained : covered⊆s := filter_subset .. 
  have inject : (s\covered).card≤(forward s).card := by
    apply card_le_card_of_injOn Neg.neg
    · intro p hp
      obtain ⟨hs,unused⟩ := mem_sdiff.mp hp
      have outside : ¬(p.1=2 ∨ p.1=3) := fun h => disjoint_left.mp out hs (mem_full.mpr h)
      have notSum : ¬(p.1-3=2 ∨ p.1-3=3) := fun h => unused (mem_filter.mpr ⟨hs,h⟩)
      have kinds : ∀ i : Fin 5, ¬(i=2 ∨ i=3) → ¬(i-3=2 ∨ i-3=3) → (-i=0 ∨ -i=1) := by decide
      exact mem_filter.mpr ⟨mem_signed.mpr (Or.inr (by simpa using hs)),kinds _ outside notSum⟩
    · exact neg_injective.injOn
  have total := card_sdiff_add_card_eq_card contained
  change s.card ≤ (forward s).card+covered.card
  omega

private def headLayer (h : Fin 5) : Finset (Raw.Point K) := {h} ×ˢ ((univ : Finset K) ×ˢ {1,4})

theorem domain_stats (s : Finset (Pt K)) (sf : Free s) :
    (Raw.domain (K:=K)).card=4*Fintype.card K ∧
    (∑ x∈(Raw.domain (K:=K)), (neighbors (edge (plane s)) Raw.domain x).card) =
      (2*Fintype.card K)*(headDegree s 2+headDegree s 3) := by
  have split : (Raw.domain (K:=K))=headLayer 2 ∪ headLayer 3 := by
    ext x
    simp only [Raw.domain,mem_filter,mem_univ,true_and,headLayer,mem_union,mem_product,mem_singleton,
      mem_insert]
    tauto
  have shape {h : Fin 5} {v : Raw.Point K} (hv : v∈headLayer h) : v.1=h :=
    mem_singleton.mp (mem_product.mp hv).1
  have dis : Disjoint (headLayer (K:=K) 2) (headLayer 3) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (by decide : (2:Fin 5)≠3) ((shape hx).symm.trans (shape hy))
  have count (h : Fin 5) : (headLayer (K:=K) h).card=2*Fintype.card K := by
    simp [headLayer,mul_comm]
  constructor
  · rw [split,card_union_of_disjoint dis,count,count]; omega
  · have layer (h : Fin 5) : (∑ x∈headLayer (K:=K) h,headDegree s x.1)=
        (2*Fintype.card K)*headDegree s h := by
      rw [←count h,←Nat.nsmul_eq_mul,←sum_const]
      exact sum_congr rfl (fun _ hx => congrArg (headDegree s) (shape hx))
    calc
      _ = ∑ x∈(Raw.domain (K:=K)), headDegree s x.1 := sum_congr rfl fun _ hx => degree_on_head s sf hx
      _ = _ := by rw [split,sum_union dis,layer,layer,Nat.mul_add]

def maximumDegree (s : Finset (Pt K)) := max (headDegree s 2) (headDegree s 3)

def minimumDegree (s : Finset (Pt K)) := min (headDegree s 2) (headDegree s 3)

def seedLayer (s : Finset (Pt K)) (h : Fin 5) := s.filter fun p => p.1=h

private theorem layer_disjoint (s : Finset (Pt K)) {i j : Fin 5} (ne : i≠j) :
    Disjoint (seedLayer s i) (seedLayer s j) := disjoint_left.mpr
  (fun _ hi hj => ne ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2))

/-- The degree formulas count the zero and nonzero layers separately.
    The signed zero layer contributes Z and the signed layer one contributes U. -/
theorem profiles (s : Finset (Pt K)) (out : Disjoint s (full K)) :
    let z := (seedLayer s 0).card
    let p := (seedLayer s 1).card
    let q := (seedLayer s 4).card
    let Z := (seedLayer (forward s) 0).card
    let U := (seedLayer (forward s) 1).card
    s.card=z+p+q ∧ p≤U ∧ q≤U ∧ headDegree s 2=Z+U+z+q ∧ headDegree s 3=Z+U+z+p := by
  dsimp only
  have split : s=(seedLayer s 0 ∪ seedLayer s 1)∪seedLayer s 4 := by
    ext x
    simp only [seedLayer,mem_union,mem_filter]
    constructor
    · intro h
      have no : ¬(x.1=2 ∨ x.1=3) := fun head => disjoint_left.mp out h (mem_full.mpr head)
      have heads : ∀ i : Fin 5, ¬(i=2 ∨ i=3) → (i=0 ∨ i=1) ∨ i=4 := by decide
      rcases heads _ no with (a|a)|a <;> tauto
    · tauto
  have dis : Disjoint (seedLayer s 0 ∪ seedLayer s 1) (seedLayer s 4) :=
    disjoint_union_left.mpr ⟨layer_disjoint s (by decide),layer_disjoint s (by decide)⟩
  have sc := congrArg Finset.card split
  rw [card_union_of_disjoint dis,card_union_of_disjoint (layer_disjoint s (by decide : (0:Fin 5)≠1))] at sc
  have fsplit : forward s=seedLayer (forward s) 0 ∪ seedLayer (forward s) 1 := by
    ext x
    simp only [seedLayer,mem_filter,mem_union]
    constructor
    · intro h; rcases (mem_filter.mp h).2 with h2|h2 <;> tauto
    · tauto
  have fc := congrArg Finset.card fsplit
  rw [card_union_of_disjoint (layer_disjoint _ (by decide : (0:Fin 5)≠1))] at fc
  have parts (h j : Fin 5) (ok : ∀ i : Fin 5, (i-h=2 ∨ i-h=3) ↔ i=0 ∨ i=j)
      (ne : (0:Fin 5)≠j) :
      (sumPart s h).card=(seedLayer s 0).card+(seedLayer s j).card := by
    rw [←card_union_of_disjoint (layer_disjoint s ne)]
    congr 1; ext x
    simp only [sumPart,seedLayer,mem_union,mem_filter,ok]
    tauto
  refine ⟨sc,?_,?_,?_,?_⟩
  · apply card_le_card
    intro x hx
    obtain ⟨hs,head⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inl hs),Or.inr head⟩,head⟩
  · apply card_le_card_of_injOn Neg.neg
    · intro x hx
      obtain ⟨hs,head⟩ := mem_filter.mp hx
      have h1 : (-x).1=1 := by change -x.1=1; rw [head]; decide
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inr (by simpa using hs)),Or.inr h1⟩,h1⟩
    · exact neg_injective.injOn
  · rw [headDegree,fc,parts 2 4 (by decide) (by decide)]; omega
  · rw [headDegree,fc,parts 3 1 (by decide) (by decide)]; omega

theorem mixed_profile {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s)
    (out : Disjoint s (full _)) (mixed : (seedLayer s 0).Nonempty) :
    s.card+2≤minimumDegree s ∧ maximumDegree s≤2*minimumDegree s-3 := by
  obtain ⟨x,hx⟩ := mixed
  obtain ⟨sx,head⟩ := mem_filter.mp hx
  have nonzero : (0:Pt (Space k))∉s := fun h => sf 0 h 0 h 0 h (zero_add _)
  have nonop : x≠-x := by
    intro e
    have tail : x.2= -x.2 := congrArg Prod.snd e
    have odd : ∀ b : Field5, b= -b → b=0 := by decide
    have tz : x.2=0 := funext fun i => odd _ (congrFun tail i)
    exact nonzero ((Prod.ext head tz : x=0) ▸ sx)
  have pair : ({x,-x} : Finset (Pt (Space k))) ⊆ seedLayer (forward s) 0 := by
    intro y hy
    rcases (show y=x ∨ y= -x by simpa using hy) with rfl|rfl
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inl sx),Or.inl head⟩,head⟩
    · have zero : (-x).1=0 := by change -x.1=0; rw [head,neg_zero]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inr (by simpa using sx)),Or.inl zero⟩,zero⟩
  have ztwo : 2≤(seedLayer (forward s) 0).card := by
    simpa only [card_pair nonop] using card_le_card pair
  have zone : 1≤(seedLayer s 0).card := card_pos.mpr ⟨x,hx⟩
  obtain ⟨sc,p,q,h2,h3⟩ := profiles s out
  unfold minimumDegree maximumDegree
  omega

theorem two_colors {k : ℕ} (s : Finset (Pt (Space k))) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) :
    ∃ p q : Finset (Space k), s=Reduction.TwoColors p q := by
  let p := (univ : Finset (Space k)).filter fun x => (1,x)∈s
  let q := (univ : Finset (Space k)).filter fun x => (4,-x)∈s
  refine ⟨p,q,?_⟩
  ext ⟨i,u⟩
  simp only [Reduction.TwoColors,p,q,mem_filter,mem_univ,true_and,neg_neg]
  constructor
  · intro hs
    have nh : ¬(i=2 ∨ i=3) := fun h => disjoint_left.mp out hs (mem_full.mpr h)
    have nz : i≠0 := fun h => nozero ⟨(i,u),mem_filter.mpr ⟨hs,h⟩⟩
    have heads : ∀ h : Fin 5, h≠0 → ¬(h=2 ∨ h=3) → h=1 ∨ h=4 := by decide
    rcases heads _ nz nh with rfl|rfl <;> tauto
  · rintro (⟨rfl,h⟩|⟨rfl,h⟩) <;> exact h

theorem two_color_profile {k : ℕ} (p q : Finset (Space k)) :
    let s := Reduction.TwoColors p q
    s.card=p.card+q.card ∧ headDegree s 2=(p∪q).card+q.card ∧
      headDegree s 3=(p∪q).card+p.card := by
  let row (i : Fin 5) (x : Space k) : Pt (Space k) := (i,x)
  let back (x : Space k) : Pt (Space k) := (4,-x)
  have rowInj (h : Fin 5) : Function.Injective (row h) := fun _ _ e => congrArg Prod.snd e
  have backInj : Function.Injective back := fun _ _ e => neg_injective (congrArg Prod.snd e)
  let s := Reduction.TwoColors p q
  have base : s=p.image (row 1) ∪ q.image back := by
    ext ⟨i,x⟩
    simp [s,Reduction.TwoColors,back,row,eq_comm,and_comm]
    apply or_congr_right
    exact ⟨fun h => ⟨-x,h.2,h.1,(neg_neg _).symm⟩,
      fun ⟨y,hy,h,e⟩ => ⟨h,by simpa [e] using hy⟩⟩
  have dis : Disjoint (p.image (row 1)) (q.image back) := by
    apply disjoint_left.mpr
    intro x hp hq
    obtain ⟨u,_,rfl⟩ := mem_image.mp hp
    obtain ⟨v,_,e⟩ := mem_image.mp hq
    exact (by decide : (4:Fin 5)≠1) (congrArg Prod.fst e)
  have f : forward s=(p∪q).image (row 1) := by
    ext ⟨i,x⟩
    fin_cases i <;> simp (config:={decide:=true}) [forward,s,Reduction.TwoColors,row,Prod.neg_mk]
  have right : sumPart s 2=q.image back := by
    ext ⟨i,x⟩
    fin_cases i <;> simp (config:={decide:=true}) [sumPart,s,Reduction.TwoColors,back,eq_comm]
    exact ⟨fun h => ⟨-x,h,(neg_neg _).symm⟩,fun ⟨y,hy,e⟩ => by simpa [e] using hy⟩
  have left : sumPart s 3=p.image (row 1) := by
    ext ⟨i,x⟩
    fin_cases i <;> simp (config:={decide:=true}) [sumPart,s,Reduction.TwoColors,row]
  change s.card=_ ∧ headDegree s 2=_ ∧ headDegree s 3=_
  refine ⟨?_,?_,?_⟩
  · rw [base,card_union_of_disjoint dis,card_image_of_injective _ (rowInj _),card_image_of_injective _ backInj]
  · rw [headDegree,f,right,card_image_of_injective _ (rowInj _),card_image_of_injective _ backInj]
  · rw [headDegree,f,left,card_image_of_injective _ (rowInj _),card_image_of_injective _ (rowInj _)]

/-- The non-nested no-zero models on at least seven seed points have exactly
    one of the triangle-free degree regimes used in the manuscript. -/
theorem nozero_cases {k : ℕ} (s : Finset (Pt (Space k))) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) (size : 7≤s.card) :
    Reduction.MatrixCovered s ∨ (maximumDegree s≤10 ∧ 17≤headDegree s 2+headDegree s 3) ∨
    (maximumDegree s≤12 ∧ 18≤headDegree s 2+headDegree s 3) ∨
    (12≤maximumDegree s ∧ maximumDegree s≤2*minimumDegree s) := by
  obtain ⟨p,q,rfl⟩ := two_colors s out nozero
  obtain ⟨sz,d2,d3⟩ := two_color_profile p q
  have cp := card_le_card (subset_union_left (s₁:=p) (s₂:=q))
  have cq := card_le_card (subset_union_right (s₁:=p) (s₂:=q))
  by_cases sp : (p∪q).card=p.card
  · have eq : p=p∪q := eq_of_subset_of_card_le subset_union_left sp.le
    exact Or.inl (.nested _ _ (Or.inr (show q⊆p by rw [eq]; exact subset_union_right)))
  by_cases sq : (p∪q).card=q.card
  · have eq : q=p∪q := eq_of_subset_of_card_le subset_union_right sq.le
    exact Or.inl (.nested _ _ (Or.inl (show p⊆q by rw [eq]; exact subset_union_left)))
  right
  unfold maximumDegree minimumDegree
  omega

/-- Extend the induced four-layer graph to the full coordinate type by
    giving all coordinates outside the four layers degree zero. -/
def within (s : Finset (Pt K)) (x y : Raw.Point K) : Prop :=
  x∈Raw.domain ∧ y∈Raw.domain ∧ edge (plane s) x y

theorem within_sym (s : Finset (Pt K)) : Symmetric (within s) :=
  fun _ _ h => ⟨h.2.1,h.1,edge_sym _ h.2.2⟩

theorem within_irr (s : Finset (Pt K)) : Irreflexive (within s) :=
  fun _ h => h.2.2.1 rfl

private def side (i t : Fin 5) : Bool := decide ((i=2) ↔ (t=1))

theorem nozero_triangleFree (s : Finset (Pt K)) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) : Sumfree.TriangleFree (within s) := by
  have heads {p : Pt K} (hp : p∈s) : p.1=1 ∨ p.1=4 := by
    have no : ¬(p.1=2 ∨ p.1=3) := fun h => disjoint_left.mp out hp (mem_full.mpr h)
    have nz : p.1≠0 := fun z => nozero ⟨p,mem_filter.mpr ⟨hp,z⟩⟩
    exact (show ∀ h : Fin 5, h≠0 → ¬(h=2 ∨ h=3) → h=1 ∨ h=4 by decide) _ nz no
  have crossing : ∀ a b c d : Fin 5, (a=2 ∨ a=3) → (b=1 ∨ b=4) →
      (c=2 ∨ c=3) → (d=1 ∨ d=4) →
      ((a+c=1 ∨ a+c=4) ∧ b+d=0 ∨ (c-a=1 ∨ c-a=4) ∧ d-b=0 ∨
        (a-c=1 ∨ a-c=4) ∧ b-d=0) → side a b≠side c d := by decide
  have diff {x y : Raw.Point K} (h : within s x y) : side x.1 x.2.2≠side y.1 y.2.2 := by
    obtain ⟨hx,tx⟩ := (mem_filter.mp h.1).2
    obtain ⟨hy,ty⟩ := (mem_filter.mp h.2.1).2
    apply crossing _ _ _ _ hx tx hy ty
    rcases h.2.2.2 with plus|minus|minus
    · obtain ⟨mem,t⟩ := (in_plane ..).mp plus
      exact Or.inl ⟨heads mem,t⟩
    · obtain ⟨mem,t⟩ := (in_plane ..).mp minus
      exact Or.inr (Or.inl ⟨heads mem,t⟩)
    · obtain ⟨mem,t⟩ := (in_plane ..).mp minus
      exact Or.inr (Or.inr ⟨heads mem,t⟩)
  intro x y z xy yz xz
  exact (show ∀ a b c : Bool, a≠b → b≠c → a≠c → False by decide) _ _ _ (diff xy) (diff yz) (diff xz)

theorem within_count (s : Finset (Pt K)) :
    rankCount s=Sumfree.mis (within s) Raw.domain := by
  apply Sumfree.count_congr
  intro x hx y hy
  exact ⟨fun h => ⟨hx,hy,h⟩,fun h => h.2.2⟩

theorem within_degree {s : Finset (Pt K)} (sf : Free s) {x : Raw.Point K} (hx : x∈Raw.domain) :
    (neighbors (within s) Raw.domain x).card=headDegree s x.1 := by
  rw [←degree_on_head s sf hx]
  congr 1; ext y
  simp only [neighbors,mem_filter,within,hx,true_and,and_self_left]

theorem within_cap {s : Finset (Pt K)} (sf : Free s) :
    ∀ x∈Raw.domain,(neighbors (within s) Raw.domain x).card≤maximumDegree s := by
  intro x hx
  rw [within_degree sf hx]
  rcases (mem_filter.mp hx).2.1 with h|h <;> rw [h]
  · exact le_max_left .. 
  · exact le_max_right ..

theorem within_volume (s : Finset (Pt K)) (sf : Free s) :
    (∑ x∈Raw.domain,(neighbors (within s) Raw.domain x).card) =
      (2*Fintype.card K)*(headDegree s 2+headDegree s 3) := by
  rw [←(domain_stats s sf).2]
  exact sum_congr rfl (fun _ hx => (within_degree sf hx).trans (degree_on_head s sf hx).symm)

/-- Every signed difference neighbor of a no-zero seed lies on the opposite head layer. -/
theorem opposite_neighbors (s : Finset (Pt K)) (sf : Free s) (nz : ¬(seedLayer s 0).Nonempty)
    {x : Raw.Point K} (hx : x∈Raw.domain) :
    (forward s).card ≤ ((neighbors (within s) Raw.domain x).filter fun y => y.1≠x.1).card := by
  let v : Vtx K := ⟨project x,mem_full.mpr (mem_filter.mp hx).2.1⟩
  let t := x.2.2
  have good : t=1 ∨ t=4 := (mem_filter.mp hx).2.2
  have no (p : Pt K) (hp : p∈s) : p.1≠0 := fun h => nz ⟨p,mem_filter.mpr ⟨hp,h⟩⟩
  have sub : (difference s v).image (liftSign t) ⊆
      (neighbors (within s) Raw.domain x).filter fun y => y.1≠x.1 := by
    intro y hy
    have ed : y∈neighbors (edge (plane s)) Raw.domain x := by
      change y∈neighbors (edge (plane s)) Raw.domain (liftSign t v)
      rw [split_neighbors s sf v good]; exact mem_union_left _ hy
    obtain ⟨hd,ee⟩ := mem_filter.mp ed
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hd,hx,hd,ee⟩,?_⟩
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
    intro same
    change w.val.1=v.val.1 at same
    rcases mem_signed.mp (mem_filter.mp hw).2 with hit|hit
    · exact no _ hit (show w.val.1-v.val.1=0 by rw [same,sub_self])
    · exact no _ hit (show -(w.val.1-v.val.1)=0 by rw [same,sub_self,neg_zero])
  have count := card_le_card sub
  rwa [card_image_of_injective _ (inject_sign _),difference_card] at count

theorem within_quarter (s : Finset (Pt K)) (sf : Free s)
    (upper : (Sumfree.mis (within s) Raw.domain:ℝ)≤(3:ℝ)^(((Raw.domain (K:=K)).card:ℝ)/4)) :
    rankCount s≤3^Fintype.card K := by
  rw [within_count]
  rw [(domain_stats s sf).1,Nat.cast_mul,Nat.cast_ofNat,
    show (4*(Fintype.card K:ℝ))/4=(Fintype.card K:ℝ) by ring,Real.rpow_natCast] at upper
  exact_mod_cast upper

theorem two_degree_sum (s : Finset (Pt K)) (sf : Free s) (n : ℕ)
    (low : n≤headDegree s 2+headDegree s 3) :
    n*(Raw.domain (K:=K)).card ≤ 2*TriangleBase.vol (within s) Raw.domain := by
  change _≤2*(∑ x∈Raw.domain,(neighbors (within s) Raw.domain x).card)
  rw [(domain_stats s sf).1,within_volume s sf]
  calc
    _ = 4*(Fintype.card K)*n := by ring
    _ ≤ 4*(Fintype.card K)*(headDegree s 2+headDegree s 3) := Nat.mul_le_mul_left _ low
    _ = _ := by ring

theorem nozero_TF10 (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) (cap : maximumDegree s ≤ 10)
    (high : 17≤headDegree s 2+headDegree s 3) : rankCount s≤3^Fintype.card K :=
  within_quarter s sf (TriangleTen.dense (within_sym s) (within_irr s) (nozero_triangleFree s out nozero)
    Raw.domain (fun x hx => (within_cap sf x hx).trans cap) (two_degree_sum s sf 17 high))

theorem nozero_TF12 (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) (cap : maximumDegree s ≤ 12)
    (high : 18≤headDegree s 2+headDegree s 3) : rankCount s≤3^Fintype.card K := by
  apply within_quarter s sf
  apply TriangleTwelve.dense (within_sym s) (within_irr s) (nozero_triangleFree s out nozero)
    (D:=12) (by decide) Raw.domain (fun x hx => (within_cap sf x hx).trans cap)
  have h := two_degree_sum s sf 18 high
  omega

theorem maximum_stats (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K)) :
    s.card≤maximumDegree s ∧
    (∀ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card≤maximumDegree s) ∧
    3*maximumDegree s*(Raw.domain (K:=K)).card ≤
      4*(∑ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card) := by
  refine ⟨(seed_le_degree s out).trans (le_max_left ..),?_,?_⟩
  · intro x hx
    rw [degree_on_head s sf hx]
    rcases (mem_filter.mp hx).2.1 with head|head <;> rw [head]
    · exact le_max_left .. 
    · exact le_max_right ..
  · obtain ⟨c,v⟩ := domain_stats s sf
    rw [c,v]
    have a := head_bounds s (h:=2) (Or.inl rfl)
    have b := head_bounds s (h:=3) (Or.inr rfl)
    have mid : 3*maximumDegree s ≤ 2*(headDegree s 2+headDegree s 3) := by
      unfold maximumDegree
      omega
    calc
      _ = (3*maximumDegree s)*4*Fintype.card K := by ring
      _ ≤ (2*(headDegree s 2+headDegree s 3))*4*Fintype.card K :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 4 mid)
      _ = _ := by ring

theorem nozero_large_degree (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) (large : 12≤maximumDegree s) : rankCount s≤3^Fintype.card K := by
  apply within_quarter s sf
  apply TriangleTwelve.dense (within_sym s) (within_irr s) (nozero_triangleFree s out nozero)
    large Raw.domain (within_cap sf)
  have h := (maximum_stats s sf out).2.2
  change _ ≤ 4*(∑ x∈Raw.domain,(neighbors (within s) Raw.domain x).card)
  rw [within_volume s sf,←(domain_stats s sf).2]
  exact h

/-- The generic-block bound for every seed avoiding head zero and containing at least seven points. -/
theorem nozero_many {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s) (out : Disjoint s (full _))
    (nozero : ¬(seedLayer s 0).Nonempty) (size : 7≤s.card) : rankCount s≤3^(5^k) := by
  have result : rankCount s≤3^Fintype.card (Space k) := by
    rcases nozero_cases s out nozero size with known|⟨cap,high⟩|⟨cap,high⟩|⟨large,_⟩
    · exact Reduction.covered_count known
    · exact nozero_TF10 s sf out nozero cap high
    · exact nozero_TF12 s sf out nozero cap high
    · exact nozero_large_degree s sf out nozero large
  simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using result

theorem padded_stats (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K))
    (large : 54 ≤ headDegree s 2+headDegree s 3) :
    let D := max 36 (maximumDegree s)
    (∀ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card≤D) ∧
    3*D*(Raw.domain (K:=K)).card ≤
      4*(∑ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card) := by
  dsimp only
  obtain ⟨_,cap,avg⟩ := maximum_stats s sf out
  refine ⟨fun x hx => (cap x hx).trans (le_max_right ..),?_⟩
  by_cases high : 36≤maximumDegree s
  · rwa [max_eq_right high]
  rw [max_eq_left (by omega : maximumDegree s ≤ 36)]
  obtain ⟨c,v⟩ := domain_stats s sf
  rw [c,v]
  calc
    _ = 8*(Fintype.card K)*54 := by ring
    _ ≤ 8*(Fintype.card K)*(headDegree s 2+headDegree s 3) := Nat.mul_le_mul_left _ large
    _ = _ := by ring

private theorem count_of_stats (s : Finset (Pt K)) (sf : Free s) {D : ℕ} (large : 36≤D)
    (cap : ∀ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card≤D)
    (avg : 3*D*(Raw.domain (K:=K)).card ≤
      4*(∑ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card)) :
    rankCount s ≤ 3^Fintype.card K := by
  have bound := Potential.dense (edge (plane s)) (edge_sym _) (fun _ h => h.1 rfl) large Raw.domain cap avg
  have c := (domain_stats s sf).1
  rw [c,Nat.cast_mul,Nat.cast_ofNat,show (4*(Fintype.card K:ℝ))/4=(Fintype.card K:ℝ) by ring,
    Real.rpow_natCast] at bound
  exact_mod_cast bound

theorem of_degree (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K))
    (large : 36≤maximumDegree s) : rankCount s≤3^Fintype.card K := by
  obtain ⟨_,cap,avg⟩ := maximum_stats s sf out
  exact count_of_stats s sf large cap avg

theorem of_degree_sum (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K))
    (large : 54≤headDegree s 2+headDegree s 3) : rankCount s≤3^Fintype.card K := by
  obtain ⟨cap,avg⟩ := padded_stats s sf out large
  exact count_of_stats s sf (le_max_left ..) cap avg

/-- Every seed with at least 27 elements already satisfies the sharp generic-block bound. -/
theorem many {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s) (out : Disjoint s (full _))
    (large : 27≤s.card) : rankCount s ≤ 3^(5^k) := by
  have two := seed_le_degree s out
  have three := seed_le_degree_three s out
  simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using
    (of_degree_sum s sf out (by omega))

namespace FiniteProfile
open Sumfree Potential GraphMeasure
variable {V : Type} [Fintype V] [DecidableEq V] (r : V → V → Prop)

private def weight (β : ℝ) (s : Finset V) := mu r (2*β) s + β*s.card

private theorem loss (sym : Symmetric r) {s t : Finset V} (ts : t⊆s) {d : ℕ}
    (cap : ∀ x∈t,(neighbors r s x).card≤d) {β : ℝ} (pos : 0≤β) :
    (t.card:ℝ)/3-β*(2*d*t.card-3*t.card-(volume r t:ℝ)) ≤ weight r β s-weight r β (s\t) := by
  have g := GraphMeasure.drop r sym ts cap (b:=2*β) (by positivity)
  have n : ((s\t).card:ℝ)+t.card=s.card := by exact_mod_cast card_sdiff_add_card_eq_card ts
  unfold weight
  nlinarith only [g,congrArg (fun q : ℝ => β*q) n]

private theorem ball_info (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V} {x : V}
    (hx : x∈s) :
    let n := neighbors r s x
    let t := closed r s x
    t.card=n.card+1 ∧ 2*n.card≤volume r t := by
  let n := neighbors r s x
  have eq : closed r s x=insert x n := by
    ext y
    change y∈closed r s x ↔ y∈insert x (neighbors r s x)
    simp only [mem_closed,mem_insert,neighbors,mem_filter]
    constructor
    · exact fun h => h.2.imp_right (fun e => ⟨h.1,sym e⟩)
    · rintro (rfl|⟨inS,ed⟩)
      · exact ⟨hx,Or.inl rfl⟩
      · exact ⟨inS,Or.inr (sym ed)⟩
  have no : x∉n := fun h => irr x (mem_filter.mp h).2
  have same : neighbors r n x=n := by ext y; simp [neighbors,n,and_assoc]
  dsimp only
  rw [eq,card_insert_of_not_mem no,volume_insert r sym irr no,same]
  exact ⟨rfl,Nat.le_add_left ..⟩

private theorem induction_bound (sym : Symmetric r) (irr : Irreflexive r)
    {D : ℕ} {β : ℝ} (pos : 0≤β)
    (checks : ∀ (d : ℕ), 4≤d → d≤D →
      (3:ℝ)^(-(1/3-β*(2*d-3)))+
      (3:ℝ)^(-(((d:ℝ)+1)/3-β*(2*d*d-3*(d+1)))) ≤ 1)
    (s : Finset V) (cap : ∀ x∈s, (neighbors r s x).card≤D) :
    (mis r s:ℝ) ≤ (3:ℝ)^(weight r β s) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases low : ∀ x∈s,(neighbors r s x).card≤3
    · apply (moon_moser sym irr s).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
      have v : (volume r s:ℝ)≤s.card*3 := by exact_mod_cast volume_le r low
      unfold weight mu
      nlinarith only [mul_le_mul_of_nonneg_left v pos]
    push_neg at low
    obtain ⟨y,hy,large⟩ := low
    obtain ⟨x,xs,maximum⟩ := s.exists_max_image (fun x => (neighbors r s x).card) ⟨y,hy⟩
    let d := (neighbors r s x).card
    have dl : 4≤d := Nat.le_trans large (maximum y hy)
    let t := closed r s x
    have xt : x∈t := mem_closed.mpr ⟨xs,Or.inl rfl⟩
    have ts : t⊆s := fun _ h => (mem_closed.mp h).1
    have ht := ball_info r sym irr xs
    change t.card=d+1 ∧ 2*d≤volume r t at ht
    have rec (u : Finset V) (xu : x∈u) :
        (mis r (s\u):ℝ) ≤ (3:ℝ)^(weight r β (s\u)) := by
      have strict := Finset.ssubset_iff_subset_ne.mpr ⟨(sdiff_subset : s\u⊆s),fun h =>
        (mem_sdiff.mp (h.symm ▸ xs)).2 xu⟩
      exact ih _ strict (fun z hz => (degree_mono r sdiff_subset _).trans (cap z (mem_sdiff.mp hz).1))
    let A : ℝ := 1/3-β*(2*d-3)
    let B : ℝ := ((d:ℝ)+1)/3-β*(2*d*d-3*(d+1))
    have small : weight r β (s\{x}) ≤ weight r β s-A := by
      have h := loss r sym (singleton_subset_iff.mpr xs : {x}⊆s) (d:=d)
        (fun z hz => maximum z ((singleton_subset_iff.mpr xs : {x}⊆s) hz)) pos
      rw [card_singleton,Nat.cast_one] at h
      dsimp [A]
      nlinarith only [h,mul_nonneg pos (Nat.cast_nonneg (α:=ℝ) (volume r {x}))]
    have big : weight r β (s\t) ≤ weight r β s-B := by
      have h := loss r sym ts (d:=d) (fun z hz => maximum z (ts hz)) pos
      have v : (2:ℝ)*d≤volume r t := by exact_mod_cast ht.2
      rw [ht.1,Nat.cast_add,Nat.cast_one] at h
      dsimp [B]
      nlinarith only [h,mul_le_mul_of_nonneg_left v pos]
    have ra := (rec {x} (mem_singleton_self _)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) small)
    have rb := (rec t xt).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) big)
    have step : (mis r s:ℝ)≤(mis r (s\{x}):ℝ)+(mis r (s\t):ℝ) := by exact_mod_cast branch r s x
    apply step.trans ((add_le_add ra rb).trans _)
    simp only [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ)<3),←mul_add]
    exact (mul_le_mul_of_nonneg_left (checks d dl (cap x xs)) (Real.rpow_nonneg (by norm_num) _)).trans_eq
      (mul_one _)

private def numerator (d : ℕ) : ℕ :=
  (#[0,0,0,0,3008,3077,3149,3221,3296,3372,3450,3530,3561,3589,3614,3594,3616,3635,
    3654,3670,3686,3700,3714,3726,3738,3717,3728,3709,3719,3702,3712,3697,3706,3692,3700,3688]
    : Array ℕ)[d]?.getD 0

private def qden (a b : ℕ) := 6*(a+b-6)
private def first (a b d : ℕ) := 2*(a+b)+3-(2*d+12)
private def second (a b d : ℕ) := (d+1)*(2*(a+b)-9)-2*d*d

private def auditWeight (a b d : ℕ) : Bool :=
  if b≤a ∧ a≤2*b ∧ 4≤d ∧ d≤a ∧ (12≤b ∨ (11≤b ∧ a≤14)) then
    let i := numerator d
    let n := qden a b
    decide (i≤4096 ∧ (4096:ℕ)^n ≤ 3^(first a b d)*i^n ∧
      (4096:ℕ)^n ≤ 3^(second a b d)*(4096-i)^n)
  else true

private theorem weight_check :
    (List.range 36).all (fun a => (List.range 36).all fun b => (List.range 36).all (auditWeight a b)) =
      true := by native_decide

private theorem certificate : ∀ a b d : Fin 36, b≤a → a.val≤2*b.val → 4≤d.val → d≤a →
    (12≤b.val ∨ (11≤b.val ∧ a.val≤14)) →
    let i := numerator d
    let n := qden a b
    i≤4096 ∧ (4096:ℕ)^n ≤ 3^(first a b d)*i^n ∧
      (4096:ℕ)^n ≤ 3^(second a b d)*(4096-i)^n := by
  intro a b d ord ratio lo hi cover
  have x := List.all_eq_true.mp weight_check a.val (List.mem_range.mpr a.isLt)
  have y := List.all_eq_true.mp x b.val (List.mem_range.mpr b.isLt)
  have z := List.all_eq_true.mp y d.val (List.mem_range.mpr d.isLt)
  simpa only [auditWeight,if_pos (show b.val≤a.val ∧ a.val≤2*b.val ∧ 4≤d.val ∧ d.val≤a.val ∧ _
    from ⟨ord,ratio,lo,hi,cover⟩),decide_eq_true_eq] using z

private theorem rational_weight (p n u : ℕ) (pos : 0<n)
    (cert : (4096:ℕ)^n≤3^p*u^n) : (3:ℝ)^(-(p:ℝ)/n)≤u/4096 := by
  have npos : (0:ℝ)<n := by exact_mod_cast pos
  have raw : (4096:ℝ)^n≤3^p*u^n := by exact_mod_cast cert
  by_contra! h
  have raising := pow_lt_pow_left₀ h (by positivity) pos.ne'
  have eq : ((3:ℝ)^(-(p:ℝ)/n))^n=((3:ℝ)^p)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),div_mul_cancel₀ _ npos.ne',
      Real.rpow_neg (by norm_num),Real.rpow_natCast]
  rw [eq,div_pow] at raising
  have bad := (div_lt_iff₀ (show 0<(4096:ℝ)^n by positivity)).mp raising
  have multiplied := mul_lt_mul_of_pos_left bad (show 0<(3:ℝ)^p by positivity)
  rw [←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul] at multiplied
  exact (not_lt_of_ge raw) multiplied

private theorem bounded_profiles {a b : ℕ} (small : a<36) (order : b≤a) (ratio : a≤2*b)
    (cover : 12≤b ∨ (11≤b ∧ a≤14)) :
    let β := 1/(qden a b:ℝ)
    ∀ d : ℕ, 4≤d → d≤a →
      (3:ℝ)^(-(1/3-β*(2*d-3)))+
      (3:ℝ)^(-(((d:ℝ)+1)/3-β*(2*d*d-3*(d+1)))) ≤ 1 := by
  intro β d dlo dhi
  obtain ⟨ub,e1,e2⟩ := certificate ⟨a,small⟩ ⟨b,by omega⟩ ⟨d,by omega⟩ order ratio dlo dhi cover
  have bmin : 11≤b := by omega
  have sub : 6≤a+b := by omega
  have npos : 0<qden a b := by unfold qden; omega
  have q : (qden a b:ℝ)=6*((a:ℝ)+b-6) := by simp [qden,Nat.cast_sub sub]
  have p1 : (first a b d:ℝ)=2*((a:ℝ)+b)+3-(2*d+12) := by
    unfold first
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have nn : 2*d*d ≤ (d+1)*(2*(a+b)-9) := by
    have h : 2*d≤2*(a+b)-9 := by omega
    nlinarith only [Nat.mul_le_mul_left (d+1) h]
  have p2 : (second a b d:ℝ)=((d:ℝ)+1)*(2*(a+b)-9)-2*d*d := by
    simp [second,Nat.cast_sub nn,Nat.cast_sub (show 9≤2*(a+b) by omega)]
  have nz : (qden a b:ℝ)≠0 := by exact_mod_cast npos.ne'
  have factor1 : -(1/3-β*(2*d-3))= -(first a b d:ℝ)/(qden a b:ℝ) := by
    dsimp [β]; field_simp; rw [p1,q]; ring
  have factor2 : -(((d:ℝ)+1)/3-β*(2*d*d-3*(d+1)))= -(second a b d:ℝ)/(qden a b:ℝ) := by
    dsimp [β]; field_simp; rw [p2,q]; ring
  rw [factor1,factor2]
  have w1 := rational_weight _ _ _ npos e1
  have w2 := rational_weight _ _ _ npos e2
  have subU : ((4096-numerator d:ℕ):ℝ)=4096-(numerator d:ℝ) := by rw [Nat.cast_sub ub,Nat.cast_ofNat]
  apply (add_le_add w1 w2).trans
  rw [subU]; linarith

theorem pair_count (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full _))
    (cover : 12≤minimumDegree s ∨ (11≤minimumDegree s ∧ maximumDegree s≤14)) :
    rankCount s ≤ 3^Fintype.card K := by
  let a := maximumDegree s
  let b := minimumDegree s
  by_cases large : 36≤a
  · exact of_degree s sf out large
  have order : b≤a := (min_le_left ..).trans (le_max_left ..)
  have h2 := head_bounds s (h:=2) (Or.inl rfl)
  have h3 := head_bounds s (h:=3) (Or.inr rfl)
  have ratio : a≤2*b := by dsimp [a,b,maximumDegree,minimumDegree]; omega
  let β : ℝ := 1/(qden a b:ℝ)
  have castQ : (qden a b:ℝ)=6*((a:ℝ)+b-6) := by
    have h : 6≤a+b := by change 12≤b ∨ (11≤b ∧ a≤14) at cover; omega
    simp [qden,Nat.cast_sub h]
  have bmin : (11:ℝ)≤b := by
    exact_mod_cast (show 11≤b by change 12≤b ∨ (11≤b ∧ a≤14) at cover; omega)
  have qp : 0<(qden a b:ℝ) := by rw [castQ]; linarith [Nat.cast_nonneg (α:=ℝ) a]
  have generic := induction_bound (within s) (within_sym s) (within_irr s)
    (β:=β) (by dsimp [β]; positivity) (bounded_profiles (by omega : a<36) order ratio cover) Raw.domain
    (within_cap sf)
  apply within_quarter s sf
  have sum : headDegree s 2+headDegree s 3=a+b := by dsimp [a,b,minimumDegree,maximumDegree]; omega
  have card := (domain_stats s sf).1
  have vol : volume (within s) Raw.domain=2*Fintype.card K*(a+b) := by
    simpa only [sum] using within_volume s sf
  apply generic.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
  unfold weight mu
  rw [card,vol]
  push_cast
  dsimp [β]
  apply le_of_eq
  field_simp [qp.ne']
  rw [castQ]; ring

end FiniteProfile

/-- An independent bounded-degree branch check certifies all seeds of size at least twelve. -/
theorem many_twelve {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s) (out : Disjoint s (full _))
    (large : 12≤s.card) : rankCount s ≤ 3^(5^k) := by
  have two := seed_le_degree s out
  have three := seed_le_degree_three s out
  have cover : 12≤minimumDegree s := le_min (large.trans two) (large.trans three)
  simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using FiniteProfile.pair_count s sf out (Or.inl cover)

end
end Audit.Degrees
