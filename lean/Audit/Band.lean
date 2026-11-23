import Audit.Lower
import Audit.Fingerprint
import Sumfree.Induced

namespace Audit.Band

open Finset Link Lower Sumfree
open scoped Classical
set_option linter.unusedSectionVars false
noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def edge (s : Finset G) (x y : G) : Prop :=
  x≠y ∧ (x+y∈s ∨ y-x∈s ∨ x-y∈s)

theorem edge_sym (s : Finset G) : Symmetric (edge s) := by
  intro x y h
  obtain ⟨ne,h⟩ := h
  exact ⟨ne.symm,by rw [add_comm y x]; tauto⟩

theorem legal_edge {s b : Finset G} (fb : Free b) {x y : G}
    (lx : x∈legal s b) (ly : y∈legal s b) : clash s x y ↔ edge s x y := by
  obtain ⟨xb,fx⟩ := mem_legal.mp lx
  obtain ⟨yb,fy⟩ := mem_legal.mp ly
  constructor
  · rintro ⟨ne,bad⟩
    refine ⟨ne,?_⟩
    by_contra! none
    obtain ⟨noSum,noYX,noXY⟩ := none
    apply bad
    intro a ha b' hb c hc eq
    have ca : c-a=b' := sub_eq_iff_eq_add.mpr (by simpa [add_comm] using eq.symm)
    have cb : c-b'=a := sub_eq_iff_eq_add.mpr eq.symm
    have rev : b'+a=c := by rwa [add_comm]
    simp only [mem_insert] at ha hb hc
    rcases ha with rfl|rfl|ha <;> rcases hb with rfl|rfl|hb <;> rcases hc with rfl|rfl|hc
    all_goals first
      | apply fb _ ?_ _ ?_ _ ?_ eq <;> assumption
      | apply fx _ ?_ _ ?_ _ ?_ eq <;> first | exact mem_insert_self _ _ | (apply mem_insert_of_mem; assumption)
      | apply fy _ ?_ _ ?_ _ ?_ eq <;> first | exact mem_insert_self _ _ | (apply mem_insert_of_mem; assumption)
      | apply noSum; rwa [eq]
      | apply noSum; rwa [rev]
      | apply noYX; rwa [ca]
      | apply noXY; rwa [ca]
      | apply noYX; rwa [cb]
      | apply noXY; rwa [cb]
  · rintro ⟨ne,h⟩
    refine ⟨ne,fun f => ?_⟩
    rcases h with h|h|h
    · exact f x (by simp) y (by simp) _ (by simp [h]) rfl
    · exact f (y-x) (by simp [h]) x (by simp) y (by simp) (sub_add_cancel _ _)
    · exact f (x-y) (by simp [h]) y (by simp) x (by simp) (sub_add_cancel _ _)

theorem legal_le_edges {s b : Finset G} (fb : Free b) :
    mis (clash s) (legal s b) ≤ mis (edge s) b := by
  classical
  have changeRel := mis_image (legal s b) id (clash s) (edge s)
    (fun _ _ _ _ h => h) (fun _ hx _ hy => legal_edge fb hx hy)
  rw [image_id] at changeRel
  rw [changeRel]
  exact induced_mono (edge_sym s) (fun _ hx => (mem_legal.mp hx).1) (fun _ _ h => h.1 rfl)

variable {H : Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
abbrev full (H : Type*) [Fintype H] := band (univ : Finset H)
abbrev Vtx (H : Type*) [Fintype H] := ↥(full H)

def signed (s : Finset (Pt H)) := s ∪ s.image Neg.neg
def forward (s : Finset (Pt H)) := (signed s).filter fun p => p.1=0 ∨ p.1=1

@[simp] theorem mem_signed {s : Finset (Pt H)} {d : Pt H} : d∈signed s ↔ d∈s ∨ -d∈s := by
  simp only [signed,mem_union]
  apply or_congr_right
  constructor
  · intro h; obtain ⟨a,ha,rfl⟩ := mem_image.mp h; simpa using ha
  · intro h; exact mem_image.mpr ⟨-d,h,neg_neg _⟩

@[simp] theorem mem_full {u : Pt H} : u∈full H ↔ u.1=2 ∨ u.1=3 := by
  rcases u with ⟨a,x⟩; simp

private theorem sign_head (a : Fin 5) : (a=2 ∨ a=3) ↔ (-a=2 ∨ -a=3) := by
  revert a; decide

def flip (v : Vtx H) : Vtx H :=
  ⟨-v.val,mem_full.mpr ((sign_head _).mp (mem_full.mp v.2))⟩

theorem flip_inj : Function.Injective (flip (H:=H)) := by
  intro v w eq; apply Subtype.ext; exact neg_injective (congrArg Subtype.val eq)

theorem seed_card {s : Finset (Pt H)} (outside : Disjoint s (full H)) :
    s.card ≤ 2*(forward s).card := by
  have sub : s ⊆ forward s ∪ (forward s).image Neg.neg := by
    intro d hd
    have no : ¬(d.1=2 ∨ d.1=3) := fun h => disjoint_left.mp outside hd (mem_full.mpr h)
    have types : ∀ a : Fin 5, ¬(a=2 ∨ a=3) → (a=0 ∨ a=1) ∨ (-a=0 ∨ -a=1) := by decide
    rcases types _ no with yes|yes
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_signed.mpr (Or.inl hd),yes⟩)
    · apply mem_union_right _; apply mem_image.mpr
      exact ⟨-d,mem_filter.mpr ⟨mem_signed.mpr (Or.inr (by simpa)),yes⟩,neg_neg _⟩
  have h := (card_le_card sub).trans (card_union_le ..)
  have im := card_image_le (f:=Neg.neg) (s:=forward s)
  omega

def difference (s : Finset (Pt H)) (v : Vtx H) : Finset (Vtx H) :=
  univ.filter fun w => w.val-v.val∈signed s

def sumNeighbors (s : Finset (Pt H)) (v : Vtx H) : Finset (Vtx H) :=
  univ.filter fun w => v.val+w.val∈s

private theorem ambient_diff (s : Finset (Pt H)) (v : Vtx H)
    (v2 : v.val.1=2) :
    (difference s v).image Subtype.val = (forward s).image (v.val+·) := by
  ext w
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := mem_image.mp h
    have heads : ∀ a : Fin 5, (a=2 ∨ a=3) → a-2=0 ∨ a-2=1 := by decide
    have head := heads _ (mem_full.mp u.2)
    refine mem_image.mpr ⟨u.val-v.val,mem_filter.mpr ⟨(mem_filter.mp hu).2,?_⟩,?_⟩
    · change u.val.1-v.val.1=0 ∨ u.val.1-v.val.1=1
      rwa [v2]
    · simp
  · intro h
    obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    obtain ⟨ds,dh⟩ := mem_filter.mp hd
    have heads : ∀ a : Fin 5, (a=0 ∨ a=1) → 2+a=2 ∨ 2+a=3 := by decide
    have ok : v.val+d∈full H := by
      apply mem_full.mpr; change v.val.1+d.1=2 ∨ v.val.1+d.1=3
      rw [v2]; exact heads _ dh
    refine mem_image.mpr ⟨⟨_,ok⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    simpa using ds

theorem difference_card (s : Finset (Pt H)) (v : Vtx H) :
    (difference s v).card = (forward s).card := by
  have layerTwo (w : Vtx H) (two : w.val.1=2) :
      (difference s w).card = (forward s).card := by
    have h := congrArg Finset.card (ambient_diff s w two)
    rwa [card_image_of_injective _ Subtype.val_injective,
      card_image_of_injective _ (add_right_injective _)] at h
  rcases mem_full.mp v.2 with ht|ht
  · exact layerTwo v ht
  · have two : (flip v).val.1=2 := by change -v.val.1=2; rw [ht]; decide
    rw [←layerTwo (flip v) two]
    apply card_bij (fun w _ => flip w)
    · intro w hw
      have h := (mem_filter.mp hw).2
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      change -w.val- -v.val∈signed s
      have eq : -w.val- -v.val= -(w.val-v.val) := by abel
      simpa only [eq,mem_signed,neg_neg,or_comm] using h
    · exact fun _ _ _ _ eq => flip_inj eq
    · intro w hw
      have h := (mem_filter.mp hw).2
      refine ⟨flip w,mem_filter.mpr ⟨mem_univ _,?_⟩,Subtype.ext (neg_neg _)⟩
      change -w.val-v.val∈signed s
      change w.val- -v.val∈signed s at h
      have eq : -w.val-v.val= -(w.val- -v.val) := by abel
      rw [eq]; simpa only [mem_signed,neg_neg,or_comm] using h

theorem sum_card (s : Finset (Pt H)) (v : Vtx H) :
    (sumNeighbors s v).card ≤ (difference s v).card := by
  apply card_le_card_of_injOn flip
  · intro w hw
    have h := (mem_filter.mp hw).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,mem_signed.mpr (Or.inr ?_)⟩
    change -(-w.val-v.val)∈s
    simpa [neg_sub] using h
  · exact flip_inj.injOn

theorem degrees {s : Finset (Pt H)} (sf : Free s) (v : Vtx H) :
    let nbs := Fingerprint.neighbors (fun a b : Vtx H => edge s a.val b.val) univ v
    (forward s).card ≤ nbs.card ∧ nbs.card ≤ 2*(forward s).card := by
  classical
  dsimp only
  let nbs := Fingerprint.neighbors (fun a b : Vtx H => edge s a.val b.val) univ v
  have zero : (0:Pt H)∉s := fun hs => sf 0 hs 0 hs 0 hs (zero_add _)
  have lower : difference s v ⊆ nbs := by
    intro w hw
    have d := mem_signed.mp (mem_filter.mp hw).2
    have ne : v.val≠w.val := by
      intro e; rcases d with h|h <;> simp [e,zero] at h
    refine mem_filter.mpr ⟨mem_univ _,ne,Or.inr ?_⟩
    simpa only [neg_sub] using d
  have upper : nbs ⊆ difference s v ∪ sumNeighbors s v := by
    intro w hw
    rcases (mem_filter.mp hw).2.2 with h|h|h
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,mem_signed.mpr (Or.inl h)⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,mem_signed.mpr (Or.inr (by simpa only [neg_sub]))⟩)
  have u := (card_le_card upper).trans (card_union_le ..)
  have vBound := sum_card s v
  have l := card_le_card lower
  change (forward s).card ≤ nbs.card ∧ nbs.card ≤ 2*(forward s).card
  rw [←difference_card s v]
  omega

/-- The complete large-seed branch of the actual link, for every finite abelian tail group. -/
theorem large_seed {s : Finset (Pt H)} (sf : Free s) (outside : Disjoint s (full H))
    (large : 8192 ≤ s.card) :
    (mis (clash s) (legal s (full H)):ℝ) ≤ (3:ℝ)^((Fintype.card H:ℝ)/2) := by
  classical
  let r (v w : Vtx H) := edge s v.val w.val
  let d := (forward s).card
  have h := seed_card outside
  have threshold : 4096≤d := by dsimp [d]; omega
  have f := Fingerprint.large_graph r (fun _ _ h => edge_sym s h) (fun _ h => h.1 rfl)
    (Δ:=2*d) threshold le_rfl (fun x => (degrees sf x).1) (fun x => (degrees sf x).2)
  have trans := mis_image (univ : Finset (Vtx H)) Subtype.val r (edge s)
    Subtype.val_injective.injOn (fun _ _ _ _ => Iff.rfl)
  have vs : (univ : Finset (Vtx H)).image Subtype.val = full H := by ext x; simp
  rw [vs] at trans
  have eq : Fintype.card (Vtx H) = 2*Fintype.card H := by
    rw [Fintype.card_coe]; simp [full,band]
  have small := legal_le_edges (s:=s) (band_free (univ : Finset H))
  calc
    _ ≤ (mis (edge s) (full H):ℝ) := by exact_mod_cast small
    _ = _ := by exact_mod_cast trans.symm
    _ ≤ _ := f
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [eq]; push_cast
      have hn : (0:ℝ) ≤ Fintype.card H := by positivity
      linarith

end
end Audit.Band
