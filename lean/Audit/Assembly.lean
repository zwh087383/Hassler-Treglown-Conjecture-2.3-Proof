import Audit.Blocks
import Audit.Removal
import Audit.Asymptotic

namespace Audit.Assembly
open Finset Link Lower Band Blocks Sumfree Filter
open scoped Classical Topology
noncomputable section
set_option linter.unusedSectionVars false

variable {G J : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup J] [DecidableEq J]

theorem free_image (e : G ≃+ J) (s : Finset G) : Free (s.image e) ↔ Free s := by
  constructor
  · intro f x hx y hy z hz eq
    exact f _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy) _ (mem_image_of_mem _ hz)
      (by rw [←map_add,eq])
  · intro f x hx y hy z hz eq
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
    exact f _ ha _ hb _ hc (e.injective (by rwa [map_add]))

theorem link_image (e : G ≃+ J) (s b : Finset G) :
    mis (clash s) (legal s b) = mis (clash (s.image e)) (legal (s.image e) (b.image e)) := by
  classical
  have compat {x : G} : Free (insert (e x) (s.image e)) ↔ Free (insert x s) := by
    rw [←image_insert]; exact free_image e _
  have eq : (legal s b).image e=legal (s.image e) (b.image e) := by
    ext y; obtain ⟨x,rfl⟩ := e.surjective y
    simp only [mem_image,mem_legal, e.injective.eq_iff,exists_eq_right,compat]
  rw [←eq]
  apply mis_image _ _ _ _ e.injective.injOn
  intro x _ y _
  simp only [clash,e.injective.ne_iff]
  have h := free_image e (insert x (insert y s))
  rw [image_insert,image_insert] at h
  tauto

abbrev group (k : ℕ) := Pt (Space k)
def order (k : ℕ) : ℝ := (5:ℝ)^(k+1)

theorem total_order (k : ℕ) : (Fintype.card (group k):ℝ) = order k := by
  simp [group,Pt,Space,Field5,Fintype.card_fun,order,pow_succ,mul_comm]

theorem tail_order (k : ℕ) : (Fintype.card (Space k):ℝ)/2 = order k/10 := by
  simp [Space,Field5,Fintype.card_fun,order,pow_succ]; ring

/-- The precise structural input needed from the large sum-free set theorem.
    Containment suffices. Maximality upgrades it to equality below. -/
def LargeSetStructure : Prop := ∀ (k : ℕ) (m : Finset (group k)),
  Free m → 3*order k/10 < m.card →
    ∃ e : group k ≃+ group k, m.image e ⊆ full (Space k)

/-- A qualitative container input with two independent accuracies. -/
def SparseCovers : Prop := ∀ η : ℝ, 0<η → ∀ δ : ℝ, 0<δ →
  ∀ᶠ k : ℕ in atTop, ∃ F : Finset (Finset (group k)),
    (F.card:ℝ) ≤ (2:ℝ)^(η*order k) ∧
    (∀ x∈maximalSets (univ : Finset (group k)),∃ c∈F,x⊆c) ∧
    ∀ c∈F, ((Removal.triples c).card:ℝ) < δ*(order k)^2

theorem full_of_maximal {k : ℕ} {m : Finset (group k)} (mx : MaxIn univ m)
    (e : group k ≃+ group k) (sub : m.image e ⊆ full (Space k)) :
    m.image e=full (Space k) := by
  let b := full (Space k)
  have large : m ⊆ b.image e.symm := by
    intro x hx; exact mem_image.mpr ⟨e x,sub (mem_image_of_mem _ hx),e.symm_apply_apply x⟩
  have eq := mx.2.2 _ (subset_univ _) ((free_image e.symm b).mpr (band_free _)) large
  apply Subset.antisymm sub
  intro y hy
  exact mem_image.mpr ⟨e.symm y, eq ▸ mem_image_of_mem e.symm hy, e.apply_symm_apply y⟩

def StandardBand : Prop := ∀ (k : ℕ) (s : Finset (group k)),
  Free s → Disjoint s (full (Space k)) →
    (mis (clash s) (legal s (full (Space k))):ℝ) ≤
      (3:ℝ)^((Fintype.card (Space k):ℝ)/2+errorConstant)

theorem maximal_link_with_band (structureInput : LargeSetStructure) (bandBound : StandardBand)
    {k : ℕ} {m s : Finset (group k)} (mx : MaxIn univ m) (sf : Free s) (dis : Disjoint s m) :
    (mis (clash s) (legal s m):ℝ) ≤ (3:ℝ)^(order k/10+errorConstant) := by
  classical
  by_cases small : (m.card:ℝ)≤3*order k/10
  · apply (moon_moser (clash_sym s) (fun _ h => h.1 rfl) (legal s m)).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have sub : legal s m ⊆ m := fun _ h => (mem_legal.mp h).1
    have h : ((legal s m).card:ℝ)≤m.card := by exact_mod_cast card_le_card sub
    have pos : 0 ≤ errorConstant := by unfold errorConstant; positivity
    linarith
  · obtain ⟨e,sub⟩ := structureInput k m mx.2.1 (lt_of_not_ge small)
    have eq := full_of_maximal mx e sub
    rw [link_image e,eq,←tail_order]
    apply bandBound _ _ ((free_image e _).mpr sf)
    rw [←eq]
    exact (Finset.disjoint_image e.injective).mpr dis

theorem maximal_link (structureInput : LargeSetStructure) (gb : BlockBound)
    {k : ℕ} {m s : Finset (group k)} (mx : MaxIn univ m) (sf : Free s) (dis : Disjoint s m) :
    (mis (clash s) (legal s m):ℝ) ≤ (3:ℝ)^(order k/10+errorConstant) :=
  maximal_link_with_band structureInput (fun _ _ => all_seeds gb) mx sf dis

def LocalBound (k : ℕ) (b : ℝ) : Prop := ∀ m s : Finset (group k),
  MaxIn univ m → Free s → Disjoint s m → (mis (clash s) (legal s m):ℝ) ≤ b

theorem per_container_with
    {k : ℕ} {η : ℝ} (hη : 0<η) (unit : η≤1)
    {bound : ℝ} (nonneg : 0≤bound) (links : LocalBound k bound)
    (c : Finset (group k)) (few : ((Removal.triples c).card:ℝ) <
      27*SimpleGraph.triangleRemovalBound (η/27)*(order k)^2) :
    (((maximalSets (univ : Finset (group k))).filter fun x => x⊆c).card:ℝ)
      ≤ (2:ℝ)^(η*order k)*bound := by
  classical
  obtain ⟨e,_,size,free⟩ := (Removal.remove (G:=group k) η hη unit).2 c (by rwa [total_order])
  rw [total_order] at size
  obtain ⟨m,hm,ins⟩ := extend free (subset_univ _)
  let exc := e \ m
  have cover : c ⊆ m∪exc := by
    intro x hx; by_cases h : x∈m
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨by by_contra he; exact h (ins (mem_sdiff.mpr ⟨hx,he⟩)),h⟩)
  let seeds := exc.powerset.filter (fun s => Free s)
  have one (s : Finset (group k)) (hs : s∈seeds) :
      (mis (clash s) (legal s m):ℝ) ≤ bound := by
    obtain ⟨sub,sf⟩ := mem_filter.mp hs
    exact links m s (mem_maximalSets.mp hm) sf (disjoint_left.mpr
      (fun _ x y => (mem_sdiff.mp ((mem_powerset.mp sub) x)).2 y))
  have count : (seeds.card:ℝ) ≤ (2:ℝ)^(η*order k) := by
    have a := card_le_card (filter_subset (fun s => Free s) exc.powerset)
    rw [card_powerset] at a
    calc
      _ ≤ (2:ℝ)^exc.card := by exact_mod_cast a
      _ = (2:ℝ)^(exc.card:ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact (show (exc.card:ℝ) ≤ e.card by exact_mod_cast card_le_card (sdiff_subset : exc⊆e)).trans size
  have counted := container_count m exc (mem_maximalSets.mp hm).2.1
  have card0 := card_le_card (monotone_filter_right (maximalSets (univ : Finset (group k)))
    (fun x (h : x⊆c) => h.trans cover))
  calc
    _ ≤ ∑ s ∈ seeds, (mis (clash s) (legal s m):ℝ) := by exact_mod_cast card0.trans counted
    _ ≤ ∑ _s ∈ seeds, bound := sum_le_sum one
    _ = seeds.card*bound := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right count nonneg

theorem upper_with (covers : SparseCovers) (b : ℕ → ℝ)
    (nonneg : ∀ k, 0≤b k) (links : ∀ k, LocalBound k (b k))
    {η : ℝ} (hη : 0<η) (unit : η≤1) :
    ∀ᶠ k : ℕ in atTop, (Asymptotic.fmax (k+1):ℝ) ≤
      (2:ℝ)^((2*η)*order k)*b k := by
  have pos := (Removal.remove (G:=group 0) η hη unit).1
  filter_upwards [covers η hη _ pos] with k hk
  obtain ⟨F,size,cover,few⟩ := hk
  let all := maximalSets (univ : Finset (group k))
  let restricted (c : Finset (group k)) := all.filter fun x => x⊆c
  have sub : all ⊆ F.biUnion restricted := by
    intro x hx; obtain ⟨c,hc,h⟩ := cover x hx
    exact mem_biUnion.mpr ⟨c,hc,mem_filter.mpr ⟨hx,h⟩⟩
  let base := (2:ℝ)^(η*order k)
  let bound := b k
  change (all.card:ℝ) ≤ _
  calc
    _ ≤ ∑ c∈F, ((restricted c).card:ℝ) := by exact_mod_cast (card_le_card sub).trans (card_biUnion_le ..)
    _ ≤ ∑ _c∈F, base*bound := by
      apply sum_le_sum; intro c hc
      exact per_container_with hη unit (nonneg k) (links k) c (few c hc)
    _ = F.card*(base*bound) := by simp
    _ ≤ base*(base*bound) := mul_le_mul_of_nonneg_right size (mul_nonneg (by dsimp [base]; positivity) (nonneg k))
    _ = _ := by dsimp [base,bound]; rw [←mul_assoc,←Real.rpow_add (by norm_num)]; congr 2; ring

theorem upper_with_band (covers : SparseCovers) (structural : LargeSetStructure)
    (bandBound : StandardBand) {η : ℝ} (hη : 0<η) (unit : η≤1) :
    ∀ᶠ k : ℕ in atTop, (Asymptotic.fmax (k+1):ℝ) ≤
      (2:ℝ)^((2*η)*order k)*(3:ℝ)^(order k/10+errorConstant) :=
  upper_with covers _ (fun _ => Real.rpow_nonneg (by norm_num) _)
    (fun _ _ _ => maximal_link_with_band structural bandBound) hη unit

theorem upper_at_accuracy (covers : SparseCovers) (structureInput : LargeSetStructure)
    (gb : BlockBound) {η : ℝ} (hη : 0<η) (unit : η≤1) :
    ∀ᶠ k : ℕ in atTop, (Asymptotic.fmax (k+1):ℝ) ≤
      (2:ℝ)^((2*η)*order k)*(3:ℝ)^(order k/10+errorConstant) :=
  upper_with_band covers structureInput (fun _ _ => all_seeds gb) hη unit

end
end Audit.Assembly
