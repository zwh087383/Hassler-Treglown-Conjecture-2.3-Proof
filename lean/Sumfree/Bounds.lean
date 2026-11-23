import Sumfree.Graph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sumfree
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {R : V → V → Prop}
set_option linter.unusedSectionVars false

def closed (R : V → V → Prop) (s : Finset V) (y : V) : Finset V := by
  classical exact s.filter fun z => z = y ∨ R z y

@[simp] theorem mem_closed {s : Finset V} {x y : V} :
    x ∈ closed R s y ↔ x ∈ s ∧ (x = y ∨ R x y) := by classical simp [closed]

def picked (R : V → V → Prop) (s : Finset V) (y : V) (f : Finset V) := by
  classical exact (family R s).filter fun I => y ∈ I ∧ Disjoint I f

@[simp] theorem mem_picked {s f I : Finset V} {y : V} :
    I ∈ picked R s y f ↔ IsMIS R s I ∧ y ∈ I ∧ Disjoint I f := by
  classical simp [picked]

/-- When a maximal independent set contains y and avoids f, remove y.
    The remaining choices inject into the graph outside N[y] and f. -/
theorem picked_bound (s : Finset V) (y : V) (f : Finset V) :
    (picked R s y f).card ≤ mis R (s \ (closed R s y ∪ f)) := by
  classical
  apply card_le_card_of_injOn (fun I => I.erase y)
  · intro I hi
    obtain ⟨hI, hy, hd⟩ := mem_picked.mp hi
    have sub : I.erase y ⊆ s \ (closed R s y ∪ f) := by
      intro z hz
      obtain ⟨ne, zi⟩ := mem_erase.mp hz
      exact mem_sdiff.mpr ⟨hI.1 zi, fun hu => (mem_union.mp hu).elim
        (fun hc => ((mem_closed.mp hc).2).elim ne (hI.2.1 _ zi _ hy))
        (Finset.disjoint_left.mp hd zi)⟩
    refine mem_family.mpr ⟨sub, fun x hx z hz => hI.2.1 _ (mem_of_mem_erase hx)
      _ (mem_of_mem_erase hz), ?_⟩
    intro z hz hn
    obtain ⟨zs, nz⟩ := mem_sdiff.mp hz
    have hc : z ∉ closed R s y := fun ha => nz (mem_union_left _ ha)
    have hh : ¬ (z = y ∨ R z y) := fun h => hc (mem_closed.mpr ⟨zs,h⟩)
    obtain ⟨w, wi, zw⟩ := hI.2.2 _ zs (fun zi => hn (mem_erase.mpr ⟨fun e => hh (.inl e),zi⟩))
    refine ⟨w, mem_erase.mpr ⟨?_, wi⟩, zw⟩
    intro eq
    subst w
    exact hh (.inr zw)
  · intro I hI J hJ eq
    have hi := (mem_picked.mp hI).2.1
    have hj := (mem_picked.mp hJ).2.1
    simpa [hi,hj] using congrArg (insert y) eq

theorem hit_closed (sym : Symmetric R) {s I : Finset V} (h : IsMIS R s I)
    {x : V} (xs : x ∈ s) : ∃ y ∈ closed R s x, y ∈ I := by
  by_cases xi : x ∈ I
  · exact ⟨x, mem_closed.mpr ⟨xs, Or.inl rfl⟩, xi⟩
  · obtain ⟨y, yi, e⟩ := h.2.2 _ xs xi
    exact ⟨y, mem_closed.mpr ⟨h.1 yi, Or.inr (sym e)⟩, yi⟩

theorem cover_count (sym : Symmetric R) {s : Finset V} {x : V} (xs : x ∈ s) :
    mis R s ≤ ∑ y ∈ closed R s x, (picked R s y ∅).card := by
  classical
  apply le_trans (Finset.card_le_card (t := (closed R s x).biUnion (fun y => picked R s y ∅)) ?_)
    Finset.card_biUnion_le
  intro I hi
  have h := mem_family.mp hi
  obtain ⟨y, hy, yi⟩ := hit_closed sym h xs
  exact mem_biUnion.mpr ⟨y,hy, mem_picked.mpr ⟨h,yi,disjoint_empty_right _⟩⟩

def TriangleFree (R : V → V → Prop) := ∀ x y z, R x y → R y z → ¬ R x z

private theorem grow (b : ℝ) (k : ℕ) (b1 : 1 ≤ b) (step : (1 : ℝ) ≤ k * (b-1))
    (start : (k : ℝ) ≤ b^k) (t : ℕ) (ht : k ≤ t) : (t : ℝ) ≤ b^t := by
  induction t, ht using Nat.le_induction with
  | base => exact start
  | succ n hn ih =>
    have hk : (k : ℝ) ≤ n := by exact_mod_cast hn
    have inc := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr b1)
    have m := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ b)
    rw [pow_succ, Nat.cast_succ]
    linarith

/-- Common minimum-degree induction. In the triangle-free degree-two case,
    previous choices in the closed neighborhood give one extra excluded vertex. -/
theorem branching_bound (sym : Symmetric R) (_irr : Irreflexive R)
    (b : ℝ) (b1 : 1 ≤ b)
    (cost : ∀ t : ℕ, 0 < t → (t : ℝ) ≤ b^t ∨
      (t = 3 ∧ TriangleFree R ∧ 2*b+1 ≤ b^4)) (s : Finset V) :
    (mis R s : ℝ) ≤ b^s.card := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases empty : s = ∅
    · subst s
      have h : family R ∅ ⊆ ({∅} : Finset (Finset V)) := by
        intro I hi
        simpa using (Finset.subset_empty.mp (mem_family.mp hi).1)
      have h' := Finset.card_le_card h
      simp only [mis, Finset.card_empty, pow_zero, Nat.cast_le_one]
      simpa using h'
    obtain ⟨x,xs,minimal⟩ := s.exists_min_image (fun y => (closed R s y).card)
      (Finset.nonempty_iff_ne_empty.mpr empty)
    let t := (closed R s x).card
    have xc : x ∈ closed R s x := mem_closed.mpr ⟨xs, Or.inl rfl⟩
    have pos : 0 < t := Finset.card_pos.mpr ⟨_,xc⟩
    have inside (y : V) : closed R s y ⊆ s := fun z hz => (mem_closed.mp hz).1
    have ts : t ≤ s.card := card_le_card (inside x)
    have pick {y : V} (ys : y ∈ s) (f : Finset V) (hf : f ⊆ s)
        (m : ℕ) (hm : m ≤ (closed R s y ∪ f).card) :
        ((picked R s y f).card : ℝ) ≤ b^(s.card-m) := by
      let removed := closed R s y ∪ f
      have hr : removed ⊆ s := Finset.union_subset (inside y) hf
      have yr : y ∈ removed := mem_union_left _ (mem_closed.mpr ⟨ys,Or.inl rfl⟩)
      have hss : s \ removed ⊂ s := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.sdiff_subset, fun eq => (Finset.mem_sdiff.mp (eq.symm ▸ ys)).2 yr⟩
      have branch := ih _ hss
      have hp : ((picked R s y f).card : ℝ) ≤ mis R (s \ removed) := by exact_mod_cast picked_bound (R := R) s y f
      apply hp.trans (branch.trans (pow_le_pow_right₀ b1 ?_))
      rw [Finset.card_sdiff hr]
      exact Nat.sub_le_sub_left hm _
    have single {y : V} (ys : y ∈ s) : ((picked R s y ∅).card : ℝ) ≤ b^(s.card-t) :=
      pick ys ∅ (empty_subset _) t (by simpa using minimal y ys)
    rcases cost t pos with normal | ⟨three,tri,extra⟩
    · have cover : (mis R s : ℝ) ≤ ∑ y ∈ closed R s x, ((picked R s y ∅).card : ℝ) := by
        exact_mod_cast cover_count sym xs
      calc
        _ ≤ _ := cover
        _ ≤ ∑ _y ∈ closed R s x, b^(s.card-t) := sum_le_sum (fun y hy => single (inside x hy))
        _ = (t : ℝ)*b^(s.card-t) := by simp [t]
        _ ≤ b^t*b^(s.card-t) := mul_le_mul_of_nonneg_right normal (by positivity)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le ts]
    · obtain ⟨y,z,ne,hyz⟩ := Finset.card_eq_two.mp
        (show ((closed R s x).erase x).card = 2 by rw [Finset.card_erase_of_mem xc]; omega)
      have cl : closed R s x = insert x {y,z} := by rw [← hyz, Finset.insert_erase xc]
      have spec (w : V) (hw : w ∈ ({y,z} : Finset V)) : w ≠ x ∧ w ∈ s ∧ R w x := by
        have he := Finset.mem_erase.mp (hyz.symm ▸ hw)
        have hc := mem_closed.mp he.2
        exact ⟨he.1, hc.1, hc.2.resolve_left he.1⟩
      have Y := spec y (by simp)
      have Z := spec z (by simp)
      have yn : y ∉ closed R s z := fun h => (mem_closed.mp h).2.elim ne (tri y x z Y.2.2 (sym Z.2.2))
      have m4 : 4 ≤ (closed R s z ∪ {y}).card := by
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_not_mem yn]
        have := minimal z Z.2.1
        change t ≤ _ at this
        omega
      have s4 : 4 ≤ s.card := m4.trans (card_le_card (union_subset (inside z) (by simpa using Y.2.1)))
      have cover : family R s ⊆ picked R s x ∅ ∪ picked R s y ∅ ∪ picked R s z {y} := by
        intro I hi
        have h := mem_family.mp hi
        by_cases xi : x ∈ I
        · exact mem_union_left _ (mem_union_left _ (mem_picked.mpr ⟨h,xi,by simp⟩))
        by_cases yi : y ∈ I
        · exact mem_union_left _ (mem_union_right _ (mem_picked.mpr ⟨h,yi,by simp⟩))
        obtain ⟨w,hw,wi⟩ := hit_closed sym h xs
        rw [cl] at hw
        simp only [mem_insert,mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · contradiction
        · contradiction
        · exact mem_union_right _ (mem_picked.mpr ⟨h,wi,by simpa using yi⟩)
      have count := (card_le_card cover).trans ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _))
      have cr : (mis R s : ℝ) ≤ ((picked R s x ∅).card : ℝ) + (picked R s y ∅).card +
          (picked R s z {y}).card := by exact_mod_cast count
      have cz := pick Z.2.1 {y} (by simpa using Y.2.1) 4 m4
      have h3 : s.card-t = s.card-4+1 := by omega
      have hn : s.card-4+4 = s.card := by omega
      have h := add_le_add (add_le_add (single xs) (single Y.2.1)) cz
      rw [h3, pow_succ] at h
      have m := mul_le_mul_of_nonneg_left extra (show 0 ≤ b^(s.card-4) by positivity)
      calc
        _ ≤ _ := cr.trans h
        _ = b^(s.card-4)*(2*b+1) := by ring
        _ ≤ _ := m
        _ = _ := by rw [← pow_add,hn]

theorem moon_moser (sym : Symmetric R) (irr : Irreflexive R) (s : Finset V) :
    (mis R s : ℝ) ≤ (3 : ℝ)^((s.card : ℝ)/3) := by
  let b := (3 : ℝ)^((1 : ℝ)/3)
  have b1 : 1 ≤ b := Real.one_le_rpow (by norm_num) (by norm_num)
  have cube : b^3 = 3 := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have grow3 : (4:ℝ)/3 ≤ b := by
    by_contra! hn
    have := pow_lt_pow_left₀ hn (n := 3) (by linarith) (by decide)
    norm_num at this
    linarith
  have two : (2:ℝ) ≤ b^2 := by
    by_contra! h
    have dbl := mul_lt_mul_of_pos_right h (by linarith : 0 < b)
    have small : b < 3/2 := by nlinarith [sq_nonneg (b-3/2)]
    nlinarith [cube]
  have bound := branching_bound sym irr b b1 (fun t ht => Or.inl (by
    rcases t with _ | _ | _ | k
    · omega
    · simpa using b1
    · simpa using two
    · exact grow b 3 b1 (by norm_num; linarith) (by norm_num; linarith) _ (by omega))) s
  convert bound using 1
  dsimp [b]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring

theorem hujter_tuza (sym : Symmetric R) (irr : Irreflexive R) (tri : TriangleFree R) (s : Finset V) :
    (mis R s : ℝ) ≤ (2 : ℝ)^((s.card : ℝ)/2) := by
  let b := Real.sqrt 2
  have sq : b^2 = 2 := Real.sq_sqrt (by norm_num)
  have non : 0 ≤ b := Real.sqrt_nonneg _
  have b1 : 1 ≤ b := by nlinarith
  have b4 : b^4 = 4 := by nlinarith [sq, sq_nonneg (b^2-2), congrArg (fun v : ℝ => v*v) sq]
  have bl : 5/4 ≤ b := by nlinarith [sq_nonneg (b-5/4)]
  have bu : b ≤ 3/2 := by nlinarith [sq_nonneg (b-3/2)]
  have bound := branching_bound sym irr b b1 (fun t ht => by
    rcases t with _ | _ | _ | _ | k
    · omega
    · exact Or.inl (by simpa using b1)
    · exact Or.inl (by norm_num; linarith)
    · exact Or.inr ⟨rfl,tri,by linarith⟩
    · exact Or.inl (grow b 4 b1 (by norm_num; linarith) (by norm_num; linarith) _ (by omega))) s
  convert bound using 1
  dsimp [b]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

end
end Sumfree
