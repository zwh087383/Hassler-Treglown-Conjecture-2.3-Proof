import Sumfree.Symmetric
import Sumfree.Transport
import Mathlib.LinearAlgebra.Span.Basic

namespace Sumfree.Pair
open Finset
abbrev F := ZMod 5
variable {H : Type*} [AddCommGroup H] [Module F H] [DecidableEq H]
set_option linter.unusedSectionVars false

def band {H : Type*} (x : F × H) : Prop := x.1 = 2 ∨ x.1 = 3
instance {H : Type*} (x : F × H) : Decidable (band x) := inferInstanceAs (Decidable (_ ∨ _))
def layers [Fintype H] : Finset (Ambient H) := univ.filter band

def seedSet (s t : Ambient H) : Set (Ambient H) := {s,t}
def legalAt (s t x : Ambient H) := SumFree (insert x (seedSet s t))
def edges (s t x y : Ambient H) := x ≠ y ∧ raw (seedSet s t) x y

def coeffs : List F := List.finRange 5
@[simp] theorem mem_coeffs (a : F) : a ∈ coeffs := List.mem_finRange _

def points (s t g : Ambient H) : List (Ambient H) :=
  ([g,-g].flatMap fun h => coeffs.flatMap fun a =>
    coeffs.map fun b => h+a • s+b • t).filter (fun x => decide (band x))
def cell (s t g : Ambient H) := (points s t g).toFinset

def K (s t : Ambient H) : AddSubgroup (Ambient H) where
  carrier := {u | ∃ a b : F, u = a • s + b • t}
  zero_mem' := ⟨0,0,by simp⟩
  add_mem' := by rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩; exact ⟨a+c,b+d,by simp only [add_smul]; abel⟩
  neg_mem' := by rintro _ ⟨a,b,rfl⟩; exact ⟨-a,-b,by simp only [neg_smul]; abel⟩

def related (s t x y : Ambient H) := y-x ∈ K s t ∨ y+x ∈ K s t

theorem refl_rel (s t x : Ambient H) : related s t x x :=
  Or.inl (by rw [sub_self]; exact (K s t).zero_mem)
theorem sym_rel {s t x y : Ambient H} : related s t x y → related s t y x := by
  rintro (h|h)
  · exact Or.inl (by simpa using (K s t).neg_mem h)
  · exact Or.inr (by simpa [add_comm] using h)
theorem trans_rel {s t x y z : Ambient H} : related s t x y → related s t y z → related s t x z := by
  rintro (a|a) (b|b)
  · exact Or.inl (by convert (K s t).add_mem b a using 1; abel)
  · exact Or.inr (by convert (K s t).sub_mem b a using 1; abel)
  · exact Or.inr (by convert (K s t).add_mem b a using 1; abel)
  · exact Or.inl (by convert (K s t).sub_mem b a using 1; abel)

theorem mem_cell {s t g x : Ambient H} : x ∈ cell s t g ↔ band x ∧ related s t g x := by
  simp only [cell,List.mem_toFinset,points,List.mem_filter,decide_eq_true_eq,List.mem_flatMap,
    List.mem_map,mem_coeffs,true_and,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨⟨h,hg,a,b,rfl⟩,bx⟩
    refine ⟨bx,?_⟩
    rcases hg with rfl | rfl
    · exact Or.inl ⟨a,b,by abel⟩
    · exact Or.inr ⟨a,b,by abel⟩
  · rintro ⟨bx,hy⟩
    refine ⟨?_,bx⟩
    rcases hy with ⟨a,b,e⟩ | ⟨a,b,e⟩
    · exact ⟨g,Or.inl rfl,a,b,by rw [add_assoc,← e]; abel⟩
    · exact ⟨-g,Or.inr rfl,a,b,by rw [add_assoc,← e]; abel⟩

theorem edge_rel {s t x y : Ambient H} (h : edges s t x y) : related s t x y := by
  have seeds {v} (vS : v ∈ seedSet s t) : v ∈ K s t := by
    rcases vS with rfl | rfl
    · exact ⟨1,0,by simp⟩
    · exact ⟨0,1,by simp⟩
  rcases h.2 with e | e | e
  · exact Or.inr (by rw [add_comm]; exact seeds e)
  · exact Or.inl (by simpa using (K s t).neg_mem (seeds e))
  · exact Or.inl (seeds e)

noncomputable def allowed (s t : Ambient H) (A : Finset (Ambient H)) : Finset (Ambient H) := by
  classical exact A.filter (legalAt s t)
@[simp] theorem mem_allowed {s t : Ambient H} {A : Finset (Ambient H)} {x : Ambient H} :
    x ∈ allowed s t A ↔ x ∈ A ∧ legalAt s t x := by classical simp [allowed]

/-- A bound on each orbit, raised to integer powers, gives a bound on the entire band. -/
theorem assemble [Fintype H] (s t : Ambient H) (power base : ℕ)
    (localBound : ∀ g, band g → (mis (edges s t) (allowed s t (cell s t g)))^power ≤
      base^(cell s t g).card) :
    (mis (edges s t) (allowed s t layers))^power ≤ base^(layers (H := H)).card := by
  classical
  have inductionStep (A : Finset (Ambient H)) (banded : ∀ x ∈ A, band x)
      (closed : ∀ x ∈ A, cell s t x ⊆ A) :
      (mis (edges s t) (allowed s t A))^power ≤ base^A.card := by
    induction A using Finset.strongInductionOn with
    | _ A ih =>
      by_cases empty : A = ∅
      · subst A
        have le : family (edges s t) (allowed s t ∅) ⊆ ({∅} : Finset (Finset (Ambient H))) := by
          intro I hi
          have h := (mem_family.mp hi).1
          simp [allowed] at h
          simpa using h
        simpa [mis] using Nat.pow_le_pow_left (card_le_card le) power
      obtain ⟨g,hg⟩ := nonempty_iff_ne_empty.mpr empty
      let B := cell s t g
      let D := A \ B
      have Bg : g ∈ B := mem_cell.mpr ⟨banded _ hg,refl_rel ..⟩
      have BA : B ⊆ A := closed g hg
      have Ds : D ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
        intro e
        have bad : g ∈ A \ B := by rw [e]; exact hg
        exact (mem_sdiff.mp bad).2 Bg
      have cd : ∀ x ∈ D, cell s t x ⊆ D := by
        intro x hx y hy
        refine mem_sdiff.mpr ⟨closed _ (mem_sdiff.mp hx).1 hy,fun yb => ?_⟩
        exact (mem_sdiff.mp hx).2 (mem_cell.mpr ⟨banded _ (mem_sdiff.mp hx).1,
          trans_rel (mem_cell.mp yb).2 (sym_rel (mem_cell.mp hy).2)⟩)
      have sep : ∀ x ∈ allowed s t B, ∀ y ∈ allowed s t D, ¬ edges s t x y := by
        intro x xh y yh e
        obtain ⟨yd,_⟩ := mem_allowed.mp yh
        exact (mem_sdiff.mp yd).2 (mem_cell.mpr ⟨banded _ (mem_sdiff.mp yd).1,
          trans_rel (mem_cell.mp (mem_allowed.mp xh).1).2 (edge_rel e)⟩)
      have dis : Disjoint (allowed s t B) (allowed s t D) := disjoint_left.mpr
        (fun _ hx hy => (mem_sdiff.mp (mem_allowed.mp hy).1).2 (mem_allowed.mp hx).1)
      have union : allowed s t A = allowed s t B ∪ allowed s t D := by
        ext x
        simp only [mem_allowed,mem_union,D,mem_sdiff]
        by_cases h : x ∈ B
        · simp [h,BA h]
        · simp [h]
      have count := disjoint_count (R := edges s t)
        (fun _ _ h => ⟨h.1.symm,raw_sym _ h.2⟩) _ _ dis sep
      have mul := Nat.mul_le_mul (localBound g (banded _ hg))
        (ih D Ds (fun _ hx => banded _ (mem_sdiff.mp hx).1) cd)
      rw [union,count,Nat.mul_pow]
      rw [← pow_add,Nat.add_comm,card_sdiff_add_card_eq_card BA] at mul
      exact mul
  exact inductionStep layers (fun _ hx => (mem_filter.mp hx).2)
    (fun _ _ _ hy => mem_filter.mpr ⟨mem_univ _,(mem_cell.mp hy).1⟩)

end Sumfree.Pair
