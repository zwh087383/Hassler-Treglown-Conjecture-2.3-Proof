import Audit.Link
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace Audit.PlaneCert
open Finset

abbrev P := Fin 25
def point (i : P) : Fin 5 × Fin 5 := (⟨i.val%5,Nat.mod_lt _ (by decide)⟩,⟨i.val/5,by omega⟩)
def index (p : Fin 5 × Fin 5) : P := ⟨p.1.val+5*p.2.val,by have := p.1.isLt; have := p.2.isLt; omega⟩
theorem point_index (p : Fin 5 × Fin 5) : point (index p)=p := by revert p; decide
theorem index_point (i : P) : index (point i)=i := by revert i; decide
def line (b : Fin 5) (i : P) : Bool :=
  let (x,y) := point i
  decide (x+b*y=1 ∨ x+b*y=4)
def obstruction (l : Finset P) (i j : P) : Prop :=
  index (point i+point j)∈l ∨ index (point i-point j)∈l ∨ index (point j-point i)∈l
instance (l : Finset P) (i j : P) : Decidable (obstruction l i j) := by unfold obstruction; infer_instance

inductive Tree
  | line (slope : Fin 5)
  | weight (m : ℕ) (pairs : List (P × P)) (singles : List P)
  | split (i : P) (absent present : Tree)

def labels (e : List (P × P)) : List P := e.flatMap fun p => [p.1,p.2]
def balanced (lo hi : Finset P) (m : ℕ) (pairs : List (P × P)) (singles : List P) : Prop :=
  (∀ p∈pairs,obstruction lo p.1 p.2) ∧
  (∀ i : P, (labels pairs ++ singles).count i =
      (if i∈hi then 2 else 0) + (if i=1 ∨ i=4 then 2*m else 0)) ∧
  pairs.length+singles.length ≤ 15+3*m
instance (lo hi : Finset P) (m : ℕ) (p : List (P × P)) (s : List P) :
    Decidable (balanced lo hi m p s) := by unfold balanced; infer_instance
def verify (lo hi : Finset P) : Tree → Bool
  | .line b => decide (∀ i∈hi,line b i=true)
  | .weight m e s => decide (balanced lo hi m e s)
  | .split i left right => verify lo (hi.erase i) left && verify (insert i lo) hi right

private theorem listWeights (w : P → ℕ) (s : List P) :
    (s.map w).sum = ∑ i : P,s.count i*w i := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih,List.count_cons]
    simp_rw [add_mul]
    rw [sum_add_distrib]
    simp [add_comm]

private theorem pairWeights (w : P → ℕ) {lo : Finset P} (q : ℕ)
    (restr : ∀ i j, obstruction lo i j → w i+w j≤q)
    (pairs : List (P × P)) (valid : ∀ p∈pairs,obstruction lo p.1 p.2) :
    ((labels pairs).map w).sum ≤ pairs.length*q := by
  induction pairs with
  | nil => simp [labels]
  | cons p ps ih =>
    have a := restr p.1 p.2 (valid _ (List.mem_cons_self ..))
    have b := ih (fun t h => valid _ (List.mem_cons_of_mem _ h))
    simp only [labels,List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,
      List.sum_cons,List.length_cons,Nat.succ_mul] at *
    omega

structure Weights (w : P → ℕ) (q : ℕ) : Prop where
  cap : ∀ i,w i≤q
  pairs : ∀ i j, obstruction (univ.filter fun z => 0<w z) i j → w i+w j≤q
  dense : 15*q < 2*∑ i : P,w i
  axis : 3*q < 2*(w 1+w 4)

theorem sound (w : P → ℕ) (q : ℕ) (h : Weights w q) (t : Tree) (lo hi : Finset P)
    (known : ∀ i∈lo,0<w i) (bounded : ∀ i,0<w i → i∈hi) (check : verify lo hi t=true) :
    ∃ b : Fin 5, ∀ i,0<w i → line b i=true := by
  induction t generalizing lo hi with
  | line b =>
    exact ⟨b,fun i pos => of_decide_eq_true check i (bounded i pos)⟩
  | split i left right il ir =>
    have both : verify lo (hi.erase i) left=true ∧ verify (insert i lo) hi right=true := by
      simpa [verify] using check
    obtain ⟨okL,okR⟩ := both
    by_cases pos : 0<w i
    · apply ir (insert i lo) hi _ bounded okR
      intro j hj; rcases mem_insert.mp hj with rfl|hj
      · exact pos
      · exact known _ hj
    · apply il lo (hi.erase i) known _ okL
      intro j hj; exact mem_erase.mpr ⟨fun e => pos (e ▸ hj),bounded _ hj⟩
  | weight m p s =>
    obtain ⟨ob,cnt,cost⟩ := of_decide_eq_true check
    have restrict (i j : P) (ho : obstruction lo i j) : w i+w j≤q := by
      apply h.pairs
      rcases ho with v|v|v
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _,known _ v⟩)
      · exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ _,known _ v⟩))
      · exact Or.inr (Or.inr (mem_filter.mpr ⟨mem_univ _,known _ v⟩))
    have pairCost := pairWeights w q restrict p ob
    have singletonCost : (s.map w).sum≤s.length*q := by
      clear * - h
      induction s with
      | nil => simp
      | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]; linarith [h.cap x]
    have total : (((labels p ++ s).map w).sum) ≤ (15+3*m)*q := by
      rw [List.map_append,List.sum_append]
      exact (Nat.add_le_add pairCost singletonCost).trans (by rw [←Nat.add_mul]; exact Nat.mul_le_mul_right _ cost)
    have site (i : P) : (if i∈hi then 2 else 0)*w i=2*w i := by
      by_cases b : i∈hi
      · simp [b]
      · have zero : w i=0 := Nat.eq_zero_of_not_pos (fun hp => b (bounded _ hp)); simp [zero]
    rw [listWeights] at total
    simp_rw [cnt,add_mul,site] at total
    rw [sum_add_distrib,←mul_sum] at total
    have axis : (∑ i : P, (if i=1 ∨ i=4 then 2*m else 0)*w i) = (2*m)*(w 1+w 4) := by
      have term (i : P) : (if i=1 ∨ i=4 then 2*m else 0)*w i =
          (if i=1 then 2*m*w i else 0)+(if i=4 then 2*m*w i else 0) := by
        by_cases a : i=1 <;> by_cases b : i=4 <;> simp_all
      simp_rw [term]; rw [sum_add_distrib]; simp [mul_add]
    rw [axis] at total
    exfalso
    nlinarith only [total,h.dense,Nat.mul_le_mul_left m h.axis.le]

end Audit.PlaneCert
