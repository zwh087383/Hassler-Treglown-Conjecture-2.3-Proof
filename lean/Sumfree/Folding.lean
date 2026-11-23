import Sumfree.Graph
import Mathlib.Data.Fin.Basic

namespace Sumfree
noncomputable section
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

def C5 (i j : Fin 5) := i+1 = j ∨ j+1 = i
instance : DecidableRel C5 := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
def five (R : V → V → Prop) (p q : Fin 5 × V) := C5 p.1 q.1 ∧ R p.2 q.2
def cover (R : V → V → Prop) (p q : Bool × V) := p.1 ≠ q.1 ∧ R p.2 q.2
def indeps (R : V → V → Prop) (s : Finset V) : Finset (Finset V) := by
  classical exact s.powerset.filter (Independent R)

def slice {T : Type*} [DecidableEq T] (I : Finset (T × V)) (i : T) : Finset V :=
  univ.filter fun v => (i,v) ∈ I
@[simp] theorem mem_slice {T : Type*} [DecidableEq T] (I : Finset (T × V)) (i : T) (v : V) :
    v ∈ slice I i ↔ (i,v) ∈ I := by simp [slice]

def polar (R : V → V → Prop) (A : Finset V) : Finset V := by
  classical exact univ.filter fun x => ∀ y ∈ A, ¬ R x y
@[simp] theorem mem_polar {R : V → V → Prop} {A : Finset V} {v : V} :
    v ∈ polar R A ↔ ∀ w ∈ A, ¬ R v w := by classical simp [polar]

def twoRows (A B : Finset V) : Finset (Bool × V) :=
  univ.filter fun p => if p.1 then p.2 ∈ B else p.2 ∈ A
@[simp] theorem mem_two_false (A B : Finset V) (x : V) : (false,x) ∈ twoRows A B ↔ x ∈ A := by simp [twoRows]
@[simp] theorem mem_two_true (A B : Finset V) (x : V) : (true,x) ∈ twoRows A B ↔ x ∈ B := by simp [twoRows]
theorem twoRows_inj {A B C D : Finset V} (h : twoRows A B = twoRows C D) : A = C ∧ B = D :=
  ⟨Finset.ext (fun x => by simpa using (Finset.ext_iff.mp h (false,x))),
   Finset.ext (fun x => by simpa using (Finset.ext_iff.mp h (true,x)))⟩

theorem two_ind {R : V → V → Prop} (sym : Symmetric R) {A B : Finset V}
    (no : ∀ x ∈ A, ∀ y ∈ B, ¬ R x y) : twoRows A B ∈ indeps (cover R) univ := by
  classical
  apply mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),?_⟩
  rintro ⟨c,x⟩ hx ⟨d,y⟩ hy ⟨ne,e⟩
  cases c <;> cases d <;> simp_all only [mem_two_false,mem_two_true,ne_eq,not_true_eq_false]
  exact no y hy x hx (sym e)

theorem two_max {R : V → V → Prop} {A B : Finset V}
    (a : A = polar R B) (b : B = polar R A) : IsMIS (cover R) univ (twoRows A B) := by
  apply isMIS_of_iff
  rintro ⟨c,x⟩
  cases c
  · simp only [mem_two_false, mem_univ,true_and, Prod.forall, Bool.forall_bool, cover,
      mem_two_true, ne_eq, not_true_eq_false, false_and, not_false_eq_true, implies_true,
      true_and, Bool.false_eq_true, and_true]
    simpa only [mem_polar] using (Finset.ext_iff.mp a x)
  · simp only [mem_two_true, mem_univ,true_and, Prod.forall, Bool.forall_bool, cover,
      mem_two_false, ne_eq, not_true_eq_false, false_and, not_false_eq_true, implies_true,
      true_and, Bool.true_eq_false, and_true]
    simpa only [mem_polar] using (Finset.ext_iff.mp b x)

theorem row_formula {R : V → V → Prop} {I : Finset (Fin 5 × V)} (h : IsMIS (five R) univ I)
    (i j k : Fin 5) (near : ∀ z, C5 i z ↔ z = j ∨ z = k) :
    slice I i = polar R (slice I j) ∩ polar R (slice I k) := by
  ext x
  rw [mem_slice,member_iff h,mem_inter,mem_polar,mem_polar]
  simp only [mem_univ,true_and]
  constructor
  · intro e
    exact ⟨fun y hy r => e (j,y) ((mem_slice ..).1 hy) ⟨(near _).2 (.inl rfl),r⟩,
      fun y hy r => e (k,y) ((mem_slice ..).1 hy) ⟨(near _).2 (.inr rfl),r⟩⟩
  · rintro ⟨ej,ek⟩ ⟨z,y⟩ hy ⟨cy,r⟩
    rcases (near _).1 cy with rfl | rfl
    · exact ej _ ((mem_slice ..).2 hy) r
    · exact ek _ ((mem_slice ..).2 hy) r

/-- The five-cycle folding inequality for every finite symmetric relation.
    The second factor is a maximal set in the full bipartite cover. -/
theorem folding {R : V → V → Prop} (sym : Symmetric R) :
    mis (five R) univ ≤ (indeps (cover R) univ).card * mis (cover R) univ := by
  classical
  let encode (I : Finset (Fin 5 × V)) := (twoRows (slice I 3) (slice I 4),
    twoRows (slice I 1) (polar R (slice I 1)))
  rw [← Finset.card_product]
  apply card_le_card_of_injOn encode
  · intro I hi
    have h := mem_family.mp hi
    have f0 := row_formula h 0 1 4 (by decide)
    have f1 := row_formula h 1 0 2 (by decide)
    have f2 := row_formula h 2 1 3 (by decide)
    apply mem_product.mpr
    constructor
    · exact two_ind sym fun x hx y hy e => h.2.1 (3,x) ((mem_slice ..).1 hx)
        (4,y) ((mem_slice ..).1 hy) ⟨by change C5 3 4; decide,e⟩
    · apply mem_family.mpr
      apply two_max _ rfl
      ext x
      constructor
      · intro hx
        exact mem_polar.mpr fun y hy r => (mem_polar.mp hy) x hx (sym r)
      · intro hx
        rw [f1,Finset.mem_inter]
        constructor
        · exact mem_polar.mpr fun y hy => mem_polar.mp hx y (Finset.mem_inter.mp (f0 ▸ hy)).1
        · exact mem_polar.mpr fun y hy => mem_polar.mp hx y (Finset.mem_inter.mp (f2 ▸ hy)).1
  · intro I hi J hj eq
    have a := twoRows_inj (congrArg Prod.fst eq)
    have b := (twoRows_inj (congrArg Prod.snd eq)).1
    change slice I 3 = slice J 3 ∧ slice I 4 = slice J 4 at a
    change slice I 1 = slice J 1 at b
    have agree (i j k : Fin 5) (near : ∀ z, C5 i z ↔ z = j ∨ z = k)
        (ej : slice I j = slice J j) (ek : slice I k = slice J k) : slice I i = slice J i := by
      rw [row_formula (mem_family.mp hi) i j k near,row_formula (mem_family.mp hj) i j k near,ej,ek]
    have allRows : ∀ i, slice I i = slice J i := by
      intro i
      have en : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
      rcases en with rfl | rfl | rfl | rfl | rfl
      · exact agree 0 1 4 (by decide) b a.2
      · exact b
      · exact agree 2 1 3 (by decide) b a.1
      · exact a.1
      · exact a.2
    ext ⟨i,x⟩
    simpa using Finset.ext_iff.mp (allRows i) x

end
end Sumfree
