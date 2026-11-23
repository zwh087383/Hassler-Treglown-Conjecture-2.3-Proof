import Audit.Bipartite
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Audit.Stars
open Bipartite Finset
set_option linter.unusedSectionVars false

inductive Color | p | q | common deriving DecidableEq, Repr
def permits (tag : Color) (i j : Bool) : Bool :=
  match tag with
  | .p => i || j
  | .q => !(i && j)
  | .common => true

def rule {K : Type*} {d : ℕ} (t : Fin d → K) (tags : Fin d → Color) : Rule K :=
  fun a i j => ∃ k, t k=a ∧ permits (tags k) i j=true

theorem symmetric {K : Type*} {d : ℕ} (t : Fin d → K) (tags : Fin d → Color) (a i j) :
    rule t tags a i j ↔ rule t tags a j i := by
  have h (tag : Color) : permits tag i j = permits tag j i := by
    cases tag <;> cases i <;> cases j <;> rfl
  simp only [rule,h]

def out {d : ℕ} (tags : Fin d → Color) (z : Fin d → State) : State :=
  let available (j : Bool) := decide (∀ k i, bit (z k) i = true → permits (tags k) i j ≠ true)
  pack (available false) (available true)

theorem bit_out {d : ℕ} (tags : Fin d → Color) (z : Fin d → State) (j : Bool) :
    bit (out tags z) j = true ↔ ∀ k i, bit (z k) i = true → permits (tags k) i j ≠ true := by
  cases j <;> simp [out,bit_pack]

variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]
theorem star {d : ℕ} (t : Fin d → K) (tags : Fin d → Color)
    (b : Sample (rule t tags)) (y : K) :
    right b y = out tags (fun i => left b (y-t i)) := by
  apply state_ext; intro j; apply Bool.eq_iff_iff.mpr
  rw [bit_out,b.2.2 y j]
  constructor
  · intro h k i sel perm
    exact h (y-t k) i sel ⟨k,by abel,perm⟩
  · rintro h x i sel ⟨k,eq,perm⟩
    have pos : y-t k=x := by rw [eq]; abel
    exact h k i (pos.symm ▸ sel) perm

def acTag (common : Bool) (i : Fin 4) : Color :=
  if i=3 then .q else if common && i==0 then .common else .p
def good (z : Fin 4 → State) : Prop := z 3=2 → ∀ k, k≠3 → z k=0
instance (z : Fin 4 → State) : Decidable (good z) := inferInstanceAs (Decidable (_ → ∀ _, _ → _))

theorem ac_support (c : Bool) (t : Fin 4 → K) (b : Sample (rule t (acTag c))) (y : K) :
    good (fun i => left b (y-t i)) := by
  classical
  let x := y-t 3
  intro s2
  change left b x = 2 at s2
  have selB : bit (left b x) true=true := by rw [s2]; decide
  have noA : bit (left b x) false ≠ true := by rw [s2]; decide
  have missing : ¬ ∀ v j, bit (right b v) j = true → ¬rule t (acTag c) (v-x) false j :=
    fun h => noA ((b.2.1 x false).mpr h)
  push_neg at missing
  obtain ⟨v,j,sel,k,eq,perm⟩ := missing
  have excl : permits (acTag c k) true j ≠ true :=
    fun h => (b.2.2 v j).mp sel x true selB ⟨k,eq,h⟩
  have uniqueQ : ∀ c k j, permits (acTag c k) false j=true →
      permits (acTag c k) true j≠true → k=3 ∧ j=true := by decide
  obtain ⟨rfl,rfl⟩ := uniqueQ c k j perm excl
  have pos : v=y := by have a := (eq_sub_iff_add_eq.mp eq).symm; simpa [x] using a
  subst v
  have hits : ∀ c k i, k≠3 → permits (acTag c k) i true=true := by decide
  have empty : ∀ s : State, (∀ i, bit s i ≠ true) → s=0 := by decide
  intro k hk
  apply empty; intro i hi
  exact (b.2.2 y true).mp sel (y-t k) i hi ⟨k,by abel,hits c k i hk⟩

def bTag (i : Fin 4) : Color := if i.val<2 then .p else .q
def four {V : Type*} (a b c d : V) (i : Fin 4) := (![a,b,c,d] : Fin 4 → V) i
def first (z : Fin 7 → State) := four (z 0) (z 1) (z 3) (z 4)
def second (z : Fin 7 → State) := four (z 2) (z 0) (z 5) (z 6)
def offsets (u v w : K) : Fin 7 → K := ![0,-u,u,-v,-w,u-v,u-w]
def bSeed (u v w : K) := four 0 u v w

theorem b_outputs (u v w : K) (b : Sample (rule (bSeed u v w) bTag)) (y : K) :
    let z := fun i => left b (y+offsets u v w i)
    right b y = out bTag (first z) ∧ right b (y+u) = out bTag (second z) := by
  dsimp only
  constructor
  · rw [star]; congr 1; funext i; fin_cases i <;> simp [bSeed,first,four,offsets,sub_eq_add_neg]
  · rw [star]; congr 1; funext i; fin_cases i <;>
      simp [bSeed,second,four,offsets,sub_eq_add_neg,add_assoc]

end Audit.Stars
