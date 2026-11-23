import Sumfree.Graph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

namespace Audit.Bipartite
set_option linter.unusedSectionVars false
open Finset
abbrev State := Fin 4
def bit (s : State) (i : Bool) : Bool :=
  if i then decide (2 ≤ s.val) else s.val % 2 == 1
def pack (a b : Bool) : State := if a then (if b then 3 else 1) else (if b then 2 else 0)
theorem bit_pack : ∀ a b i, bit (pack a b) i = (if i then b else a) := by decide
theorem state_ext : ∀ {a b : State}, (∀ i, bit a i = bit b i) → a=b := by decide

variable {K : Type*} [AddCommGroup K]
abbrev Rule (K : Type*) := K → Bool → Bool → Prop
abbrev Board (K : Type*) := (K → State) × (K → State)
abbrev Vertex (K : Type*) := Bool × K × Bool

/-- The right bit order is D,C and the left bit order is A,B. -/
def adj (r : Rule K) (u v : Vertex K) : Prop :=
  match u.1,v.1 with
  | false,true => r (v.2.1-u.2.1) u.2.2 v.2.2
  | true,false => r (u.2.1-v.2.1) v.2.2 u.2.2
  | _,_ => False

def Closed (r : Rule K) (b : Board K) : Prop :=
  (∀ x i, bit (b.1 x) i = true ↔
    ∀ y j, bit (b.2 y) j = true → ¬r (y-x) i j) ∧
  (∀ y j, bit (b.2 y) j = true ↔
    ∀ x i, bit (b.1 x) i = true → ¬r (y-x) i j)
abbrev Sample (r : Rule K) := {b : Board K // Closed r b}
variable [Fintype K] [DecidableEq K]
noncomputable instance (r : Rule K) : Fintype (Sample r) := Fintype.ofFinite _

def read (s : Finset (Vertex K)) (side : Bool) (x : K) : State :=
  pack (decide ((side,x,false) ∈ s)) (decide ((side,x,true) ∈ s))
@[simp] theorem bit_read (s : Finset (Vertex K)) (side : Bool) (x : K) (i : Bool) :
    bit (read s side x) i = true ↔ (side,x,i) ∈ s := by cases i <;> simp [read,bit_pack]

theorem closed_iff (r : Rule K) (s : Finset (Vertex K)) :
    Closed r (read s false,read s true) ↔ Sumfree.IsMIS (adj r) univ s := by
  constructor
  · intro h
    apply Sumfree.isMIS_of_iff
    rintro ⟨c,x,i⟩
    cases c
    · simpa [Prod.forall,Bool.forall_bool,adj] using h.1 x i
    · simpa [Prod.forall,Bool.forall_bool,adj] using h.2 x i
  · intro h
    constructor
    · intro x i
      simpa [Prod.forall,Bool.forall_bool,adj] using Sumfree.member_iff h (false,x,i)
    · intro x i
      simpa [Prod.forall,Bool.forall_bool,adj] using Sumfree.member_iff h (true,x,i)

def chosen (b : Board K) : Finset (Vertex K) :=
  univ.filter fun v => bit ((if v.1 then b.2 else b.1) v.2.1) v.2.2

theorem read_chosen (b : Board K) (c : Bool) : read (chosen b) c = (if c then b.2 else b.1) := by
  funext x
  apply state_ext
  intro i
  apply Bool.eq_iff_iff.mpr
  simp [chosen]

theorem card_graph (r : Rule K) :
    Fintype.card (Sample r) = Sumfree.mis (adj r) univ := by
  classical
  let e : Sample r ≃ ↥(Sumfree.family (adj r) univ) := {
    toFun b := ⟨chosen b.1,Sumfree.mem_family.mpr ((closed_iff r _).mp (by
      simp only [read_chosen,Bool.false_eq_true,if_false,if_true,Prod.mk.eta]; exact b.2))⟩
    invFun s := ⟨(read s.1 false,read s.1 true),(closed_iff r _).mpr (Sumfree.mem_family.mp s.2)⟩
    left_inv b := Subtype.ext (by simp [read_chosen])
    right_inv s := Subtype.ext (by ext ⟨c,x,i⟩; cases c <;> simp [chosen]) }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

abbrev left {r : Rule K} (b : Sample r) := b.val.1
abbrev right {r : Rule K} (b : Sample r) := b.val.2
theorem left_injective (r : Rule K) : Function.Injective (@left K _ r) := by
  intro b c eq
  apply Subtype.ext; apply Prod.ext eq
  funext y; apply state_ext; intro j
  apply Bool.eq_iff_iff.mpr
  rw [b.2.2,c.2.2]
  change (∀ x i, bit (left b x) i = true → _) ↔ (∀ x i, bit (left c x) i = true → _)
  rw [eq]

def reflect (t : K) (b : Board K) : Board K := (fun x => b.2 (t-x), fun y => b.1 (t-y))

theorem reflect_closed {r : Rule K} (symm : ∀ a i j, r a i j ↔ r a j i)
    (t : K) {b : Board K} (h : Closed r b) : Closed r (reflect t b) := by
  have invol (x : K) : t-(t-x)=x := by abel
  have diff (x y : K) : (t-x)-(t-y)=y-x := by abel
  have transport (f : K → Bool → Prop) (g : K → Bool → Prop) :
      (∀ x i, f x i ↔ g (t-x) i) → ((∀ x i, f x i) ↔ ∀ x i, g x i) := by
    intro e; constructor
    · intro hf x i; simpa only [invol] using (e (t-x) i).mp (hf _ _)
    · intro hg x i; exact (e x i).mpr (hg _ _)
  constructor
  · intro x i
    change (bit (b.2 (t-x)) i = true) ↔ _
    rw [h.2]
    apply transport
    intro y j
    simp only [reflect,invol,sub_sub_cancel_left,diff]
    rw [symm _ j i]
    have e : (t-x)-y=(t-y)-x := by abel
    rw [e]
  · intro y j
    change (bit (b.1 (t-y)) j = true) ↔ _
    rw [h.1]
    apply transport
    intro x i
    simp only [reflect,invol,diff]
    rw [symm _ j i]
    have e : x-(t-y)=y-(t-x) := by abel
    rw [e]

def exchange {r : Rule K} (symm : ∀ a i j, r a i j ↔ r a j i) (t : K) :
    Sample r ≃ Sample r where
  toFun b := ⟨reflect t b.val,reflect_closed symm t b.property⟩
  invFun b := ⟨reflect t b.val,reflect_closed symm t b.property⟩
  left_inv b := Subtype.ext (by dsimp [reflect]; simp)
  right_inv b := Subtype.ext (by dsimp [reflect]; simp)

theorem marginal {r : Rule K} (symm : ∀ a i j, r a i j ↔ r a j i)
    (x y : K) (w : State → ℝ) : ∑ b : Sample r, w (left b x) = ∑ b : Sample r, w (right b y) := by
  have h := (exchange symm (y+x)).sum_comp (fun b => w (left b x))
  simpa [exchange,reflect,left,right] using h.symm

end Audit.Bipartite
