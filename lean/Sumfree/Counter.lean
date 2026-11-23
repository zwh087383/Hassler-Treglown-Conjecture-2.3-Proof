import Sumfree.Graph
import Mathlib.Data.Fin.Tuple.Basic

namespace Sumfree.Counter
open Finset

/-- A literal stores a zero-based variable and the bit value making it true. -/
abbrev Lit := Nat × Bool
abbrev Formula := List (List Lit)

def readBit {n} (bits : Fin n → Bool) (i : Nat) : Bool :=
  if h : i < n then bits ⟨i,h⟩ else false

def sat (F : Formula) (read : Nat → Bool) : Bool :=
  F.all fun c => c.any fun l => read l.1 == l.2

def lower : Lit → Option Lit
  | (0,_) => none
  | (i+1,t) => some (i,t)

def assign (b : Bool) (F : Formula) : Formula :=
  F.filterMap fun c => if (0,b) ∈ c then none else some (c.filterMap lower)

theorem read_cons {n} (b : Bool) (v : Fin n → Bool) :
    readBit (Fin.cons b v) = fun i => match i with
      | 0 => b | j+1 => readBit v j := by
  funext i
  cases i with
  | zero => simp [readBit]
  | succ j =>
    by_cases h : j < n
    · simp only [readBit, h, Nat.succ_lt_succ h, dif_pos]
      change Fin.cons (α := fun _ => Bool) b v (Fin.succ ⟨j,h⟩) = _
      rw [Fin.cons_succ]
    · simp [readBit,h]

theorem sat_assign (F : Formula) (v : Nat → Bool) (b : Bool) :
    sat (assign b F) v = sat F (fun i => match i with | 0 => b | j+1 => v j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sat,List.all_eq_true,List.any_eq_true,beq_iff_eq,assign,List.mem_filterMap]
  constructor
  · intro h c hc
    by_cases hit : (0,b) ∈ c
    · exact ⟨(0,b),hit,rfl⟩
    obtain ⟨l,hl,good⟩ := h (c.filterMap lower) ⟨c,hc,by simp [hit]⟩
    obtain ⟨⟨i,t⟩,hi,eq⟩ := List.mem_filterMap.mp hl
    cases i with
    | zero => simp [lower] at eq
    | succ j =>
      simp [lower] at eq
      subst l
      exact ⟨(j+1,t),hi,good⟩
  · intro h d hd
    obtain ⟨c,hc,eq⟩ := hd
    split at eq
    · contradiction
    · rename_i hn
      simp only [Option.some.injEq] at eq
      subst d
      obtain ⟨⟨i,t⟩,hi,good⟩ := h c hc
      cases i with
      | zero =>
        change b = t at good
        subst t
        contradiction
      | succ j =>
        exact ⟨(j,t),List.mem_filterMap.mpr ⟨(j+1,t),hi,rfl⟩,good⟩

def solve : Nat → Formula → Nat
  | 0,F => if sat F (fun _ => false) then 1 else 0
  | n+1,F => if [] ∈ F then 0 else solve n (assign false F) + solve n (assign true F)

abbrev Models (n : Nat) (F : Formula) := { f : Fin n → Bool // sat F (readBit f) }

private def splitModels (F : Formula) (n : Nat) :
    Models (n+1) F ≃ (Models n (assign false F) ⊕ Models n (assign true F)) := by
  have consSat (b : Bool) (v : Fin n → Bool) :
      sat (assign b F) (readBit v) = sat F (readBit (Fin.cons b v)) := by rw [sat_assign, read_cons]
  have tailSat (v : Models (n+1) F) (b) (hv : v.val 0 = b) :
      sat (assign b F) (readBit (Fin.tail v.val)) := by
    subst b
    rw [consSat,Fin.cons_self_tail]
    exact v.property
  let forward (v : Models (n+1) F) : Models n (assign false F) ⊕ Models n (assign true F) :=
    if h : v.val 0 = true then Sum.inr ⟨Fin.tail v.val,tailSat v _ h⟩
    else Sum.inl ⟨Fin.tail v.val,tailSat v _ (Bool.eq_false_iff.mpr h)⟩
  let back : Models n (assign false F) ⊕ Models n (assign true F) → Models (n+1) F
    | .inl v => ⟨Fin.cons false v.val, by rw [← consSat]; exact v.property⟩
    | .inr v => ⟨Fin.cons true v.val, by rw [← consSat]; exact v.property⟩
  refine ⟨forward, back, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    cases h : v.val 0 <;> simp [forward,back,h] <;>
      simp only [← h,Fin.cons_self_tail]
  · intro v
    cases v <;> simp [forward,back,Fin.cons_zero,Fin.tail_cons]

/-- Correctness of exact model counting, for every formula and every number of bits. -/
theorem solve_correct (n : Nat) (F : Formula) : solve n F = Nat.card (Models n F) := by
  induction n generalizing F with
  | zero =>
    have rd (v : Fin 0 → Bool) : readBit v = fun _ => false := by funext i; simp [readBit]
    by_cases h : sat F (fun _ => false) = true
    · have u : Unique (Models 0 F) := ⟨⟨⟨Fin.elim0,by simpa [rd] using h⟩⟩,fun _ => Subsingleton.elim _ _⟩
      letI := u
      simp [solve,h]
    · have emp : IsEmpty (Models 0 F) := ⟨fun v => h (by simpa [rd] using v.property)⟩
      letI := emp
      simp [solve,h]
  | succ n ih =>
    by_cases dead : [] ∈ F
    · have emp : IsEmpty (Models (n+1) F) := ⟨fun v => by
        have no := (List.all_eq_true.mp v.property) [] dead
        simp at no⟩
      letI := emp
      simp [solve,dead]
    · rw [solve,if_neg dead,ih,ih,Nat.card_congr (splitModels F n),Nat.card_sum]

/-- Encode each forbidden edge and each required domination clause.
    Loops are represented separately by 'allowed', exactly as in the paper. -/
def graphFormula (n : Nat) (edge : Fin n → Fin n → Bool) (allowed : Fin n → Bool)
    (maximal : Bool := true) : Formula :=
  (List.finRange n).flatMap fun x =>
    let neighbors := (List.finRange n).filter (edge x)
    let conflicts := neighbors.map (fun y => [(x.val,false),(y.val,false)])
    if allowed x then
      if maximal then ([(x.val,true)] ++ neighbors.map (fun y => (y.val,true))) :: conflicts
      else conflicts
    else [[(x.val,false)]]

def selected {n} (f : Fin n → Bool) := univ.filter fun x => f x
def domain {n} (a : Fin n → Bool) := univ.filter fun x => a x

theorem graph_semantics {n} (edge : Fin n → Fin n → Bool) (a f : Fin n → Bool) (m : Bool) :
    sat (graphFormula n edge a m) (readBit f) ↔
    selected f ⊆ domain a ∧ Independent (fun x y => edge x y = true) (selected f) ∧
    (m = true → ∀ x ∈ domain a, x ∉ selected f → ∃ y ∈ selected f, edge x y = true) := by
  classical
  have bit (x : Fin n) : readBit f x.val = f x := by simp [readBit,x.isLt]
  have allin (x : Fin n) : x ∈ List.finRange n := List.mem_finRange x
  simp only [graphFormula,sat,List.all_eq_true,List.mem_flatMap,List.any_eq_true,
    selected,domain,Independent,mem_filter,mem_univ,true_and,beq_iff_eq]
  constructor
  · intro h
    have forbidden (x : Fin n) (ax : a x = false) : f x = false := by
      have := h [(x.val,false)] ⟨x,allin x,by simp [ax]⟩
      simpa [bit] using this
    have sub : ∀ x, f x = true → a x = true := by
      intro x hx
      cases ax : a x
      · simp [forbidden x ax] at hx
      · rfl
    refine ⟨fun x hx => by simpa using sub x (by simpa using hx), ?_, ?_⟩
    · intro x hx y hy e
      have ax := sub x hx
      have member : [(x.val,false),(y.val,false)] ∈
          ((List.finRange n).filter (edge x)).map (fun z => [(x.val,false),(z.val,false)]) :=
        List.mem_map.mpr ⟨y,by simp [allin,e],rfl⟩
      have := h [(x.val,false),(y.val,false)] ⟨x,allin x,by
        cases m <;> simp only [ax,if_true,Bool.false_eq_true,if_false,List.mem_cons] <;> tauto⟩
      simp [bit,hx,hy] at this
    · rintro rfl x ax fx
      have hy := h ([(x.val,true)] ++ ((List.finRange n).filter (edge x)).map (fun y => (y.val,true)))
        ⟨x,allin x,by simp [ax]⟩
      obtain ⟨l,hl,hit⟩ := hy
      rcases List.mem_append.mp hl with left | right
      · simp only [List.mem_singleton] at left
        subst l
        simp [bit,fx] at hit
      · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp right
        exact ⟨y,by simpa [bit] using hit,(List.mem_filter.mp hy).2⟩
  · rintro ⟨sub,ind,dom⟩ c ⟨x,_,hc⟩
    by_cases ax : a x = true
    · simp only [ax,if_true] at hc
      have conflicts (h : c ∈ ((List.finRange n).filter (edge x)).map
          (fun y => [(x.val,false),(y.val,false)])) :
          ∃ l ∈ c, readBit f l.1 = l.2 := by
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
        have e := (List.mem_filter.mp hy).2
        cases fx : f x
        · exact ⟨(x.val,false),by simp,by simpa [bit] using fx⟩
        · have fy : f y = false := by
            cases hy' : f y
            · rfl
            · exact False.elim (ind _ fx _ hy' e)
          exact ⟨(y.val,false),by simp,by simpa [bit] using fy⟩
      cases m with
      | false => exact conflicts hc
      | true =>
        rcases List.mem_cons.mp hc with rfl | rest
        · by_cases fx : f x = true
          · exact ⟨(x.val,true),by simp,by simpa [bit] using fx⟩
          · obtain ⟨y,fy,e⟩ := dom rfl _ ax fx
            exact ⟨(y.val,true),List.mem_append_right _ (List.mem_map.mpr
              ⟨y,List.mem_filter.mpr ⟨allin y,e⟩,rfl⟩),by simpa [bit] using fy⟩
        · exact conflicts rest
    · simp [ax] at hc
      subst c
      have fx : f x = false := by
        cases hx : f x
        · rfl
        · exact False.elim (ax (by have h := sub (a := x) (by simp [hx]); simpa using h))
      exact ⟨(x.val,false),by simp,by simpa [bit] using fx⟩

noncomputable section

def graphSets {n} (edge : Fin n → Fin n → Bool) (a : Fin n → Bool) (m : Bool) := by
  classical exact (domain a).powerset.filter fun I =>
    Independent (fun x y => edge x y = true) I ∧
    (m = true → ∀ x ∈ domain a, x ∉ I → ∃ y ∈ I, edge x y = true)

theorem solve_graph (n : Nat) (e : Fin n → Fin n → Bool) (a : Fin n → Bool) (m : Bool) :
    solve n (graphFormula n e a m) = (graphSets e a m).card := by
  classical
  have spec (f : Fin n → Bool) :
      sat (graphFormula n e a m) (readBit f) ↔ selected f ∈ graphSets e a m := by
    simpa only [graphSets,mem_filter,mem_powerset] using graph_semantics e a f m
  let bits (I : Finset (Fin n)) := fun x => decide (x ∈ I)
  have recover (I : Finset (Fin n)) : selected (bits I) = I := by ext x; simp [selected,bits]
  let eq : Models n (graphFormula n e a m) ≃ ↥(graphSets e a m) := {
    toFun := fun v => ⟨selected v.val,(spec _).1 v.property⟩
    invFun := fun I => ⟨bits I.val,(spec _).2 (by rw [recover]; exact I.property)⟩
    left_inv := fun v => Subtype.ext (funext (fun x => by simp [bits,selected]))
    right_inv := fun I => Subtype.ext (recover I.val)
  }
  rw [solve_correct,Nat.card_congr eq,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem solve_mis (n : Nat) (e : Fin n → Fin n → Bool) (a : Fin n → Bool) :
    solve n (graphFormula n e a true) = mis (fun x y => e x y = true) (domain a) := by
  classical
  rw [solve_graph]
  apply congrArg Finset.card
  ext I
  simp [graphSets,IsMIS, and_assoc]

end
end Sumfree.Counter
