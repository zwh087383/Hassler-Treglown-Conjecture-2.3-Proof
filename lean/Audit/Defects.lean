import Audit.DefectsNonzero

namespace Audit.Defects
open Finset Sumfree Blocks Link Lower Generic Band
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K] [Module Field5 K]

def along (a : K) (x y : Index K) := tail y - tail x=(a,0)

private theorem cycle_code (B F G ne : Prop) [Decidable F] [Decidable G] (x y : Bool)
    (apart : F → G → False) (blueNe : B → ne) (redNe : F ∨ G → ne) :
    (ne ∧ (((F ∧ (x≠false ∨ y≠true)) ∨ (G ∧ (x≠true ∨ y≠false))) ∨ B)) ↔
        B ∨ ((F ∨ G) ∧ (x≠decide G ∨ y≠decide F)) := by
  by_cases f : F <;> by_cases g : G <;> simp_all <;> tauto

/-- All symmetric backgrounds with one unpaired element in the zero layer. -/
theorem zero_layer (T : Finset (Pt K)) (stable : ∀ x,x∈T ↔ -x∈T) (zero : 0∉T)
    (a : K) (nonzero : a≠0) : rankCount (insert (0,a) T) ≤ 3^(Fintype.card K) := by
  let red (x y : Index K) := along a x y ∨ along a y x
  let color (x y : Index K) := decide (along a y x)
  have forward {x y : Index K} (h : along a x y) : y.1-x.1=a := congrArg Prod.fst h
  have separate {x y : Index K} (f : along a x y) (b : along a y x) : False := by
    have sum : a+a=0 := by
      calc
        _ = (y.1-x.1)+(x.1-y.1) := congrArg₂ (·+·) (forward f).symm (forward b).symm
        _ = 0 := by abel
    have sm : (2:Field5) • a=0 := (two_smul _ _).trans sum
    exact (by decide : (2:Field5)≠0) ((smul_eq_zero.mp sm).resolve_right nonzero)
  have rs : Symmetric red := fun _ _ h => h.symm
  have ri : Irreflexive red := by
    intro x h
    have h' : along a x x := h.elim id id
    exact separate h' h'
  have signed {x y : Index K} (xy : red x y) :
      ∃ p : Field5, (p=1 ∨ p= -1) ∧ p • a = y.1-x.1 := by
    rcases xy with f|b
    · exact ⟨1,Or.inl rfl,by rw [one_smul,forward f]⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      rw [neg_one_smul,←forward b,neg_sub]
  have tf : TriangleFree red := by
    intro x y z xy yz xz
    obtain ⟨p,ps,px⟩ := signed xy
    obtain ⟨q,qs,qx⟩ := signed yz
    obtain ⟨r,rs,rx⟩ := signed xz
    have no : ∀ p q r : Field5, (p=1 ∨ p= -1) → (q=1 ∨ q= -1) → (r=1 ∨ r= -1) →
        p+q-r≠0 := by decide
    have sm : (p+q-r) • a=0 := by rw [sub_smul,add_smul,px,qx,rx]; abel
    exact no _ _ _ ps qs rs ((smul_eq_zero.mp sm).resolve_right nonzero)
  refine count_of_lift _ (background T) red color (bg_sym T) rs (bg_irr T zero) ri tf ?_ ?_
  · intro x y z xy xz eq
    have same : along a y x ↔ along a z x := by simpa only [color,decide_eq_decide] using eq
    apply tail_injective
    by_cases back : along a y x
    · have h : tail x-tail y=tail x-tail z := back.trans (same.mp back).symm
      exact sub_right_inj.mp h
    · have fy := xy.resolve_right back
      have fz := xz.resolve_right (fun h => back (same.mpr h))
      exact sub_left_inj.mp (fy.trans fz.symm)
  · intro v w
    rw [edge_raw,insert_atom (0,a) T v w,bg_raw T stable v w,zero_formula,lifted]
    have blueNe (h : background T v.1 w.1) : v≠w := fun e => bg_irr T zero _ (e ▸ h)
    have redNe (h : red v.1 w.1) : v≠w := fun e => ri _ (e ▸ h)
    exact cycle_code _ (along a v.1 w.1) (along a w.1 v.1) _ v.2 w.2 separate blueNe redNe

/-- A single unpaired element can be in any external layer. -/
theorem one_defect (T : Finset (Pt K)) (stable : ∀ x,x∈T ↔ -x∈T) (z : Pt K)
    (free : Free (insert z T)) (outside : Disjoint (insert z T) (full K)) :
    rankCount (insert z T) ≤ 3^(Fintype.card K) := by
  have zero : 0∉T := fun h => free 0 (mem_insert_of_mem h) 0 (mem_insert_of_mem h)
    0 (mem_insert_of_mem h) (zero_add _)
  obtain ⟨j,u⟩ := z
  have notBand := disjoint_left.mp outside (mem_insert_self _ _)
  have options : ∀ j : Fin 5, ¬(j=2 ∨ j=3) → j=0 ∨ j=1 ∨ j=4 := by decide
  rcases options j (fun h => notBand ((mem_full (u:=(j,u))).mpr h)) with rfl|rfl|rfl
  · apply zero_layer T stable zero u
    intro e; subst u
    have h : 0∈insert ((0,0):Pt K) T := mem_insert_self _ _
    exact free 0 h 0 h 0 h (zero_add _)
  · exact nonzero T stable zero true false u 0 (by simp)
  · exact nonzero T stable zero false true 0 u (by simp)

end
end Audit.Defects
