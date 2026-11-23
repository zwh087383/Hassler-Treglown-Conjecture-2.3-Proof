import Audit.CollisionData
import Audit.FinalTypes
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Pi.Basic

namespace Audit.Collisions
open Bipartite Stars Weights CollisionData Finset
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def separated (r : Relation) : Prop :=
  (0,1)∉r ∧ (0,3)∉r ∧ (0,4)∉r ∧ (1,3)∉r ∧ (1,4)∉r ∧ (3,4)∉r
instance (r : Relation) : Decidable (separated r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem top_checked : univ ∈ catalogue := by native_decide
theorem col_checked : ∀ a b c : Fin 5, eqRel (offsets a b c) ∈ catalogue := by native_decide
theorem row_intersection : ∀ i j, row i ∩ row j ∈ catalogue := by native_decide
theorem row_cases : ∀ j, separated (row j) →
    row j=eqRel (id : Fin 7 → Fin 7) ∨ ∃ i : Fin cases.length, row j=eqRel (cases.get i).slot := by native_decide
theorem intersection_checked : ∀ r ∈ catalogue, ∀ s ∈ catalogue, r∩s ∈ catalogue := by
  rintro r hr s hs
  obtain ⟨i,_,rfl⟩ := mem_image.mp hr
  obtain ⟨j,_,rfl⟩ := mem_image.mp hs
  exact row_intersection i j
theorem cases_checked : ∀ r ∈ catalogue, separated r →
    r=eqRel (id : Fin 7 → Fin 7) ∨ ∃ i : Fin cases.length, r=eqRel (cases.get i).slot := by
  rintro r hr
  obtain ⟨i,_,rfl⟩ := mem_image.mp hr
  exact row_cases i

abbrev Space (k : ℕ) := Fin k → Fin 5
theorem all_dimensions {k : ℕ} (u v w : Space k) : eqRel (offsets u v w) ∈ catalogue := by
  classical
  let agree (s : Finset (Fin k)) : Relation := univ.filter fun p =>
    ∀ i∈s, offsets (u i) (v i) (w i) p.1=offsets (u i) (v i) (w i) p.2
  have core (s : Finset (Fin k)) : agree s ∈ catalogue := by
    induction s using Finset.induction_on with
    | empty => simpa [agree] using top_checked
    | insert i s _ ih =>
      have eq : agree (insert i s) = eqRel (offsets (u i) (v i) (w i)) ∩ agree s := by
        ext p; simp [eqRel,agree]
      exact eq ▸ intersection_checked _ (col_checked ..) _ ih
  have eval (j : Fin 7) (i : Fin k) : offsets u v w j i = offsets (u i) (v i) (w i) j := by
    fin_cases j <;> rfl
  have eq : eqRel (offsets u v w) = agree univ := by
    ext p; simp [eqRel,agree,funext_iff,eval]
  rw [eq]; apply core

def denominator (c : Cert) (j : Fin 2) (s : State) : ℚ :=
  if j=0 then (c.extra s)⁻¹ else c.extra s * ∏ i, c.a i s
def weight (c : Cert) (z : Fin c.width → State) : ℚ :=
  (∏ i, c.a i (z i)) / ∏ j, denominator c j (rootB (z ∘ c.slot) j)
def total (c : Cert) := ∑ z, weight c z
def Valid (c : Cert) : Prop :=
  0<c.width ∧ (∀ j, c.slot (c.rep j)=j) ∧ (∀ i s, 0<c.a i s) ∧
  (∀ j s, 0<denominator c j s) ∧ (∀ s, (∏ i, c.a i s)=∏ j, denominator c j s) ∧
  0<total c ∧ total c<3^c.width
instance (c : Cert) : Decidable (Valid c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
theorem weights_checked : ∀ i : Fin cases.length, Valid (cases.get i) := by native_decide

theorem relation_iff {A B : Type*} [DecidableEq A] [DecidableEq B]
    {s : Fin 7 → A} {t : Fin 7 → B} (e : eqRel s=eqRel t) (i j : Fin 7) :
    s i=s j ↔ t i=t j := by simpa [eqRel] using (Finset.ext_iff.mp e (i,j))

theorem collision_bound {k : ℕ} (u v w : Space k) (c : Cert) (validated : Valid c)
    (pattern : eqRel (offsets u v w)=eqRel c.slot) :
    Sumfree.mis (adj (rule (bSeed u v w) bTag)) univ < 3^(Fintype.card (Space k)) := by
  classical
  obtain ⟨width,sectionEq,posA,posG,balanced,positive,small⟩ := validated
  let t (i : Fin c.width) := offsets u v w (c.rep i)
  have d : Function.Injective t := by
    intro i j e
    simpa only [sectionEq] using (relation_iff pattern _ _).mp e
  have same (i) : t (c.slot i) = offsets u v w i :=
    (relation_iff pattern _ _).mpr (sectionEq _)
  let r := rule (bSeed u v w) bTag
  let a (i : Fin c.width) (s : State) : ℝ := c.a i s
  let g (j : Fin 2) (s : State) : ℝ := denominator c j s
  have ha (i s) : 0<a i s := by dsimp [a]; exact_mod_cast posA i s
  have hg (j s) : 0<g j s := by dsimp [g]; exact_mod_cast posG j s
  have pw (z) : 0 < weight c z := div_pos (prod_pos fun i _ => posA ..) (prod_pos fun j _ => posG ..)
  rw [← card_graph]
  apply Entropy.below_target width Fintype.card_pos (Z := (total c : ℝ))
    (by exact_mod_cast positive) (by exact_mod_cast small)
  apply Entropy.translated_power width t d (@left _ _ r) (left_injective r)
    (fun z => (weight c z : ℝ)) _ (by exact_mod_cast positive)
  · intro z; exact_mod_cast (pw z).le
  · exact_mod_cast (le_refl (total c))
  · intro y b; exact_mod_cast pw _
  · intro y
    let centers (j : Fin 2) := if j=0 then y else y+u
    have per (s : State) : (∏ i, a i s)=∏ j, g j s := by dsimp [a,g]; exact_mod_cast balanced s
    have bound := balance (symmetric (bSeed u v w) bTag) (fun i => y+t i) centers a g ha hg per
    convert bound using 1
    apply sum_congr rfl; intro b _
    have pair := b_outputs u v w b y
    have er (j : Fin 2) : rootB ((fun i => left b (y+t i)) ∘ c.slot) j=right b (centers j) := by
      simp only [Function.comp_def,same]
      by_cases h : j=0
      · simpa [rootB,centers,h] using pair.1.symm
      · simpa [rootB,centers,h] using pair.2.symm
    simp [weight,a,g,er]

/-- For every dimension k and disjoint pairs P={0,u}, Q={v,w}.
    Distinctness of the four labels is the sole geometric hypothesis. -/
theorem type_B {k : ℕ} (u v w : Space k)
    (hu : u≠0) (hv : v≠0) (hw : w≠0) (huv : u≠v) (huw : u≠w) (hvw : v≠w) :
    Sumfree.mis (adj (rule (bSeed u v w) bTag)) univ < 3^(Fintype.card (Space k)) := by
  have sep : separated (eqRel (offsets u v w)) := by
    simp [separated,eqRel,offsets,hu,hv,hw,huv,huw,hvw]
  rcases cases_checked _ (all_dimensions u v w) sep with h|⟨i,hi⟩
  · apply FinalTypes.type_B_seven; intro p q e; exact (relation_iff h p q).mp e
  · exact collision_bound u v w (cases.get i) (weights_checked i) hi

end Audit.Collisions
