import Audit.DefectsGeometry
import Audit.DefectsSupport
import Audit.ColoredBound

namespace Audit.Defects
open Finset Sumfree Lower Generic Band
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

theorem count_of_lift (s : Finset (Pt K)) (blue red : Index K → Index K → Prop)
    (color : Index K → Index K → Bool) (bs : Symmetric blue) (rs : Symmetric red)
    (bi : Irreflexive blue) (ri : Irreflexive red) (tf : TriangleFree red)
    (unique : ∀ x y z,red x y → red x z → color x y=color x z → y=z)
    (model : ∀ p q,projected s p q ↔ lifted blue red color p q) :
    rankCount s ≤ 3^(Fintype.card K) := by
  rw [raw_count, Sumfree.count_congr (s:=univ) (fun p _ q _ => model p q)]
  apply (support_injection blue red color unique).trans
  have b := Colored.bound blue red bs rs bi ri tf univ
  have scale : ((univ : Finset (Index K)).card:ℝ)/2=Fintype.card K := by
    simp [Index]
  rw [scale,Real.rpow_natCast] at b
  exact_mod_cast b

def matching (k : K) (x y : Index K) := tail x+tail y=(k,0)

private theorem match_sym (k : K) : Symmetric (matching k) := fun _ _ h => (add_comm ..).trans h

private theorem match_unique {k : K} {x y z : Index K} (xy : matching k x y)
    (xz : matching k x z) : y=z := tail_injective (add_left_cancel (xy.trans xz.symm))

private theorem opposite {k : K} {x y : Index K} (h : matching k x y) : x.2≠y.2 := by
  have z : residualSign x.2 + residualSign y.2=0 := congrArg Prod.snd h
  intro e
  rw [e] at z
  cases t : y.2 <;> rw [t] at z <;> exact (by decide : residualSign _+residualSign _≠0) z

def signedSeed (T : Finset (Pt K)) (p q : Bool) (b c : K) :=
  let U := if q then insert (4,c) T else T
  if p then insert (1,b) U else U

private theorem signed_raw (T : Finset (Pt K)) (stable : ∀ x,x∈T ↔ -x∈T)
    (p q : Bool) (b c : K) (v w : Index K × Bool) :
    raw (↑(plane (signedSeed T p q b c)) : Set (Raw.Point K)) (place v) (place w) ↔
      background T v.1 w.1 ∨
      (p=true ∧ matching (-b) v.1 w.1 ∧ (v.2≠false ∨ w.2≠false)) ∨
      (q=true ∧ matching c v.1 w.1 ∧ (v.2≠true ∨ w.2≠true)) := by
  cases p <;> cases q <;> simp only [signedSeed,if_true,Bool.false_eq_true,if_false,true_and,false_and]
  · simpa only [or_false,false_or] using (bg_raw T stable v w)
  · rw [insert_atom (4,c) T v w,bg_raw T stable v w,four_formula]; tauto
  · rw [insert_atom (1,b) T v w,bg_raw T stable v w,one_formula]
    simp only [matching,Prod.neg_mk,neg_zero]; tauto
  · rw [insert_atom (1,b) (insert (4,c) T) v w,insert_atom (4,c) T v w,bg_raw T stable v w,
        one_formula,four_formula]
    simp only [matching,Prod.neg_mk,neg_zero]; tauto

private theorem code_rule (B F G ne : Prop) [Decidable G] (a d : Bool)
    (apart : F → G → False) (blueNe : B → ne) (redNe : F ∨ G → ne) :
    (ne ∧ (B ∨ (F ∧ (a≠false ∨ d≠false)) ∨ (G ∧ (a≠true ∨ d≠true)))) ↔
      B ∨ ((F ∨ G) ∧ (a≠decide G ∨ d≠decide G)) := by
  by_cases f : F <;> by_cases g : G <;> simp_all

/-- A symmetric background and one or two unpaired seeds in the nonzero external layers. -/
theorem nonzero (T : Finset (Pt K)) (stable : ∀ x,x∈T ↔ -x∈T) (zero : 0∉T)
    (p q : Bool) (b c : K) (distinct : p=true → q=true → c≠-b) :
    rankCount (signedSeed T p q b c) ≤ 3^(Fintype.card K) := by
  let first (x y : Index K) := p=true ∧ matching (-b) x y
  let second (x y : Index K) := q=true ∧ matching c x y
  let red (x y : Index K) := first x y ∨ second x y
  let color (x y : Index K) := decide (second x y)
  have exclude (x y : Index K) (a : first x y) (b' : second x y) : False := by
    have eq : (c,(0:Fin 5))= (-b,0) := b'.2.symm.trans a.2
    exact distinct a.1 b'.1 (congrArg Prod.fst eq)
  have second_sym (x y : Index K) : second x y ↔ second y x :=
    and_congr_right (fun _ => ⟨fun h => match_sym c h,fun h => match_sym c h⟩)
  have rs : Symmetric red := fun _ _ h => h.elim
    (fun h => Or.inl ⟨h.1,match_sym _ h.2⟩) (fun h => Or.inr ((second_sym ..).mp h))
  have split {x y : Index K} (h : red x y) : x.2≠y.2 := h.elim (fun a => opposite a.2) (fun a => opposite a.2)
  have ri : Irreflexive red := fun _ h => split h rfl
  have tf : TriangleFree red := by
    intro x y z xy yz xz
    exact (show ∀ a b c : Bool,a≠b → b≠c → a≠c → False by decide) _ _ _ (split xy) (split yz) (split xz)
  refine count_of_lift _ (background T) red color (bg_sym T) rs (bg_irr T zero) ri tf ?_ ?_
  · intro x y z xy xz cc
    have same : second x y ↔ second x z := by simpa only [color,decide_eq_decide] using cc
    by_cases hit : second x y
    · exact match_unique hit.2 ((same.mp hit).2)
    · exact match_unique ((xy.resolve_right hit).2) ((xz.resolve_right (fun h => hit (same.mpr h))).2)
  · intro v w
    have flip : color w.1 v.1 = color v.1 w.1 := by
      simp only [color,decide_eq_decide]; exact second_sym _ _
    rw [edge_raw,signed_raw T stable,lifted,flip]
    have neBlue (h : background T v.1 w.1) : v≠w := fun e => bg_irr T zero _ (e ▸ h)
    have neRed (h : red v.1 w.1) : v≠w := fun e => ri _ (e ▸ h)
    simpa only [red,color,first,second,and_assoc] using
      code_rule _ (first v.1 w.1) (second v.1 w.1) _ v.2 w.2 (exclude v.1 w.1) neBlue neRed

end
end Audit.Defects
