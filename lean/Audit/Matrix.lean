import Audit.Collisions
import Sumfree.Transport

namespace Audit.Matrix
open Bipartite Stars Finset
set_option linter.unusedSectionVars false
variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- The manuscript's matrix, with the right coordinates ordered D,C:
    the low-low block is Q, the high-high block is P, and the two other
    blocks are P union Q. -/
def matrix (p q : Finset K) : Rule K := fun t i j =>
  (t∈p ∧ (i || j)=true) ∨ (t∈q ∧ !(i && j)=true)

private theorem exists_four (p : Fin 4 → Prop) : (∃ i, p i) ↔ p 0 ∨ p 1 ∨ p 2 ∨ p 3 := by
  constructor
  · rintro ⟨i,h⟩; fin_cases i <;> tauto
  · rintro (h|h|h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩

theorem ac_matrix (c : Bool) (t : Fin 4 → K) :
    rule t (acTag c) = matrix {t 0,t 1,t 2} (if c then {t 0,t 3} else {t 3}) := by
  funext x i j
  apply propext
  unfold rule
  rw [exists_four]
  cases c <;> cases i <;> cases j <;>
    simp (config := {decide := true}) [acTag,permits,matrix] <;> aesop

theorem mixed_matrix (s : Fin 4 → K) :
    rule s bTag = matrix {s 0,s 1} {s 2,s 3} := by
  funext x i j; apply propext
  unfold rule
  rw [exists_four]
  cases i <;> cases j <;> simp (config := {decide := true}) [bTag,permits,matrix] <;> aesop

def move (t : K) (p : Vertex K) : Vertex K := (p.1,if p.1 then p.2.1+t else p.2.1,p.2.2)

theorem shift (t : K) (r : Rule K) :
    Sumfree.mis (adj (fun a => r (a+t))) univ = Sumfree.mis (adj r) univ := by
  classical
  have cancel (s : K) (p : Vertex K) : move (-s) (move s p)=p := by
    rcases p with ⟨c,x,i⟩; cases c <;> simp [move]
  have image : univ.image (move t) = univ := by
    apply eq_univ_of_forall
    intro p
    exact mem_image.mpr ⟨move (-t) p,mem_univ _,by simpa using cancel (-t) p⟩
  conv_rhs => rw [←image]
  apply Sumfree.mis_image
  · intro x _ y _ e; simpa only [cancel] using congrArg (move (-t)) e
  · rintro ⟨c,x,i⟩ _ ⟨d,y,j⟩ _
    have h (a b : K) : a+t-b=a-b+t := by abel
    cases c <;> cases d <;> simp [move,adj,h]

theorem type_A (t : Fin 4 → K) (distinct : Function.Injective t) :
    Sumfree.mis (adj (matrix {t 0,t 1,t 2} {t 3})) univ < 3^(Fintype.card K) := by
  simpa only [ac_matrix,Bool.false_eq_true,if_false] using FinalTypes.type_A t distinct

theorem type_C (t : Fin 4 → K) (distinct : Function.Injective t) :
    Sumfree.mis (adj (matrix {t 0,t 1,t 2} {t 0,t 3})) univ < 3^(Fintype.card K) := by
  simpa only [ac_matrix,if_true] using FinalTypes.type_C t distinct

theorem type_B {k : ℕ} (t : Fin 4 → Collisions.Space k) (distinct : Function.Injective t) :
    Sumfree.mis (adj (matrix {t 0,t 1} {t 2,t 3})) univ < 3^(Fintype.card (Collisions.Space k)) := by
  let u:=t 1-t 0
  let v:=t 2-t 0
  let w:=t 3-t 0
  have d (i j : Fin 4) (h : i≠j) : t i≠t j := fun e => h (distinct e)
  have undec := Collisions.type_B u v w
    (sub_ne_zero.mpr (d 1 0 (by decide))) (sub_ne_zero.mpr (d 2 0 (by decide)))
    (sub_ne_zero.mpr (d 3 0 (by decide)))
    (fun e => d 1 2 (by decide) (by simpa [u,v] using e))
    (fun e => d 1 3 (by decide) (by simpa [u,w] using e))
    (fun e => d 2 3 (by decide) (by simpa [v,w] using e))
  let r := matrix {t 0,t 1} {t 2,t 3}
  have eq : rule (bSeed u v w) bTag = fun a => r (a+t 0) := by
    rw [mixed_matrix]
    funext a i j; apply propext
    simp [r,matrix,bSeed,four,u,v,w,eq_sub_iff_add_eq]
  rwa [eq,shift] at undec

end Audit.Matrix
