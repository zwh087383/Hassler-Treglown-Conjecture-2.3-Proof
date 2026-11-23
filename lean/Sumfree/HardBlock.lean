import Sumfree.FiniteCells
import Sumfree.Induced
import Sumfree.SmallCounts

namespace Sumfree.Pair
open Finset Sumfree.Counter
abbrev Rung := Fin 5 × Bool
private def rung (p q : Rung) := (p.2=q.2 ∧ C5 p.1 q.1) ∨ (p.1=q.1 ∧ p.2≠q.2)
private instance : DecidableRel rung := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
private def coverIndex (p : Fin 20) : Bool × Rung :=
  let j : Nat := p.val/2
  ((j+p.val%2)%2 == 1,(j : Fin 5),p.val%2 == 1)

private theorem ladder_edges : ∀ i j : Fin 20,
    Blocks.prismEdge 10 i j = true ↔ cover rung (coverIndex i) (coverIndex j) := by
  unfold cover
  decide

private theorem cover_counts :
    (indeps (cover rung) univ).card ≤ 6727 ∧ mis (cover rung) univ = 122 := by
  have fi : ∀ i j, coverIndex i = coverIndex j → i=j := by decide
  have onto : ∀ p, ∃ i, coverIndex i = p := by decide
  have full : univ.image coverIndex = univ := by
    ext p; simpa [Finset.mem_image] using onto p
  have a := Blocks.prism10_ind
  unfold Blocks.prism at a
  rw [solve_graph] at a
  have b := Blocks.prism10_mis
  unfold Blocks.prism at b
  rw [solve_mis] at b
  have d : domain (fun _ : Fin 20 => true) = univ := by simp [domain]
  rw [d] at b
  constructor
  · rw [← a]
    classical
    let select (I : Finset (Bool × Rung)) := univ.filter fun i => coverIndex i ∈ I
    apply card_le_card_of_injOn select
    · intro I hi
      have ind := (mem_filter.mp hi).2
      refine mem_filter.mpr ⟨mem_powerset.mpr (by rw [d]; exact subset_univ _),?_,by simp⟩
      intro x hx y hy e
      exact ind _ (mem_filter.mp hx).2 _ (mem_filter.mp hy).2 ((ladder_edges _ _).1 e)
    · intro I _ J _ eq
      ext p
      obtain ⟨i,rfl⟩ := onto p
      simpa [select] using Finset.ext_iff.mp eq i
  · rw [← full,← mis_image univ coverIndex (fun i j => Blocks.prismEdge 10 i j = true)
      _ (fun i _ j _ => fi i j) (fun i _ j _ => ladder_edges i j)]
    exact b

def hardS : Ambient Plane := (0,1,0)
def hardT : Ambient Plane := (0,0,1)

/-- beta and gamma are the coefficients of (e1-e2)/2 and (e1+e2)/2;
    on the other rail the tail is negated after subtracting (e1+e2)/2. -/
private def hardMap (p : Fin 5 × Rung) : Ambient Plane :=
  let x : F := 3*((p.1.val:F)+(p.2.1.val:F))
  let y : F := 3*((p.2.1.val:F)-(p.1.val:F))
  if p.2.2 then (3,3-x,3-y) else (2,x,y)

set_option maxHeartbeats 0
set_option maxRecDepth 10000
private theorem hard_edges : ∀ p q, five rung p q ↔ edgeB hardS hardT (hardMap p) (hardMap q) := by
  unfold five
  decide

theorem hard_cell (g : Ambient Plane) :
    mis (edges hardS hardT) (allowed hardS hardT (cell hardS hardT g)) ≤ 820694 := by
  have inj : ∀ x y, hardMap x = hardMap y → x=y := by decide
  have onto : ∀ x : Ambient Plane, band x → ∃ p, hardMap p=x := by decide
  have sub : allowed hardS hardT (cell hardS hardT g) ⊆ univ.image hardMap := by
    intro x hx
    obtain ⟨p,eq⟩ := onto x (mem_cell.mp (mem_allowed.mp hx).1).1
    exact mem_image.mpr ⟨p,mem_univ _,eq⟩
  have bound := induced_mono (R := edges hardS hardT)
    (fun _ _ h => ⟨h.1.symm,raw_sym _ h.2⟩) sub (fun _ _ h => h.1 rfl)
  rw [← mis_image univ hardMap (five rung) _ (fun i _ j _ => inj i j)
    (fun i _ j _ => (hard_edges i j).trans (edge_bool ..))] at bound
  have sym : Symmetric rung := by
    intro x y
    unfold rung C5
    rintro (⟨e,a|b⟩ | ⟨e,a⟩)
    · exact Or.inl ⟨e.symm,Or.inr a⟩
    · exact Or.inl ⟨e.symm,Or.inl b⟩
    · exact Or.inr ⟨e.symm,a.symm⟩
  have f := folding sym
  rw [cover_counts.2] at f
  exact (bound.trans f).trans (Nat.mul_le_mul_right 122 cover_counts.1)

end Sumfree.Pair
