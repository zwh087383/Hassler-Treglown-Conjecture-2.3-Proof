import Audit.Generic
import Audit.SeedFamilies
import Audit.Coverage

namespace Audit.Reduction
open Finset Blocks Band Lower Link Generic Assembly
open scoped Classical Topology
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {K L : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup L] [Fintype L] [DecidableEq L]

def relabel (e : K ≃+ L) : Pt K ≃+ Pt L := (AddEquiv.refl (Fin 5)).prodCongr e

theorem rankCount_relabel (e : K ≃+ L) (s : Finset (Pt K)) :
    rankCount s = rankCount (s.image (relabel e)) := by
  let f : Raw.Point K ≃+ Raw.Point L := (AddEquiv.refl (Fin 5)).prodCongr (e.prodCongr (AddEquiv.refl (Fin 5)))
  have planeMap : (plane s).image f=plane (s.image (relabel e)) := by
    ext z
    obtain ⟨⟨i,u,t⟩,rfl⟩ := f.surjective z
    simp only [mem_image,f.injective.eq_iff,exists_eq_right,in_plane]
    change ((i,u)∈s ∧ t=0) ↔ (∃ a∈s, relabel e a=(i,e u)) ∧ t=0
    have eq (a : Pt K) : relabel e a=(i,e u) ↔ a=(i,u) := by
      change relabel e a = relabel e (i,u) ↔ _
      exact (relabel e).injective.eq_iff
    simp only [eq,exists_eq_right]
  have dom : Raw.domain.image f=Raw.domain := by
    ext z
    obtain ⟨p,rfl⟩ := f.surjective z
    simp only [mem_image,f.injective.eq_iff,exists_eq_right]
    simp only [Raw.domain,mem_filter,mem_univ,true_and]
    rfl
  unfold rankCount
  rw [←dom]
  apply Sumfree.mis_image _ _ _ _ f.injective.injOn
  intro x _ y _
  have eq := faithful_edges f.toAddMonoidHom f.injective (plane s) x y
  simpa only [AddEquiv.coe_toAddMonoidHom,planeMap] using eq

theorem rankCount_raw (p q : Finset K) :
    rankCount (univ.filter fun a : Pt K => (a.1=1 ∧ a.2∈p) ∨ (a.1=4 ∧ -a.2∈q)) =
      Sumfree.mis (Raw.ordinary p q) Raw.domain := by
  let s := (univ.filter fun a : Pt K => (a.1=1 ∧ a.2∈p) ∨ (a.1=4 ∧ -a.2∈q))
  apply Sumfree.count_congr
  intro x _ y _
  have e (a : Raw.Point K) : a∈plane s ↔ Raw.inSeed p q a := by
    simp [in_plane,s,Raw.inSeed,and_comm]
  change edge (plane s) x y ↔ Raw.ordinary p q x y
  simp only [edge,Raw.ordinary,e]; tauto

def TwoColors {k : ℕ} (p q : Finset (Space k)) : Finset (Pt (Space k)) :=
  univ.filter fun a => (a.1=1 ∧ a.2∈p) ∨ (a.1=4 ∧ -a.2∈q)

/-- Shapes for which the previous matrix and entropy modules give a universal proof. -/
inductive MatrixCovered {k : ℕ} : Finset (Pt (Space k)) → Prop
  | nested (p q : Finset (Space k)) (h : p⊆q ∨ q⊆p) : MatrixCovered (TwoColors p q)
  | typeA (t : Fin 4 → Space k) (h : Function.Injective t) :
      MatrixCovered (TwoColors {t 0,t 1,t 2} {t 3})
  | typeB (t : Fin 4 → Space k) (h : Function.Injective t) :
      MatrixCovered (TwoColors {t 0,t 1} {t 2,t 3})
  | typeC (t : Fin 4 → Space k) (h : Function.Injective t) :
      MatrixCovered (TwoColors {t 0,t 1,t 2} {t 0,t 3})

theorem covered_count {r : ℕ} {s : Finset (Pt (Space r))} (covered : MatrixCovered s) :
    rankCount s ≤ 3^(Fintype.card (Space r)) := by
  cases covered with
  | nested p q h =>
    rw [TwoColors,rankCount_raw,Raw.raw_matrix]; exact Coverage.nested_colors p q h
  | typeA t h => rw [TwoColors,rankCount_raw]; exact (Raw.type_A t h).le
  | typeB t h => rw [TwoColors,rankCount_raw]; exact (Raw.type_B t h).le
  | typeC t h => rw [TwoColors,rankCount_raw]; exact (Raw.type_C t h).le

end
end Audit.Reduction
