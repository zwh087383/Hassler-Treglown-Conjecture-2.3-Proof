import Audit.Sharp

namespace Audit.DefinitionCheck
open Finset Filter
open scoped Classical Topology
noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

def forbidsSums (s : Finset G) : Prop := ∀ x∈s,∀ y∈s,x+y∉s

omit [DecidableEq G] [Fintype G] in
theorem free_iff (s : Finset G) : Link.Free s ↔ forbidsSums s :=
  ⟨fun h _ hx _ hy sum => h _ hx _ hy _ sum rfl,
   fun h x hx y hy _ hz eq => h x hx y hy (eq.symm ▸ hz)⟩

/-- A separate spelling of the manuscript's definition: every new single point breaks
    the sum-free property. It is equivalent to maximality among all supersets. -/
def paperFamily (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] :=
  (univ : Finset G).powerset.filter fun s => forbidsSums s ∧ ∀ x∉s,¬forbidsSums (insert x s)

theorem same_family : paperFamily G=Link.maximalSets (univ : Finset G) := by
  ext s
  simp only [paperFamily,mem_filter,mem_powerset,subset_univ,true_and,Link.mem_maximalSets]
  constructor
  · rintro ⟨h,maximal⟩
    refine ⟨subset_univ _,(free_iff _).mpr h,?_⟩
    intro t _ tf sub
    refine Subset.antisymm ?_ sub
    intro x hx
    by_contra miss
    exact maximal x miss ((free_iff _).mp (Link.smaller (insert_subset hx sub) tf))
  · intro h
    refine ⟨(free_iff _).mp h.2.1,?_⟩
    intro x miss extension
    have eq := h.2.2 (insert x s) (subset_univ _) ((free_iff _).mpr extension) (subset_insert _ _)
    exact miss (eq ▸ mem_insert_self x s)

theorem paper_statement :
    ∃ e : ℕ → ℝ, e =o[atTop] (fun k : ℕ => (5:ℝ)^k) ∧
      ∀ k : ℕ, ((paperFamily (Fin k → ZMod 5)).card:ℝ)=(3:ℝ)^((5:ℝ)^k/10+e k) := by
  simpa only [same_family] using Sharp.main_theorem

end
end Audit.DefinitionCheck
