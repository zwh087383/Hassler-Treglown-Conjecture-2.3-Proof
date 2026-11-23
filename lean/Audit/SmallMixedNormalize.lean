import Audit.MixedStrip
import Audit.MixedCounts

namespace Audit.SmallMixed
open Finset Lower Link Band Blocks Generic
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] [Module Field5 V]

def scalar (a : Fin 5) : Field5 := a

def lineMap (u : V) : Field5 →ₗ[Field5] V :=
  LinearMap.id.smulRight u

def pairMap (u v : V) : Field5 × Field5 →ₗ[Field5] V :=
  MixedStrip.linear u v

theorem pairMap_apply (u v : V) (a b : Field5) : pairMap u v (a,b)=a • u+b • v := rfl

theorem line_bound {s : Finset (Pt V)} (sf : Free s) (out : Disjoint s (full V))
    {u : V} (nz : u≠0) (along : ∀x∈s, ∃a : Field5, x.2=a • u) :
    rankCount s≤3^(Fintype.card V) := by
  let project (p : Pt Field5) : Pt V := (p.1,p.2 • u)
  let t := (univ : Finset (Pt Field5)).filter fun p => project p∈s
  have me (p : Pt Field5) : p∈t ↔ project p∈s := by simp [t]
  have back : StripFamily.embedded (lineMap u) t=s := by
    ext p
    constructor
    · rintro h
      obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      exact (me j).mp hj
    · intro hp
      obtain ⟨a,h⟩ := along p hp
      have eq : project (p.1,a)=p := Prod.ext rfl h.symm
      exact mem_image.mpr ⟨(p.1,a),(me _).mpr (eq.symm ▸ hp),eq⟩
  have ft : Free t := by
    intro p hp q hq r hr eq
    apply sf _ ((me p).mp hp) _ ((me q).mp hq) _ ((me r).mp hr)
    rw [←eq]
    exact Prod.ext rfl (add_smul ..).symm
  have ot : Disjoint t (full Field5) := by
    apply disjoint_left.mpr
    intro p hp h
    exact disjoint_left.mp out ((me p).mp hp) ((mem_full (u:=project p)).mpr ((mem_full (u:=p)).mp h))
  rw [←back]
  apply StripFamily.bound_embedding (lineMap u) (smul_left_injective Field5 nz)
  exact RankOneBridge.all t ft ot

theorem pairMap_injective (u v : V) (nz : u≠0) (ind : ¬∃c : Field5,v=c • u) :
    Function.Injective (pairMap u v) := MixedStrip.plane_injective u v nz ind

/-- A collapsed two-coordinate model lies on a line, whose exact count is already certified. -/
theorem pair_bound (s : Strip.Seed) (known : rankCount s≤3^25) (u v : V) (nz : u≠0)
    (sf : Free (StripFamily.embedded (pairMap u v) s))
    (out : Disjoint (StripFamily.embedded (pairMap u v) s) (full V)) :
    rankCount (StripFamily.embedded (pairMap u v) s) ≤ 3^(Fintype.card V) :=
  MixedStrip.image_bound u v nz s known sf out

end
end Audit.SmallMixed


