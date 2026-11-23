import Audit.TenEightModels

namespace Audit.TenEight
open Lower Generic

abbrev Plane := Fin 5 × Fin 5
abbrev Solid := Plane × Fin 5
def e1 : Plane := (1,0)
def e2 : Plane := (0,1)
def f1 : Solid := (e1,0)
def f2 : Solid := (e2,0)
def f3 : Solid := ((0,0),1)

def sumfree {K : Type} [AddCommGroup K] [DecidableEq K] (s : Finset (Pt K)) :=
  ∀ x∈s,∀ y∈s, x+y∉s
instance {K : Type} [AddCommGroup K] [DecidableEq K] (s : Finset (Pt K)) :
    Decidable (sumfree s) := by unfold sumfree; infer_instance

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem plane_checked : ∀c : Plane, sumfree (pat e1 e2 c) → (pat e1 e2 c).card=5 → pass (pat e1 e2 c) := by
  native_decide

theorem solid_checked : pass (pat f1 f2 f3) := by native_decide

theorem plane_count {c : Plane} (sf : Link.Free (pat e1 e2 c)) (size : (pat e1 e2 c).card=5) :
    rankCount (pat e1 e2 c)≤3^Fintype.card Plane := by
  exact base_count _ (plane_checked c (fun x hx y hy h => sf _ hx _ hy _ h rfl) size)

theorem solid_count : rankCount (pat f1 f2 f3)≤3^Fintype.card Solid := base_count _ solid_checked

end Audit.TenEight
