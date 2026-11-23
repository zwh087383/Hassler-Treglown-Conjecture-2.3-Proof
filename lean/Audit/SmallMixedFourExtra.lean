import Audit.SmallMixedFourBases
import Audit.TriangleRaw

namespace Audit.SmallMixed
open Finset Sumfree Lower Link Generic Band Blocks Degrees Fingerprint TriangleBase
set_option maxRecDepth 18000

private def inside (p : Strip.P) : Bool := p.2.2==0 && decide ((p.1,p.2.1)∈extra true)
private def buddyEdge (x y : Strip.P) : Bool := decide (x∈Raw.domain) && decide (y∈Raw.domain) &&
  (x != y) && (inside (x+y) || inside (x-y) || inside (y-x))

private def nearby (t : Finset Strip.P) (x : Strip.P) := t.filter fun y => buddyEdge x y
private def rawVol (t : Finset Strip.P) : ℕ := ∑ x∈t,(nearby t x).card
private def rawZone (x : Strip.P) : Finset Strip.P := nearby Raw.domain x ∪
  Raw.domain.filter (fun y => 2≤(nearby (nearby Raw.domain x) y).card)

private def localCheck (x : Strip.P) : Bool :=
  let w := -x
  let n := nearby Raw.domain x
  let m := nearby Raw.domain w
  let common := m∩rawZone x
  decide (6≤rawVol n ∧ w∈Raw.domain ∧ w≠x ∧ buddyEdge w x=false ∧
    6≤(n∩m).card ∧ 8≤common.card ∧ 6≤rawVol common)

private theorem verified : ∀ (x : Strip.P), x∈Raw.domain → localCheck x=true := by native_decide

private theorem buddy_iff (x y : Strip.P) : buddyEdge x y=true ↔ within (extra true) x y := by
  simp only [buddyEdge,inside,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,
    decide_eq_true_eq,within,Band.edge,in_plane]
  tauto

private theorem neighbor_eq (t : Finset Strip.P) (x : Strip.P) :
    neighbors (within (extra true)) t x=nearby t x := by
  ext y; simp [neighbors,nearby,buddy_iff]

private theorem vol_eq (t : Finset Strip.P) : vol (within (extra true)) t=rawVol t := by
  simp only [vol,cross,deg,neighbor_eq,rawVol]

private theorem zone_eq (x : Strip.P) : TrianglePartner.protectedZone (within (extra true)) Raw.domain x=rawZone x := by
  simp only [TrianglePartner.protectedZone,deg,neighbor_eq,rawZone]

private theorem partner : TrianglePartner.Certificate (within (extra true)) Raw.domain := by
  intro v hv
  have result := verified v hv
  simp only [localCheck,decide_eq_true_eq] at result
  obtain ⟨a,b,c,d,e,f,g⟩ := result
  right
  refine ⟨by rwa [neighbor_eq,vol_eq],-v,b,c,?_,?_,?_,?_⟩
  · exact fun h => Bool.false_ne_true (d.symm.trans ((buddy_iff _ _).mpr h))
  · rwa [neighbor_eq,neighbor_eq]
  · rwa [neighbor_eq,zone_eq]
  · rwa [vol_eq,neighbor_eq,zone_eq]

private theorem no_pair : ∀x∈extra true,∀y∈extra true,x+y∉extra true := by
  simp only [extra,forall_mem_insert,mem_singleton,forall_eq]
  repeat' apply And.intro
  all_goals decide

theorem extra_bound (flag : Bool) : rankCount (extra flag)≤3^25 := by
  cases flag with
  | false =>
    let t : Strip.Seed := {(0,1,0),(0,4,0)}
    have stable : ∀ x,x∈t ↔ -x∈t := by dsimp only [t]; native_decide
    have nz : 0∉t := by decide
    have dist : ((0,1):Strip.K) ≠ -(0,0) := by decide
    have eq : extra false=insert (1,(0,0)) (insert (4,(0,1)) t) := by decide
    rw [eq]
    exact Defects.nonzero t stable nz true true (0,0) (0,1) (fun _ _ => dist)
  | true =>
    have sf : Free (extra true) := fun x hx y hy z hz eq => no_pair x hx y hy (eq.symm ▸ hz)
    have d : maximumDegree (extra true)=9 ∧ headDegree (extra true) 2+headDegree (extra true) 3=18 := by native_decide
    exact TriangleRaw.nine sf d.1.le d.2.ge partner

end Audit.SmallMixed


