import Audit.Generic
import Audit.Reduction
import Mathlib.LinearAlgebra.Projection

namespace Audit.StripFamily
open Finset Lower Link Band Blocks Generic Reduction Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {K L : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
  [AddCommGroup L] [Fintype L] [DecidableEq L]

/-- The seed automorphism acts on the first two coordinates and fixes the residual coordinate. -/
def lift (e : Pt K ≃+ Pt L) : Raw.Point K ≃+ Raw.Point L :=
  (AddEquiv.prodAssoc : (Pt K × Fin 5) ≃+ Raw.Point K).symm.trans
    ((e.prodCongr (AddEquiv.refl _)).trans AddEquiv.prodAssoc)

theorem transport (e : Pt K ≃+ Pt L) (bands : ∀ x, x∈full K ↔ e x∈full L)
    (s : Finset (Pt K)) : rankCount s=rankCount (s.image e) := by
  let f := lift e
  have seeds : (plane s).image f=plane (s.image e) := by
    ext z; obtain ⟨⟨a,k,t⟩,rfl⟩ := f.surjective z
    simp only [mem_image,f.injective.eq_iff,exists_eq_right,in_plane]
    change ((a,k)∈s ∧ t=0) ↔ (∃ b∈s,e b=e (a,k)) ∧ t=0
    simp only [e.injective.eq_iff,exists_eq_right]
  have domain : Raw.domain.image f=Raw.domain := by
    ext z; obtain ⟨⟨a,k,t⟩,rfl⟩ := f.surjective z
    simp only [mem_image,f.injective.eq_iff,exists_eq_right,Raw.domain,mem_filter,mem_univ,true_and]
    have eq := bands (a,k)
    simp only [mem_full] at eq
    exact and_congr_left (fun _ => eq)
  unfold rankCount
  rw [←domain]
  apply mis_image _ _ _ _ f.injective.injOn
  intro x _ y _
  simpa only [AddEquiv.coe_toAddMonoidHom,seeds] using faithful_edges f.toAddMonoidHom f.injective (plane s) x y

variable [Module Field5 K] [Module Field5 L]

private def scalar (i : Fin 5) : Field5 := i

def shear (u : K) : Pt K ≃+ Pt K where
  toFun x := (x.1,x.2+scalar x.1 • u)
  invFun x := (x.1,x.2-scalar x.1 • u)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    refine Prod.ext rfl ?_
    change x.2+y.2+(scalar x.1+scalar y.1) • u = (x.2+scalar x.1 • u)+(y.2+scalar y.1 • u)
    rw [add_smul]; abel

theorem shear_count (u : K) (s : Finset (Pt K)) : rankCount s=rankCount (s.image (shear u)) :=
  transport _ (fun x => (mem_full (u:=x)).trans (mem_full (u:=shear u x)).symm) s

theorem negate_count (s : Finset (Pt K)) : rankCount s=rankCount (s.image Neg.neg) := by
  apply transport (AddEquiv.neg _) _ s
  intro x
  simp only [mem_full]
  exact (show ∀ a : Fin 5, (a=2 ∨ a=3) ↔ (-a=2 ∨ -a=3) by decide) x.1

/-- Extend the seed by zero in a complementary vector space. -/
def includeSeed (L : Type) [Zero L] (s : Finset (Pt K)) : Finset (Pt (K × L)) :=
  s.image fun p => (p.1,p.2,0)

def fiberMap (w : L) : Raw.Point K →+ Raw.Point (K × L) where
  toFun p := (p.1,(p.2.1,scalar p.2.2 • w),p.2.2)
  map_zero' := by simp [scalar]
  map_add' p q := by
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    exact Prod.ext rfl (add_smul ..)

theorem fiber_injective (w : L) : Function.Injective (fiberMap (K:=K) w) := by
  intro x y eq
  exact congrArg (fun a : Raw.Point (K × L) => (a.1,a.2.1.1,a.2.2)) eq

theorem included_plane (w : L) (s : Finset (Pt K)) :
    (plane s).image (fiberMap w)=plane (includeSeed L s) := by
  simp only [plane,includeSeed,image_image]
  congr 1
  funext p
  simp [fiberMap,Function.comp_def,scalar]

def fiber (K : Type) [Fintype K] [AddCommGroup K] [DecidableEq K] (w : L) :=
  Raw.domain.image (fiberMap (K:=K) w)

private def projection : Raw.Point (K × L) →+ Field5 × L where
  toFun p := (p.2.2,p.2.1.2)
  map_zero' := rfl
  map_add' _ _ := rfl

private def index (x : Field5 × L) := x.1⁻¹ • x.2

private theorem index_neg (x : Field5 × L) : index (-x)=index x := by
  change (-x.1)⁻¹ • (-x.2)=x.1⁻¹ • x.2
  simp

private theorem index_eq {w : L} {p : Raw.Point (K × L)} (h : p∈fiber K w) :
    index (projection p)=w := by
  obtain ⟨q,hq,rfl⟩ := mem_image.mp h
  have nz : scalar q.2.2≠0 := by
    rcases (mem_filter.mp hq).2.2 with eq|eq <;> rw [eq] <;> decide
  change (scalar q.2.2)⁻¹ • (scalar q.2.2 • w)=w
  rw [smul_smul,inv_mul_cancel₀ nz,one_smul]

private theorem no_cross (s : Finset (Pt K)) {w v : L} {x y : Raw.Point (K × L)}
    (hx : x∈fiber K w) (hy : y∈fiber K v)
    (e : edge (plane (includeSeed L s)) x y) : w=v := by
  have vanishes : ∀ p∈plane (includeSeed L s),projection p=0 := by
    intro p hp
    rw [←included_plane (0:L)] at hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    apply Prod.ext ((in_plane ..).mp hq).2
    change scalar q.2.2 • (0:L)=0
    exact smul_zero _
  rcases orbit_edge vanishes e with h|h
  · exact (index_eq hx).symm.trans ((congrArg index h).trans (index_eq hy))
  · rw [←index_eq hx,←index_neg (projection x),h,index_eq hy]

theorem one_fiber (s : Finset (Pt K)) (w : L) :
    mis (edge (plane (includeSeed L s))) (fiber K w)=rankCount s := by
  symm
  apply mis_image _ _ _ _ (fiber_injective w).injOn
  intro x _ y _
  simpa only [included_plane] using faithful_edges (fiberMap w) (fiber_injective w) (plane s) x y

theorem fibers_product (s : Finset (Pt K)) (t : Finset L) :
    mis (edge (plane (includeSeed L s))) (t.biUnion (fiber K)) = (rankCount s)^t.card := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have empty : family (edge (plane (includeSeed L s))) ∅ = {∅} := by
      ext I; by_cases h : I=∅
      · subst I; simp [IsMIS,Independent]
      · simp [IsMIS,h]
    simp [mis,empty]
  | @insert w t notMem ih =>
    rw [biUnion_insert,card_insert_of_not_mem notMem,pow_succ]
    have split : mis (edge (plane (includeSeed L s))) (fiber K w ∪ t.biUnion (fiber K)) =
        mis (edge (plane (includeSeed L s))) (fiber K w) *
          mis (edge (plane (includeSeed L s))) (t.biUnion (fiber K)) := by
      apply disjoint_count (edge_sym _)
      · apply disjoint_left.mpr
        intro x h1 h2
        obtain ⟨v,hv,hx⟩ := mem_biUnion.mp h2
        exact notMem ((index_eq hx).symm.trans (index_eq h1) ▸ hv)
      · intro x hx y hy e
        obtain ⟨v,hv,hv'⟩ := mem_biUnion.mp hy
        exact notMem ((no_cross s hx hv' e).symm ▸ hv)
    rw [split,ih,one_fiber,mul_comm]

theorem rankCount_directSum (s : Finset (Pt K)) :
    rankCount (includeSeed L s)=rankCount s ^ Fintype.card L := by
  have cover : (univ : Finset L).biUnion (fiber K)=Raw.domain := by
    ext p
    constructor
    · intro h
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp h
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hw
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hq).2⟩
    · intro hp
      let q : Raw.Point K := (p.1,p.2.1.1,p.2.2)
      let w := (scalar p.2.2)⁻¹ • p.2.1.2
      have nz : scalar p.2.2≠0 := by
        rcases (mem_filter.mp hp).2.2 with h|h <;> rw [h] <;> decide
      refine mem_biUnion.mpr ⟨w,mem_univ _,mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2⟩,?_⟩⟩
      refine Prod.ext rfl (Prod.ext (Prod.ext rfl ?_) rfl)
      change scalar p.2.2 • ((scalar p.2.2)⁻¹ • p.2.1.2)=p.2.1.2
      rw [smul_smul,mul_inv_cancel₀ nz,one_smul]
  simpa only [card_univ,cover] using fibers_product s (univ : Finset L)

end
end Audit.StripFamily
