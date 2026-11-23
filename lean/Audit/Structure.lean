import Audit.PlaneFibers
import Audit.Assembly

namespace Audit.Structure
open Finset Link Blocks PlaneFibers Hyperplanes
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option linter.unusedSectionVars false

private theorem one_dimensional (s : Finset Field5) (sf : Free s) :
    ∃ b : Field5, b≠0 ∧ ∀ x∈s, b*x=1 ∨ b*x=4 := by
  have small : ∀ u : Finset Field5,
      (∀ x∈u,∀ y∈u,∀ z∈u,x+y≠z) →
      ∃ b : Field5, b≠0 ∧ ∀ x∈u, b*x=1 ∨ b*x=4 := by decide
  exact small s sf

theorem normal_induction (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module Field5 V] [Fintype V], Module.finrank Field5 V=n →
      ∀ a : Finset V, Free a → 3*Nat.card V<10*a.card → Normal a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ dim a sf density
    classical
    cases n with
    | zero =>
      have size : Nat.card V=1 := by rw [card_from_rank,dim,pow_zero]
      have nz : (0:V)∉a := fun h => sf _ h _ h _ h (zero_add _)
      have bound := card_le_univ (insert 0 a)
      rw [card_insert_of_not_mem nz,←Nat.card_eq_fintype_card,size] at bound
      omega
    | succ n =>
      cases n with
      | zero =>
        let e := LinearEquiv.ofFinrankEq (R:=Field5) V Field5 (by rw [dim,Module.finrank_self])
        obtain ⟨b,b0,good⟩ := one_dimensional (a.image e) ((Assembly.free_image e.toAddEquiv a).mpr sf)
        let f := b • e.toLinearMap
        have val (x : V) : f x=b*e x := rfl
        refine ⟨f,?_,fun x hx => good _ (mem_image_of_mem e hx)⟩
        intro zero
        obtain ⟨x,hx⟩ := e.surjective 1
        have h : f x=0 := by rw [zero]; rfl
        rw [val,hx,mul_one] at h; exact b0 h
      | succ r =>
        obtain ⟨f,nz,big⟩ := heavy_plane r dim a sf density
        have kd := Module.Dual.finrank_ker_add_one_of_ne_zero nz
        have kdim : Module.finrank Field5 (LinearMap.ker f)=r+1 := by omega
        apply lift_dense a sf density f nz big
        exact ih (r+1) (by omega) (LinearMap.ker f) kdim _ (cut_free _ _ sf) big

private def splitForm {V : Type} [AddCommGroup V] [Module Field5 V]
    (f : V →ₗ[Field5] Field5) (z : V) (hz : f z=1) : V ≃ₗ[Field5] Field5 × (LinearMap.ker f) where
  __ := f.prod (projKer f z hz)
  invFun p := p.2.val+p.1 • z
  left_inv x := by change (x-f x • z)+f x • z=x; abel
  right_inv := by
    rintro ⟨p,u⟩
    apply Prod.ext
    · change f (u.val+p • z)=p
      rw [map_add,(show f u.val=0 from u.2),map_smul,hz,smul_eq_mul,mul_one,zero_add]
    · apply Subtype.ext
      change u.val+p • z - f (u.val+p • z) • z = u.val
      rw [map_add,(show f u.val=0 from u.2),map_smul,hz,smul_eq_mul,mul_one,zero_add,add_sub_cancel_right]

/-- The density threshold and the automorphism are both proved for the exact groups being counted. -/
theorem largeSetStructure : Assembly.LargeSetStructure := by
  intro k m sf threshold
  classical
  let V := Field5 × Space k
  let a : Finset V := m
  have dim : Module.finrank Field5 V=k+1 := by
    rw [Module.finrank_prod,Module.finrank_self,Module.finrank_fin_fun,Nat.add_comm]
  have dense : 3*Nat.card V<10*a.card := by
    rw [←Assembly.total_order] at threshold
    rw [Nat.card_eq_fintype_card]
    change 3*Fintype.card (Assembly.group k)<10*m.card
    exact_mod_cast (show (3:ℝ)*Fintype.card (Assembly.group k)<10*m.card by linarith)
  obtain ⟨f,nz,norm⟩ := normal_induction _ V dim a sf dense
  let φ := (2:Field5) • f
  have φnz : φ≠0 := by
    obtain ⟨x,hx⟩ := onto_of_ne nz 1
    intro h
    have eq : φ x=0 := by rw [h]; rfl
    change 2*f x=0 at eq; rw [hx,mul_one] at eq; exact (by decide : (2:Field5)≠0) eq
  obtain ⟨z,hz⟩ := onto_of_ne φnz 1
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero φnz
  let tail := LinearEquiv.ofFinrankEq (R:=Field5) (LinearMap.ker φ) (Space k) (by
    rw [Module.finrank_fin_fun]; omega)
  let e := (splitForm φ z hz).trans ((LinearEquiv.refl Field5 Field5).prodCongr tail)
  refine ⟨e.toAddEquiv,?_⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  apply Band.mem_full.mpr
  change 2*f x=2 ∨ 2*f x=3
  rcases norm x hx with p|p <;> rw [p] <;> decide

end
end Audit.Structure
