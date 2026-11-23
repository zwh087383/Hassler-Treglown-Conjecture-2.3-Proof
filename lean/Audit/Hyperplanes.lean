import Audit.Blocks
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Audit.Hyperplanes
open Finset Link Blocks
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option linter.unusedSectionVars false

variable {V : Type} [AddCommGroup V] [Module Field5 V] [Fintype V]
local notation "D" => Module.Dual Field5 V

theorem card_from_rank (J : Type) [AddCommGroup J] [Module Field5 J] [Finite J] :
    Nat.card J=5^Module.finrank Field5 J := by
  rw [Module.natCard_eq_pow_finrank (K:=Field5),Nat.card_eq_fintype_card,ZMod.card]

def cut (f : V →ₗ[Field5] Field5) (a : Finset V) : Finset (LinearMap.ker f) := by
  classical exact univ.filter fun x : (LinearMap.ker f) => x.val∈a

theorem cut_free (f : V →ₗ[Field5] Field5) (a : Finset V) (sf : Free a) : Free (cut f a) := by
  intro x hx y hy z hz eq
  exact sf _ (mem_filter.mp hx).2 _ (mem_filter.mp hy).2 _ (mem_filter.mp hz).2 (congrArg Subtype.val eq)

theorem cut_card (f : V →ₗ[Field5] Field5) (a : Finset V) :
    (cut f a).card=(a.filter fun x => f x=0).card := by
  classical
  apply card_bij (fun x _ => x.val)
  · exact fun x h => mem_filter.mpr ⟨(mem_filter.mp h).2,x.2⟩
  · exact fun _ _ _ _ h => Subtype.ext h
  · intro y hy; obtain ⟨ha, h0⟩ := mem_filter.mp hy
    exact ⟨⟨y,h0⟩,mem_filter.mpr ⟨mem_univ _,ha⟩,rfl⟩

theorem kernel_card (f : V →ₗ[Field5] Field5) (nz : f≠0)
    {d : ℕ} (dim : Module.finrank Field5 V=d+1) :
    Nat.card (LinearMap.ker f)=5^d := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero nz
  rw [card_from_rank, show Module.finrank Field5 (LinearMap.ker f)=d by omega]

theorem filter_ker (f : V →ₗ[Field5] Field5) :
    ((univ : Finset V).filter fun x => f x=0).card=Nat.card (LinearMap.ker f) := by
  classical
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  rw [←cut_card, Nat.card_eq_fintype_card]
  have e : cut f univ=univ := by ext; simp [cut]
  rw [e,card_univ]

/-- The integer gap at density 3/10 gives a dense hyperplane by incidence counting. -/
theorem heavy_plane (r : ℕ) (dim : Module.finrank Field5 V=r+2) (a : Finset V) (sf : Free a)
    (density : 3*Nat.card V < 10*a.card) :
    ∃ f : V →ₗ[Field5] Field5, f≠0 ∧ 3*Nat.card (LinearMap.ker f) < 10*(cut f a).card := by
  classical
  letI : Fintype D := Fintype.ofInjective (fun f : D => (f : V → Field5)) DFunLike.coe_injective
  let fs := (univ : Finset D).erase 0
  let h := 5^(r+1)
  have ncard : Nat.card V =5*h := by rw [card_from_rank,dim]; simp [h,pow_succ',Nat.add_assoc]
  have dc : Nat.card D=Nat.card V := by
    rw [card_from_rank,card_from_rank,Subspace.dual_finrank_eq]
  have fsCount : fs.card+1=5*h := by
    have e := card_erase_add_one (mem_univ (0:D))
    simpa only [card_univ,←Nat.card_eq_fintype_card,dc,ncard] using e
  have zero : (0:V)∉a := fun ha => sf _ ha _ ha _ ha (zero_add _)
  have column (x : V) (xa : x∈a) : (fs.filter fun f => f x=0).card+1=h := by
    let e := Module.Dual.eval Field5 V x
    have nz : e≠0 := fun eq => zero ((Module.eval_apply_eq_zero_iff Field5 x |>.mp eq) ▸ xa)
    have dD : Module.finrank Field5 D=(r+1)+1 := Subspace.dual_finrank_eq.trans dim
    have hc := (filter_ker e).trans (kernel_card e nz dD)
    let xs := (univ : Finset D).filter fun f => f x=0
    have eq : fs.filter (fun f => f x=0)=xs.erase 0 := by ext; simp [fs,xs,and_comm]
    have has : (0:D)∈xs := mem_filter.mpr ⟨mem_univ _,rfl⟩
    change xs.card=h at hc
    rw [eq,card_erase_add_one has,hc]
  have swap : (∑ f∈fs,(cut f a).card) = ∑ x∈a,(fs.filter fun f => f x=0).card := by
    simp_rw [cut_card]
    have row (f : D) : (a.filter fun x => f x=0).card = ∑ x∈a, if f x=0 then 1 else 0 := by
      simp [←sum_filter]
    have col (x : V) : (fs.filter fun f => f x=0).card = ∑ f∈fs, if f x=0 then 1 else 0 := by
      simp [←sum_filter]
    simp_rw [row,col]; exact sum_comm
  have tot : (∑ f∈fs,(cut f a).card)+a.card=a.card*h := by
    rw [swap]
    calc
      _ = ∑ x∈a, ((fs.filter fun f => f x=0).card+1) := by simp [sum_add_distrib]
      _ = _ := by simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using sum_congr rfl column
  obtain ⟨v,hv⟩ := (show Odd (5:ℕ) from ⟨2,rfl⟩).pow (n:=r)
  have oddH : h=10*v+5 := by dsimp only [h]; rw [pow_succ,hv]; omega
  apply Classical.byContradiction
  intro noPlane
  have low (f : D) (mem : f∈fs) : 10*(cut f a).card+5 ≤ 3*h := by
    have nz : f≠0 := (mem_erase.mp mem).1
    have lim : 10*(cut f a).card ≤ 3*Nat.card (LinearMap.ker f) :=
      le_of_not_gt (fun h => noPlane ⟨f,nz,h⟩)
    rw [kernel_card f nz dim] at lim
    change 10*(cut f a).card≤3*h at lim
    omega
  have hsum := sum_le_sum low
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul] at hsum
  rw [ncard] at density
  have pos : 1≤h := by omega
  have over := Nat.mul_le_mul_right (h-1) density.le
  have decomp : h-1+1=h := by omega
  have hsub : a.card*(h-1)+a.card=a.card*h := by
    exact (Nat.mul_succ ..).symm.trans (congrArg (a.card*·) decomp)
  have scaled := congrArg (·*(3*h)) fsCount
  dsimp only at scaled
  nlinarith only [hsum,tot,fsCount,oddH,over,hsub,scaled,
    show 5*h*(h-1)+5*h=5*h*h from (Nat.mul_succ ..).symm.trans (congrArg (5*h*·) decomp)]

end
end Audit.Hyperplanes
