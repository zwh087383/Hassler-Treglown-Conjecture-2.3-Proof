import Audit.TriangleTen
import Audit.TriangleParam

namespace Audit.TriangleLarge
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleParam
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s : Finset V} {x : V}

private theorem scalar_bounds (D d : ℕ) (capD : d≤D)
    (above : (13≤D ∧ 11≤d) ∨ (D=12 ∧ d=11)) :
    14*((D:ℤ)-1) ≤ 5*(7*D-5-4*(d:ℤ)) ∧
    3*(14*((D:ℤ)-1)) ≤ (7*(D:ℤ)-5)*((d:ℤ)+1)-4*(d*d:ℕ) := by
  have capReal : (d:ℤ)≤D := by exact_mod_cast capD
  push_cast
  rcases above with ⟨hi,lo⟩|⟨rfl,rfl⟩
  · constructor
    · omega
    · by_cases enough : 13≤d
      · have d13 : (13:ℤ)≤d := by exact_mod_cast enough
        nlinarith only [mul_nonneg (show (0:ℤ)≤7*(D-d) by omega) (show (0:ℤ)≤d-5 by omega),
          mul_nonneg (show (0:ℤ)≤d-1 by omega) (show (0:ℤ)≤3*d-37 by omega)]
      · have cases : d=11 ∨ d=12 := by omega
        rcases cases with rfl|rfl <;> omega
  · norm_num

theorem plain (sym : Symmetric r) (irr : Irreflexive r) {D : ℕ}
    (xs : x∈s) (d : ℕ) (dx : deg r s x=d) (all : cap r s d) (capD : d≤D)
    (above : (13≤D ∧ 11≤d) ∨ (D=12 ∧ d=11)) (ih : allSmaller D r s) :
    (mis r s:ℝ)≤W D r s := by
  have large : 12≤D := by rcases above with h|h <;> omega
  have dl : (12:ℝ)≤D := by exact_mod_cast large
  have pos : 0<denom D := by unfold denom; linarith
  have ⟨ac,bc⟩ := scalar_bounds D d capD above
  have ca:=single D sym xs
  have cb:=TriangleParam.closed D sym irr xs
  have count:=adjacent_sum all dx
  rw [dx] at ca cb
  have a : 14*((D:ℤ)-1) ≤5*(price D r s-price D r (cut s x)) := by omega
  have b : 3*(14*((D:ℤ)-1)) ≤price D r s-price D r (s\ball r s x) := by omega
  have ar : 14*((D:ℝ)-1) ≤5*((price D r s:ℝ)-price D r (cut s x)) := by exact_mod_cast a
  have br : 3*(14*((D:ℝ)-1)) ≤(price D r s:ℝ)-price D r (s\ball r s x) := by exact_mod_cast b
  apply two_branches (vertex_branch s x)
  · apply (ih _ (del_strict xs (mem_singleton_self x))).trans
    apply decay (q:=7/8) (a:=1/5) pos
    · unfold denom; linarith
    · simpa only [neg_div,Nat.cast_one,Nat.cast_ofNat] using
        scalar 1 5 (7/8) (by decide) (by norm_num) (by norm_num)
  · apply (ih _ (del_strict xs (ball_self xs))).trans
    apply decay (q:=1/8) (a:=3) pos br
    rw [Real.rpow_neg (by norm_num)]
    norm_num
  · norm_num

theorem using_ten (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    {D : ℕ} (large : 12≤D) (c : cap r s 10) (ih : allSmaller D r s) :
    (mis r s:ℝ)≤W D r s := by
  by_cases isolated : ∃ x∈s,deg r s x=0
  · obtain ⟨x,hx,dx⟩:=isolated
    exact TriangleParam.isolated large sym hx dx ih
  · exact (TriangleTen.ten sym irr tri s c).trans (ten_to_w large (positive_degrees
      (fun x hx => Nat.pos_of_ne_zero (fun h => isolated ⟨x,hx,h⟩))))

/-- Uniform in the degree cap, including caps far larger than the seed size. -/
theorem large (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (D : ℕ) (above : 13≤D) (s : Finset V) (c : cap r s D) :
    (mis r s:ℝ)≤W D r s := by
  induction s using Finset.strongInduction with
  | H s smaller =>
    have ih : allSmaller D r s := fun t ht => smaller t ht (cap_sub (Finset.ssubset_iff_subset_ne.mp ht).1 c)
    by_cases low : cap r s 10
    · exact using_ten sym irr tri (by omega) low ih
    · unfold cap at low
      push_neg at low
      obtain ⟨u,hu,du⟩:=low
      obtain ⟨x,xs,maximal⟩:=s.exists_max_image (deg r s) ⟨u,hu⟩
      exact plain sym irr xs _ rfl maximal (c x xs) (Or.inl ⟨above,du.trans_le (maximal u hu)⟩) ih

theorem to_quarter {D : ℕ} (large : 12≤D) (aver : 3*D*s.card≤4*vol r s) :
    W D r s≤(3:ℝ)^((s.card:ℝ)/4) := by
  have dl : (12:ℝ)≤D := by exact_mod_cast large
  have pos : 0<denom D := by unfold denom; linarith
  have av : 3*(D:ℝ)*s.card≤4*vol r s := by exact_mod_cast aver
  have scalarBound : (2:ℝ)^((61:ℝ)/154)≤(3:ℝ)^((1:ℝ)/4) := by
    by_contra! bad
    have absurd := pow_lt_pow_left₀ bad (n:=308) (Real.rpow_nonneg (by norm_num) _) (by decide)
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),←Real.rpow_natCast,←Real.rpow_mul (by norm_num)] at absurd
    norm_num at absurd
  have target := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) scalarBound (Nat.cast_nonneg (α:=ℝ) s.card)
  rw [←Real.rpow_mul (by norm_num),←Real.rpow_mul (by norm_num)] at target
  rw [show 1/4*(s.card:ℝ)=s.card/4 by ring] at target
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) target
  change (price D r s:ℝ)/denom D ≤ _
  apply (div_le_iff₀ pos).mpr
  unfold price denom
  push_cast
  nlinarith only [av,mul_le_mul_of_nonneg_right dl (Nat.cast_nonneg (α:=ℝ) s.card)]

theorem dense (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    {D : ℕ} (above : 13≤D) (s : Finset V) (c : cap r s D) (aver : 3*D*s.card≤4*vol r s) :
    (mis r s:ℝ)≤(3:ℝ)^((s.card:ℝ)/4) :=
  (large sym irr tri D above s c).trans (to_quarter (by omega) aver)

end
end Audit.TriangleLarge
