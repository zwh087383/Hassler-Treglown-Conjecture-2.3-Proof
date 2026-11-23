import Audit.TriangleLocal

namespace Audit.TriangleParam
open Finset Sumfree Fingerprint TriangleBase TriangleLocal
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t : Finset V} {x : V}

def price (D : ℕ) (r : V → V → Prop) (s : Finset V) : ℤ :=
  (7*(D:ℤ)-5)*s.card-2*vol r s
def denom (D : ℕ) : ℝ := 14*((D:ℝ)-1)
def W (D : ℕ) (r : V → V → Prop) (s : Finset V) : ℝ := (2:ℝ)^((price D r s:ℝ)/denom D)
def allSmaller (D : ℕ) (r : V → V → Prop) (s : Finset V) : Prop :=
  ∀ t ⊂ s, (mis r t:ℝ) ≤ W D r t

theorem single (D : ℕ) (sym : Symmetric r) {x : V} (xs : x∈s) :
    7*(D:ℤ)-5-4*(deg r s x:ℤ)≤price D r s-price D r (cut s x) := by
  have ct := card_sdiff_add_card_eq_card (singleton_subset_iff.mpr xs)
  have vi := volume_id sym (singleton_subset_iff.mpr xs)
  have eq : cross r {x} s=deg r s x := by simp [cross]
  rw [eq] at vi
  simp only [card_singleton] at ct
  have count : ((cut s x).card:ℤ)+1=s.card := by exact_mod_cast ct
  have vol : (vol r s:ℤ)≤vol r (cut s x)+2*deg r s x := by dsimp [cut]; omega
  unfold price
  nlinarith only [vol,count,congrArg (fun z : ℤ => z*(D:ℤ)) count]

theorem closed (D : ℕ) (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) :
    (7*(D:ℤ)-5)*((deg r s x:ℤ)+1)-4*cross r (neighbors r s x) s
      ≤price D r s-price D r (s\ball r s x) := by
  have ct := card_sdiff_add_card_eq_card (ball_sub (r:=r) s x)
  have vi := volume_id sym (ball_sub (r:=r) s x)
  have vn := ball_internal sym irr xs
  have cs : cross r (ball r s x) s=deg r s x+cross r (neighbors r s x) s := by
    unfold cross
    rw [ball_eq sym xs,sum_insert (self_neigh irr s x)]
  rw [cs] at vi
  rw [ball_card sym irr xs] at ct
  have count : ((s\ball r s x).card:ℤ)+((deg r s x:ℤ)+1)=s.card := by exact_mod_cast ct
  have v : (vol r s:ℤ)≤vol r (s\ball r s x)+2*cross r (neighbors r s x) s := by omega
  unfold price
  nlinarith only [v,count,congrArg (fun z : ℤ => z*(D:ℤ)) count]

theorem scalar (i n : ℕ) (q : ℝ) (hn : 0<n) (hq : 0<q) (cert : 1≤(2:ℝ)^i*q^n) :
    (2:ℝ)^(-(i:ℝ)/n)≤q := by
  have p : (0:ℝ)<n := by exact_mod_cast hn
  by_contra! h
  have hp := pow_lt_pow_left₀ h hq.le hn.ne'
  have e : ((2:ℝ)^(-(i:ℝ)/n))^n=((2:ℝ)^i)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),div_mul_cancel₀ _ p.ne',
      Real.rpow_neg (by norm_num),Real.rpow_natCast]
  rw [e] at hp
  have tmp := mul_lt_mul_of_pos_left hp (show 0<(2:ℝ)^i by positivity)
  rw [mul_inv_cancel₀ (by positivity)] at tmp
  linarith

theorem decay {D : ℕ} {a q : ℝ} (pos : 0<denom D)
    (p : a*denom D≤(price D r s:ℝ)-price D r t) (base : (2:ℝ)^(-a)≤q) :
    W D r t ≤ q*W D r s := by
  have reduce : (price D r t:ℝ)/denom D ≤ -a+(price D r s:ℝ)/denom D := by
    apply (div_le_iff₀ pos).mpr
    rw [add_mul,div_mul_cancel₀ _ pos.ne']
    linarith
  calc
    _ ≤ (2:ℝ)^(-a+(price D r s:ℝ)/denom D) := Real.rpow_le_rpow_of_exponent_le (by norm_num) reduce
    _ = _ := Real.rpow_add (by norm_num) _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right base (by positivity)

theorem ten_to_w {D : ℕ} (large : 12≤D) (sum : s.card≤vol r s) : weight r s≤W D r s := by
  have dl : (12:ℝ)≤D := by exact_mod_cast large
  have av : (s.card:ℝ)≤vol r s := by exact_mod_cast sum
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  unfold denom
  apply (div_le_div_iff₀ (by norm_num) (by linarith : 0<14*((D:ℝ)-1))).mpr
  unfold cost price
  push_cast
  nlinarith only [mul_nonneg (show 0≤14*(D:ℝ)-158 by linarith) (sub_nonneg.mpr av)]

theorem positive_degrees (h : ∀x∈s,1≤deg r s x) : s.card≤vol r s := by
  simpa only [vol,cross,sum_const,nsmul_eq_mul,mul_one] using sum_le_sum h

theorem two_branches {D : ℕ} {u v : Finset V} {a b : ℝ}
    (branch : mis r s≤mis r u+mis r v)
    (l : (mis r u:ℝ)≤a*W D r s) (h : (mis r v:ℝ)≤b*W D r s) (sum : a+b≤1) :
    (mis r s:ℝ)≤W D r s := by
  have m : (mis r s:ℝ)≤mis r u+mis r v := by exact_mod_cast branch
  refine m.trans ((add_le_add l h).trans ?_)
  rw [←add_mul]
  exact (mul_le_mul_of_nonneg_right sum (by unfold W; positivity)).trans_eq (one_mul _)

theorem isolated {D : ℕ} (large : 12≤D) (sym : Symmetric r) (xs : x∈s) (dx : deg r s x=0)
    (ih : allSmaller D r s) : (mis r s:ℝ)≤W D r s := by
  have e : neighbors r s x=∅ := card_eq_zero.mp dx
  have v : ball r s x={x} := by rw [ball_eq sym xs,e]; rfl
  have m := cover_count (R:=r) sym xs
  change mis r s≤∑ u∈ball r s x,(picked r s u ∅).card at m
  rw [v,sum_singleton] at m
  have l := m.trans (picked_bound (R:=r) s x ∅)
  rw [union_empty] at l
  change mis r s≤mis r (s\ball r s x) at l
  rw [v] at l
  apply (show (mis r s:ℝ)≤mis r (cut s x) by exact_mod_cast l).trans
  apply (ih _ (del_strict xs (mem_singleton_self x))).trans
  have c := single D sym xs
  rw [dx] at c
  have cp : price D r (cut s x)≤price D r s := by omega
  have dl : (12:ℝ)≤D := by exact_mod_cast large
  have dp : (0:ℝ)≤denom D := by unfold denom; linarith
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_div_of_nonneg_right (by exact_mod_cast cp) dp)

end
end Audit.TriangleParam
