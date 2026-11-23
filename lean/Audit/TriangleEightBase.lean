import Audit.TriangleParam

namespace Audit.TriangleEightBase
open Finset Sumfree Fingerprint TriangleBase TriangleLocal
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t : Finset V} {x y : V}

def budget (r : V → V → Prop) (s : Finset V) : ℤ := cost r s-5*s.card
def W (r : V → V → Prop) (s : Finset V) : ℝ := (2:ℝ)^((budget r s:ℝ)/62)
def Prev (r : V → V → Prop) (s : Finset V) : Prop := ∀t⊂s,(mis r t:ℝ)≤W r t
def ratio (r : V → V → Prop) (s : Finset V) (f : ℝ) := (mis r s:ℝ)≤f*W r s
theorem inheritPrev (sub : t⊆s) (ih : Prev r s) : Prev r t :=
  fun u h => ih u (Finset.ssubset_of_ssubset_of_subset h sub)

theorem cost_single (sym : Symmetric r) (hx : x∈s) : 32-2*(deg r s x:ℤ)≤budget r s-budget r (cut s x) := by
  have c:=single_loss sym hx
  have size:=card_sdiff_add_card_eq_card (singleton_subset_iff.mpr hx)
  rw [card_singleton] at size
  change (cut s x).card+1=s.card at size
  unfold budget; omega
theorem cost_ball (sym : Symmetric r) (irr : Irreflexive r) (hx : x∈s) :
    32*((deg r s x:ℤ)+1)-2*cross r (neighbors r s x) s≤budget r s-budget r (s\ball r s x) := by
  have c:=closed_loss sym irr hx
  have size:=card_sdiff_add_card_eq_card (ball_sub (r:=r) s x)
  rw [ball_card sym irr hx] at size
  unfold budget; omega

theorem weight_cmp {p : ℕ} {q : ℝ} (loss : (p:ℤ)≤budget r s-budget r t)
    (prob : (2:ℝ)^(-(p:ℝ)/62)≤q) : W r t≤q*W r s := by
  have v : (p:ℝ)≤(budget r s:ℝ)-budget r t := by exact_mod_cast loss
  calc
    _ ≤ (2:ℝ)^(-(p:ℝ)/62+(budget r s:ℝ)/62) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := Real.rpow_add (by norm_num) _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right prob (by positivity)
macro "tf8_numeric" : tactic => `(tactic| exact TriangleParam.scalar _ 62 _ (by decide) (by norm_num) (by norm_num))

theorem scaled {p : ℕ} {q : ℝ} (loss : (p:ℤ)≤budget r s-budget r t)
    (prob : (2:ℝ)^(-(p:ℝ)/62)≤q) (base : (mis r t:ℝ)≤W r t) : (mis r t:ℝ)≤q*W r s :=
  base.trans (weight_cmp loss prob)
theorem rescale {a q : ℝ} (pos : 0≤a) (h : ratio r t a) (d : W r t≤q*W r s) :
    (mis r t:ℝ)≤(a*q)*W r s := h.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left d pos)
theorem total {a b f : ℝ} {u v : Finset V} (h : mis r s≤mis r u+mis r v)
    (l : (mis r u:ℝ)≤a*W r s) (rr : (mis r v:ℝ)≤b*W r s) (sum : a+b≤f) : ratio r s f := by
  have nat : (mis r s:ℝ)≤mis r u+mis r v := by exact_mod_cast h
  apply nat.trans ((add_le_add l rr).trans _)
  rw [←add_mul]; exact mul_le_mul_of_nonneg_right sum (by unfold W; positivity)
theorem relax {a b : ℝ} (ab : a≤b) (h : ratio r s a) : ratio r s b :=
  h.trans (mul_le_mul_of_nonneg_right ab (by unfold W; positivity))

theorem iso (sym : Symmetric r) (xs : x∈s) (d : deg r s x=0) (ih : Prev r s) : ratio r s (3/4) := by
  have e : ball r s x={x} := by rw [ball_eq sym xs,card_eq_zero.mp d]; rfl
  have h:=cover_count (R:=r) sym xs
  change mis r s≤∑ y∈ball r s x,(picked r s y ∅).card at h
  rw [e,sum_singleton] at h
  have m:=h.trans (picked_bound (R:=r) s x ∅)
  rw [union_empty] at m
  change mis r s≤mis r (s\ball r s x) at m
  rw [e] at m
  apply (show (mis r s:ℝ)≤mis r (cut s x) by exact_mod_cast m).trans
  have l:=cost_single sym xs
  exact scaled (p:=32) (by change (32:ℤ)≤budget r s-budget r (cut s x); omega) (by tf8_numeric)
    (ih _ (del_strict xs (mem_singleton_self x)))

theorem leaf_cost (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) (hy : y∈neighbors r s x)
    (dx : deg r s x=1) {k : ℕ} (c : cap r s k) :
    64-2*(deg r s y:ℤ) ≤ budget r s-budget r (s\ball r s x) ∧
    32*((deg r s y:ℤ)+1)-2*((deg r s y:ℤ)*k+1-k) ≤ budget r s-budget r (s\ball r s y) := by
  have a:=cost_ball sym irr xs
  have b:=cost_ball sym irr (mem_filter.mp hy).1
  rw [dx,leaf_eq dx hy] at a
  simp only [cross,sum_singleton] at a
  have low:=sum_one_low (reverse sym xs hy) (fun z h => c z (mem_filter.mp h).1)
  rw [dx] at low
  constructor <;> omega

theorem leaf3 (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) (hy : y∈neighbors r s x)
    (dx : deg r s x=1) (dy : deg r s y=3) (c : cap r s 3) (ih : Prev r s) : ratio r s (81/100) := by
  have ⟨a,b⟩:=leaf_cost sym irr xs hy dx c
  rw [dy] at a b
  have ys:=(mem_filter.mp hy).1
  exact total (leaf_branch sym irr xs dx hy)
    (scaled (p:=58) (by omega) (q:=53/100) (by tf8_numeric) (ih _ (del_strict xs (ball_self xs))))
    (scaled (p:=114) (by omega) (q:=28/100) (by tf8_numeric) (ih _ (del_strict ys (ball_self ys)))) (by norm_num)
theorem small_leaf (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) (hy : y∈neighbors r s x)
    (dx : deg r s x=1) (dy : 2≤deg r s y) (c : cap r s 3) (ih : Prev r s) : ratio r s (9/10) := by
  have ys:=(mem_filter.mp hy).1
  by_cases eq : deg r s y=3
  · exact relax (by norm_num) (leaf3 sym irr xs hy dx eq c ih)
  have ⟨a,b⟩:=leaf_cost sym irr xs hy dx c
  have hi:=c y ys
  obtain d : deg r s y=2 := by omega
  rw [d] at a b
  exact total (leaf_branch sym irr xs dx hy)
    (scaled (p:=60) (by omega) (q:=21/40) (by tf8_numeric) (ih _ (del_strict xs (ball_self xs))))
    (scaled (p:=88) (by omega) (q:=3/8) (by tf8_numeric) (ih _ (del_strict ys (ball_self ys)))) (by norm_num)
theorem pair (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) (hy : y∈neighbors r s x)
    (dx : deg r s x=1) (dy : deg r s y=1) (ih : Prev r s) : ratio r s 1 := by
  have loss {u v : V} (us : u∈s) (hv : v∈neighbors r s u) (du : deg r s u=1) (dv : deg r s v=1) :
      (62:ℤ)≤budget r s-budget r (s\ball r s u) := by
    have h:=cost_ball sym irr us
    rw [du,leaf_eq du hv] at h
    simp only [cross,sum_singleton,dv] at h
    omega
  have ys:=(mem_filter.mp hy).1
  exact total (leaf_branch sym irr xs dx hy)
    (scaled (p:=62) (loss xs hy dx dy) (q:=1/2) (by tf8_numeric) (ih _ (del_strict xs (ball_self xs))))
    (scaled (p:=62) (loss ys (reverse sym xs hy) dy dx) (q:=1/2) (by tf8_numeric)
      (ih _ (del_strict ys (ball_self ys)))) (by norm_num)
end
end Audit.TriangleEightBase
