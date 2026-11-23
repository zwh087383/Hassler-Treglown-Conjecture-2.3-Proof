import Audit.TriangleBase

namespace Audit.TriangleLocal
open Finset Sumfree Fingerprint TriangleBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t : Finset V} {x y z : V}

abbrev nb (s : Finset V) (x y : V) := y∈neighbors r s x
theorem leaf_eq (d : deg r s x=1) (hy : y∈neighbors r s x) : neighbors r s x={y} :=
  eq_of_subset_of_card_le (singleton_subset_iff.mpr hy) (by simpa using d.le) |>.symm
theorem second_neighbor (d : deg r s x=2) (hy : y∈neighbors r s x) :
    ∃ z, z≠y ∧ z∈neighbors r s x := by
  have p := card_erase_add_one hy
  have positive : 0<((neighbors r s x).erase y).card := by change (neighbors r s x).card=2 at d; omega
  obtain ⟨z,h⟩ := card_pos.mp positive
  exact ⟨z,(mem_erase.mp h).1,(mem_erase.mp h).2⟩
theorem reverse (sym : Symmetric r) (xs : x∈s) (hy : y∈neighbors r s x) : x∈neighbors r s y :=
  mem_filter.mpr ⟨xs,sym (mem_filter.mp hy).2⟩
theorem degree_cut_yes (ys : y∈s) (h : r x y) : deg r (cut s y) x+1=deg r s x := by
  have eq : neighbors r (cut s y) x=(neighbors r s x).erase y := by
    ext u; simp [neighbors,cut,and_assoc,and_left_comm,and_comm]
  change (neighbors r (cut s y) x).card+1=_
  rw [eq]
  exact card_erase_add_one (mem_filter.mpr ⟨ys,h⟩ : y∈neighbors r s x)
theorem degree_cut_no (h : ¬r x y) : deg r (cut s y) x=deg r s x := by
  apply congrArg Finset.card
  ext u
  simp only [neighbors,mem_filter,cut,mem_sdiff,mem_singleton]
  constructor
  · exact fun k => ⟨k.1.1,k.2⟩
  · exact fun k => ⟨⟨k.1,fun eq => h (eq ▸ k.2)⟩,k.2⟩

def rel (r : V → V → Prop) (s : Finset V) (f : ℝ) := (mis r s:ℝ)≤f*weight r s
theorem normal (ih : IH r s) (strict : t ⊂ s) : rel r t 1 := by
  simpa [rel] using ih t strict
theorem relay {a q : ℝ} (ha : 0≤a) (bound : rel r t a)
    (decay : weight r t≤q*weight r s) : (mis r t:ℝ)≤(a*q)*weight r s := by
  apply bound.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left decay ha
theorem add_children {u v : Finset V} {a b f : ℝ} (branch : mis r s≤mis r u+mis r v)
    (l : (mis r u:ℝ)≤a*weight r s) (h : (mis r v:ℝ)≤b*weight r s) (sum : a+b≤f) :
    rel r s f := by
  have e : (mis r s:ℝ)≤mis r u+mis r v := by exact_mod_cast branch
  refine e.trans ((add_le_add l h).trans ?_)
  rw [←add_mul]
  exact mul_le_mul_of_nonneg_right sum (by unfold weight; positivity)
theorem rel_mono {a b : ℝ} (le : a≤b) (bound : rel r s a) : rel r s b :=
  bound.trans (mul_le_mul_of_nonneg_right le (by unfold weight; positivity))

macro "tf_numeric" : tactic => `(tactic| exact neg_power _ _ (by norm_num) (by norm_num))

theorem scale {u : Finset V} {n : ℕ} {q : ℝ} (costBound : (n:ℤ)≤cost r s-cost r u)
    (power : (2:ℝ)^(-(n:ℝ)/72)≤q) (bounds : (mis r u:ℝ)≤weight r u) :
    (mis r u:ℝ)≤q*weight r s := bounds.trans (compare costBound power)

theorem leaf_branch (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s)
    (dx : deg r s x=1) (hy : y∈neighbors r s x) :
    mis r s≤mis r (s\ball r s x)+mis r (s\ball r s y) := by
  have ne : x≠y := fun h => irr _ (h ▸ (mem_filter.mp hy).2)
  have h:=cover_count (R:=r) sym xs
  change mis r s≤∑ u∈ball r s x,(picked r s u ∅).card at h
  rw [ball_eq sym xs,leaf_eq dx hy,sum_insert (by simpa using ne),sum_singleton] at h
  have f (z : V) := picked_bound (R:=r) s z ∅
  simpa only [union_empty] using h.trans (Nat.add_le_add (f x) (f y))

theorem isolated (sym : Symmetric r) (xs : x∈s) (dx : deg r s x=0) (ih : IH r s) :
    rel r s (3/4) := by
  have e : neighbors r s x=∅ := card_eq_zero.mp dx
  have single : ball r s x={x} := by rw [ball_eq sym xs,e]; rfl
  have m := cover_count (R:=r) sym xs
  change mis r s≤∑ u∈ball r s x,(picked r s u ∅).card at m
  rw [single,sum_singleton] at m
  have h:=m.trans (picked_bound (R:=r) s x ∅)
  rw [union_empty] at h
  change mis r s≤mis r (s\ball r s x) at h
  rw [single] at h
  have sub := ih _ (del_strict xs (mem_singleton_self x))
  apply (show (mis r s:ℝ)≤mis r (cut s x) by exact_mod_cast h).trans
  apply scale (n:=37) _ (by tf_numeric) sub
  have q:=single_loss sym xs
  change (37:ℤ)≤cost r s-cost r (cut s x)
  omega

theorem adjacent_sum {k d : ℕ} (c : cap r s k) (dx : deg r s x=d) :
    cross r (neighbors r s x) s≤d*k := by
  rw [←dx]
  exact sum_le (fun w hw => c w (mem_filter.mp hw).1)
theorem leaf_losses (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s)
    (hy : y∈neighbors r s x) (dx : deg r s x=1) {k : ℕ} (c : cap r s k) :
    (74-2*(deg r s y:ℤ) ≤ cost r s-cost r (s\ball r s x)) ∧
    (37*((deg r s y:ℤ)+1)-2*((deg r s y:ℤ)*k+1-k) ≤ cost r s-cost r (s\ball r s y)) := by
  have xloss := closed_loss sym irr xs
  rw [dx,leaf_eq dx hy] at xloss
  simp only [cross,sum_singleton] at xloss
  have yloss := closed_loss sym irr (mem_filter.mp hy).1
  have low := sum_one_low (reverse sym xs hy) (fun _ h => c _ (mem_filter.mp h).1)
  rw [dx] at low
  constructor <;> omega

theorem leaf (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s)
    (hy : y∈neighbors r s x) (dx : deg r s x=1) (dy : 2≤deg r s y)
    (c : cap r s 3) (ih : IH r s) : rel r s (177/200) := by
  have ⟨a,b⟩ := leaf_losses sym irr xs hy dx c
  have ys := (mem_filter.mp hy).1
  have hi:=c y ys
  have left := ih _ (del_strict xs (ball_self (r:=r) xs))
  have right := ih _ (del_strict ys (ball_self (r:=r) ys))
  have cases : deg r s y=2 ∨ deg r s y=3 := by omega
  rcases cases with h|h
  · rw [h] at a b
    exact add_children (leaf_branch sym irr xs dx hy)
      (scale (n:=70) (by omega) (q:=51/100) (by tf_numeric) left)
      (scale (n:=103) (by omega) (q:=3/8) (by tf_numeric) right) (by norm_num)
  · rw [h] at a b
    exact add_children (leaf_branch sym irr xs dx hy)
      (scale (n:=68) (by omega) (q:=21/40) (by tf_numeric) left)
      (scale (n:=134) (by omega) (q:=1/3) (by tf_numeric) right) (by norm_num)

theorem lone_edge (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s)
    (hy : y∈neighbors r s x) (dx : deg r s x=1) (dy : deg r s y=1) (ih : IH r s) :
    rel r s 1 := by
  have loss {u v : V} (us : u∈s) (hv : v∈neighbors r s u) (du : deg r s u=1) (dv : deg r s v=1) :
      (72:ℤ)≤cost r s-cost r (s\ball r s u) := by
    have h:=closed_loss sym irr us
    rw [du,leaf_eq du hv] at h
    simp only [cross,sum_singleton,dv] at h
    omega
  have ys:=(mem_filter.mp hy).1
  exact add_children (leaf_branch sym irr xs dx hy)
    (scale (n:=72) (loss xs hy dx dy) (q:=1/2) (by tf_numeric) (ih _ (del_strict xs (ball_self xs))))
    (scale (n:=72) (loss ys (reverse sym xs hy) dy dx) (q:=1/2) (by tf_numeric)
      (ih _ (del_strict ys (ball_self ys)))) (by norm_num)

end
end Audit.TriangleLocal
