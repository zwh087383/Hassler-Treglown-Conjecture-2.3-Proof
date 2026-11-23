import Audit.TriangleExceptional

namespace Audit.TenEightPotential
open Finset Sumfree Fingerprint TriangleBase TriangleExceptional
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t : Finset V} {x : V}

def Strong (r : V → V → Prop) (s : Finset V) : Prop :=
  ∃ x∈s,deg r s x=10 ∧ cross r (neighbors r s x) s≤87 ∧ 6≤vol r (neighbors r s x)

def Nine (r : V → V → Prop) (s : Finset V) : Prop :=
  ∀ x∈s,deg r s x=9 → cross r (neighbors r s x) s≤77 ∧ 2≤vol r (neighbors r s x)

def Partners (r : V → V → Prop) (s : Finset V) : Prop :=
  ∃ x∈s, ∃ w∈cut s x, deg r s x=10 ∧ cross r (neighbors r s x) s≤90 ∧ 6≤vol r (neighbors r s x) ∧
    deg r (cut s x) w=8 ∧ cross r (neighbors r (cut s x) w) (cut s x)≤68 ∧
    6≤vol r (neighbors r (cut s x) w) ∧
    (cross r (neighbors r s x) s≤89 ∨ Strong r (cut (cut s x) w))

private theorem factor (i : ℕ) (q : ℝ) (pos : 0<q) (pow : 1≤(3:ℝ)^i*q^84)
    (loss : (i:ℤ)≤cash 14 r s-cash 14 r t) : W 14 r t≤q*W 14 r s :=
  scale (by decide) loss (by simpa only [Nat.cast_ofNat,show (6:ℝ)*14=84 by norm_num]
    using Potential.neg_weight i 84 q (by decide) pos pow)

private theorem skip_gains {a b : ℝ} (pos : 0≤a)
    (small : (mis r t:ℝ)≤a*W 14 r t) (decrease : W 14 r t≤b*W 14 r s) :
    (mis r t:ℝ)≤(a*b)*W 14 r s := by
  apply small.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left decrease pos

private theorem strong_gain (sym : Symmetric r) (irr : Irreflexive r)
    (useful : Strong r s) (ih : Prev 14 r s) : (mis r s:ℝ)≤(9976/10000)*W 14 r s := by
  obtain ⟨x,hx,dx,high,inside⟩:=useful
  have a:=cost1 14 sym hx
  have b:=costN 14 sym irr hx
  rw [dx] at a b
  apply combine (x:=x) (a:=87741/100000) (b:=12019/100000)
  · exact (ih _ (del_strict hx (mem_singleton_self x))).trans
      (factor (s:=s) (t:=cut s x) 10 _ (by norm_num) (by norm_num) (by omega))
  · exact (ih _ (del_strict hx (ball_self hx))).trans
      (factor 162 _ (by norm_num) (by norm_num) (by omega))
  · norm_num

private theorem partial_prev (ih : Prev 14 r s) (sub : t⊆s) : Prev 14 r t :=
  fun l hl => ih l (Finset.ssubset_of_ssubset_of_subset hl sub)

theorem bound (sym : Symmetric r) (irr : Irreflexive r) (g : Finset V)
    (c : cap r g 10) (nine : ∀ s⊆g,cap r s 9 → Nine r s)
    (step : ∀ s⊆g,¬cap r s 9 → ¬Strong r s → Partners r s)
    (av : 18*g.card≤2*vol r g) : (mis r g:ℝ)≤(3:ℝ)^((g.card:ℝ)/4) := by
  suffices all : ∀s⊆g,(mis r s:ℝ)≤W 14 r s from
    (all g (Finset.Subset.refl _)).trans (quarter (by decide) av)
  intro s
  induction s using Finset.strongInduction with
  | H s prev =>
    intro sub
    have ih : Prev 14 r s := fun l h => prev l h ((Finset.ssubset_iff_subset_ne.mp h).1.trans sub)
    by_cases base : cap r s 8
    · exact weighted_base (D:=8) (l:=10) sym irr (by decide) (by decide) (by native_decide) s base
    by_cases small : cap r s 9
    · unfold cap at base
      push_neg at base
      obtain ⟨x,hx,dx⟩:=base
      have full : deg r s x=9 := by have := small x hx; omega
      obtain ⟨high,inside⟩:=nine s sub small x hx full
      have a:=cost1 14 sym hx
      have b:=costN 14 sym irr hx
      rw [full] at a b
      have k := combine (s:=s) (x:=x) (f:=1)
        ((ih _ (del_strict hx (mem_singleton_self x))).trans
          (factor (s:=s) (t:=cut s x) 12 (171/200) (by norm_num) (by norm_num) (by omega)))
        ((ih _ (del_strict hx (ball_self hx))).trans
          (factor 148 (29/200) (by norm_num) (by norm_num) (by omega))) (by norm_num)
      simpa only [one_mul] using k
    by_cases strong : Strong r s
    · exact (strong_gain sym irr strong ih).trans (by
        apply mul_le_of_le_one_left (show 0≤W 14 r s by unfold W; positivity)
        norm_num)
    obtain ⟨x,hx,w,hw,dx,high,ein,dw,hW,eW,either⟩ := step s sub small strong
    let u := cut s x
    have wu : w∈u := hw
    have iu : Prev 14 r u := partial_prev ih sdiff_subset
    have xskip := cost1 14 sym hx
    have xpick := costN 14 sym irr hx
    have wskip := cost1 14 sym wu
    have wpick := costN 14 sym irr wu
    change deg r u w=8 at dw
    change cross r (neighbors r u w) u≤68 at hW
    change 6≤vol r (neighbors r u w) at eW
    rw [dx] at xskip xpick
    rw [dw] at wskip wpick
    have start : W 14 r u≤(8775/10000)*W 14 r s := by
      apply factor 10 _ (by norm_num) (by norm_num)
      exact (show (10:ℤ)≤cash 14 r s-cash 14 r (cut s x) by omega)
    have endX := ih _ (del_strict hx (ball_self (r:=r) hx))
    have w1 : W 14 r (cut u w)≤(8327/10000)*W 14 r u :=
      factor 14 _ (by norm_num) (by norm_num) (by omega)
    have w2 : (mis r (u\ball r u w):ℝ)≤(1603/10000)*W 14 r u :=
      (iu _ (del_strict wu (ball_self wu))).trans (factor 140 _ (by norm_num) (by norm_num) (by omega))
    rcases either with less|after
    · have a : (mis r u:ℝ)≤(993/1000)*W 14 r u :=
        combine (x:=w) ((iu _ (del_strict wu (mem_singleton_self w))).trans w1) w2 (by norm_num)
      have b : (mis r (s\ball r s x):ℝ)≤(127/1000)*W 14 r s :=
        endX.trans (factor 158 _ (by norm_num) (by norm_num) (by omega))
      have done := combine (x:=x) (f:=1) (skip_gains (by norm_num) a start) b (by norm_num)
      simpa only [one_mul] using done
    · have child := strong_gain sym irr after (partial_prev iu sdiff_subset)
      have first : (mis r (cut u w):ℝ)≤((9976/10000)*(8327/10000))*W 14 r u :=
        skip_gains (by norm_num) child w1
      have a : (mis r u:ℝ)≤((9976/10000)*(8327/10000)+1603/10000)*W 14 r u :=
        combine (x:=w) first w2 le_rfl
      have b : (mis r (s\ball r s x):ℝ)≤(13/100)*W 14 r s :=
        endX.trans (factor 156 _ (by norm_num) (by norm_num) (by omega))
      have done := combine (x:=x) (f:=1) (skip_gains (by norm_num) a start) b (by norm_num)
      simpa only [one_mul] using done

end
end Audit.TenEightPotential
