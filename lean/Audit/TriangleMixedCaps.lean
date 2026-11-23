import Audit.TriangleExceptional

namespace Audit.TriangleMixedCaps
open Finset Sumfree Fingerprint TriangleBase TriangleExceptional
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}

def HighNeighbors (r : V → V → Prop) (g : Finset V) (k : ℕ) : Prop :=
  ∀x∈g, 9<deg r g x → ((neighbors r g x).filter fun y => 9<deg r g y).card≤k
def Inner (r : V → V → Prop) (g : Finset V) (D E : ℕ) : Prop :=
  ∀x∈g, deg r g x=D → E≤vol r (neighbors r g x)

theorem twelve_nine (sym : Symmetric r) (irr : Irreflexive r)
    (g : Finset V) (c : cap r g 12) (neighborsBound : HighNeighbors r g 6)
    (av : 21*g.card≤2*vol r g) : (mis r g:ℝ)≤(3:ℝ)^((g.card:ℝ)/4) := by
  suffices bound : ∀ s⊆g,(mis r s:ℝ)≤W 17 r s from (bound g (Finset.Subset.refl _)).trans (quarter (by decide) av)
  intro s
  induction s using Finset.strongInduction with
  | H s prev =>
    intro sub
    have ih : Prev 17 r s := fun t ht => prev t ht ((Finset.ssubset_iff_subset_ne.mp ht).1.trans sub)
    by_cases small : cap r s 9
    · exact weighted_base (D:=9) (l:=12) sym irr (by decide) (by decide) (by native_decide) s small
    unfold cap at small
    push_neg at small
    obtain ⟨u,hu,du⟩:=small
    obtain ⟨x,hx,maximal⟩:=s.exists_max_image (deg r s) ⟨u,hu⟩
    let d:=deg r s x
    have lo : 10≤d := du.trans_le (maximal u hu)
    have upper : d≤12 := (mono sub x).trans (c x (sub hx))
    have high := neighborsBound x (sub hx) (du.trans_le ((maximal u hu).trans (mono sub x)))
    have sum := profile_sum sub (d:=d) (by omega) maximal rfl high
    have a:=cost1 17 sym hx
    have b:=costN 17 sym irr hx
    change 2*((17:ℤ)+1)-2*(d:ℤ)≤_ at a
    change 2*((17:ℤ)+1)*((d:ℤ)+1)-2*cross r (neighbors r s x) s+vol r (neighbors r s x)≤_ at b
    have p : (12:ℤ)≤cash 17 r s-cash 17 r (TriangleBase.cut s x) := by omega
    have q : (204:ℤ)≤cash 17 r s-cash 17 r (s\ball r s x) := by omega
    have h1 := scale (p:=12) (f:=8/9) (by decide) p (by
      simpa only [Nat.cast_ofNat,show (6:ℝ)*17=102 by norm_num] using Potential.neg_weight 12 102 (8/9) (by decide) (by norm_num) (by norm_num))
    have h2 := scale (p:=204) (f:=1/9) (by decide) q (by norm_num)
    have result := combine ((ih _ (del_strict hx (mem_singleton_self x))).trans h1)
      ((ih _ (del_strict hx (ball_self hx))).trans h2) (show (8/9:ℝ)+1/9≤1 by norm_num)
    simpa only [one_mul] using result

theorem ten_nine (sym : Symmetric r) (irr : Irreflexive r)
    (g : Finset V) (c : cap r g 10) (neighborsBound : HighNeighbors r g 5)
    (internal : Inner r g 10 4) (av : 19*g.card≤2*vol r g) :
    (mis r g:ℝ)≤(3:ℝ)^((g.card:ℝ)/4) := by
  suffices bound : ∀ s⊆g,(mis r s:ℝ)≤W 15 r s from (bound g (Finset.Subset.refl _)).trans (quarter (by decide) av)
  intro s
  induction s using Finset.strongInduction with
  | H s prev =>
    intro sub
    have ih : Prev 15 r s := fun t ht => prev t ht ((Finset.ssubset_iff_subset_ne.mp ht).1.trans sub)
    by_cases small : cap r s 9
    · exact weighted_base (D:=9) (l:=10) sym irr (by decide) (by decide) (by native_decide) s small
    unfold cap at small
    push_neg at small
    obtain ⟨x,hx,dx⟩:=small
    have cs : cap r s 10 := cap_sub sub c
    have d : deg r s x=10 := by have := cs x hx; omega
    have f := full_neighbors sub c hx d
    have dd : deg r g x=10 := by change (neighbors r g x).card=10; rw [←f]; exact d
    have ins := internal x (sub hx) dd
    rw [←f] at ins
    have hs := neighborsBound x (sub hx) (by omega)
    have sum:=profile_sum sub (by decide : 9≤10) cs d hs
    have a:=cost1 15 sym hx
    have b:=costN 15 sym irr hx
    rw [d] at a b
    have p : (12:ℤ)≤cash 15 r s-cash 15 r (cut s x) := by omega
    have q : (166:ℤ)≤cash 15 r s-cash 15 r (s\ball r s x) := by omega
    have h1 := scale (p:=12) (f:=13/15) (by decide) p (by
      simpa only [Nat.cast_ofNat,show (6:ℝ)*15=90 by norm_num] using Potential.neg_weight 12 90 (13/15) (by decide) (by norm_num) (by norm_num))
    have h2 := scale (p:=166) (f:=2/15) (by decide) q (by
      simpa only [Nat.cast_ofNat,show (6:ℝ)*15=90 by norm_num] using Potential.neg_weight 166 90 (2/15) (by decide) (by norm_num) (by norm_num))
    have result := combine ((ih _ (del_strict hx (mem_singleton_self x))).trans h1)
      ((ih _ (del_strict hx (ball_self hx))).trans h2) (show (13/15:ℝ)+2/15≤1 by norm_num)
    simpa only [one_mul] using result

end
end Audit.TriangleMixedCaps
