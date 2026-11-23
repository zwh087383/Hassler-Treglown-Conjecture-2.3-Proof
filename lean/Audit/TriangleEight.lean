import Audit.TriangleEightCubic
import Audit.TriangleStar

namespace Audit.TriangleEight
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleEightBase TriangleEightCubic TriangleStar
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t : Finset V} {x : V}

private theorem middle (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) (d : ℕ)
    (eq : deg r s x=d) (range : d=5 ∨ d=6 ∨ d=7) (c : cap r s d) (ih : Prev r s) :
    ratio r s 1 := by
  have a:=cost_single sym xs
  have b:=cost_ball sym irr xs
  have ns:=adjacent_sum c eq
  rw [eq] at a b
  have l:=ih _ (del_strict xs (mem_singleton_self x))
  have rr:=ih _ (del_strict xs (ball_self (r:=r) xs))
  rcases range with rfl|rfl|rfl
  · exact total (vertex_branch s x)
      (scaled (p:=22) (by omega) (q:=79/100) (by tf8_numeric) l)
      (scaled (p:=142) (by omega) (q:=21/100) (by tf8_numeric) rr) (by norm_num)
  · exact total (vertex_branch s x)
      (scaled (p:=20) (by omega) (q:=81/100) (by tf8_numeric) l)
      (scaled (p:=152) (by omega) (q:=19/100) (by tf8_numeric) rr) (by norm_num)
  · exact total (vertex_branch s x)
      (scaled (p:=18) (by omega) (q:=41/50) (by tf8_numeric) l)
      (scaled (p:=158) (by omega) (q:=9/50) (by tf8_numeric) rr) (by norm_num)

theorem eight (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (maxdeg : cap r s 8) : (mis r s:ℝ)≤W r s := by
  induction s using Finset.strongInduction with
  | H s smaller =>
    have ih : Prev r s := fun t ht => smaller t ht (cap_sub (Finset.ssubset_iff_subset_ne.mp ht).1 maxdeg)
    suffices h : ratio r s 1 by simpa only [ratio,one_mul] using h
    by_cases empty : s=∅
    · subst s
      simpa [ratio,W,budget,cost,cross] using hujter_tuza sym irr tri (∅ : Finset V)
    obtain ⟨v,vs,highest⟩ := s.exists_max_image (deg r s) (Finset.nonempty_iff_ne_empty.mpr empty)
    let d:=deg r s v
    have capD : cap r s d := highest
    have dv : deg r s v=d := rfl
    have hi : d≤8 := maxdeg v vs
    by_cases four : 4≤d
    · by_cases ex : d=4 ∨ d=8
      · exact full_star sym irr tri ex vs dv capD ih
      · exact middle sym irr vs d dv (by omega) capD ih
    have cubicCap : cap r s 3 := fun x hx => (capD x hx).trans (by omega)
    by_cases zero : ∃x∈s,deg r s x=0
    · obtain ⟨x,xs,dx⟩:=zero
      exact relax (by norm_num) (iso sym xs dx ih)
    by_cases one : ∃x∈s,deg r s x=1
    · obtain ⟨x,xs,dx⟩:=one
      obtain ⟨y,hy⟩ := card_pos.mp (show 0<deg r s x by omega)
      have ys := (mem_filter.mp hy).1
      by_cases dy : deg r s y=1
      · exact pair sym irr xs hy dx dy ih
      have yz : deg r s y≠0 := fun h => zero ⟨y,ys,h⟩
      exact relax (by norm_num) (small_leaf sym irr xs hy dx (by omega) cubicCap ih)
    have low (u : V) (hu : u∈s) : 2≤deg r s u := by
      have a : deg r s u≠0 := fun h => zero ⟨u,hu,h⟩
      have b : deg r s u≠1 := fun h => one ⟨u,hu,h⟩
      omega
    by_cases mix : ∃u∈s,∃w∈neighbors r s u,deg r s u=3 ∧ deg r s w=2
    · obtain ⟨u,us,w,hw,du,dw⟩:=mix
      exact relax (by norm_num) (mixed_case sym irr tri (mem_filter.mp hw).1 (reverse sym us hw)
        dw du low cubicCap ih (9/10) (Or.inl le_rfl))
    by_cases three : ∃u∈s,deg r s u=3
    · obtain ⟨u,us,du⟩:=three
      exact cubic_case sym irr tri us du low cubicCap (fun a ha b hb da db => mix ⟨a,ha,b,hb,da,db⟩) ih
    apply cycles sym irr tri vs _ ih
    intro u hu
    have a:=low u hu
    have b:=cubicCap u hu
    have c : deg r s u≠3 := fun h => three ⟨u,hu,h⟩
    omega

theorem quarter (avg : 15*s.card≤2*vol r s) : W r s≤(3:ℝ)^((s.card:ℝ)/4) := by
  have bound : (2:ℝ)^((49:ℝ)/124)≤(3:ℝ)^((1:ℝ)/4) := by
    by_contra! bad
    have absurd := pow_lt_pow_left₀ bad (n:=124) (Real.rpow_nonneg (by norm_num) _) (by decide)
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),←Real.rpow_natCast,←Real.rpow_mul (by norm_num)] at absurd
    norm_num at absurd
  have result:=Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) bound (Nat.cast_nonneg (α:=ℝ) s.card)
  rw [←Real.rpow_mul (by norm_num),←Real.rpow_mul (by norm_num)] at result
  rw [show 1/4*(s.card:ℝ)=s.card/4 by ring] at result
  have av : (15:ℝ)*s.card≤2*vol r s := by exact_mod_cast avg
  apply le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _) result
  change (budget r s:ℝ)/62≤_
  unfold budget cost
  push_cast
  linarith

theorem dense (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (maxdeg : cap r s 8) (avg : 15*s.card≤2*vol r s) :
    (mis r s:ℝ)≤(3:ℝ)^((s.card:ℝ)/4) := (eight sym irr tri s maxdeg).trans (quarter avg)

/-- The degree-nine hypothesis is hereditary since a surviving vertex of degree
    nine has retained its full original neighborhood. -/
def NineRule (r : V → V → Prop) (s : Finset V) : Prop :=
  ∀x∈s,deg r s x=9 → cross r (neighbors r s x) s≤73

theorem hereditary (h : NineRule r s) (c : cap r s 9) (sub : t⊆s) : NineRule r t := by
  intro x xt dx
  have da:=mono (r:=r) sub x
  have ds:=c x (sub xt)
  have d : deg r s x=9 := by omega
  have eq : neighbors r t x=neighbors r s x := eq_of_subset_of_card_le (filter_subset_filter _ sub)
    (by change deg r s x≤deg r t x; omega)
  rw [eq]
  exact (sum_le_sum (fun u _ => mono (r:=r) sub u)).trans (h x (sub xt) d)

theorem nine (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (c : cap r s 9) (h : NineRule r s) : (mis r s:ℝ)≤W r s := by
  induction s using Finset.strongInduction with
  | H s prev =>
    have ih : Prev r s := fun t ht => prev t ht (cap_sub (Finset.ssubset_iff_subset_ne.mp ht).1 c)
      (hereditary h c (Finset.ssubset_iff_subset_ne.mp ht).1)
    by_cases low : cap r s 8
    · exact eight sym irr tri s low
    unfold cap at low
    push_neg at low
    obtain ⟨x,hx,dx⟩:=low
    have c' := c x hx
    have d : deg r s x=9 := by omega
    have sum := h x hx d
    have a:=cost_single sym hx
    have b:=cost_ball sym irr hx
    rw [d] at a b
    have result : ratio r s 1 := total (vertex_branch s x)
      (scaled (p:=14) (by omega) (q:=107/125) (by tf8_numeric) (ih _ (del_strict hx (mem_singleton_self x))))
      (scaled (p:=174) (by omega) (q:=18/125) (by tf8_numeric) (ih _ (del_strict hx (ball_self hx)))) (by norm_num)
    simpa only [ratio,one_mul] using result

theorem capNine (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (c : cap r s 9) (h : NineRule r s) (avg : 15*s.card≤2*vol r s) :
    (mis r s:ℝ)≤(3:ℝ)^((s.card:ℝ)/4) := (nine sym irr tri s c h).trans (quarter avg)

end
end Audit.TriangleEight
