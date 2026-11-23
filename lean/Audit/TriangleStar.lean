import Audit.TriangleEightBase

namespace Audit.TriangleStar
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleEightBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}

def skip (d : ℕ) : ℝ := if d=4 then 765/1000 else 8363/10000
def take (d j : ℕ) : ℝ := if d=4 then
    match j with
    | 0 => 240/1000 | 1 => 234/1000 | 2 => 229/1000 | _ => 224/1000
  else match j with
    | 0 => 1672/10000 | 1 => 1635/10000 | 2 => 1599/10000 | _ => 1564/10000

def coeff (d j : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => coeff d (j+1) k*skip d+take d j
theorem coeff_nonneg (d j k : ℕ) : 0≤coeff d j k := by
  induction k generalizing j with
  | zero => simp [coeff]
  | succ k ih =>
    rw [coeff]
    have a : 0≤skip d := by unfold skip; split <;> norm_num
    have b : 0≤take d j := by
      unfold take; split <;> split <;> norm_num
    exact add_nonneg (mul_nonneg (ih _) a) b

private theorem dropPair (sym : Symmetric r) (irr : Irreflexive r)
    {s : Finset V} {x y : V} {j d : ℕ} (dChoice : d=4 ∨ d=8) (jlt : j<4)
    (xs : x∈s) (hy : y∈neighbors r s x) (dy : deg r s y=d)
    (c : cap r s d) (gap : deg r s x+j≤d) :
    W r (cut s y)≤skip d*W r s ∧ W r (s\ball r s y)≤take d j*W r s := by
  have ys:=(mem_filter.mp hy).1
  have sums:=sum_one_low (reverse sym xs hy) (fun u h => c u (mem_filter.mp h).1)
  have a:=cost_single sym ys
  have b:=cost_ball sym irr ys
  rw [dy] at sums a b
  obtain rfl|rfl := dChoice
  · constructor
    · exact weight_cmp (p:=24) (by omega) (show (2:ℝ)^(-(24:ℝ)/62)≤765/1000 by tf8_numeric)
    · obtain rfl|rfl|rfl|rfl : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      · exact weight_cmp (p:=128) (by omega) (show (2:ℝ)^(-(128:ℝ)/62)≤240/1000 by tf8_numeric)
      · exact weight_cmp (p:=130) (by omega) (show (2:ℝ)^(-(130:ℝ)/62)≤234/1000 by tf8_numeric)
      · exact weight_cmp (p:=132) (by omega) (show (2:ℝ)^(-(132:ℝ)/62)≤229/1000 by tf8_numeric)
      · exact weight_cmp (p:=134) (by omega) (show (2:ℝ)^(-(134:ℝ)/62)≤224/1000 by tf8_numeric)
  · constructor
    · exact weight_cmp (p:=16) (by omega) (show (2:ℝ)^(-(16:ℝ)/62)≤8363/10000 by tf8_numeric)
    · obtain rfl|rfl|rfl|rfl : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
      · exact weight_cmp (p:=160) (by omega) (show (2:ℝ)^(-(160:ℝ)/62)≤1672/10000 by tf8_numeric)
      · exact weight_cmp (p:=162) (by omega) (show (2:ℝ)^(-(162:ℝ)/62)≤1635/10000 by tf8_numeric)
      · exact weight_cmp (p:=164) (by omega) (show (2:ℝ)^(-(164:ℝ)/62)≤1599/10000 by tf8_numeric)
      · exact weight_cmp (p:=166) (by omega) (show (2:ℝ)^(-(166:ℝ)/62)≤1564/10000 by tf8_numeric)

private theorem expand (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    {d : ℕ} (dChoice : d=4 ∨ d=8) (k j : ℕ) (s good : Finset V) (x : V)
    (xs : x∈s) (sub : good⊆neighbors r s x) (enough : k≤good.card)
    (all : ∀y∈good,deg r s y=d) (c : cap r s d) (jlim : j+k≤4) (gap : deg r s x+j≤d)
    (ih : Prev r s) (base : k=0 → (mis r s:ℝ)≤W r s) : ratio r s (coeff d j k) := by
  induction k generalizing j s good with
  | zero => simpa [ratio,coeff] using base rfl
  | succ k induction =>
    obtain ⟨y,yg⟩:=card_pos.mp (show 0<good.card by omega)
    have hy:=sub yg
    have ys:=(mem_filter.mp hy).1
    let b:=cut s y
    have xb : x∈b := mem_sdiff.mpr ⟨xs,fun eq => irr _ ((mem_singleton.mp eq) ▸ (mem_filter.mp hy).2)⟩
    have stable (z : V) (hz : z∈good.erase y) :
        z∈neighbors r b x ∧ deg r b z=d := by
      obtain ⟨ne,hg⟩ := mem_erase.mp hz
      obtain ⟨zs,xz⟩ := mem_filter.mp (sub hg)
      have notZY : ¬r z y := fun h => tri z x y (sym xz) (mem_filter.mp hy).2 h
      exact ⟨mem_filter.mpr ⟨mem_sdiff.mpr ⟨zs,fun eq => ne (mem_singleton.mp eq)⟩,xz⟩,
        (degree_cut_no notZY).trans (all z hg)⟩
    have card := card_erase_add_one yg
    have pivot:=degree_cut_yes ys (mem_filter.mp hy).2
    change deg r b x+1=deg r s x at pivot
    have h' := induction (j+1) b (good.erase y) xb (fun z hz => (stable z hz).1) (by omega)
      (fun z hz => (stable z hz).2) (cap_sub sdiff_subset c) (by omega) (by omega)
      (inheritPrev sdiff_subset ih) (fun _ => ih _ (del_strict ys (mem_singleton_self y)))
    obtain ⟨wd,wn⟩ := dropPair sym irr dChoice (j:=j) (by omega) xs hy (all y yg) c gap
    exact total (vertex_branch s y) (rescale (coeff_nonneg ..) h' wd)
      ((ih _ (del_strict ys (ball_self ys))).trans wn) le_rfl

theorem full_star (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    {s : Finset V} {x : V} {d : ℕ} (dChoice : d=4 ∨ d=8) (xs : x∈s)
    (dx : deg r s x=d) (c : cap r s d) (ih : Prev r s) : ratio r s 1 := by
  by_cases high : ∀y∈neighbors r s x,deg r s y=d
  · have enough : 4≤(neighbors r s x).card := by change 4≤deg r s x; omega
    have result := expand sym irr tri dChoice 4 0 s (neighbors r s x) x xs
      (Finset.Subset.refl _) enough high c (by omega) (by omega) ih (by omega)
    exact relax (by rcases dChoice with rfl|rfl <;> norm_num [coeff,skip,take]) result
  · push_neg at high
    obtain ⟨y,hy,deficit⟩:=high
    have ys:=(mem_filter.mp hy).1
    have cy:=c y ys
    obtain ⟨wd,wn⟩ := dropPair sym irr dChoice (j:=1) (by omega) ys (reverse sym xs hy) dx c (by omega)
    exact total (vertex_branch s x) ((ih _ (del_strict xs (mem_singleton_self x))).trans wd)
      ((ih _ (del_strict xs (ball_self xs))).trans wn)
      (by rcases dChoice with rfl|rfl <;> norm_num [skip,take])

end
end Audit.TriangleStar
