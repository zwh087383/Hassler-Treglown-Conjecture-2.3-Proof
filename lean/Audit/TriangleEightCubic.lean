import Audit.TriangleCubic
import Audit.TriangleEightBase

namespace Audit.TriangleEightCubic
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleCubic TriangleEightBase
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s : Finset V} {x y z : V}

/-- In maximum degree two, a path with at least three vertices gives extra room
    even when other components are arbitrary. -/
theorem path (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (xs : x∈s) (hy : y∈neighbors r s x) (dx : deg r s x=1) (dy : deg r s y=2)
    (c : cap r s 2) (ih : Prev r s) : ratio r s (17/20) := by
  have ys := (mem_filter.mp hy).1
  have xy := (mem_filter.mp hy).2
  obtain ⟨p,px,hp⟩ := second_neighbor dy (reverse sym xs hy)
  obtain ⟨ps,yp⟩ := mem_filter.mp hp
  have py : p≠y := fun e => irr y (e ▸ yp)
  have noPX : ¬r p x := fun h => tri x y p xy yp (sym h)
  let a:=s\ball r s x
  let b:=s\ball r s y
  have strictA : a ⊂ s := del_strict xs (ball_self xs)
  have strictB : b ⊂ s := del_strict ys (ball_self ys)
  have pA : p∈a := mem_sdiff.mpr ⟨ps,fun hh =>
    ((mem_closed.mp hh).2).elim px noPX⟩
  have loses := leaf_cost sym irr xs hy dx c
  rw [dy] at loses
  have da : W r a ≤ (13/25)*W r s :=
    weight_cmp (p:=60) (by dsimp only [a]; omega) (by tf8_numeric)
  have db : W r b ≤ (11/30)*W r s :=
    weight_cmp (p:=90) (by dsimp only [b]; omega) (by tf8_numeric)
  have range := c p ps
  have pp : 0<deg r s p := card_pos.mpr ⟨y,reverse sym ys hp⟩
  by_cases dp : deg r s p=1
  · have pa := isolated_after dp (reverse sym ys hp) (mem_closed.mpr ⟨ys,Or.inr (sym xy)⟩ : y∈ball r s x)
    have a0 := iso sym pA pa (inheritPrev sdiff_subset ih)
    exact total (leaf_branch sym irr xs dx hy)
      (rescale (by norm_num) a0 da) ((ih _ strictB).trans db) (by norm_num)
  · have p2 : deg r s p=2 := by omega
    obtain ⟨q,qy,hq⟩ := second_neighbor p2 (reverse sym ys hp)
    obtain ⟨qs,pq⟩ := mem_filter.mp hq
    have qp : q≠p := fun e => irr p (e ▸ pq)
    have notQY : ¬r q y := fun h => tri y p q yp pq (sym h)
    have qx : q≠x := fun e => noPX (e ▸ pq)
    have nxq : ¬r x q := fun h => qy (by
      have he : q∈neighbors r s x := mem_filter.mpr ⟨qs,h⟩
      simpa only [leaf_eq dx hy,mem_singleton] using he)
    have qA : q∈a := mem_sdiff.mpr ⟨qs,fun hh => (mem_closed.mp hh).2.elim qx (fun h => nxq (sym h))⟩
    have qB : q∈b := mem_sdiff.mpr ⟨qs,fun hh => (mem_closed.mp hh).2.elim qy notQY⟩
    by_cases dq : deg r s q=1
    · have pb : p∈ball r s y := mem_closed.mpr ⟨ps,Or.inr (sym yp)⟩
      have after := isolated_after dq (reverse sym ps hq) pb
      have red := iso sym qB after (inheritPrev sdiff_subset ih)
      exact total (leaf_branch sym irr xs dx hy)
        ((ih _ strictA).trans da) (rescale (by norm_num) red db) (by norm_num)
    · have dqp : 0<deg r s q := card_pos.mpr ⟨p,reverse sym ps hq⟩
      have dqr := c q qs
      have dQ : deg r a q=2 := by
        dsimp only [a]
        rw [leaf_pair sym xs dx hy,degree_cut_no notQY,degree_cut_no (fun h => nxq (sym h))]
        omega
      have dP : deg r a p=1 := by
        have yA : y∈cut s x := mem_sdiff.mpr ⟨ys,fun h => irr _ ((mem_singleton.mp h) ▸ xy)⟩
        have tmp:=degree_cut_yes (x:=p) yA (sym yp)
        rw [degree_cut_no noPX] at tmp
        rw [←leaf_pair sym xs dx hy] at tmp
        change deg r a p+1=deg r s p at tmp
        omega
      have capA : cap r a 3 := fun u hu => (mono (sdiff_subset : a⊆s) u).trans
        ((c u (mem_sdiff.mp hu).1).trans (by decide))
      have red := small_leaf sym irr pA (mem_filter.mpr ⟨qA,pq⟩ : q∈neighbors r a p) dP dQ.ge capA
        (inheritPrev sdiff_subset ih)
      exact total (leaf_branch sym irr xs dx hy)
        (rescale (by norm_num) red da) ((ih _ strictB).trans db) (by norm_num)

theorem mixed_case (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (xs : x∈s) (hy : y∈neighbors r s x) (dx : deg r s x=2) (dy : deg r s y=3)
    (floor : ∀ u∈s, 2≤deg r s u) (c : cap r s 3) (ih : Prev r s) :
    (g : ℝ) → (9/10≤g ∨ (81/100≤g ∧ ∀z∈neighbors r s x,deg r s z=3)) →
    ratio r s (g*(3/4)+3/10) := by
  intro g criterion
  have ys := (mem_filter.mp hy).1
  have xy := (mem_filter.mp hy).2
  obtain ⟨u,uy,hu⟩ := second_neighbor dx hy
  obtain ⟨us,xu⟩ := mem_filter.mp hu
  have notUY : ¬r u y := fun h => tri u x y (sym xu) xy h
  let a:=cut s y
  have xa : x∈a := mem_sdiff.mpr ⟨xs,fun h => irr _ ((mem_singleton.mp h) ▸ xy)⟩
  have ua : u∈a := mem_sdiff.mpr ⟨us,fun h => uy (mem_singleton.mp h)⟩
  have diff:=degree_cut_yes ys xy
  have dx' : deg r a x=1 := by change deg r a x+1=_ at diff; omega
  have du' : 2≤deg r a u := by rw [show deg r a u=deg r s u from degree_cut_no notUY]; exact floor u us
  have hu' : u∈neighbors r a x := mem_filter.mpr ⟨ua,xu⟩
  have gp : 0≤g := by rcases criterion with big|⟨big,_⟩ <;> linarith
  have boost : ratio r a g := by
    rcases criterion with big|⟨big,degrees⟩
    · exact relax big (small_leaf sym irr xa hu' dx' du' (cap_sub sdiff_subset c) (inheritPrev sdiff_subset ih))
    · have d3 : deg r a u=3 := (degree_cut_no notUY).trans (degrees u hu)
      exact relax big (leaf3 sym irr xa hu' dx' d3 (cap_sub sdiff_subset c) (inheritPrev sdiff_subset ih))
  have l := cost_single sym ys
  have costB := cost_ball sym irr ys
  have nbSum := sum_one_low (reverse sym xs hy) (fun u h => c u (mem_filter.mp h).1)
  rw [dx,dy] at nbSum
  rw [dy] at l costB
  exact total (vertex_branch s y)
    (rescale gp boost (weight_cmp (p:=26) (q:=3/4) (by omega) (by tf8_numeric)))
    (scaled (p:=112) (by omega) (q:=3/10) (by tf8_numeric) (ih _ (del_strict ys (ball_self ys)))) (by norm_num)

theorem cubic_case (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (xs : x∈s) (dx : deg r s x=3) (floor : ∀ u∈s, 2≤deg r s u)
    (c : cap r s 3) (noMix : ∀ u∈s, ∀ v∈neighbors r s u, deg r s u=3 → deg r s v≠2)
    (ih : Prev r s) : ratio r s 1 := by
  obtain ⟨y,hy⟩ := card_pos.mp (show 0<deg r s x by omega)
  obtain ⟨ys,xy⟩ := mem_filter.mp hy
  have same (u : V) (us : u∈s) (u3 : deg r s u=3) (v : V) (hv : v∈neighbors r s u) :
      deg r s v=3 := by
    have a:=floor v (mem_filter.mp hv).1
    have b:=c v (mem_filter.mp hv).1
    have h:=noMix u us v hv u3
    omega
  have dy:=same x xs dx y hy
  let a:=cut s x
  have ya : y∈a := mem_sdiff.mpr ⟨ys,fun h => irr _ ((mem_singleton.mp h) ▸ xy)⟩
  have dyCut:=degree_cut_yes xs (sym xy)
  have dya : deg r a y=2 := by change deg r a y+1=_ at dyCut; omega
  obtain ⟨z,hz⟩ := card_pos.mp (show 0<deg r a y by omega)
  obtain ⟨za,yz⟩ := mem_filter.mp hz
  have zs : z∈s := (mem_sdiff.mp za).1
  have noZX : ¬r z x := fun h => tri x y z xy yz (sym h)
  have dza : deg r a z=3 := (degree_cut_no noZX).trans (same y ys dy z (mem_filter.mpr ⟨zs,yz⟩))
  have floorA (u : V) (hu : u∈a) : 2≤deg r a u := by
    have us := (mem_sdiff.mp hu).1
    by_cases ux : r u x
    · have du := same x xs dx u (mem_filter.mpr ⟨us,sym ux⟩)
      have d' := degree_cut_yes xs ux
      change deg r a u+1=_ at d'
      omega
    · rw [show deg r a u=deg r s u from degree_cut_no ux]
      exact floor u us
  have every (z : V) (hz : z∈neighbors r a y) : deg r a z=3 := by
    obtain ⟨za,yz⟩:=mem_filter.mp hz
    have none : ¬r z x := fun h => tri x y z xy yz (sym h)
    exact (degree_cut_no none).trans (same y ys dy z (mem_filter.mpr ⟨(mem_sdiff.mp za).1,yz⟩))
  have boost := mixed_case sym irr tri ya hz dya dza floorA (cap_sub sdiff_subset c) (inheritPrev sdiff_subset ih) (81/100) (Or.inr ⟨le_rfl,every⟩)
  have l:=cost_single sym xs
  have h:=cost_ball sym irr xs
  have dsum:=adjacent_sum c dx
  rw [dx] at l h
  exact total (vertex_branch s x)
    (rescale (by norm_num) boost (weight_cmp (p:=26) (q:=3/4) (by omega) (by tf8_numeric)))
    (scaled (p:=110) (by omega) (q:=3/10) (by tf8_numeric) (ih _ (del_strict xs (ball_self xs)))) (by norm_num)

theorem cycles (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (xs : x∈s) (all : ∀ u∈s,deg r s u=2) (ih : Prev r s) : ratio r s 1 := by
  have dx:=all x xs
  obtain ⟨y,hy⟩ := card_pos.mp (show 0<deg r s x by omega)
  obtain ⟨ys,xy⟩ := mem_filter.mp hy
  have dy:=all y ys
  obtain ⟨z,zx,hz⟩ := second_neighbor dy (reverse sym xs hy)
  obtain ⟨zs,yz⟩ := mem_filter.mp hz
  let a:=cut s x
  have ya : y∈a := mem_sdiff.mpr ⟨ys,fun h => irr _ ((mem_singleton.mp h) ▸ xy)⟩
  have za : z∈a := mem_sdiff.mpr ⟨zs,fun h => zx (mem_singleton.mp h)⟩
  have d1:=degree_cut_yes xs (sym xy)
  have dya : deg r a y=1 := by change deg r a y+1=_ at d1; omega
  have dza : deg r a z=2 := (degree_cut_no (fun h => tri x y z xy yz (sym h))).trans (all z zs)
  have c : cap r s 2 := fun u hu => (all u hu).le
  have stronger := path sym irr tri ya (mem_filter.mpr ⟨za,yz⟩ : z∈neighbors r a y) dya dza
    (cap_sub sdiff_subset c) (inheritPrev sdiff_subset ih)
  have l:=cost_single sym xs
  have h:=cost_ball sym irr xs
  have dsum:=adjacent_sum c dx
  rw [dx] at l h
  exact total (vertex_branch s x)
    (rescale (by norm_num) stronger (weight_cmp (p:=28) (q:=11/15) (by omega) (by tf8_numeric)))
    (scaled (p:=88) (by omega) (q:=3/8) (by tf8_numeric) (ih _ (del_strict xs (ball_self xs)))) (by norm_num)

end
end Audit.TriangleEightCubic
