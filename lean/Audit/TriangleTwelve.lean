import Audit.TriangleLarge

namespace Audit.TriangleTwelve
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleParam TriangleLarge
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t : Finset V} {x : V}

private theorem decay12 (p : ℕ) (q : ℝ) (pos : 0<q) (cert : 1≤(2:ℝ)^p*q^154)
    (loss : (p:ℤ)≤price 12 r s-price 12 r t) : W 12 r t≤q*W 12 r s := by
  apply decay (a:=(p:ℝ)/154) (by norm_num [denom])
  · norm_num [denom]
    exact_mod_cast loss
  · simpa only [neg_div,Nat.cast_ofNat] using scalar p 154 q (by decide) pos cert

private theorem stage (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s)
    (dx : deg r s x=12) (j : ℕ) (cutEdges : cross r (neighbors r s x) s+j≤144)
    (f q : ℝ) (fpos : 0≤f) (qpos : 0<q) (cert : 1≤(2:ℝ)^(451+4*j)*q^154)
    (left : (mis r (cut s x):ℝ)≤f*W 12 r (cut s x))
    (right : (mis r (s\ball r s x):ℝ)≤W 12 r (s\ball r s x)) :
    (mis r s:ℝ)≤(f*(87/100)+q)*W 12 r s := by
  have a:=single 12 sym xs
  have b:=TriangleParam.closed 12 sym irr xs
  rw [dx] at a b
  have wd := decay12 31 (87/100) (by norm_num) (by norm_num) (by omega : (31:ℤ)≤price 12 r s-price 12 r (cut s x))
  have wn := decay12 (451+4*j) q qpos cert (by omega : _≤price 12 r s-price 12 r (s\ball r s x))
  have l : (mis r (cut s x):ℝ) ≤ (f*(87/100))*W 12 r s := by
    apply left.trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left wd fpos
  rw [add_mul]
  exact (show (mis r s:ℝ)≤mis r (cut s x)+mis r (s\ball r s x) by exact_mod_cast vertex_branch s x).trans
    (add_le_add l (right.trans wn))

private theorem inh {s t : Finset V} (ih : allSmaller 12 r s) (sub : t⊆s) : allSmaller 12 r t :=
  fun l h => ih l (Finset.ssubset_of_ssubset_of_subset h sub)

private theorem regular_step (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (xs : x∈s) (dx : deg r s x=12) (high : ∀y∈neighbors r s x,deg r s y=12)
    (cap12 : cap r s 12) (ih : allSmaller 12 r s) : (mis r s:ℝ)≤W 12 r s := by
  let n:=neighbors r s x
  have size : n.card=12 := dx
  obtain ⟨u,hu⟩:=card_pos.mp (show 0<n.card by omega)
  have n' := card_erase_add_one hu
  obtain ⟨v,hv⟩:=card_pos.mp (show 0<(n.erase u).card by omega)
  have n'' := card_erase_add_one hv
  obtain ⟨w,hw⟩:=card_pos.mp (show 0<((n.erase u).erase v).card by omega)
  obtain ⟨vu,vx⟩:=mem_erase.mp hv
  obtain ⟨wv,wn'⟩:=mem_erase.mp hw
  obtain ⟨wu,wx⟩:=mem_erase.mp wn'
  have separated (a b : V) (ha : a∈n) (hb : b∈n) : ¬r a b :=
    fun h => tri a x b (sym (mem_filter.mp ha).2) (mem_filter.mp hb).2 h
  have outside (a : V) (ha : a∈n) : x≠a := fun eq => irr _ (eq ▸ (mem_filter.mp ha).2)
  have kept {z u : V} {ss : Finset V} (h : z∈ss) (ne : z≠u) : z∈cut ss u :=
    mem_sdiff.mpr ⟨h,fun e => ne (mem_singleton.mp e)⟩
  let s1:=cut s u
  let s2:=cut s1 v
  let s3:=cut s2 w
  have us:=(mem_filter.mp hu).1
  have v1 : v∈s1 := kept (mem_filter.mp vx).1 vu
  have w2 : w∈s2 := kept (kept (mem_filter.mp wx).1 wu) wv
  have x1 : x∈s1 := kept xs (outside _ hu)
  have x2 : x∈s2 := kept x1 (outside _ vx)
  have xs1 := degree_cut_yes us (mem_filter.mp hu).2
  change deg r s1 x+1=deg r s x at xs1
  have xs2 := degree_cut_yes v1 (mem_filter.mp vx).2
  change deg r s2 x+1=deg r s1 x at xs2
  have vdeg : deg r s1 v=12 := (degree_cut_no (separated _ _ vx hu)).trans (high _ vx)
  have wdeg : deg r s2 w=12 :=
    (degree_cut_no (separated _ _ wx vx)).trans ((degree_cut_no (separated _ _ wx hu)).trans (high _ wx))
  have c1 : cap r s1 12 := cap_sub sdiff_subset cap12
  have c2 : cap r s2 12 := cap_sub sdiff_subset c1
  have e2 := sum_one_low (mem_filter.mpr ⟨x2,sym (mem_filter.mp wx).2⟩ : x∈neighbors r s2 w)
    (fun z h => c2 z (mem_filter.mp h).1)
  have e1 := sum_one_low (mem_filter.mpr ⟨x1,sym (mem_filter.mp vx).2⟩ : x∈neighbors r s1 v)
    (fun z h => c1 z (mem_filter.mp h).1)
  rw [vdeg] at e1
  rw [wdeg] at e2
  have ih1 : allSmaller 12 r s1 := inh ih sdiff_subset
  have ih2 : allSmaller 12 r s2 := inh ih1 sdiff_subset
  have last : (mis r s3:ℝ) ≤ 1*W 12 r s3 := by
    rw [one_mul]; exact ih2 _ (del_strict w2 (mem_singleton_self w))
  have b2 := stage sym irr w2 wdeg 2 (by omega) 1 (127/1000) (by norm_num) (by norm_num)
    (by norm_num) last (ih2 _ (del_strict w2 (ball_self w2)))
  have b1 := stage sym irr v1 vdeg 1 (by omega) _ (13/100) (by norm_num) (by norm_num)
    (by norm_num) b2 (ih1 _ (del_strict v1 (ball_self v1)))
  have e0:=adjacent_sum cap12 (high u hu)
  have b0 := stage sym irr us (high u hu) 0 (by omega) _ (33/250) (by norm_num) (by norm_num)
    (by norm_num) b1 (ih _ (del_strict us (ball_self us)))
  exact b0.trans ((mul_le_mul_of_nonneg_right (by norm_num : (((1:ℝ)*(87/100)+127/1000)*(87/100)+13/100)*
    (87/100)+33/250≤1) (by unfold W; positivity)).trans_eq (one_mul _))

theorem twelve (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (c : cap r s 12) : (mis r s:ℝ)≤W 12 r s := by
  induction s using Finset.strongInduction with
  | H s smaller =>
    have ih : allSmaller 12 r s := fun t ht => smaller t ht (cap_sub (Finset.ssubset_iff_subset_ne.mp ht).1 c)
    by_cases low : cap r s 10
    · exact using_ten sym irr tri (by decide) low ih
    unfold cap at low
    push_neg at low
    obtain ⟨z,hz,dz⟩:=low
    obtain ⟨x,xs,maximal⟩:=s.exists_max_image (deg r s) ⟨z,hz⟩
    have cx:=c x xs
    have cmp:=maximal z hz
    by_cases eleven : deg r s x=11
    · exact plain sym irr xs _ rfl maximal cx (Or.inr ⟨rfl,eleven⟩) ih
    have dx : deg r s x=12 := by omega
    by_cases all : ∀y∈neighbors r s x,deg r s y=12
    · exact regular_step sym irr tri xs dx all c ih
    push_neg at all
    obtain ⟨y,hy,lowy⟩:=all
    have cy:=c y (mem_filter.mp hy).1
    have edges:=sum_one_low hy (fun z h => c z (mem_filter.mp h).1)
    rw [dx] at edges
    have a : (mis r (cut s x):ℝ) ≤ 1*W 12 r (cut s x) := by
      rw [one_mul]; exact ih _ (del_strict xs (mem_singleton_self x))
    have result := stage sym irr xs dx 1 (by omega) 1 (13/100) (by norm_num) (by norm_num) (by norm_num)
      a (ih _ (del_strict xs (ball_self xs)))
    norm_num at result; exact result

theorem dense (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r) {D : ℕ}
    (above : 12≤D) (s : Finset V) (c : cap r s D) (avg : 3*D*s.card≤4*vol r s) :
    (mis r s:ℝ) ≤ (3:ℝ)^((s.card:ℝ)/4) := by
  by_cases eq : D=12
  · subst D; exact (twelve sym irr tri s c).trans (to_quarter above avg)
  · exact TriangleLarge.dense sym irr tri (by omega) s c avg

end
end Audit.TriangleTwelve
