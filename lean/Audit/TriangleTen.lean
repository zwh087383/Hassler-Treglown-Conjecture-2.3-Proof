import Audit.TriangleCubic

namespace Audit.TriangleTen
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleCubic
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}

private theorem factors (d : ℕ) (lo : 4≤d) (hi : d≤10) :
    ∃ i j : ℕ, ∃ a b : ℝ, (i:ℤ)≤37-2*d ∧ (j:ℤ)≤37*((d:ℤ)+1)-2*(d*d:ℕ) ∧
    (2:ℝ)^(-(i:ℝ)/72)≤a ∧ (2:ℝ)^(-(j:ℝ)/72)≤b ∧ a+b≤1 := by
  obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl : d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 := by omega
  · refine ⟨29,153,760/1000,240/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩
  · refine ⟨27,172,780/1000,220/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩
  · refine ⟨25,187,790/1000,210/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩
  · refine ⟨23,198,805/1000,195/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩
  · refine ⟨21,205,820/1000,180/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩
  · refine ⟨19,208,840/1000,160/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩
  · refine ⟨17,207,850/1000,150/1000,by norm_num,by norm_num,by tf_numeric,by tf_numeric,by norm_num⟩

theorem ten (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (maxdeg : cap r s 10) : (mis r s:ℝ)≤weight r s := by
  classical
  induction s using Finset.strongInduction with
  | H s smaller =>
    have ih : IH r s := fun t ht => smaller t ht (cap_sub (Finset.ssubset_iff_subset_ne.mp ht).1 maxdeg)
    suffices h : rel r s 1 by simpa only [rel,one_mul] using h
    by_cases empty : s=∅
    · subst s
      have h := hujter_tuza sym irr tri (∅ : Finset V)
      simpa [rel,weight,cost,cross] using h
    have ne := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨v,vs,highest⟩ := s.exists_max_image (deg r s) ne
    let d:=deg r s v
    have capD : cap r s d := highest
    by_cases four : 4≤d
    · obtain ⟨i,j,a,b,ia,jb,pa,pb,sum⟩ := factors d four (maxdeg v vs)
      have l := single_loss sym vs
      have h := closed_loss sym irr vs
      have ns := adjacent_sum (x:=v) capD rfl
      change _≤ d*d at ns
      change 37-2*(d:ℤ)≤_ at l
      change 37*((d:ℤ)+1)-2*cross r (neighbors r s v) s≤_ at h
      exact add_children (vertex_branch s v)
        (scale (ia.trans l) pa (ih _ (del_strict vs (mem_singleton_self v))))
        (scale (by omega : (j:ℤ)≤_) pb (ih _ (del_strict vs (ball_self vs)))) sum
    have cubicCap : cap r s 3 := fun x hx => (capD x hx).trans (by omega)
    by_cases iso : ∃x∈s,deg r s x=0
    · obtain ⟨x,xs,dx⟩:=iso
      exact rel_mono (by norm_num) (isolated sym xs dx ih)
    by_cases one : ∃x∈s,deg r s x=1
    · obtain ⟨x,xs,dx⟩:=one
      obtain ⟨y,hy⟩ := card_pos.mp (show 0<deg r s x by omega)
      have ys := (mem_filter.mp hy).1
      by_cases dy : deg r s y=1
      · exact lone_edge sym irr xs hy dx dy ih
      have yz : deg r s y≠0 := fun h => iso ⟨y,ys,h⟩
      exact rel_mono (by norm_num) (leaf sym irr xs hy dx (by omega) cubicCap ih)
    have low (u : V) (hu : u∈s) : 2≤deg r s u := by
      have a : deg r s u≠0 := fun h => iso ⟨u,hu,h⟩
      have b : deg r s u≠1 := fun h => one ⟨u,hu,h⟩
      omega
    by_cases mix : ∃u∈s,∃w∈neighbors r s u,deg r s u=3 ∧ deg r s w=2
    · obtain ⟨u,us,w,hw,du,dw⟩:=mix
      exact rel_mono (by norm_num) (mixed sym irr tri (mem_filter.mp hw).1 (reverse sym us hw) dw du low cubicCap ih)
    by_cases three : ∃u∈s,deg r s u=3
    · obtain ⟨u,us,du⟩:=three
      exact cubic sym irr tri us du low cubicCap (fun a ha b hb da db => mix ⟨a,ha,b,hb,da,db⟩) ih
    apply degree_two sym irr tri vs _ ih
    intro u hu
    have a:=low u hu
    have b:=cubicCap u hu
    have c : deg r s u≠3 := fun h => three ⟨u,hu,h⟩
    omega

/-- If the average degree is at least 17/2 then the maximum-degree-ten
    triangle-free potential attains the exponent 1/4. -/
theorem dense (sym : Symmetric r) (irr : Irreflexive r) (tri : TriangleFree r)
    (s : Finset V) (maxdeg : cap r s 10) (avg : 17*s.card≤2*vol r s) :
    (mis r s:ℝ)≤(3:ℝ)^((s.card:ℝ)/4) := by
  have comparison : (2:ℝ)^((19:ℝ)/48) ≤ (3:ℝ)^((1:ℝ)/4) := by
    by_contra! bad
    have absurd := pow_lt_pow_left₀ bad (n:=48) (Real.rpow_nonneg (by norm_num) _) (by decide)
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),←Real.rpow_natCast,←Real.rpow_mul (by norm_num)] at absurd
    norm_num at absurd
  apply (ten sym irr tri s maxdeg).trans
  have av : (17:ℝ)*s.card≤2*vol r s := by exact_mod_cast avg
  have b:=Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) comparison (Nat.cast_nonneg (α:=ℝ) s.card)
  rw [←Real.rpow_mul (by norm_num),←Real.rpow_mul (by norm_num)] at b
  rw [show 1/4*(s.card:ℝ)=s.card/4 by ring] at b
  apply le_trans _ b
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  simp only [cost,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
  linarith

end
end Audit.TriangleTen
