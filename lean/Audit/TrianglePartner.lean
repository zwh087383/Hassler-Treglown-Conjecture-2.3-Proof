import Audit.TriangleExceptional

namespace Audit.TrianglePartner
open Finset Sumfree Fingerprint TriangleBase TriangleLocal TriangleExceptional
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t g a : Finset V} {v w : V}

def protectedZone (r : V → V → Prop) (g : Finset V) (v : V) :=
  neighbors r g v ∪ g.filter (fun u => 2≤deg r (neighbors r g v) u)

/-- The original graph is all the checker has to inspect. A pair of consecutive
    neighborhood deletions is proved below for every induced subgraph. -/
def Certificate (r : V → V → Prop) (g : Finset V) : Prop :=
  ∀ v∈g, let n:=neighbors r g v
    10≤vol r n ∨ 6≤vol r n ∧ ∃ w∈g, w≠v ∧ ¬r w v ∧
      6≤(n∩neighbors r g w).card ∧
      8≤(neighbors r g w∩protectedZone r g v).card ∧
      6≤vol r (neighbors r g w∩protectedZone r g v)

theorem low_sum {d : ℕ} (sub : a⊆s) (c : ∀u∈s,deg r t u≤d) (low : ∀u∈a,deg r t u<d) :
    cross r s t+a.card≤s.card*d := by
  have each (u : V) (hu : u∈s) : deg r t u+(if u∈a then 1 else 0)≤d := by
    by_cases mem : u∈a
    · rw [if_pos mem]; exact low u mem
    · rw [if_neg mem,add_zero]; exact c u hu
  have b:=sum_le_sum each
  rw [sum_add_distrib,sum_ite,sum_const_zero,add_zero,sum_const,sum_const] at b
  have eq : s.filter (·∈a)=a := by ext x; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  rw [eq] at b
  simpa only [nsmul_eq_mul,mul_one] using b

private theorem force (sym : Symmetric r) (sub : t⊆g) (c : cap r g 9)
    (vIn : v∈t) (dv : deg r t v=9) (tight : 79<cross r (neighbors r t v) t) :
    protectedZone r g v⊆t := by
  have nEq:=full_neighbors sub c vIn dv
  have nsub : neighbors r g v⊆t := by rw [←nEq]; exact filter_subset .. 
  intro u hu
  rcases mem_union.mp hu with member|high
  · exact nsub member
  obtain ⟨ug,degree⟩:=mem_filter.mp high
  by_contra un
  have tcut : t⊆cut g u := fun _ hy => mem_sdiff.mpr ⟨sub hy,fun e => un ((mem_singleton.mp e) ▸ hy)⟩
  let a:=neighbors r (neighbors r g v) u
  have aSub : a⊆neighbors r t v := by rw [nEq]; exact filter_subset .. 
  have low (p : V) (hp : p∈a) : deg r t p<9 := by
    obtain ⟨pn,up⟩:=mem_filter.mp hp
    have loss:=degree_cut_yes ug (sym up)
    have capP:=c p (sub (nsub pn))
    have cp:=mono (r:=r) tcut p
    omega
  have sum:=low_sum aSub (fun z hz => (cap_sub sub c) z (mem_filter.mp hz).1) low
  change _+a.card≤deg r t v*9 at sum
  change 2≤a.card at degree
  omega

private theorem qnum (p : ℕ) (q : ℝ) (pos : 0<q) (cert : 1≤(3:ℝ)^p*q^84)
    (loss : (p:ℤ)≤cash 14 r s-cash 14 r t) : W 14 r t≤q*W 14 r s :=
  scale (by decide) loss (by simpa only [Nat.cast_ofNat,show (6:ℝ)*14=84 by norm_num] using Potential.neg_weight p 84 q (by decide) pos cert)

private theorem partner_branch (sym : Symmetric r) (irr : Irreflexive r)
    (sub : t⊆g) (c : cap r g 9) (vIn : v∈t) (dv : deg r t v=9)
    (tight : 79<cross r (neighbors r t v) t) (wg : w∈g) (wv : w≠v) (notWV : ¬r w v)
    (common : 6≤(neighbors r g v∩neighbors r g w).card)
    (enough : 8≤(neighbors r g w∩protectedZone r g v).card)
    (triple : 6≤vol r (neighbors r g w∩protectedZone r g v)) (ih : Prev 14 r t) :
    (mis r (cut t v):ℝ)≤(99/100)*W 14 r (cut t v) := by
  let u:=cut t v
  let shared:=neighbors r g v∩neighbors r g w
  let safe:=neighbors r g w∩protectedZone r g v
  change 6≤shared.card at common
  have nEq:=full_neighbors sub c vIn dv
  have member (z : V) (h : z∈neighbors r g v) : z∈t := (mem_filter.mp (nEq.symm ▸ h)).1
  have compelled := force sym sub c vIn dv tight
  have wcommon : neighbors r (neighbors r g v) w=shared := by
    ext z; simp only [neighbors,shared,mem_filter,mem_inter]
    tauto
  have wforced : w∈protectedZone r g v :=
    mem_union_right _ (mem_filter.mpr ⟨wg,show 2≤deg r (neighbors r g v) w by
      change 2≤(neighbors r (neighbors r g v) w).card; rw [wcommon]; omega⟩)
  have wu : w∈u := mem_sdiff.mpr ⟨compelled wforced,fun e => wv (mem_singleton.mp e)⟩
  have ss : safe ⊆ neighbors r u w := by
    intro z hz
    obtain ⟨wn,f⟩:=mem_inter.mp hz
    obtain ⟨_,wz⟩:=mem_filter.mp wn
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨compelled f,fun h => notWV ((mem_singleton.mp h) ▸ wz)⟩,wz⟩
  have sh : shared ⊆ neighbors r u w := by
    intro z hz
    obtain ⟨nv,nw⟩:=mem_inter.mp hz
    exact ss (mem_inter.mpr ⟨nw,mem_union_left _ nv⟩)
  have limits : cap r u 9 := cap_sub (sdiff_subset.trans sub) c
  have low (p : V) (hp : p∈shared) : deg r u p<9 := by
    have h:=degree_cut_yes vIn (sym (mem_filter.mp (mem_inter.mp hp).1).2)
    have cp:=(cap_sub sub c) p (member p (mem_inter.mp hp).1)
    change deg r u p+1=deg r t p at h
    omega
  have cv:=low_sum sh (fun z hz => limits z (mem_filter.mp hz).1) low
  change cross r (neighbors r u w) u+shared.card≤deg r u w*9 at cv
  have ed:=triple.trans (vol_mono ss)
  have min:=enough.trans (card_le_card ss)
  change 8≤deg r u w at min
  have max:=limits w wu
  have ih' : Prev 14 r u := fun l hl => ih l (Finset.ssubset_of_ssubset_of_subset hl sdiff_subset)
  have left:=ih' _ (del_strict wu (mem_singleton_self w))
  have right:=ih' _ (del_strict wu (ball_self (r:=r) wu))
  have ca:=cost1 14 sym wu
  have cb:=costN 14 sym irr wu
  have cases : deg r u w=8 ∨ deg r u w=9 := by omega
  rcases cases with k|k
  · rw [k] at ca cb cv
    exact combine (s:=u) (x:=w)
      (left.trans (qnum (s:=u) (t:=cut u w) 14 (5/6) (by norm_num) (by norm_num) (by omega)))
      (right.trans (qnum (s:=u) (t:=u\ball r u w) 144 (47/300) (by norm_num) (by norm_num) (by omega))) (by norm_num)
  · rw [k] at ca cb cv
    exact combine (s:=u) (x:=w)
      (left.trans (qnum (s:=u) (t:=cut u w) 12 (171/200) (by norm_num) (by norm_num) (by omega)))
      (right.trans (qnum (s:=u) (t:=u\ball r u w) 156 (27/200) (by norm_num) (by norm_num) (by omega))) (by norm_num)

theorem bound (sym : Symmetric r) (irr : Irreflexive r)
    (g : Finset V) (c : cap r g 9) (cert : Certificate r g) (av : 18*g.card≤2*vol r g) :
    (mis r g:ℝ)≤(3:ℝ)^((g.card:ℝ)/4) := by
  suffices all : ∀t⊆g,(mis r t:ℝ)≤W 14 r t from (all g (Finset.Subset.refl _)).trans (quarter (by decide) av)
  intro t
  induction t using Finset.strongInduction with
  | H t prev =>
    intro sub
    have ih : Prev 14 r t := fun l h => prev l h ((Finset.ssubset_iff_subset_ne.mp h).1.trans sub)
    by_cases low : cap r t 8
    · exact weighted_base (D:=8) (l:=10) sym irr (by decide) (by decide) (by native_decide) t low
    unfold cap at low
    push_neg at low
    obtain ⟨v,hv,dh⟩:=low
    have capT:=cap_sub sub c
    have hi:=capT v hv
    have dv : deg r t v=9 := by omega
    have nEq:=full_neighbors sub c hv dv
    have ca:=cost1 14 sym hv
    have cb:=costN 14 sym irr hv
    have su:=adjacent_sum capT dv
    rw [dv] at ca cb
    have left:=ih _ (del_strict hv (mem_singleton_self v))
    have right:=ih _ (del_strict hv (ball_self (r:=r) hv))
    have skip:=qnum 12 (171/200) (by norm_num) (by norm_num) (by omega : _≤cash 14 r t-cash 14 r (cut t v))
    have capped (p : (148:ℤ)≤cash 14 r t-cash 14 r (t\ball r t v)) : (mis r t:ℝ)≤W 14 r t := by
      have m:=combine (left.trans skip) (right.trans (qnum 148 (29/200) (by norm_num) (by norm_num) p))
        (show (171/200:ℝ)+29/200≤1 by norm_num)
      simpa only [one_mul] using m
    rcases cert v (sub hv) with edge5|⟨edge3,w,wg,wv,wn,comm,prot,inside⟩
    · rw [←nEq] at edge5
      exact capped (by omega)
    · rw [←nEq] at edge3
      by_cases tight : 79<cross r (neighbors r t v) t
      · have lb:=partner_branch sym irr sub c hv dv tight wg wv wn comm prot inside ih
        have rb:=qnum 144 (153/1000) (by norm_num) (by norm_num)
          (by omega : _≤cash 14 r t-cash 14 r (t\ball r t v))
        have l' : (mis r (cut t v):ℝ)≤((99/100)*(171/200))*W 14 r t := by
          apply lb.trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left skip (by norm_num)
        have ans:=combine l' (right.trans rb)
          (show ((99/100:ℝ)*(171/200))+153/1000≤1 by norm_num)
        simpa only [one_mul] using ans
      · exact capped (by omega)

end
end Audit.TrianglePartner
