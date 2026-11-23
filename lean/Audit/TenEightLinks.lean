import Audit.TriangleTenEight

namespace Audit.TenEightLinks
open Finset Sumfree Fingerprint TriangleBase TriangleExceptional
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}

def deficit (r : V → V → Prop) (g t : Finset V) (x : V) :=
  cross r (neighbors r g x) (g\t)

def around (r : V → V → Prop) (s : Finset V) (x : V) := cross r (neighbors r s x) s

/-- Conditions in a fixed original graph, checked on one-, two- and three-step neighborhoods. -/
structure Local (r : V → V → Prop) (g : Finset V) : Prop where
  types : ∀x∈g, deg r g x=8 ∨ deg r g x=10
  original : ∀x∈g, deg r g x=10 → around r g x≤90 ∧ 6≤vol r (neighbors r g x)
  injured : ∀x∈g, deg r g x=10 → ∀y∈neighbors r g x,
    (((neighbors r g x).erase y).filter fun q => deg r g q=10).card ≤ 5 ∧
    2≤vol r ((neighbors r g x).erase y)
  partner : ∀x∈g, deg r g x=10 → ∃ w∈g, x≠w ∧ ¬r x w ∧
    deg r g w=8 ∧ around r g w≤74 ∧ 6≤vol r (neighbors r g w) ∧
    6≤deg r (neighbors r g w) x ∧
    (∀ y∈insert w (neighbors r g w), y∈neighbors r g x ∨
      3≤deg r (neighbors r g x) y ∨
      ∃ q∈neighbors r g x, deg r g q=10 ∧ ¬r q y ∧
        2≤deg r (neighbors r g x) y ∧ 3≤deg r (neighbors r g q) y) ∧
    ∃ q∈neighbors r g x, deg r g q=10 ∧ ∃z∈neighbors r g q,
      deg r g z=10 ∧ z≠x ∧ z≠w ∧ ¬r x z ∧ ¬r w z ∧
      3≤deg r (neighbors r g z) x+deg r (neighbors r g z) w

theorem split (sym : Symmetric r) {t g : Finset V} (sub : t⊆g) (n : Finset V) :
    cross r n t+cross r n (g\t)=cross r n g := by
  have dis : Disjoint t (g\t) := by exact disjoint_left.mpr (fun _ h k => (mem_sdiff.mp k).2 h)
  rw [←cross_right sym dis,union_sdiff_of_subset sub]

theorem cross_le (sym : Symmetric r) {t g : Finset V} (sub : t⊆g) (n : Finset V) :
    cross r n t≤cross r n g := Nat.le.intro ((split sym sub n))

theorem cross_flip (sym : Symmetric r) (a b : Finset V) : cross r a b=cross r b a := cross_sum r sym _ _

theorem degree_missing (sym : Symmetric r) {t g : Finset V} (sub : t⊆g) (x : V) :
    deg r t x+deg r (g\t) x=deg r g x := by
  simpa only [cross,sum_singleton] using split sym sub ({x}:Finset V)

theorem gap_one (sym : Symmetric r) {g t : Finset V} {x y : V} (yg : y∈g) (yt : y∉t) :
    deg r (neighbors r g x) y ≤ deficit r g t x := by
  unfold deficit
  rw [cross_flip sym]
  exact single_le_sum (fun q _ => Nat.zero_le (deg r (neighbors r g x) q)) (mem_sdiff.mpr ⟨yg,yt⟩)

theorem gap_pair (sym : Symmetric r) {g t : Finset V} {x y z : V} (yg : y∈g) (yt : y∉t)
    (zg : z∈g) (zt : z∉t) (ne : y≠z) :
    deg r (neighbors r g x) y + deg r (neighbors r g x) z ≤ deficit r g t x := by
  unfold deficit
  rw [cross_flip sym]
  have sub : {y,z}⊆g\t := insert_subset (mem_sdiff.mpr ⟨yg,yt⟩) (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨zg,zt⟩))
  have h := sum_le_sum_of_subset (f:=deg r (neighbors r g x)) sub
  simpa [ne] using h

theorem full_set {g t : Finset V} (sub : t⊆g) {x : V} (d : deg r t x=deg r g x) :
    neighbors r t x=neighbors r g x :=
  eq_of_subset_of_card_le (filter_subset_filter _ sub) (le_of_eq d.symm)

theorem full_iff {g t : Finset V} (sub : t⊆g) (x : V) :
    deg r t x=deg r g x ↔ neighbors r g x⊆t := by
  constructor
  · intro h
    rw [←full_set sub h]
    exact filter_subset ..
  · intro h
    apply congrArg Finset.card
    ext y
    simp only [neighbors,mem_filter]
    exact ⟨fun k => ⟨sub k.1,k.2⟩, fun k => ⟨h (mem_filter.mpr k),k.2⟩⟩

theorem full_sum (sym : Symmetric r) {g t : Finset V} (sub : t⊆g) {x : V} (d : deg r t x=deg r g x) :
    around r t x+deficit r g t x=around r g x := by
  unfold around deficit
  rw [full_set sub d]
  exact split sym sub _

theorem missed_neighbor (sym : Symmetric r) {g t : Finset V} (sub : t⊆g) {x y q : V}
    (yg : y∈g) (yt : y∉t) (qn : q∈neighbors r g x) (notAdj : ¬r q y)
    (drop : deg r t q≠deg r g q) : deg r (neighbors r g x) y+1≤deficit r g t x := by
  have missing := (full_iff sub q).not.mp drop
  obtain ⟨z,zq,zt⟩ := not_subset.mp missing
  have zy : y≠z := fun e => notAdj (e.symm ▸ (mem_filter.mp zq).2)
  have inside : 1≤deg r (neighbors r g x) z := card_pos.mpr ⟨q,mem_filter.mpr ⟨qn,sym (mem_filter.mp zq).2⟩⟩
  exact Nat.le_trans (Nat.add_le_add_left inside _) (gap_pair sym yg yt (mem_filter.mp zq).1 zt zy)

theorem next_full (sym : Symmetric r) {g t : Finset V} (sub : t⊆g) {x q : V}
    (qn : q∈neighbors r g x) (no : deficit r g t x=0) : deg r t q=deg r g q := by
  apply (full_iff sub q).mpr
  intro y hy
  by_contra yt
  have gap := gap_one (x:=x) sym (mem_filter.mp hy).1 yt
  have pos : 1≤deg r (neighbors r g x) y := card_pos.mpr ⟨q,mem_filter.mpr ⟨qn,sym (mem_filter.mp hy).2⟩⟩
  omega

theorem cut_full {g t : Finset V} (sub : t⊆g) {x w : V}
    (f : deg r t w=deg r g w) (no : ¬r w x) : deg r (cut t x) w=deg r g w := by
  apply (full_iff (sdiff_subset.trans sub) w).mpr
  intro y hy
  refine mem_sdiff.mpr ⟨(full_iff sub w).mp f hy,?_⟩
  intro hit
  exact no (mem_singleton.mp hit ▸ (mem_filter.mp hy).2)

theorem one_erased {g t : Finset V} (sub : t⊆g) {x : V} (injured : deg r t x+1=deg r g x) :
    ∃y∈neighbors r g x, neighbors r t x=(neighbors r g x).erase y := by
  let n:=neighbors r t x
  let all:=neighbors r g x
  have ns : n⊆all := filter_subset_filter _ sub
  have size := card_sdiff_add_card_eq_card ns
  have single : (all\n).card=1 := by change n.card+1=all.card at injured; omega
  obtain ⟨y,eq⟩ := card_eq_one.mp single
  have hy : y∈all\n := eq.symm ▸ mem_singleton_self y
  refine ⟨y,(mem_sdiff.mp hy).1,?_⟩
  ext w
  change w∈n ↔ w∈all.erase y
  rw [mem_erase]
  constructor
  · exact fun h => ⟨fun e => (mem_sdiff.mp hy).2 (e ▸ h),ns h⟩
  · rintro ⟨ne,ha⟩
    by_contra hn
    exact ne (mem_singleton.mp (eq ▸ mem_sdiff.mpr ⟨ha,hn⟩))

def Strong (r : V → V → Prop) (t : Finset V) : Prop :=
  ∃x∈t, deg r t x=10 ∧ around r t x≤87 ∧ 6≤vol r (neighbors r t x)

theorem nine {g t : Finset V} (h : Local r g) (sub : t⊆g) (small : cap r t 9) :
    ∀x∈t, deg r t x=9 → around r t x≤77 ∧ 2≤vol r (neighbors r t x) := by
  intro x xt d
  have hi := mono (r:=r) sub x
  have orig : deg r g x=10 := (h.types x (sub xt)).resolve_left (by omega)
  obtain ⟨y,yn,eq⟩ := one_erased (r:=r) sub (x:=x) (by omega)
  obtain ⟨hc,vi⟩ := h.injured x (sub xt) orig y yn
  rw [←eq] at hc vi
  refine ⟨?_,vi⟩
  have point (q : V) (hq : q∈neighbors r t x) :
      deg r t q≤8+(if deg r g q=10 then 1 else 0) := by
    have qt := (mem_filter.mp hq).1
    have a := h.types q (sub qt)
    have b := small q qt
    have c := mono (r:=r) sub q
    split <;> omega
  have sm := sum_le_sum point
  rw [sum_add_distrib,sum_const,sum_ite,sum_const_zero,add_zero,sum_const] at sm
  simp only [nsmul_eq_mul,mul_one] at sm
  change _≤(neighbors r t x).card*8+_ at sm
  change (neighbors r t x).card=9 at d
  change (∑ q∈neighbors r t x,deg r t q)≤77
  apply sm.trans
  change (neighbors r t x).card*8 + ((neighbors r t x).filter fun q => deg r g q=10).card≤77
  omega

theorem gap_strong (sym : Symmetric r) {g t : Finset V} (h : Local r g) (sub : t⊆g)
    {x : V} (xt : x∈t) (d : deg r t x=10) (gap : 3≤deficit r g t x) : Strong r t := by
  have hi := mono (r:=r) sub x
  have orig : deg r g x=10 := (h.types x (sub xt)).resolve_left (by omega)
  have equal := d.trans orig.symm
  obtain ⟨bound,inner⟩ := h.original x (sub xt) orig
  have add := full_sum sym sub equal
  rw [←full_set sub equal] at inner
  exact ⟨x,xt,d,by omega,inner⟩

theorem partners (sym : Symmetric r) {g t : Finset V} (h : Local r g) (sub : t⊆g)
    (large : ¬ cap r t 9) (weak : ¬Strong r t) :
    ∃x∈t, ∃w∈cut t x, deg r t x=10 ∧ around r t x≤90 ∧ 6≤vol r (neighbors r t x) ∧
      deg r (cut t x) w=8 ∧ around r (cut t x) w≤68 ∧ 6≤vol r (neighbors r (cut t x) w) ∧
      (around r t x≤89 ∨ Strong r (cut (cut t x) w)) := by
  classical
  let largeGap := ∃x∈t, deg r t x=10 ∧ 0<deficit r g t x
  have found : ∃x∈t, deg r t x=10 ∧ (0<deficit r g t x ∨ ¬largeGap) := by
    by_cases has : largeGap
    · obtain ⟨x,xt,hi,po⟩ := has
      exact ⟨x,xt,hi,Or.inl po⟩
    · unfold cap at large
      push_neg at large
      obtain ⟨x,xt,hi⟩ := large
      have ty := h.types x (sub xt)
      have le := mono (r:=r) sub x
      exact ⟨x,xt,by omega,Or.inr has⟩
  obtain ⟨x,xt,dx,choice⟩ := found
  have hi := mono (r:=r) sub x
  have xo : deg r g x=10 := (h.types x (sub xt)).resolve_left (by omega)
  have xf := dx.trans xo.symm
  have ng := full_set sub xf
  have retain := (full_iff sub x).mp xf
  have smallGap {u : V} (ut : u∈t) (du : deg r t u=10) : deficit r g t u≤2 := by
    by_contra! more
    exact weak (gap_strong sym h sub ut du more)
  have gx := smallGap xt dx
  obtain ⟨origA,origI⟩ := h.original x (sub xt) xo
  have sumx := full_sum sym sub xf
  obtain ⟨w,wg,xw,miss,wd,wa,wi,common,near,q,qn,qd,z,zn,zd,zx,zw,az,bz,both⟩ :=
    h.partner x (sub xt) xo
  have survives (y : V) (ylist : y∈insert w (neighbors r g w)) : y∈t := by
    by_contra yt
    have yg : y∈g := (mem_insert.mp ylist).elim (fun eq => eq.symm ▸ wg) (fun k => (mem_filter.mp k).1)
    rcases near y ylist with yes|tri|⟨q,qn,qd,qy,two,three⟩
    · exact yt (retain yes)
    · have loss := gap_one (x:=x) sym yg yt
      omega
    · have qt := retain qn
      have full : deg r t q=deg r g q := by
        by_contra lost
        have more := missed_neighbor sym sub yg yt qn qy lost
        omega
      have upper := smallGap qt (full.trans qd)
      have lower := gap_one (x:=q) sym yg yt
      omega
  have wt := survives w (mem_insert_self ..)
  have wf : deg r t w=deg r g w := (full_iff sub w).mpr (fun _ nw => survives _ (mem_insert_of_mem nw))
  have subx : cut t x⊆g := sdiff_subset.trans sub
  have wtx : w∈cut t x := mem_sdiff.mpr ⟨wt,fun u => xw (mem_singleton.mp u).symm⟩
  have wx := cut_full sub wf (fun e => miss (sym e))
  have sumw := full_sum sym subx wx
  have opx : x∉cut t x := fun m => (mem_sdiff.mp m).2 (mem_singleton_self x)
  have lost := gap_one (x:=w) sym (sub xt) opx
  rw [←ng] at origI
  rw [←full_set subx wx] at wi
  refine ⟨x,xt,w,wtx,dx,by omega,origI,wx.trans wd,by omega,wi,?_⟩
  rcases choice with pos|not
  · exact Or.inl (by omega)
  · right
    have gapZero {u : V} (ut : u∈t) (du : deg r t u=10) : deficit r g t u=0 := by
      by_contra! bad
      exact not ⟨u,ut,du,Nat.pos_of_ne_zero bad⟩
    have fullq := next_full sym sub qn (gapZero xt dx)
    have qt := retain qn
    have zt := (full_iff sub q).mp fullq zn
    have fullz := next_full sym sub zn (gapZero qt (fullq.trans qd))
    have f1 := cut_full sub fullz (fun e => az (sym e))
    have f2 := cut_full subx f1 (fun e => bz (sym e))
    have subw : cut (cut t x) w⊆g := sdiff_subset.trans subx
    have memz : z∈cut (cut t x) w := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨zt,fun e => zx (mem_singleton.mp e)⟩,
      fun e => zw (mem_singleton.mp e)⟩
    have skipx : x∉cut (cut t x) w := fun e => opx (mem_sdiff.mp e).1
    have skipw : w∉cut (cut t x) w := fun e => (mem_sdiff.mp e).2 (mem_singleton_self w)
    exact gap_strong sym h subw memz (f2.trans zd)
      (both.trans (gap_pair sym (sub xt) skipx wg skipw xw))

theorem bound (sym : Symmetric r) (irr : Irreflexive r) (g : Finset V) (h : Local r g)
    (avg : 18*g.card≤2*vol r g) : (mis r g:ℝ)≤(3:ℝ)^((g.card:ℝ)/4) := by
  apply TenEightPotential.bound sym irr g _ _ _ avg
  · intro x xg
    rcases h.types x xg with a|a <;> omega
  · intro t sub c
    exact nine h sub c
  · intro t sub big weak
    exact partners sym h sub big weak

end
end Audit.TenEightLinks
