import Audit.ColoredWeights

namespace Audit.Colored
open Finset Fingerprint Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (blue red : V → V → Prop)

theorem bound_power (bs : Symmetric blue) (rs : Symmetric red) (bi : Irreflexive blue)
    (ri : Irreflexive red) (tf : TriangleFree red) (s : Finset V) :
    ((family blue red s).card:ℝ) ≤ base^s.card := by
  classical
  let g := edge blue red
  let f := family blue red
  have sym := edge_sym blue red bs rs
  have irr := edge_irr blue red bi ri
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases empty : s=∅
    · subst s
      have h := card_le_card (filter_subset (Valid blue red (∅:Finset V)) (∅:Finset V).powerset)
      simpa only [card_powerset,card_empty,pow_zero,Nat.cast_le_one] using h
    let M : ℝ := base^s.card
    have Mp : 0≤M := pow_nonneg base_pos.le _
    let deg (x : V) := (neighbors g s x).card
    let colored (x : V) := (neighbors red s x).card
    let nb (x : V) := closed g s x
    have closed_size {x : V} (xs : x∈s) : (nb x).card=deg x+1 := Subcubic.closed_card g sym irr xs
    have sclosed (x : V) : nb x⊆s := fun _ h => (mem_closed.mp h).1
    have inClosed {x : V} (xs : x∈s) : x∈nb x := mem_closed.mpr ⟨xs,Or.inl rfl⟩
    have region {t : Finset V} (non : t.Nonempty) (sub : t⊆s) {i : ℕ} (size : i≤t.card) :
        ((f (s\t)).card:ℝ) ≤ M/base^i := by
      obtain ⟨z,zt⟩ := non
      have strict : s\t⊂s := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun eq => (mem_sdiff.mp (eq.symm ▸ sub zt)).2 zt⟩
      apply pow_le_div Mp _ (ih _ strict) rfl
      have := card_sdiff_add_card_eq_card sub; omega
    have unionBound {x : V} (xs : x∈s) (y : V) {i : ℕ} (sz : i≤(nb x∪nb y).card) :
        ((f (s\(nb x∪nb y))).card:ℝ) ≤ M/base^i :=
      region ⟨x,mem_union_left _ (inClosed xs)⟩ (union_subset (sclosed x) (sclosed y)) sz
    have redSub (x : V) : neighbors red s x ⊆ neighbors g s x :=
      fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1,Or.inr (mem_filter.mp h).2⟩
    have choose (x : V) (xs : x∈s) (skip : ℝ) (cost : ℕ)
        (skipBound : (((f s).filter (fun I => x∉I)).card:ℝ)≤skip)
        (unions : ∀ y∈neighbors red s x,cost≤(nb x∪nb y).card) :
        ((f s).card:ℝ)≤skip+M/base^(deg x+1)+(colored x:ℝ)*(M/base^cost) := by
      have br : ((f s).card:ℝ) ≤ (((f s).filter fun I => x∉I).card:ℝ)+
          ((f (s\nb x)).card:ℝ)+∑ y∈neighbors red s x,((f (s\(nb x∪nb y))).card:ℝ) := by
        exact_mod_cast branch blue red bs rs bi ri s xs
      have sum := sum_le_sum (fun y hy => unionBound xs y (unions y hy))
      rw [sum_const,nsmul_eq_mul] at sum
      exact br.trans (add_le_add (add_le_add skipBound
        (region ⟨x,inClosed xs⟩ (sclosed x) (closed_size xs).ge)) sum)
    have basicSkip {x : V} (xs : x∈s) :
        (((f s).filter fun I => x∉I).card:ℝ)≤M/base := by
      have inc : ((f s).filter fun I => x∉I)⊆pattern blue red s ∅ {x} := by
        intro I hi; obtain ⟨valid,out⟩ := mem_filter.mp hi
        exact mem_filter.mpr ⟨valid,disjoint_iff_inter_eq_empty.mp (disjoint_singleton_right.mpr out)⟩
      have h := (card_le_card inc).trans (pattern_le blue red sym s ∅ {x} (by simp))
      apply (Nat.cast_le.mpr h).trans
      simpa using region (singleton_nonempty x) (singleton_subset_iff.mpr xs) (i:=1) (by simp)
    obtain ⟨first,fs,minDeg⟩ := s.exists_min_image deg (nonempty_iff_ne_empty.mpr empty)
    let lowest := s.filter fun v => deg v=deg first
    obtain ⟨x,xMin,minRed⟩ := lowest.exists_min_image colored ⟨first,mem_filter.mpr ⟨fs,rfl⟩⟩
    obtain ⟨xs,dx⟩ := mem_filter.mp xMin
    have low (y : V) (ys : y∈s) : deg x≤deg y := dx ▸ minDeg y ys
    let d := deg x
    by_cases isolate : d=0
    case pos =>
      have nzero : neighbors g s x=∅ := card_eq_zero.mp isolate
      have forced {I : Finset V} (h : I∈f s) : x∈I := by
        apply Classical.byContradiction; intro no
        have valid := (mem_family blue red).mp h
        obtain ⟨z,zi,e⟩ := valid.2.2.2 _ xs no
        have zmem : z∈neighbors g s x := mem_filter.mpr ⟨valid.1 zi,e⟩
        rw [nzero] at zmem; exact not_mem_empty z zmem
      have sub : f s ⊆ pattern blue red s {x} {x} := by
        intro I h; exact mem_filter.mpr ⟨h,inter_eq_right.mpr (singleton_subset_iff.mpr (forced h))⟩
      have bound := (card_le_card sub).trans (pattern_le blue red sym s {x} {x} (by
        intro u hu z zs e; obtain rfl := mem_singleton.mp hu
        have nz : z∈neighbors g s u := mem_filter.mpr ⟨zs,e⟩
        rw [nzero] at nz; exact False.elim (not_mem_empty z nz)))
      apply (Nat.cast_le.mpr bound).trans
      apply (region (singleton_nonempty x) (singleton_subset_iff.mpr xs) (i:=0) (by simp)).trans_eq
      simp [M]
    by_cases leaf : d=1
    case pos =>
      obtain ⟨w,neigh⟩ := card_eq_one.mp leaf
      have win : w∈neighbors g s x := neigh ▸ mem_singleton_self _
      obtain ⟨ws,xw⟩ := mem_filter.mp win
      have different : x≠w := fun eq => irr x (eq ▸ xw)
      have skipLeaf : (((f s).filter fun I => w∉I).card:ℝ)≤ M/base^2 := by
        have inc : ((f s).filter fun I => w∉I) ⊆ pattern blue red s {x} {x,w} := by
          intro I h
          obtain ⟨hi,wi⟩ := mem_filter.mp h
          have valid := (mem_family blue red).mp hi
          have xi : x∈I := by
            apply Classical.byContradiction; intro h
            obtain ⟨z,zi,e⟩ := valid.2.2.2 x xs h
            have zmem : z∈neighbors g s x := mem_filter.mpr ⟨valid.1 zi,e⟩
            exact wi ((mem_singleton.mp (neigh ▸ zmem)) ▸ zi)
          exact mem_filter.mpr ⟨hi,by ext z; simp [or_and_left,and_or_left,xi,wi]⟩
        have h := (card_le_card inc).trans (pattern_le blue red sym s {x} {x,w} (by
          intro u hu z zs e; obtain rfl := mem_singleton.mp hu
          have nz : z∈neighbors g s u := mem_filter.mpr ⟨zs,e⟩
          exact mem_insert_of_mem (neigh ▸ nz)))
        apply (Nat.cast_le.mpr h).trans (region (insert_nonempty ..) (insert_subset xs (singleton_subset_iff.mpr ws)) _)
        simp [different]
      have selected := choose w ws _ (deg w+1) skipLeaf (fun y _ =>
        (closed_size ws).ge.trans (card_le_card (subset_union_left (s₂:=nb y))))
      have redLe : (colored w:ℝ)≤deg w := Nat.cast_le.mpr (card_le_card (redSub w))
      have lo : 1≤deg w := leaf ▸ low w ws
      have rate := leaf_weight lo
      have bound := mul_le_mul_of_nonneg_left rate Mp
      change ((f s).card:ℝ)≤M
      apply selected.trans
      calc
        _ ≤ M/base^2+M/base^(deg w+1)+(deg w:ℝ)*(M/base^(deg w+1)) := by
          exact add_le_add_left (mul_le_mul_of_nonneg_right redLe (div_nonneg Mp (pow_nonneg base_pos.le _))) _
        _ = M*(1/base^2+((deg w:ℝ)+1)/base^(deg w+1)) := by ring
        _ ≤ _ := by simpa using bound
    have minimum : 2≤d := by omega
    have redLe : colored x≤d := card_le_card (redSub x)
    by_cases partialRed : colored x<d
    case pos =>
      have selected := choose x xs _ (d+1) (basicSkip xs) (fun y _ =>
        (closed_size xs).ge.trans (card_le_card (subset_union_left (s₂:=nb y))))
      have rd : (colored x:ℝ)+1≤d := by exact_mod_cast (show colored x+1≤d by omega)
      change ((f s).card:ℝ)≤M
      apply selected.trans
      calc
        _ = M/base+((colored x:ℝ)+1)*(M/base^(d+1)) := by dsimp [d]; ring
        _ ≤ M/base+(d:ℝ)*(M/base^(d+1)) := by
          exact add_le_add_left (mul_le_mul_of_nonneg_right rd (div_nonneg Mp (pow_nonneg base_pos.le _))) _
        _ = M*(1/base+(d:ℝ)/base^(d+1)) := by ring
        _ ≤ M := by simpa using mul_le_mul_of_nonneg_left (missing_weight minimum) Mp
    have redEq : colored x=d := by omega
    have onlyX : neighbors red s x=neighbors g s x := eq_of_subset_of_card_le (redSub x) redEq.ge
    have unions (y : V) (hy : y∈neighbors red s x) : d+2≤(nb x∪nb y).card := by
      obtain ⟨ys,xy⟩ := mem_filter.mp hy
      by_cases many : d<deg y
      · have h := card_le_card (subset_union_right (s₁:=nb x) (s₂:=nb y))
        rw [closed_size ys] at h; omega
      have degy : deg y=d := le_antisymm (Nat.le_of_not_gt many) (low y ys)
      have ry := minRed y (mem_filter.mpr ⟨ys,degy.trans dx⟩)
      have onlyY : neighbors red s y=neighbors g s y :=
        eq_of_subset_of_card_le (redSub y) (show deg y≤colored y from by rw [degy,←redEq]; exact ry)
      have ex : ∃ z∈neighbors g s y,z≠x := by
        apply Classical.byContradiction; intro none
        have sub : neighbors g s y ⊆ {x} := fun z hz => mem_singleton.mpr (Classical.byContradiction (fun nz => none ⟨z,hz,nz⟩))
        have h : deg y≤1 := (card_le_card sub).trans_eq (card_singleton _)
        omega
      obtain ⟨z,zy,zx⟩ := ex
      have outside : z∉nb x := by
        intro zcx
        rcases (mem_closed.mp zcx).2 with eq|e
        · exact zx eq
        · have xz : z∈neighbors g s x := mem_filter.mpr ⟨(mem_filter.mp zy).1,sym e⟩
          exact tf x y z xy ((mem_filter.mp (onlyY.symm ▸ zy)).2) ((mem_filter.mp (onlyX.symm ▸ xz)).2)
      have zmem : z∈nb y := mem_closed.mpr ⟨(mem_filter.mp zy).1,Or.inr (sym (mem_filter.mp zy).2)⟩
      have h := card_le_card (insert_subset (mem_union_right (nb x) zmem) (subset_union_left (s₁:=nb x) (s₂:=nb y)))
      rw [card_insert_of_not_mem outside,closed_size xs] at h
      exact h
    have selected := choose x xs _ (d+2) (basicSkip xs) unions
    rw [redEq] at selected
    change ((f s).card:ℝ)≤M
    apply selected.trans
    calc
      _ = M*(1/base+1/base^(d+1)+(d:ℝ)/base^(d+2)) := by dsimp only [d]; ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left (red_weight minimum) Mp

theorem bound (bs : Symmetric blue) (rs : Symmetric red) (bi : Irreflexive blue)
    (ri : Irreflexive red) (tf : TriangleFree red) (s : Finset V) :
    ((family blue red s).card:ℝ) ≤ (3:ℝ)^((s.card:ℝ)/2) := by
  apply (bound_power blue red bs rs bi ri tf s).trans_eq
  rw [base,Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
  congr 1; ring

end
end Audit.Colored
