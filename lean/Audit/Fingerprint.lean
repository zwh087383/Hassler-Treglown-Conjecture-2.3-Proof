import Sumfree.Bounds
import Audit.Global
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Audit.Fingerprint
open Finset Sumfree
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop)
set_option linter.unusedSectionVars false

def remaining (t : Finset V) := univ.filter fun v => ∀ x∈t, ¬r x v
def neighbors (s : Finset V) (v : V) := s.filter (r v)
def low (t : Finset V) := (remaining r t).filter fun v => (neighbors r (remaining r t) v).card ≤ 511
def codes : Finset (Finset V) := univ.powerset.filter fun t => 513*t.card ≤ Fintype.card V

theorem update (v : V) (t : Finset V) :
    (remaining r (insert v t)).card + (neighbors r (remaining r t) v).card = (remaining r t).card := by
  classical
  have eq : remaining r (insert v t) = (remaining r t).filter (fun x => ¬r v x) := by
    ext x; simp [remaining,and_comm]
  rw [eq,add_comm]
  exact filter_card_add_filter_neg_card_eq_card ..

/-- Maximizing the size of an admissible fingerprint supplies a finite
    proof of termination, and works for every maximal independent set. -/
theorem exists_code {i : Finset V} (h : IsMIS r univ i) :
    ∃ t∈codes (V:=V), i∈family r (low r t) := by
  classical
  let good := i.powerset.filter fun t => 512*t.card+(remaining r t).card ≤ Fintype.card V
  have emp : ∅∈good := by simp [good,remaining]
  obtain ⟨t,ht,best⟩ := exists_max_image good Finset.card ⟨_,emp⟩
  obtain ⟨ti,budget⟩ := mem_filter.mp ht
  have sub := mem_powerset.mp ti
  have remains : i ⊆ remaining r t := by
    intro v hv; exact mem_filter.mpr ⟨mem_univ _,fun x hx => h.2.1 x (sub hx) v hv⟩
  have tn := card_le_card (sub.trans remains)
  have ic : i ⊆ low r t := by
    intro v vi
    apply mem_filter.mpr ⟨remains vi,?_⟩
    by_contra! large
    have newv : v∉t := by
      intro vt
      have empty : neighbors r (remaining r t) v=∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro z hz
        obtain ⟨az,rz⟩ := mem_filter.mp hz
        exact (mem_filter.mp az).2 v vt rz
      simp [empty] at large
    have price := update r v t
    have more : insert v t ∈ good := by
      apply mem_filter.mpr ⟨mem_powerset.mpr (insert_subset vi sub),?_⟩
      rw [card_insert_of_not_mem newv]
      omega
    have contradiction := best _ more
    rw [card_insert_of_not_mem newv] at contradiction
    omega
  refine ⟨t,mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),by omega⟩,mem_family.mpr ?_⟩
  exact ⟨ic,h.2.1,fun x _ hx => h.2.2 x (mem_univ _) hx⟩

theorem covering_bound : mis r (univ : Finset V) ≤ ∑ t ∈ codes, mis r (low r t) := by
  classical
  have sub : family r univ ⊆ codes.biUnion (fun t => family r (low r t)) := by
    intro i hi; exact mem_biUnion.mpr (exists_code r (mem_family.mp hi))
  exact (card_le_card sub).trans (card_biUnion_le ..)

theorem cross_sum (sym : Symmetric r) (a b : Finset V) :
    ∑ x ∈ a, (neighbors r b x).card = ∑ y ∈ b, (neighbors r a y).card := by
  classical
  have eq (x : V) (s : Finset V) : (neighbors r s x).card = ∑ y ∈ s, if r x y then 1 else 0 := by
    simp [neighbors,←sum_filter]
  simp_rw [eq]
  rw [sum_comm]
  exact sum_congr rfl (fun y _ => sum_congr rfl (fun x _ => if_congr ⟨@sym x y,@sym y x⟩ rfl rfl))

/-- The degree hypotheses are those of the paper's large-seed lemma.
    The residual estimate applies to every fingerprint. -/
theorem residual (sym : Symmetric r) {δ Δ : ℕ} (threshold : 4096≤δ) (cap : Δ≤2*δ)
    (lower : ∀ x, δ≤(neighbors r univ x).card) (upper : ∀ x, (neighbors r univ x).card≤Δ)
    (t : Finset V) : ((low r t).card:ℝ) ≤ 8192/11777*(Fintype.card V) := by
  classical
  let a := remaining r t
  let u := low r t
  let b := univ\a
  have part (x : V) : (neighbors r univ x).card = (neighbors r a x).card+(neighbors r b x).card := by
    have dis : Disjoint (neighbors r a x) (neighbors r b x) := by
      apply disjoint_left.mpr
      intro y hy hb
      exact (mem_sdiff.mp (mem_filter.mp hb).1).2 (mem_filter.mp hy).1
    have eq : neighbors r univ x=neighbors r a x∪neighbors r b x := by
      ext y; by_cases yy : y∈a <;> simp [neighbors,b,yy]
    rw [eq,card_union_of_disjoint dis]
  have degrees (x) (hx : x∈u) : δ-511 ≤ (neighbors r b x).card := by
    have deg := lower x
    have small : (neighbors r a x).card ≤511 := (mem_filter.mp hx).2
    rw [part] at deg; omega
  have un := card_le_card (show u⊆a from filter_subset _ _)
  have bc : b.card=Fintype.card V-a.card := by simp [b,card_sdiff (subset_univ a)]
  have mixed : (δ-511)*u.card ≤ Δ*(Fintype.card V-u.card) := by
    calc
      _ = ∑ _x ∈ u, (δ-511) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun x hx => degrees x hx)
      _ = _ := cross_sum r sym u b
      _ ≤ ∑ _y ∈ b, Δ := by
        apply sum_le_sum; intro y _
        exact (card_le_card (show neighbors r u y ⊆ neighbors r univ y from
          fun z hz => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩)).trans (upper y)
      _ ≤ _ := by simp [bc,mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left un _)
  have univBound : u.card ≤ Fintype.card V := card_le_univ _
  apply Global.fingerprint_remainder (δ := (δ:ℝ)) (Δ := (Δ:ℝ))
    (by exact_mod_cast threshold) (by exact_mod_cast cap) (by positivity) (by exact_mod_cast univBound)
  have casted : ((δ-511:ℕ):ℝ)*u.card ≤ (Δ:ℝ)*((Fintype.card V-u.card:ℕ):ℝ) := by exact_mod_cast mixed
  rw [Nat.cast_sub (show 511≤δ by omega),Nat.cast_sub univBound] at casted
  exact casted

/-- Bound the entire set of fingerprints by weighting every subset of size s
    by 512^(-s) and using the binomial identity. -/
theorem number_of_codes : ((codes (V:=V)).card : ℝ) ≤ (3:ℝ)^(8*(Fintype.card V:ℝ)/513) := by
  classical
  let n := Fintype.card V
  let q := n/513
  let b : ℝ := 513/512
  have one (t : Finset V) (ht : t∈codes) : (1/512:ℝ)^q ≤ (1/512:ℝ)^t.card := by
    have h := (mem_filter.mp ht).2
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp [q,n]; omega
  have weighted : ((codes (V:=V)).card:ℝ)*(1/512:ℝ)^q ≤ b^n := by
    calc
      _ = ∑ _t ∈ codes (V:=V), (1/512:ℝ)^q := by simp
      _ ≤ _ := sum_le_sum (fun t ht => one t ht)
      _ ≤ ∑ t ∈ (univ : Finset V).powerset, (1/512:ℝ)^t.card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = b^n := by
        have h := sum_pow_mul_eq_add_pow (1/512:ℝ) 1 (univ : Finset V)
        norm_num [n,b] at h ⊢
        exact h
  have bound : ((codes (V:=V)).card:ℝ) ≤ (512:ℝ)^q*b^n := by
    have h := mul_le_mul_of_nonneg_left weighted (show 0≤(512:ℝ)^q by positivity)
    calc
      _ = ((codes (V:=V)).card:ℝ) * ((512:ℝ)*(1/512))^q := by norm_num
      _ = _ := by rw [mul_pow]; ring
      _ ≤ _ := h
  have step : q*513 ≤ n := Nat.div_mul_le_self n _
  have fixed : (512:ℝ)*b^513 ≤ (3:ℝ)^8 := by
    dsimp [b]
    have num : (512:ℚ)*(513/512)^513 ≤ (3:ℚ)^8 := by native_decide
    have casted : (((512:ℚ)*(513/512)^513 : ℚ):ℝ) ≤ (((3:ℚ)^8 : ℚ):ℝ) := Rat.cast_le.mpr num
    push_cast at casted; exact casted
  have all : ((codes (V:=V)).card:ℝ)^513 ≤ ((3:ℝ)^8)^n := by
    calc
      _ ≤ ((512:ℝ)^q*b^n)^513 := pow_le_pow_left₀ (by positivity) bound _
      _ = (512:ℝ)^(q*513)*(b^513)^n := by rw [mul_pow,← pow_mul,← pow_mul,← pow_mul,Nat.mul_comm n 513]
      _ ≤ (512:ℝ)^n*(b^513)^n := by
        apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) step)
        dsimp [b]; positivity
      _ ≤ _ := by rw [←mul_pow]; exact pow_le_pow_left₀ (by dsimp [b]; positivity) fixed _
  apply le_of_not_gt
  intro h
  have tooBig := pow_lt_pow_left₀ h (Real.rpow_nonneg (by norm_num) _) (by decide : (513:ℕ)≠0)
  have root : ((3:ℝ)^((8:ℝ)*n/513))^(513:ℕ) = ((3:ℝ)^8)^n := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    rw [←pow_mul,←Real.rpow_natCast]
    congr 1; push_cast; ring
  change ((3:ℝ)^(8*(n:ℝ)/513))^(513:ℕ) < _ at tooBig
  rw [root] at tooBig
  exact not_lt_of_ge all tooBig

theorem large_graph (sym : Symmetric r) (irr : Irreflexive r) {δ Δ : ℕ}
    (threshold : 4096≤δ) (cap : Δ≤2*δ)
    (lower : ∀ x, δ≤(neighbors r univ x).card) (upper : ∀ x, (neighbors r univ x).card≤Δ) :
    (mis r (univ : Finset V):ℝ) ≤ (3:ℝ)^((8192/35331+8/513)*(Fintype.card V:ℝ)) := by
  classical
  let n : ℝ := Fintype.card V
  have localBound (t : Finset V) : (mis r (low r t):ℝ) ≤ (3:ℝ)^(8192/35331*n) := by
    apply (moon_moser sym irr _).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hs := residual r sym threshold cap lower upper t
    dsimp [n]; linarith
  have cov := covering_bound r
  calc
    _ ≤ ∑ t ∈ codes, (mis r (low r t):ℝ) := by exact_mod_cast cov
    _ ≤ ∑ _t ∈ codes (V:=V), (3:ℝ)^(8192/35331*n) := sum_le_sum (fun t _ => localBound t)
    _ = ((codes (V:=V)).card:ℝ)*(3:ℝ)^(8192/35331*n) := by simp
    _ ≤ (3:ℝ)^(8*n/513)*(3:ℝ)^(8192/35331*n) :=
      mul_le_mul_of_nonneg_right number_of_codes (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [←Real.rpow_add (by norm_num)]; congr 1; dsimp [n]; ring

end
end Audit.Fingerprint
