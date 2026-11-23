import Audit.Fingerprint
import Mathlib.Tactic.FieldSimp

namespace Audit.Potential
open Finset Fingerprint Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [DecidableEq V] [Fintype V] (r : V → V → Prop)

def volume (s : Finset V) := ∑ x∈s, (neighbors r s x).card
def measure (D : ℕ) (s : Finset V) : ℝ := s.card/3+((3:ℝ)*s.card-volume r s)/(8*D)

theorem degree_mono {s t : Finset V} (sub : s⊆t) (x : V) :
    (neighbors r s x).card ≤ (neighbors r t x).card :=
  card_le_card (fun _ h => mem_filter.mpr ⟨sub (mem_filter.mp h).1,(mem_filter.mp h).2⟩)

theorem volume_le {s : Finset V} {d : ℕ} (cap : ∀ x∈s,(neighbors r s x).card≤d) :
    volume r s ≤ s.card*d := by
  calc
    _ ≤ ∑ _x∈s,d := sum_le_sum cap
    _ = _ := by simp

theorem volume_removal (sym : Symmetric r) {s t : Finset V} (sub : t⊆s) {d : ℕ}
    (cap : ∀ x∈s,(neighbors r s x).card≤d) :
    volume r s ≤ volume r (s\t)+2*t.card*d := by
  let b := s\t
  have apart : Disjoint b t := disjoint_left.mpr (fun _ h => (mem_sdiff.mp h).2)
  have eq : b∪t=s := sdiff_union_of_subset sub
  have degree (x : V) : (neighbors r s x).card=(neighbors r b x).card+(neighbors r t x).card := by
    have f : neighbors r s x=neighbors r b x∪neighbors r t x := by
      simp only [←eq,neighbors,filter_union]
    rw [f]
    exact card_union_of_disjoint (apart.mono (filter_subset ..) (filter_subset ..))
  have bound := calc
    ∑ x∈t,(neighbors r s x).card ≤ ∑ _x∈t,d := sum_le_sum (fun x hx => cap x (sub hx))
    _ = t.card*d := by simp
  have cross : (∑ x∈b,(neighbors r t x).card) ≤ t.card*d := by
    rw [cross_sum r sym]
    exact (sum_le_sum (fun x _ => degree_mono r (sdiff_subset : b⊆s) x)).trans bound
  have totals : volume r s=volume r b+(∑ x∈b,(neighbors r t x).card)+∑ x∈t,(neighbors r s x).card := by
    unfold volume
    rw [show (∑ x∈s,(neighbors r s x).card)=(∑ x∈b,(neighbors r s x).card)+
      ∑ x∈t,(neighbors r s x).card from eq ▸ sum_union apart]
    congr 1
    simp_rw [degree]
    rw [sum_add_distrib]
  rw [totals]; change _ ≤ volume r b+_
  rw [Nat.mul_assoc]
  omega

theorem branch (s : Finset V) (x : V) :
    mis r s ≤ mis r (s\{x})+mis r (s\closed r s x) := by
  let no := (family r s).filter fun I => x∉I
  have cover : family r s ⊆ no ∪ picked r s x ∅ := by
    intro I h; by_cases yes : x∈I
    · exact mem_union_right _ (mem_picked.mpr ⟨mem_family.mp h,yes,disjoint_empty_right _⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨h,yes⟩)
  have included : no⊆family r (s\{x}) := by
    intro I hi
    obtain ⟨h,miss⟩ := mem_filter.mp hi
    have data := mem_family.mp h
    exact mem_family.mpr ⟨fun y hy => mem_sdiff.mpr ⟨data.1 hy,fun eq => miss ((mem_singleton.mp eq) ▸ hy)⟩,
      data.2.1,fun _ hz hn => data.2.2 _ (mem_sdiff.mp hz).1 hn⟩
  have yes := picked_bound (R:=r) s x ∅
  rw [union_empty] at yes
  exact ((card_le_card cover).trans (card_union_le ..)).trans (Nat.add_le_add (card_le_card included) yes)

private theorem drop (sym : Symmetric r) {s t : Finset V} (sub : t⊆s) {d D : ℕ}
    (cap : ∀ x∈s,(neighbors r s x).card≤d) (pos : 0<D) :
    measure r D (s\t) ≤ measure r D s-t.card*(1/3-(d:ℝ)/(4*D)) := by
  have v : (volume r s:ℝ) ≤ volume r (s\t)+(2:ℝ)*t.card*d := by
    exact_mod_cast volume_removal r sym sub cap
  have n : ((s\t).card:ℝ)+t.card=s.card := by exact_mod_cast card_sdiff_add_card_eq_card sub
  have pd : (0:ℝ)<D := by exact_mod_cast pos
  unfold measure
  apply le_of_mul_le_mul_right _ (show (0:ℝ)<24*D by positivity)
  have simplify (a b : ℝ) : (a/3+b/(8*D))*(24*D)=a*(8*D)+3*b := by field_simp; ring
  rw [sub_mul,simplify,simplify,mul_assoc]
  rw [show (1/3-(d:ℝ)/(4*D))*(24*D)=8*D-6*d from by field_simp; ring]
  nlinarith only [v,n,congrArg (fun z : ℝ => z*(D:ℝ)) n,Nat.cast_nonneg (α:=ℝ) t.card]

theorem neg_weight (p n : ℕ) (q : ℝ) (hn : 0<n) (hq : 0<q)
    (power : 1≤(3:ℝ)^p*q^n) : (3:ℝ)^(-(p:ℝ)/n) ≤ q := by
  have positive : (0:ℝ)<n := by exact_mod_cast hn
  by_contra! h
  have qlt := pow_lt_pow_left₀ h hq.le hn.ne'
  have e : ((3:ℝ)^(-(p:ℝ)/n))^n = ((3:ℝ)^p)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    rw [div_mul_cancel₀ _ positive.ne',Real.rpow_neg (by norm_num),Real.rpow_natCast]
  rw [e] at qlt
  have hh := mul_lt_mul_of_pos_left qlt (show 0<(3:ℝ)^p by positivity)
  rw [mul_inv_cancel₀ (by positivity)] at hh
  linarith

private theorem weights {d D : ℕ} (lo : 4≤d) (hi : d≤D) (large : 36≤D) :
    let a : ℝ := 1/3-(d:ℝ)/(4*D)
    (3:ℝ)^(-a)+(3:ℝ)^(-((d:ℝ)+1)*a) ≤ 1 := by
  dsimp only
  have pos : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have cap : (d:ℝ)≤D := by exact_mod_cast hi
  have dlo : (4:ℝ)≤d := by exact_mod_cast lo
  have big : (36:ℝ)≤D := by exact_mod_cast large
  let a : ℝ := 1/3-(d:ℝ)/(4*D)
  have combine (p q u v : ℝ) (hp : p≤a) (hq : q≤((d:ℝ)+1)*a)
      (first : (3:ℝ)^(-p)≤u) (second : (3:ℝ)^(-q)≤v) (sum : u+v≤1) :
      (3:ℝ)^(-a)+(3:ℝ)^(-((d:ℝ)+1)*a) ≤ 1 := by
    apply le_trans (add_le_add _ _) sum
    · exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hp)).trans first
    · apply le_trans _ second
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  by_cases small : d≤8
  · have dsmall : (d:ℝ)≤8 := by exact_mod_cast small
    have frac : (d:ℝ)/(4*D) ≤ 1/16 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have ha : 4/15≤a := by dsimp [a]; linarith
    apply combine (4/15) (4/3) (3/4) (1/4) ha
    · nlinarith only [mul_le_mul_of_nonneg_left ha (show 0≤(d:ℝ)+1 by positivity),dlo]
    · simpa only [Nat.cast_ofNat,neg_div] using neg_weight 4 15 (3/4) (by decide) (by norm_num) (by norm_num)
    · simpa only [Nat.cast_ofNat,neg_div] using neg_weight 4 3 (1/4) (by decide) (by norm_num) (by norm_num)
    · norm_num
  by_cases mid : d≤17
  · have dmax : (d:ℝ)≤17 := by exact_mod_cast mid
    have dmin : (9:ℝ)≤d := by exact_mod_cast (show 9≤d by omega)
    have frac : (d:ℝ)/(4*D) ≤ 2/15 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have ha : 1/5≤a := by dsimp [a]; linarith
    apply combine (1/5) 2 (8/9) (1/9) ha
    · calc
        (2:ℝ) ≤ ((d:ℝ)+1)*(1/5) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)
    · simpa only [Nat.cast_one,Nat.cast_ofNat,neg_div] using neg_weight 1 5 (8/9) (by decide) (by norm_num) (by norm_num)
    · norm_num
    · norm_num
  by_cases medium : d≤29
  · have dmax : (d:ℝ)≤29 := by exact_mod_cast medium
    have dmin : (18:ℝ)≤d := by exact_mod_cast (show 18≤d by omega)
    have frac : (d:ℝ)/(4*D) ≤ 5/24 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have ha : 1/8≤a := by dsimp [a]; linarith
    apply combine (1/8) (9/4) (9/10) (1/10) ha
    · nlinarith only [mul_le_mul_of_nonneg_left ha (show 0≤(d:ℝ)+1 by positivity),dmin]
    · simpa only [Nat.cast_one,Nat.cast_ofNat,neg_div] using neg_weight 1 8 (9/10) (by decide) (by norm_num) (by norm_num)
    · simpa only [Nat.cast_ofNat,neg_div] using neg_weight 9 4 (1/10) (by decide) (by norm_num) (by norm_num)
    · norm_num
  · have dlo' : (30:ℝ)≤d := by exact_mod_cast (show 30≤d by omega)
    have frac : (d:ℝ)/(4*D) ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    have ha : 1/12≤a := by dsimp [a]; linarith
    apply combine (1/12) (5/2) (11/12) (1/12) ha
    · nlinarith only [mul_le_mul_of_nonneg_left ha (show 0≤(d:ℝ)+1 by positivity),dlo']
    · simpa only [Nat.cast_one,Nat.cast_ofNat,neg_div] using neg_weight 1 12 (11/12) (by decide) (by norm_num) (by norm_num)
    · simpa only [Nat.cast_ofNat,neg_div] using neg_weight 5 2 (1/12) (by decide) (by norm_num) (by norm_num)
    · norm_num

theorem bounded (sym : Symmetric r) (irr : Irreflexive r) (D : ℕ) (large : 36≤D)
    (s : Finset V) (cap : ∀ x∈s,(neighbors r s x).card≤D) :
    (mis r s:ℝ) ≤ (3:ℝ)^(measure r D s) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases subcubic : ∀ x∈s,(neighbors r s x).card≤3
    · apply (moon_moser sym irr s).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
      have v : (volume r s:ℝ) ≤ s.card*3 := by exact_mod_cast volume_le r subcubic
      exact le_add_of_nonneg_right (div_nonneg (by linarith) (by positivity))
    push_neg at subcubic
    obtain ⟨y,ys,ydeg⟩ := subcubic
    obtain ⟨x,xs,maximal⟩ := s.exists_max_image (fun x => (neighbors r s x).card) ⟨y,ys⟩
    let d := (neighbors r s x).card
    have dlo : 4≤d := Nat.le_trans ydeg (maximal y ys)
    let b := closed r s x
    have xb : x∈b := mem_closed.mpr ⟨xs,Or.inl rfl⟩
    have bs : b⊆s := fun _ h => (mem_closed.mp h).1
    have bsize : b.card=d+1 := by
      have eq : b=insert x (neighbors r s x) := by
        ext z
        simp only [b,mem_closed,mem_insert,neighbors,mem_filter]
        constructor
        · rintro ⟨hz,h|h⟩
          · exact Or.inl h
          · exact Or.inr ⟨hz,sym h⟩
        · rintro (rfl|⟨hz,h⟩)
          · exact ⟨xs,Or.inl rfl⟩
          · exact ⟨hz,Or.inr (sym h)⟩
      rw [eq]
      exact card_insert_of_not_mem (show x∉neighbors r s x from fun h => irr x (mem_filter.mp h).2)
    let a : ℝ := 1/3-(d:ℝ)/(4*D)
    have reduced (t : Finset V) (xt : x∈t) (ts : t⊆s) :
        (mis r (s\t):ℝ) ≤ (3:ℝ)^(measure r D s-(t.card:ℝ)*a) := by
      have strict : s\t ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun h =>
        (mem_sdiff.mp (h.symm ▸ xs)).2 xt⟩
      apply (ih _ strict (fun u hu => (degree_mono r sdiff_subset _).trans (cap _ (mem_sdiff.mp hu).1))).trans
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact drop r sym ts maximal (by omega)
    have sel := reduced b xb bs
    rw [bsize,Nat.cast_add,Nat.cast_one] at sel
    have skip := reduced {x} (mem_singleton_self x) (singleton_subset_iff.mpr xs)
    rw [card_singleton,Nat.cast_one,one_mul] at skip
    have w := weights dlo (cap x xs) large
    have sum : (3:ℝ)^(measure r D s-a)+(3:ℝ)^(measure r D s-((d:ℝ)+1)*a)
        ≤ (3:ℝ)^(measure r D s) := by
      simp only [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ)<3),←mul_add]
      have z : (3:ℝ)^(-a)+(3:ℝ)^(-(((d:ℝ)+1)*a))≤1 := by simpa only [neg_mul] using w
      exact (mul_le_mul_of_nonneg_left z (Real.rpow_nonneg (by norm_num) _)).trans_eq (mul_one _)
    exact le_trans (by exact_mod_cast branch r s x) ((add_le_add skip sel).trans sum)

/-- A two-degree graph of sufficiently large maximum degree meets the sharp exponent
    whenever its average degree is at least three quarters of the maximum. -/
theorem dense (sym : Symmetric r) (irr : Irreflexive r) {D : ℕ} (large : 36≤D)
    (s : Finset V) (cap : ∀ x∈s,(neighbors r s x).card≤D) (avg : 3*D*s.card≤4*volume r s) :
    (mis r s:ℝ) ≤ (3:ℝ)^((s.card:ℝ)/4) := by
  apply (bounded r sym irr D large s cap).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
  have av : (3:ℝ)*D*s.card ≤ 4*volume r s := by exact_mod_cast avg
  have dl : (36:ℝ)≤D := by exact_mod_cast large
  have pos : (0:ℝ)<D := by linarith
  unfold measure
  apply le_of_mul_le_mul_right _ (show (0:ℝ)<24*D by positivity)
  have a (n v : ℝ) : (n/3+(3*n-v)/(8*D))*(24*D)=n*(8*D)+3*(3*n-v) := by field_simp; ring
  rw [a,show ((s.card:ℝ)/4)*(24*D)=s.card*(6*D) by ring]
  nlinarith only [av,mul_le_mul_of_nonneg_right dl (Nat.cast_nonneg (α:=ℝ) s.card)]

end
end Audit.Potential
