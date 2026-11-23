import Audit.Fingerprint

namespace Audit.TriangleBase
open Finset Sumfree Fingerprint
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}

abbrev deg (r : V → V → Prop) (s : Finset V) (x : V) := (neighbors r s x).card
def cross (r : V → V → Prop) (a b : Finset V) := ∑ x∈a, deg r b x
abbrev vol (r : V → V → Prop) (s : Finset V) := cross r s s
def cost (r : V → V → Prop) (s : Finset V) : ℤ := 37*(s.card:ℤ)-vol r s
def weight (r : V → V → Prop) (s : Finset V) : ℝ := (2:ℝ)^((cost r s:ℝ)/72)
def cap (r : V → V → Prop) (s : Finset V) (n : ℕ) := ∀ x∈s, deg r s x≤n
def IH (r : V → V → Prop) (s : Finset V) := ∀ t ⊂ s, (mis r t:ℝ) ≤ weight r t
abbrev ball (r : V → V → Prop) (s : Finset V) (x : V) := closed r s x
abbrev cut (s : Finset V) (x : V) := s\{x}

theorem mono {a b : Finset V} (h : a⊆b) (x : V) : deg r a x≤deg r b x :=
  card_le_card (fun _ hy => mem_filter.mpr ⟨h (mem_filter.mp hy).1,(mem_filter.mp hy).2⟩)
theorem cap_sub {a b : Finset V} {n : ℕ} (h : a⊆b) (c : cap r b n) : cap r a n :=
  fun x hx => (mono h x).trans (c x (h hx))
theorem inherited {a b : Finset V} (h : a⊆b) (ih : IH r b) : IH r a :=
  fun t ht => ih t (Finset.ssubset_of_ssubset_of_subset ht h)
theorem ball_sub (s : Finset V) (x : V) : ball r s x⊆s := fun _ h => (mem_closed.mp h).1
theorem ball_self {s : Finset V} {x : V} (hx : x∈s) : x∈ball r s x := mem_closed.mpr ⟨hx,Or.inl rfl⟩
theorem del_strict {s t : Finset V} {x : V} (xs : x∈s) (xt : x∈t) : s\t ⊂ s :=
  Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun h => (mem_sdiff.mp (h.symm ▸ xs)).2 xt⟩

theorem ball_eq (sym : Symmetric r) {s : Finset V} {x : V} (xs : x∈s) :
    ball r s x=insert x (neighbors r s x) := by
  ext y
  simp only [mem_closed,mem_insert,neighbors,mem_filter]
  constructor
  · rintro ⟨ys,eq|h⟩
    · exact Or.inl eq
    · exact Or.inr ⟨ys,sym h⟩
  · rintro (rfl|⟨ys,h⟩)
    · exact ⟨xs,Or.inl rfl⟩
    · exact ⟨ys,Or.inr (sym h)⟩

theorem self_neigh (irr : Irreflexive r) (s : Finset V) (x : V) : x∉neighbors r s x :=
  fun h => irr x (mem_filter.mp h).2
theorem ball_card (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V} {x : V} (xs : x∈s) :
    (ball r s x).card=deg r s x+1 := by
  rw [ball_eq sym xs,card_insert_of_not_mem (self_neigh irr s x)]

theorem cross_left {a b : Finset V} (dis : Disjoint a b) (z : Finset V) :
    cross r (a∪b) z=cross r a z+cross r b z := sum_union dis
theorem cross_right (sym : Symmetric r) {a b : Finset V} (dis : Disjoint a b) (z : Finset V) :
    cross r z (a∪b)=cross r z a+cross r z b := by
  have flip (u v : Finset V) : cross r u v=cross r v u := cross_sum r sym u v
  rw [flip z (a∪b),cross_left dis,flip a z,flip b z]
theorem volume_id (sym : Symmetric r) {s t : Finset V} (ht : t⊆s) :
    vol r s+vol r t=vol r (s\t)+2*cross r t s := by
  let b:=s\t
  have dis : Disjoint b t := sdiff_disjoint
  have eq : b∪t=s := sdiff_union_of_subset ht
  have lhs : vol r s=vol r b+cross r b t+cross r t s := by
    have h := cross_left (r:=r) dis s
    rw [eq] at h
    change cross r s s=_
    rw [h,←cross_right sym dis b,eq]
  have rhs := cross_right (r:=r) sym dis t
  rw [eq] at rhs
  have fl : cross r b t=cross r t b := cross_sum r sym _ _
  change vol r s+cross r t t=vol r b+_
  omega

theorem ball_internal (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V} {x : V} (xs : x∈s) :
    2*deg r s x ≤ vol r (ball r s x) := by
  let n:=neighbors r s x
  let b:=ball r s x
  have xb : x∈b := ball_self xs
  have d : deg r b x=deg r s x := by
    apply congrArg Finset.card
    ext a
    simp only [neighbors,mem_filter,mem_closed,b]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1, Or.inr (sym h.2)⟩,h.2⟩⟩
  have pos (y : V) (hy : y∈n) : 1≤deg r b y :=
    card_pos.mpr ⟨x,mem_filter.mpr ⟨xb,sym (mem_filter.mp hy).2⟩⟩
  have lower : n.card ≤ cross r n b := by
    simpa only [cross,sum_const,nsmul_eq_mul,mul_one] using sum_le_sum pos
  have eq : vol r b = deg r b x+cross r n b := by
    exact (congrArg (fun z => ∑ a∈z,deg r b a) (ball_eq sym xs)).trans (sum_insert (self_neigh irr s x))
  change _ ≤ vol r b
  change deg r s x ≤ _ at lower
  omega

theorem closed_loss (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V} {x : V} (xs : x∈s) :
    37*((deg r s x:ℤ)+1)-2*cross r (neighbors r s x) s ≤ cost r s-cost r (s\ball r s x) := by
  let b:=ball r s x
  have ct := card_sdiff_add_card_eq_card (ball_sub (r:=r) s x)
  have vi := volume_id sym (ball_sub (r:=r) s x)
  have vn := ball_internal sym irr xs
  have cs : cross r b s=deg r s x+cross r (neighbors r s x) s := by
    unfold cross
    rw [show b=insert x (neighbors r s x) from ball_eq sym xs,sum_insert (self_neigh irr s x)]
  have sz := ball_card sym irr xs
  unfold cost
  dsimp only [b] at cs
  omega

theorem single_loss (sym : Symmetric r) {s : Finset V} {x : V} (xs : x∈s) :
    37-2*(deg r s x:ℤ) ≤ cost r s-cost r (cut s x) := by
  have ct := card_sdiff_add_card_eq_card (singleton_subset_iff.mpr xs)
  have vi := volume_id sym (singleton_subset_iff.mpr xs)
  have cs : cross r {x} s=deg r s x := by simp [cross]
  rw [cs] at vi
  rw [card_singleton] at ct
  unfold cost cut
  omega

theorem sum_le {s : Finset V} {x : V} {d : ℕ} (bound : ∀ y∈neighbors r s x,deg r s y≤d) :
    cross r (neighbors r s x) s≤deg r s x*d := by
  simpa only [cross,sum_const,nsmul_eq_mul] using sum_le_sum bound
theorem sum_one_low {s : Finset V} {x y : V} {d : ℕ}
    (hy : y∈neighbors r s x) (bound : ∀ z∈neighbors r s x,deg r s z≤d) :
    cross r (neighbors r s x) s + d ≤ deg r s x*d+deg r s y := by
  let n:=neighbors r s x
  have h : (∑ a∈n.erase y, deg r s a) ≤ (n.erase y).card*d := by
    simpa using sum_le_sum (s:=n.erase y) (g:=fun _ => d) (fun z hz => bound z (mem_of_mem_erase hz))
  have eq := n.sum_erase_add (fun z => deg r s z) hy
  change (∑ a∈n.erase y,deg r s a)+deg r s y=∑ a∈n,deg r s a at eq
  have ct := card_erase_add_one hy
  change (∑ a∈n,deg r s a)+d≤n.card*d+deg r s y
  rw [←show (n.erase y).card+1=n.card from ct,add_mul,one_mul]
  omega

theorem neg_power (n : ℕ) (q : ℝ) (hq : 0<q) (checked : 1≤(2:ℝ)^n*q^72) :
    (2:ℝ)^(-(n:ℝ)/72)≤q := by
  by_contra! h
  have hp := pow_lt_pow_left₀ h (n:=72) hq.le (by decide)
  have e : ((2:ℝ)^(-(n:ℝ)/72))^(72:ℕ)=((2:ℝ)^n)⁻¹ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    rw [show -(n:ℝ)/72*(↑(72:ℕ):ℝ) = -n by norm_num,Real.rpow_neg (by norm_num),Real.rpow_natCast]
  rw [e] at hp
  have hh := mul_lt_mul_of_pos_left hp (show 0<(2:ℝ)^n by positivity)
  rw [mul_inv_cancel₀ (by positivity)] at hh
  linarith

theorem compare {s t : Finset V} {n : ℕ} {q : ℝ}
    (loss : (n:ℤ)≤cost r s-cost r t) (certificate : (2:ℝ)^(-(n:ℝ)/72)≤q) :
    weight r t ≤ q*weight r s := by
  have realLoss : (n:ℝ)≤(cost r s:ℝ)-cost r t := by exact_mod_cast loss
  calc
    _ ≤ (2:ℝ)^(-(n:ℝ)/72+(cost r s:ℝ)/72) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := Real.rpow_add (by norm_num) _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right certificate (by positivity)

theorem vertex_branch (s : Finset V) (x : V) :
    mis r s ≤ mis r (cut s x)+mis r (s\ball r s x) := by
  let no := (family r s).filter fun I => x∉I
  have cover : family r s ⊆ no ∪ picked r s x ∅ := by
    intro I h; by_cases yes : x∈I
    · exact mem_union_right _ (mem_picked.mpr ⟨mem_family.mp h,yes,disjoint_empty_right _⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨h,yes⟩)
  have included : no⊆family r (cut s x) := by
    intro I hi
    obtain ⟨h,miss⟩ := mem_filter.mp hi
    have data := mem_family.mp h
    exact mem_family.mpr ⟨fun y hy => mem_sdiff.mpr ⟨data.1 hy,fun eq => miss ((mem_singleton.mp eq) ▸ hy)⟩,
      data.2.1,fun _ hz hn => data.2.2 _ (mem_sdiff.mp hz).1 hn⟩
  have yes := picked_bound (R:=r) s x ∅
  rw [union_empty] at yes
  exact ((card_le_card cover).trans (card_union_le ..)).trans (Nat.add_le_add (card_le_card included) yes)

end
end Audit.TriangleBase
