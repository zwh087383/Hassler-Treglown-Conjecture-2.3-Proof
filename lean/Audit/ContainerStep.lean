import Audit.Removal
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Audit.ContainerStep
open Finset
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

def hits (c : Finset G) (x : G) := c.filter fun y => y+x∈c
def moves (u t : Finset G) (x : G) := t.filter fun v => x+v∈u
def popular (l : ℕ) (c : Finset G) :=
  c.filter fun x => Fintype.card G ≤ 2*l*(hits c x).card
def rest (c t a : Finset G) :=
  c.filter fun y => ∀ x∈a, y-x∉t
def low (c t a : Finset G) (d : ℕ) :=
  (rest c t a).filter fun y => (moves (rest c t a) t y).card ≤ d
def codes (G : Type*) [Fintype G] (d : ℕ) :=
  ((univ : Finset G).powerset).filter fun a => d*a.card≤Fintype.card G

private theorem card_as_sum (a : Finset G) (p : G → Prop) [DecidablePred p] :
    (a.filter p).card = ∑ x∈a, if p x then 1 else 0 := by simp [←sum_filter]

theorem triple_count (c : Finset G) :
    (Removal.triples c).card = ∑ x∈c,(hits c x).card := by
  classical
  change ((c ×ˢ c).filter fun z : G × G => z.1+z.2∈c).card = _
  rw [show ((c ×ˢ c).filter fun z : G × G => z.1+z.2∈c).card =
    ∑ z∈c ×ˢ c, if z.1+z.2∈c then 1 else 0 by simp [←sum_filter],sum_product]
  apply sum_congr rfl
  intro x _; rw [hits,card_as_sum]; simp only [add_comm x]

theorem swap_count (c t : Finset G) :
    ∑ z∈t,(hits c z).card = ∑ y∈c,(moves c t y).card := by
  simp only [hits,moves,card_as_sum]; rw [sum_comm]

theorem popular_large {l : ℕ} {c : Finset G}
    (dense : (Fintype.card G)^2 ≤ l*(Removal.triples c).card) :
    Fintype.card G ≤ 2*l*(popular l c).card := by
  let n := Fintype.card G
  let p := popular l c
  have upper (x : G) (hx : x∈c) :
      2*l*(hits c x).card ≤ n + if x∈p then 2*l*n else 0 := by
    by_cases h : x∈p
    · rw [if_pos h]; exact (Nat.mul_le_mul_left _ (card_le_univ _)).trans (Nat.le_add_left ..)
    · rw [if_neg h,add_zero]
      exact le_of_not_ge (fun ge => h (mem_filter.mpr ⟨hx,ge⟩))
  have sumBound := sum_le_sum upper
  rw [←mul_sum,←triple_count,sum_add_distrib] at sumBound
  have filterEq : c.filter (·∈p) = p := by
    ext x; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => (mem_filter.mp h).1)
  rw [←sum_filter,filterEq] at sumBound
  simp only [sum_const,nsmul_eq_mul] at sumBound
  have nc : c.card*n≤n*n := Nat.mul_le_mul_right _ (card_le_univ _)
  have result : n*n≤(2*l*p.card)*n := by
    change n^2 ≤ l*(Removal.triples c).card at dense
    nlinarith only [dense,sumBound,nc]
  exact Nat.le_of_mul_le_mul_right result (Fintype.card_pos (α:=G))

private theorem move_image (c t : Finset G) (x : G) :
    (moves c t x).image (x+·) = c.filter fun y => y-x∈t := by
  ext y
  constructor
  · intro h; obtain ⟨v,hv,rfl⟩ := mem_image.mp h
    obtain ⟨vt,vc⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨vc,by simpa using vt⟩
  · intro h; obtain ⟨yc,yt⟩ := mem_filter.mp h
    refine mem_image.mpr ⟨y-x,mem_filter.mpr ⟨yt,by simpa using yc⟩,by simp⟩

theorem remove_moves (c t a : Finset G) (x : G) :
    (rest c t (insert x a)).card + (moves (rest c t a) t x).card = (rest c t a).card := by
  have eq : rest c t (insert x a) = (rest c t a).filter fun y => ¬y-x∈t := by
    ext y; simp [rest,and_assoc,and_left_comm,and_comm]
  have card := congrArg Finset.card (move_image (rest c t a) t x)
  rw [card_image_of_injective _ (add_right_injective _)] at card
  rw [eq,card,add_comm]; exact filter_card_add_filter_neg_card_eq_card .. 

theorem fingerprint {c t i : Finset G} (inside : i⊆c) (free : Link.Free i) (ti : t⊆i)
    (d : ℕ) :
    ∃ a∈codes G d, i ⊆ low c t a d := by
  classical
  let ok := i.powerset.filter fun a => d*a.card+(rest c t a).card ≤ c.card
  have emp : ∅∈ok := by simp [ok,rest]
  obtain ⟨a,ha,best⟩ := exists_max_image ok Finset.card ⟨_,emp⟩
  obtain ⟨ai,hcost⟩ := mem_filter.mp ha
  have rem : i⊆rest c t a := by
    intro x hx
    apply mem_filter.mpr ⟨inside hx,?_⟩
    intro y hy e
    exact free _ (ti e) _ ((mem_powerset.mp ai) hy) _ hx (sub_add_cancel x y)
  refine ⟨a,mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),
    (Nat.le_add_right _ _).trans (hcost.trans (card_le_univ _))⟩,?_⟩
  intro x hx
  refine mem_filter.mpr ⟨rem hx,?_⟩
  by_contra! many
  have fresh : x∉a := by
    intro xa
    have empty : moves (rest c t a) t x = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro y hy
      obtain ⟨yt,yr⟩ := mem_filter.mp hy
      exact (mem_filter.mp yr).2 x xa (by simpa using yt)
    simp [empty] at many
  have u := remove_moves c t a x
  have new : insert x a∈ok := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx (mem_powerset.mp ai)),?_⟩
    rw [card_insert_of_not_mem fresh,Nat.mul_succ]; omega
  have h := best _ new
  rw [card_insert_of_not_mem fresh] at h; omega

theorem hits_lost {u c : Finset G} (sub : u⊆c) (t : G) :
    (hits c t).card ≤ (hits u t).card + 2*(c.card-u.card) := by
  let lost := c \ u
  have incl : hits c t ⊆ (hits u t ∪ lost) ∪ lost.image (·-t) := by
    intro x hx
    obtain ⟨xc,xt⟩ := mem_filter.mp hx
    by_cases h : x∈u
    · by_cases a : x+t∈u
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨h,a⟩))
      · exact mem_union_right _ (mem_image.mpr ⟨x+t,mem_sdiff.mpr ⟨xt,a⟩,add_sub_cancel_right ..⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨xc,h⟩))
  have a := (card_le_card incl).trans (card_union_le ..)
  have b := card_union_le (hits u t) lost
  have f := card_image_le (f:=(·-t)) (s:=lost)
  have size : lost.card=c.card-u.card := card_sdiff sub
  omega

theorem low_shrinks {l d : ℕ} {c t a : Finset G} (lpos : 0<l) (dpos : 0<d)
    (inP : t⊆popular l c) (ts : t.card=4*l*d) :
    Fintype.card G ≤ 8*l*(c.card-(low c t a d).card) := by
  let u := low c t a d
  let n := Fintype.card G
  let loss := c.card-u.card
  have inc : u⊆c := (filter_subset _ _).trans (filter_subset _ _)
  have lower : t.card*n ≤ 2*l*∑ z∈t,(hits c z).card := by
    rw [mul_sum]
    simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using
      (sum_le_sum (s:=t) (f:=fun _ => n) (fun z hz => (mem_filter.mp (inP hz)).2))
  have upper : (∑ z∈t,(hits u z).card) ≤ n*d := by
    rw [swap_count]
    calc
      _ ≤ ∑ _y∈u, d := by
        apply sum_le_sum; intro y hy
        have sub : moves u t y ⊆ moves (rest c t a) t y := fun x hx =>
          mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp (mem_filter.mp hx).2).1⟩
        exact (card_le_card sub).trans (mem_filter.mp hy).2
      _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (card_le_univ _)
  have diff := sum_le_sum (s:=t) (fun z _ => hits_lost inc z)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at diff
  have h := lower.trans (Nat.mul_le_mul_left _ (diff.trans (Nat.add_le_add_right upper _)))
  change t.card*n ≤ 2*l*(n*d + t.card*(2*loss)) at h
  rw [ts] at h
  have factor : (2*l*d)*n ≤ (2*l*d)*(8*l*loss) := by nlinarith only [h]
  exact Nat.le_of_mul_le_mul_left factor (by positivity)

end
end Audit.ContainerStep
