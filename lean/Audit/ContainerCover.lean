import Audit.ContainerStep

namespace Audit.ContainerCover
open Finset ContainerStep
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

def options (l d : ℕ) (c : Finset G) : Finset (Finset G) :=
  let pool := codes G d
  insert c ((pool.image (fun t => (c \ popular l c) ∪ t)) ∪
    ((pool ×ˢ pool).image fun p => low c p.1 p.2 d))

def rate (G : Type*) [Fintype G] (d : ℕ) :=
  1 + (codes G d).card + (codes G d).card ^ 2

theorem options_card (l d : ℕ) (c : Finset G) : (options l d c).card ≤ rate G d := by
  classical
  let f (t : Finset G) := (c \ popular l c)∪t
  let g (p : Finset G × Finset G) := low c p.1 p.2 d
  let pool := codes G d
  let a := pool.image f
  let b := (pool ×ˢ pool).image g
  have h := (card_insert_le c (a∪b)).trans (Nat.add_le_add_right (card_union_le a b) 1)
  have x : a.card≤pool.card := card_image_le
  have y : b.card≤pool.card^2 := by simpa only [card_product,pow_two] using
    (card_image_le (s:=pool ×ˢ pool) (f:=g))
  change (insert c (a∪b)).card ≤ 1+pool.card+pool.card^2
  omega

theorem dense_step {l d : ℕ} (lp : 0<l) (dp : 0<d)
    (large1 : 4*l*(4*l*d)≤Fintype.card G) (large2 : d*(4*l*d)≤Fintype.card G)
    {c i : Finset G} (inside : i⊆c) (free : Link.Free i)
    (dense : (Fintype.card G)^2 ≤ l*(Removal.triples c).card) :
    ∃ v∈options l d c, i⊆v ∧ v⊆c ∧ Fintype.card G≤8*l*(c.card-v.card) := by
  classical
  let n := Fintype.card G
  let p := popular l c
  let t0 := i∩p
  let tSize := 4*l*d
  have pc : p⊆c := filter_subset _ _
  have code {t : Finset G} (h : t.card≤tSize) : t∈codes G d :=
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),(Nat.mul_le_mul_left _ h).trans large2⟩
  by_cases enough : tSize ≤ t0.card
  · obtain ⟨t,it,card⟩ := exists_subset_card_eq enough
    have tip : t⊆p := it.trans inter_subset_right
    obtain ⟨a,ac,inLow⟩ := fingerprint inside free (it.trans inter_subset_left) d
    refine ⟨low c t a d,mem_insert_of_mem (mem_union_right _ (mem_image.mpr
      ⟨(t,a),mem_product.mpr ⟨code card.le,ac⟩,rfl⟩)),inLow,?_,low_shrinks lp dp tip card⟩
    exact (filter_subset _ _).trans (filter_subset _ _)
  · let v := (c \ p)∪t0
    have ct : t0.card≤tSize := le_of_not_ge enough
    have vc : v⊆c := union_subset sdiff_subset (inter_subset_left.trans inside)
    have cv : v.card≤(c.card-p.card)+t0.card := by
      simpa only [card_sdiff pc] using card_union_le (c \ p) t0
    have cl := card_le_card pc
    have hc := card_le_card vc
    have diff : (c.card-v.card)+t0.card ≥ p.card := by omega
    have bigP := popular_large dense
    have smallT := (Nat.mul_le_mul_left (4*l) ct).trans large1
    have h := Nat.mul_le_mul_left (4*l) diff
    have shrink : Fintype.card G ≤ 4*l*(c.card-v.card) := by
      change Fintype.card G ≤ 2*l*p.card at bigP
      nlinarith only [h,bigP,smallT]
    refine ⟨v,mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨t0,code ct,rfl⟩)),?_,vc,?_⟩
    · intro x hx; by_cases xp : x∈p
      · exact mem_union_right _ (mem_inter.mpr ⟨hx,xp⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨inside hx,xp⟩)
    · exact shrink.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right l (by decide : 4≤8)))

def descendants (l d : ℕ) : ℕ → Finset G → Finset (Finset G)
  | 0,c => {c}
  | f+1,c => (options l d c).biUnion (descendants l d f)

theorem stay (l d f : ℕ) (c : Finset G) : c∈descendants l d f c := by
  induction f generalizing c with
  | zero => simp [descendants]
  | succ f ih => exact mem_biUnion.mpr ⟨c,mem_insert_self ..,ih _⟩

theorem descendants_card (l d f : ℕ) (c : Finset G) :
    (descendants l d f c).card ≤ (rate G d)^f := by
  induction f generalizing c with
  | zero => simp [descendants]
  | succ f ih =>
    calc
      _ ≤ ∑ x∈options l d c,(descendants l d f x).card := card_biUnion_le ..
      _ ≤ ∑ _x∈options l d c,(rate G d)^f := sum_le_sum fun x _ => ih x
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul,pow_succ']
        exact Nat.mul_le_mul_right _ (options_card ..)

theorem cover (l d : ℕ) (lp : 0<l) (dp : 0<d)
    (large1 : 4*l*(4*l*d)≤Fintype.card G) (large2 : d*(4*l*d)≤Fintype.card G)
    {i : Finset G} (free : Link.Free i) (f : ℕ) (c : Finset G) (inside : i⊆c)
    (fuel : 8*l*c.card≤f*Fintype.card G) :
    ∃ v∈descendants l d f c, i⊆v ∧ l*(Removal.triples v).card < (Fintype.card G)^2 := by
  induction f generalizing c with
  | zero =>
    have empty : c=∅ := card_eq_zero.mp (by simpa [Nat.mul_eq_zero,lp.ne'] using fuel)
    subst c; refine ⟨∅,stay ..,inside,?_⟩
    simp [Removal.triples,Fintype.card_pos]
  | succ f ih =>
    by_cases done_ : l*(Removal.triples c).card < (Fintype.card G)^2
    · exact ⟨c,stay ..,inside,done_⟩
    obtain ⟨v,allowed,iv,vc,gain⟩ := dense_step lp dp large1 large2 inside free (le_of_not_gt done_)
    have card := card_le_card vc
    have sum : c.card-v.card+v.card=c.card := Nat.sub_add_cancel card
    have scaled := congrArg (8*l*·) sum
    dsimp only at scaled
    rw [Nat.mul_add] at scaled
    have fbound : 8*l*c.card ≤ f*Fintype.card G+Fintype.card G := by
      simpa only [Nat.add_mul,one_mul] using fuel
    have budget : 8*l*v.card ≤ f*Fintype.card G := by
      exact Nat.le_of_add_le_add_right
        (show 8*l*v.card+Fintype.card G ≤ f*Fintype.card G+Fintype.card G from
          (Nat.add_le_add_left gain _).trans (by rw [add_comm,scaled]; exact fbound))
    obtain ⟨a,ha,ai,asparse⟩ := ih v iv budget
    exact ⟨a,mem_biUnion.mpr ⟨v,allowed,ha⟩,ai,asparse⟩

theorem finite_covers (l d : ℕ) (lp : 0<l) (dp : 0<d)
    (large1 : 4*l*(4*l*d)≤Fintype.card G) (large2 : d*(4*l*d)≤Fintype.card G) :
    ∃ F : Finset (Finset G), F.card ≤ (rate G d)^(8*l) ∧
      (∀ i : Finset G, Link.Free i → ∃ c∈F,i⊆c) ∧
      ∀ c∈F,l*(Removal.triples c).card < (Fintype.card G)^2 := by
  let all := descendants l d (8*l) (univ : Finset G)
  let F := all.filter fun c => l*(Removal.triples c).card < (Fintype.card G)^2
  refine ⟨F,(card_le_card (filter_subset _ _)).trans (descendants_card ..),?_,fun _ h => (mem_filter.mp h).2⟩
  intro i fi
  obtain ⟨c,h,ic,sc⟩ := cover l d lp dp large1 large2 fi (8*l) univ (subset_univ _) (by simp)
  exact ⟨c,mem_filter.mpr ⟨h,sc⟩,ic⟩

end
end Audit.ContainerCover
