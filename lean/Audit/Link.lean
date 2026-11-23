import Sumfree.Graph
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Audit.Link
open Finset
open scoped Classical
variable {G : Type*} [DecidableEq G] [Add G]
set_option linter.unusedSectionVars false

def Free (a : Finset G) := ∀ x ∈ a, ∀ y ∈ a, ∀ z ∈ a, x+y ≠ z
theorem smaller {a b : Finset G} (sub : a ⊆ b) (h : Free b) : Free a :=
  fun x hx y hy z hz => h x (sub hx) y (sub hy) z (sub hz)

/-- This pair definition includes precisely the possible Schur obstructions
    involving the seed. It also allows repeated summands. -/
def clash (s : Finset G) (x y : G) := x ≠ y ∧ ¬Free (insert x (insert y s))
noncomputable def legal (s b : Finset G) := by
  classical exact b.filter fun x => Free (insert x s)
@[simp] theorem mem_legal {s b : Finset G} {x : G} :
    x ∈ legal s b ↔ x∈b ∧ Free (insert x s) := by classical simp [legal]
theorem clash_sym (s : Finset G) : Symmetric (clash s) := by
  intro x y h
  exact ⟨h.1.symm,by simpa only [insert_comm y x] using h.2⟩

def MaxIn (b i : Finset G) : Prop :=
  i ⊆ b ∧ Free i ∧ ∀ j ⊆ b, Free j → i ⊆ j → j=i
def RelMax (s b i : Finset G) : Prop :=
  i ⊆ b ∧ Free (s∪i) ∧ ∀ j ⊆ b, Free (s∪j) → i ⊆ j → j=i

theorem pair_test {s b i : Finset G} (hs : Free s) (hb : Free b) (hi : i ⊆ b) :
    Free (s∪i) ↔ ∀ x∈i, ∀ y∈i, Free (insert x (insert y s)) := by
  constructor
  · intro h x hx y hy
    apply smaller _ h
    simp [insert_subset_iff,mem_union_right _ hx,mem_union_right _ hy]
  · intro pair x hx y hy z hz
    rcases mem_union.mp hx with xs|xi <;> rcases mem_union.mp hy with ys|yi <;>
      rcases mem_union.mp hz with zs|zi
    · exact hs x xs y ys z zs
    · apply pair z zi z zi x (by simp [xs]) y (by simp [ys]) z (by simp)
    · apply pair y yi y yi x (by simp [xs]) y (by simp) z (by simp [zs])
    · apply pair y yi z zi x (by simp [xs]) y (by simp) z (by simp)
    · apply pair x xi x xi x (by simp) y (by simp [ys]) z (by simp [zs])
    · apply pair x xi z zi x (by simp) y (by simp [ys]) z (by simp)
    · apply pair x xi y yi x (by simp) y (by simp) z (by simp [zs])
    · exact hb x (hi xi) y (hi yi) z (hi zi)

theorem compatible {s b i : Finset G} (hs : Free s) (hb : Free b) :
    i ⊆ b ∧ Free (s∪i) ↔ i ⊆ legal s b ∧ Sumfree.Independent (clash s) i := by
  constructor
  · rintro ⟨sub,free⟩
    have p := (pair_test hs hb sub).mp free
    exact ⟨fun x hx => mem_legal.mpr ⟨sub hx,by simpa using p x hx x hx⟩,
      fun x hx y hy e => e.2 (p x hx y hy)⟩
  · rintro ⟨safe,ind⟩
    have sub : i ⊆ b := fun x hx => (mem_legal.mp (safe hx)).1
    refine ⟨sub,(pair_test hs hb sub).mpr ?_⟩
    intro x hx y hy
    by_cases eq : x=y
    · subst y; simpa using (mem_legal.mp (safe hx)).2
    · by_contra bad; exact ind x hx y hy ⟨eq,bad⟩

theorem relative_iff {s b i : Finset G} (hs : Free s) (hb : Free b) :
    RelMax s b i ↔ Sumfree.IsMIS (clash s) (legal s b) i := by
  rw [Sumfree.isMIS_iff_maximal (clash_sym s) (fun x _ h => h.1 rfl)]
  constructor
  · rintro ⟨sub,free,maxi⟩
    obtain ⟨inb,ind⟩ := (compatible hs hb).mp ⟨sub,free⟩
    refine ⟨inb,ind,?_⟩
    intro j hj jind hij
    obtain ⟨sb,fj⟩ := (compatible hs hb).mpr ⟨hj,jind⟩
    exact maxi j sb fj hij
  · rintro ⟨inb,ind,maxi⟩
    obtain ⟨sb,free⟩ := (compatible hs hb).mpr ⟨inb,ind⟩
    refine ⟨sb,free,?_⟩
    intro j hj fj hij
    obtain ⟨safe,ij⟩ := (compatible hs hb).mp ⟨hj,fj⟩
    exact maxi j safe ij hij

noncomputable def maximalSets (b : Finset G) := by
  classical exact b.powerset.filter (MaxIn b)
@[simp] theorem mem_maximalSets {i b : Finset G} : i∈maximalSets b ↔ MaxIn b i := by
  classical simp only [maximalSets,mem_filter,mem_powerset,and_iff_right_iff_imp]; exact fun h => h.1

theorem extend {a b : Finset G} (f : Free a) (sub : a ⊆ b) :
    ∃ j ∈ maximalSets b, a⊆j := by
  classical
  let candidates := b.powerset.filter (fun j => a⊆j ∧ Free j)
  have ha : a ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr sub,Subset.rfl,f⟩
  obtain ⟨j,hj,m⟩ := exists_max_image candidates Finset.card ⟨_,ha⟩
  obtain ⟨jb,aj,fj⟩ := mem_filter.mp hj
  refine ⟨j,mem_maximalSets.mpr ⟨mem_powerset.mp jb,fj,?_⟩,aj⟩
  intro k kb fk jk
  exact (eq_of_subset_of_card_le jk (m k (mem_filter.mpr ⟨mem_powerset.mpr kb,aj.trans jk,fk⟩))).symm

/-- Each maximal link choice extends injectively to a global maximal sum-free set. -/
theorem lower_injection [Fintype G] {s b : Finset G} (hs : Free s) (hb : Free b) :
    Sumfree.mis (clash s) (legal s b) ≤ (maximalSets (univ : Finset G)).card := by
  classical
  let domain := Sumfree.family (clash s) (legal s b)
  have choice (i : ↥domain) : ∃ j ∈ maximalSets (univ : Finset G), s∪i.val ⊆ j :=
    extend ((relative_iff hs hb).mpr (Sumfree.mem_family.mp i.2)).2.1 (subset_univ _)
  choose f hf sub using choice
  have restrict (i : ↥domain) : f i ∩ b = i.val := by
    have h := (relative_iff hs hb).mpr (Sumfree.mem_family.mp i.2)
    apply h.2.2 _ inter_subset_right
    · apply smaller _ (mem_maximalSets.mp (hf i)).2.1
      exact union_subset (subset_union_left.trans (sub i)) inter_subset_left
    · exact subset_inter (subset_union_right.trans (sub i)) h.1
  have inj : Function.Injective (fun i : ↥domain => (⟨f i,hf i⟩ : ↥(maximalSets (univ : Finset G)))) := by
    intro a b e; apply Subtype.ext
    rw [← restrict a,← restrict b,show f a=f b from congrArg Subtype.val e]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ inj

theorem capture [Fintype G] {x b : Finset G} (mx : MaxIn univ x) :
    RelMax (x\b) b (x∩b) := by
  have split : x\b ∪ (x∩b) = x := by ext z; by_cases h : z∈b <;> simp [h]
  refine ⟨inter_subset_right,split.symm ▸ mx.2.1,?_⟩
  intro j jb free sub
  have up : x ⊆ (x\b)∪j := by
    conv_lhs => rw [← split]
    exact union_subset_union_right sub
  have eq := mx.2.2 _ (subset_univ _) free up
  exact Subset.antisymm (subset_inter (eq ▸ subset_union_right) jb) sub

/-- Count all globally maximal sets inside one container after its sum-free
    part is extended to b. The hypotheses allow e to overlap b. -/
theorem container_count [Fintype G] (b e : Finset G) (hb : Free b) :
    ((maximalSets (univ : Finset G)).filter fun x => x ⊆ b∪e).card ≤
      ∑ s ∈ e.powerset.filter (fun s => Free s), Sumfree.mis (clash s) (legal s b) := by
  classical
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun x => Sigma.mk (x\b) (x∩b))
  · intro x hx
    obtain ⟨xm,inC⟩ := mem_filter.mp hx
    have mx := mem_maximalSets.mp xm
    have fs := smaller (sdiff_subset : x\b ⊆ x) mx.2.1
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_powerset.mpr ?_,fs⟩,Sumfree.mem_family.mpr ((relative_iff fs hb).mp (capture mx))⟩
    intro z hz
    exact (mem_union.mp (inC (mem_sdiff.mp hz).1)).resolve_left (mem_sdiff.mp hz).2
  · intro x _ y _ eq
    have first := congrArg Sigma.fst eq
    have second := congrArg (fun p : (Σ _s : Finset G, Finset G) => p.2) eq
    change x\b=y\b at first
    change x∩b=y∩b at second
    ext z
    by_cases h : z∈b
    · simpa [h] using (Finset.ext_iff.mp second z)
    · simpa [h] using (Finset.ext_iff.mp first z)

end Audit.Link
