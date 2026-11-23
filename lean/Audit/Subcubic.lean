import Audit.GraphMeasure
import Sumfree.Symmetric

namespace Audit.Subcubic
open Finset Sumfree Fingerprint Potential GraphMeasure
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop)

def Clique (t : Finset V) := ∀ x∈t,∀ y∈t,x≠y → r x y
def Triangle (s t : Finset V) := t⊆s ∧ t.card=3 ∧ Clique r t
def avoid (s t : Finset V) := (family r s).filter fun i => Disjoint i t

theorem clique_volume (irr : Irreflexive r) {t : Finset V} (cl : Clique r t) :
    volume r t=t.card*(t.card-1) := by
  have deg (x : V) (hx : x∈t) : (neighbors r t x).card=t.card-1 := by
    have eq : neighbors r t x=t.erase x := by
      ext y
      simp only [neighbors,mem_filter,mem_erase]
      exact ⟨fun h => ⟨fun e => irr x (e ▸ h.2),h.1⟩,
        fun h => ⟨h.2,cl _ hx _ h.2 h.1.symm⟩⟩
    rw [eq,card_erase_of_mem hx]
  calc
    _ = ∑ _x∈t,(t.card-1) := sum_congr rfl deg
    _ = _ := by simp

theorem closed_card (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V} {x : V} (xs : x∈s) :
    (closed r s x).card=(neighbors r s x).card+1 := by
  have eq : closed r s x=insert x (neighbors r s x) := by
    ext z
    simp only [mem_closed,mem_insert,neighbors,mem_filter]
    exact ⟨fun ⟨hz,h⟩ => h.elim Or.inl (fun e => Or.inr ⟨hz,sym e⟩),
      fun h => h.elim (fun e => ⟨e.symm ▸ xs,Or.inl e⟩) (fun h => ⟨h.1,Or.inr (sym h.2)⟩)⟩
  rw [eq]
  exact card_insert_of_not_mem (show x∉neighbors r s x from fun h => irr x (mem_filter.mp h).2)

theorem clique_closed {s t : Finset V} (sub : t⊆s) (cl : Clique r t) {x : V} (hx : x∈t) :
    t⊆closed r s x := by
  intro y hy; exact mem_closed.mpr ⟨sub hy,or_iff_not_imp_left.mpr (cl _ hy _ hx)⟩

theorem count_cover (s t : Finset V) :
    mis r s ≤ (∑ x∈t,(picked r s x ∅).card)+(avoid r s t).card := by
  have sub : family r s ⊆ (t.biUnion fun x => picked r s x ∅)∪avoid r s t := by
    intro i hi
    by_cases clear : Disjoint i t
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,clear⟩)
    · obtain ⟨x,xi,xt⟩ := not_disjoint_iff.mp clear
      exact mem_union_left _ (mem_biUnion.mpr ⟨x,xt,mem_picked.mpr ⟨mem_family.mp hi,xi,disjoint_empty_right _⟩⟩)
  exact ((card_le_card sub).trans (card_union_le ..)).trans (Nat.add_le_add_right (card_biUnion_le ..) _)

theorem avoid_zero (sym : Symmetric r) {s t : Finset V} {x : V} (xs : x∈s)
    (closedInside : closed r s x⊆t) : (avoid r s t).card=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨member,dis⟩ := mem_filter.mp hi
  obtain ⟨z,hz,zi⟩ := hit_closed sym (mem_family.mp member) xs
  exact disjoint_left.mp dis zi (closedInside hz)

theorem chosen_le (sym : Symmetric r) (irr : Irreflexive r) {s t : Finset V} {x : V}
    (sub : t⊆closed r s x) : (picked r s x ∅).card≤mis r (s\t) := by
  have h := picked_bound (R:=r) s x ∅
  rw [union_empty] at h
  exact h.trans (induced_mono sym (fun _ h => mem_sdiff.mpr ⟨(mem_sdiff.mp h).1,fun ht => (mem_sdiff.mp h).2 (sub ht)⟩) (fun y _ => irr y))

theorem trianglefree_count (sym : Symmetric r) (irr : Irreflexive r) {s : Finset V}
    (none : ¬∃ t,Triangle r s t) : (mis r s:ℝ) ≤ (2:ℝ)^((s.card:ℝ)/2) := by
  let e (x y : V) := x∈s ∧ y∈s ∧ r x y
  have tf : TriangleFree e := by
    intro x y z xy yz xz
    have e1 : x≠y := fun eq => irr x (eq ▸ xy.2.2)
    have e2 : y≠z := fun eq => irr y (eq ▸ yz.2.2)
    have e3 : x≠z := fun eq => irr x (eq ▸ xz.2.2)
    apply none
    refine ⟨{x,y,z},?_,?_,?_⟩
    · simp [insert_subset_iff,xy.1,xy.2.1,yz.2.1]
    · simp [e1,e2,e3]
    · intro a ha b hb ne
      simp only [mem_insert,mem_singleton] at ha hb
      rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
        first | exact (ne rfl).elim | exact xy.2.2 | exact yz.2.2 | exact xz.2.2 |
          exact sym xy.2.2 | exact sym yz.2.2 | exact sym xz.2.2
  have eq : mis r s=mis e s := count_congr (fun _ hx _ hy => ⟨fun p => ⟨hx,hy,p⟩,fun p => p.2.2⟩)
  rw [eq]
  exact hujter_tuza (fun _ _ h => ⟨h.2.1,h.1,sym h.2.2⟩) (fun x h => irr x h.2.2) tf s

theorem cutoff {b : ℝ} (pos : 0≤b) (small : b≤1/36) {s : Finset V}
    (cap : ∀ x∈s,(neighbors r s x).card≤3) :
    (2:ℝ)^((s.card:ℝ)/2) ≤ (3:ℝ)^(mu r b s) := by
  have h : (volume r s:ℝ)≤s.card*3 := by exact_mod_cast volume_le r cap
  have base : (2:ℝ)^(1/2:ℝ)≤(3:ℝ)^(23/72:ℝ) := by
    by_contra! bad
    have power := pow_lt_pow_left₀ bad (Real.rpow_nonneg (by norm_num) _) (by decide : (72:ℕ)≠0)
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),←Real.rpow_natCast,←Real.rpow_mul (by norm_num)] at power
    norm_num at power
  calc
    _ = ((2:ℝ)^(1/2:ℝ))^s.card := by rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]; congr 1; ring
    _ ≤ ((3:ℝ)^(23/72:ℝ))^s.card := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) base _
    _ = (3:ℝ)^((23/72:ℝ)*s.card) := by rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      unfold mu
      nlinarith only [mul_le_mul_of_nonneg_left h pos,
        mul_le_mul_of_nonneg_right small (Nat.cast_nonneg (α:=ℝ) s.card)]

theorem ratio {b : ℝ} {s t : Finset V} {p w : ℝ}
    (ind : (mis r (s\t):ℝ)≤(3:ℝ)^(mu r b (s\t)))
    (drop : p≤mu r b s-mu r b (s\t)) (factor : (3:ℝ)^(-p)≤w) :
    (mis r (s\t):ℝ)≤w*(3:ℝ)^(mu r b s) := by
  calc
    _ ≤ _ := ind
    _ ≤ (3:ℝ)^(-p+mu r b s) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := Real.rpow_add (by norm_num) _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right factor (Real.rpow_nonneg (by norm_num) _)

end
end Audit.Subcubic
