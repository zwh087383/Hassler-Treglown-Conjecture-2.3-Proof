import Audit.Potential
import Sumfree.Induced

namespace Audit.GraphMeasure
open Finset Sumfree Fingerprint Potential
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop)

def cross (s t : Finset V) := ∑ x∈s,(neighbors r t x).card

theorem split_cross {a b : Finset V} (apart : Disjoint a b) (t : Finset V) :
    cross r t (a∪b)=cross r t a+cross r t b := by
  have one (x : V) : (neighbors r (a∪b) x).card=(neighbors r a x).card+(neighbors r b x).card := by
    unfold neighbors
    rw [filter_union,card_union_of_disjoint (apart.mono (filter_subset ..) (filter_subset ..))]
  simp only [cross,one,sum_add_distrib]

theorem split_volume (sym : Symmetric r) {a b : Finset V} (apart : Disjoint a b) :
    volume r (a∪b)=volume r a+volume r b+2*cross r a b := by
  change cross r (a∪b) _=_
  rw [split_cross r apart]
  have f (t : Finset V) : cross r (a∪b) t=cross r a t+cross r b t := sum_union apart
  rw [f,f,show cross r b a=cross r a b from cross_sum r sym b a]
  change _ = cross r a a+cross r b b+2*cross r a b
  omega

theorem removed (sym : Symmetric r) {s t : Finset V} (sub : t⊆s) {d : ℕ}
    (cap : ∀ x∈t,(neighbors r s x).card≤d) :
    volume r s+volume r t ≤ volume r (s\t)+2*(d*t.card) := by
  let b := s\t
  have dis : Disjoint t b := disjoint_left.mpr (fun _ ht hb => (mem_sdiff.mp hb).2 ht)
  have eq : t∪b=s := union_sdiff_of_subset sub
  have sum := split_cross r dis t
  rw [eq] at sum
  have ct : cross r t s ≤ d*t.card := calc
    _ ≤ ∑ _x∈t,d := sum_le_sum cap
    _ = _ := by simp [mul_comm]
  have vol := split_volume r sym dis
  rw [eq] at vol
  change _ = volume r t+cross r t b at sum
  change _ ≤ volume r b+_
  omega

theorem volume_insert (sym : Symmetric r) (irr : Irreflexive r) {t : Finset V} {x : V} (no : x∉t) :
    volume r (insert x t)=volume r t+2*(neighbors r t x).card := by
  have eq := split_volume r sym (a:={x}) (b:=t) (disjoint_singleton_left.mpr no)
  have empty : neighbors r {x} x=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro y hy
    obtain ⟨h,e⟩ := mem_filter.mp hy
    exact irr x ((mem_singleton.mp h) ▸ e)
  have v : volume r {x}=0 := by simp [volume,empty]
  simpa [v,cross] using eq

def mu (b : ℝ) (s : Finset V) : ℝ := (s.card:ℝ)/3+b*(s.card-(volume r s:ℝ)/2)

theorem difference (b : ℝ) {s t : Finset V} (sub : t⊆s) :
    mu r b s-mu r b (s\t)=(t.card:ℝ)/3+
      b*(t.card-((volume r s:ℝ)-volume r (s\t))/2) := by
  have n : ((s\t).card:ℝ)+t.card=s.card := by exact_mod_cast card_sdiff_add_card_eq_card sub
  unfold mu; rw [←n]; ring

theorem drop (sym : Symmetric r) {s t : Finset V} (sub : t⊆s) {d : ℕ}
    (cap : ∀ x∈t,(neighbors r s x).card≤d) {b : ℝ} (nonneg : 0≤b) :
    (t.card:ℝ)/3+b*(t.card-((d:ℝ)*t.card-(volume r t:ℝ)/2))
      ≤ mu r b s-mu r b (s\t) := by
  have h : (volume r s:ℝ)+volume r t ≤ volume r (s\t)+2*((d:ℝ)*t.card) := by
    exact_mod_cast removed r sym sub cap
  rw [difference r b sub]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (by linarith) nonneg) _

/-- Prescribing both positive and negative membership gives at most the MIS count
    after deleting all prescribed positions, even when some neighbors of selected
    vertices have not been prescribed. -/
theorem prescribed (sym : Symmetric r) (irr : Irreflexive r) (s a b : Finset V) :
    ((family r s).filter (fun i => a⊆i ∧ Disjoint i b)).card ≤ mis r (s\(a∪b)) := by
  let good := (s\(a∪b)).filter (fun z => ∀ x∈a,¬r z x)
  have sub : good⊆s\(a∪b) := filter_subset .. 
  apply le_trans _ (induced_mono (R:=r) sym sub (fun x _ => irr x))
  change _ ≤ mis r good
  apply card_le_card_of_injOn (fun i => i\a)
  · intro i hi
    obtain ⟨member,ai,apart⟩ := mem_filter.mp hi
    have spec := mem_family.mp member
    have sub : i\a⊆good := by
      intro z hz; obtain ⟨zi,za⟩ := mem_sdiff.mp hz
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨spec.1 zi,fun h => (mem_union.mp h).elim za (disjoint_left.mp apart zi)⟩,
        fun x hx => spec.2.1 _ zi _ (ai hx)⟩
    apply mem_family.mpr
    refine ⟨sub,fun z hz w hw => spec.2.1 _ (mem_sdiff.mp hz).1 _ (mem_sdiff.mp hw).1,?_⟩
    intro z hz missing
    obtain ⟨zb,free⟩ := mem_filter.mp hz
    have notin : z∉i := fun h => missing (mem_sdiff.mpr ⟨h,fun a => (mem_sdiff.mp zb).2 (mem_union_left _ a)⟩)
    obtain ⟨w,wi,edge⟩ := spec.2.2 _ (mem_sdiff.mp zb).1 notin
    exact ⟨w,mem_sdiff.mpr ⟨wi,fun wa => free _ wa edge⟩,edge⟩
  · intro i hi j hj eq
    have ai := (mem_filter.mp hi).2.1
    have aj := (mem_filter.mp hj).2.1
    simpa only [sdiff_union_of_subset ai,sdiff_union_of_subset aj] using congrArg (·∪a) eq

theorem inside_degree {t : Finset V} {x y : V} (hx : x∉t) (hy : y∈t) (adj : r x y)
    (sym : Symmetric r) (irr : Irreflexive r) :
    volume r t+2 ≤ volume r (insert x t) := by
  rw [volume_insert r sym irr hx]
  have h : 0<(neighbors r t x).card := card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,adj⟩⟩
  omega

end
end Audit.GraphMeasure
