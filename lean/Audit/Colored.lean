import Audit.Subcubic

namespace Audit.Colored
open Finset Fingerprint Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (blue red : V → V → Prop)

def edge (x y : V) := blue x y ∨ red x y
def Valid (s I : Finset V) : Prop :=
  I⊆s ∧ Independent blue I ∧
  (∀ x∈I,∀ u∈I,∀ v∈I,red x u → red x v → u=v) ∧
  ∀ x∈s,x∉I → ∃ y∈I,edge blue red x y
def family (s : Finset V) := s.powerset.filter (Valid blue red s)
@[simp] theorem mem_family {s I : Finset V} : I∈family blue red s ↔ Valid blue red s I := by
  simp only [family,mem_filter,mem_powerset,and_iff_right_iff_imp]
  exact fun h => h.1
def pattern (s a d : Finset V) := (family blue red s).filter fun I => I∩d=a

theorem pattern_le (sym : Symmetric (edge blue red)) (s a d : Finset V)
    (closed : ∀ x∈a,∀ y∈s,edge blue red x y → y∈d) :
    (pattern blue red s a d).card ≤ (family blue red (s\d)).card := by
  apply card_le_card_of_injOn (fun I => I\d)
  · intro I hi
    obtain ⟨mem,part⟩ := mem_filter.mp hi
    obtain ⟨sub,ind,degree,dom⟩ := (mem_family ..).mp mem
    apply (mem_family ..).mpr
    refine ⟨fun z h => mem_sdiff.mpr ⟨sub (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩,
      fun x hx y hy => ind x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1,
      fun x hx u hu v hv => degree x (mem_sdiff.mp hx).1 u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1,?_⟩
    intro z hz missing
    obtain ⟨zs,zd⟩ := mem_sdiff.mp hz
    obtain ⟨y,yi,e⟩ := dom z zs (fun old => missing (mem_sdiff.mpr ⟨old,zd⟩))
    exact ⟨y,mem_sdiff.mpr ⟨yi,fun yd => zd (closed y (part ▸ mem_inter.mpr ⟨yi,yd⟩) z zs (sym e))⟩,e⟩
  · intro I hi J hj same
    have a := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
    apply Finset.ext; intro z
    by_cases d0 : z∈d
    · simpa only [mem_inter,d0,and_true] using Finset.ext_iff.mp a z
    · simpa only [mem_sdiff,d0,not_false_eq_true,and_true] using Finset.ext_iff.mp same z

theorem edge_sym (bs : Symmetric blue) (rs : Symmetric red) : Symmetric (edge blue red) :=
  fun x y h => h.imp (fun e => @bs x y e) (fun e => @rs x y e)
theorem edge_irr (bi : Irreflexive blue) (ri : Irreflexive red) : Irreflexive (edge blue red) :=
  fun x h => h.elim (bi x) (ri x)

theorem branch (bs : Symmetric blue) (rs : Symmetric red)
    (bi : Irreflexive blue) (ri : Irreflexive red) (s : Finset V) {x : V} (xs : x∈s) :
    let g := edge blue red
    let n := closed g s x
    let r := neighbors red s x
    let f := family blue red
    let skipped := (f s).filter (fun I => x∉I)
    (f s).card ≤ skipped.card+(f (s\n)).card+∑ y∈r,(f (s\(n∪closed g s y))).card := by
  dsimp only
  let g := edge blue red
  let n := closed g s x
  let r := neighbors red s x
  let f := family blue red
  let no := (f s).filter (fun I => x∉I)
  let one := pattern blue red s {x} n
  let both (y : V) := pattern blue red s {x,y} (n∪closed g s y)
  have sym := edge_sym blue red bs rs
  have partner {I : Finset V} (valid : Valid blue red s I) {x : V} (xi : x∈I) :
      ∀ y∈I, g x y → red x y := fun y yi h => h.resolve_left (valid.2.1 _ xi _ yi)
  have sub : f s ⊆ (no∪one)∪r.biUnion both := by
    intro I hi
    have valid := (mem_family blue red).mp hi
    by_cases xi : x∈I
    case neg => exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,xi⟩))
    by_cases paired : ∃ y∈I,red x y
    case neg =>
      apply mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,?_⟩))
      ext z
      constructor
      · intro h; obtain ⟨zi,zc⟩ := mem_inter.mp h
        rcases (mem_closed.mp zc).2 with eq|e
        · exact mem_singleton.mpr eq
        · exact (paired ⟨z,zi,partner valid xi _ zi (sym e)⟩).elim
      · intro h; obtain rfl := mem_singleton.mp h; exact mem_inter.mpr ⟨xi,mem_closed.mpr ⟨xs,Or.inl rfl⟩⟩
    obtain ⟨y,yi,xy⟩ := paired
    refine mem_union_right _ (mem_biUnion.mpr ⟨y,mem_filter.mpr ⟨valid.1 yi,xy⟩,?_⟩)
    change I∈pattern blue red s {x,y} (n∪closed g s y)
    refine mem_filter.mpr ⟨hi,?_⟩
    ext z
    constructor
    · intro h; obtain ⟨zi,zc⟩ := mem_inter.mp h
      rcases mem_union.mp zc with h|h <;> rcases (mem_closed.mp h).2 with eq|e
      · exact mem_insert.mpr (Or.inl eq)
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (valid.2.2.1 x xi z zi y yi (partner valid xi _ zi (sym e)) xy)))
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr eq))
      · exact mem_insert.mpr (Or.inl (valid.2.2.1 y yi z zi x xi (partner valid yi _ zi (sym e)) (rs xy)))
    · intro h; rcases (show z=x ∨ z=y by simpa using h) with rfl|rfl
      · exact mem_inter.mpr ⟨xi,mem_union_left _ (mem_closed.mpr ⟨xs,Or.inl rfl⟩)⟩
      · exact mem_inter.mpr ⟨yi,mem_union_right _ (mem_closed.mpr ⟨valid.1 yi,Or.inl rfl⟩)⟩
  have h1 : one.card ≤ (f (s\n)).card := by
    apply pattern_le blue red sym
    intro u hu z zs e; obtain rfl := mem_singleton.mp hu; exact mem_closed.mpr ⟨zs,Or.inr (sym e)⟩
  have h2 (y : V) : (both y).card ≤ (f (s\(n∪closed g s y))).card := by
    apply pattern_le blue red sym
    intro u hu z zs e
    rcases (show u=x ∨ u=y by simpa using hu) with rfl|rfl
    · exact mem_union_left _ (mem_closed.mpr ⟨zs,Or.inr (sym e)⟩)
    · exact mem_union_right _ (mem_closed.mpr ⟨zs,Or.inr (sym e)⟩)
  have cv := (card_le_card sub).trans (card_union_le ..)
  have union := (card_union_le no one).trans (Nat.add_le_add_left h1 no.card)
  exact cv.trans (Nat.add_le_add union ((card_biUnion_le ..).trans (sum_le_sum (fun y _ => h2 y))))

end
end Audit.Colored
