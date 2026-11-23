import Sumfree.Twins
import Sumfree.Bounds
import Mathlib.Data.ZMod.Basic

namespace Sumfree
noncomputable section
open Finset
set_option linter.unusedSectionVars false

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
abbrev Ambient (H : Type*) := ZMod 5 × H

def SumFree {G : Type*} [Add G] (S : Set G) := ∀ a ∈ S, ∀ b ∈ S, a+b ∉ S
def NegStable {G : Type*} [Neg G] (S : Set G) := ∀ x, x ∈ S ↔ -x ∈ S
def Base (u : H) : Ambient H := (2,u)
/-- Coordinates on the two layers. Each (3,v) occurs as -(2,-v). -/
def vertex : Bool × H → Ambient H
  | (false,u) => Base u
  | (true,u) => -Base u

def raw (S : Set (Ambient H)) (x y : Ambient H) :=
  x+y ∈ S ∨ x-y ∈ S ∨ y-x ∈ S
def Link (S : Set (Ambient H)) (p q : Bool × H) := p ≠ q ∧ raw S (vertex p) (vertex q)
def legal (S : Set (Ambient H)) : Finset (Bool × H) := by
  classical exact univ.filter fun p => SumFree (insert (vertex p) S)
def tails (S : Set (Ambient H)) : Finset H := by
  classical exact univ.filter fun u => SumFree (insert (Base u) S)
def quotient (S : Set (Ambient H)) (u v : H) := u ≠ v ∧ raw S (Base u) (Base v)

theorem neg_legal {G : Type*} [AddCommGroup G] {S : Set G} (sym : NegStable S) (x : G) :
    SumFree (insert (-x) S) ↔ SumFree (insert x S) := by
  have transfer (z : G) (h : SumFree (insert z S)) : SumFree (insert (-z) S) := by
    have back {w : G} (hw : w ∈ insert (-z) S) : -w ∈ insert z S := by
      rcases Set.mem_insert_iff.mp hw with rfl | hs
      · simp
      · exact Set.mem_insert_of_mem _ ((sym _).1 hs)
    intro a ha b hb hab
    apply h (-a) (back ha) (-b) (back hb)
    simpa only [neg_add] using back hab
  exact ⟨fun h => by simpa using transfer (-x) h, transfer x⟩

theorem raw_sym (S : Set (Ambient H)) : Symmetric (raw S) := by
  intro x y h
  unfold raw at *
  rw [add_comm]
  tauto

private theorem raw_two {S : Set (Ambient H)} (sym : NegStable S) (x y : Ambient H) :
    raw S x y ↔ x+y ∈ S ∨ x-y ∈ S := by
  have h : y-x ∈ S ↔ x-y ∈ S := by simpa using sym (y-x)
  unfold raw
  tauto

theorem raw_neg {S : Set (Ambient H)} (sym : NegStable S) (x y : Ambient H) :
    raw S (-x) y ↔ raw S x y := by
  rw [raw_two sym, raw_two sym]
  have h1 : -x+y = -(x-y) := by abel
  have h2 : -x-y = -(x+y) := by abel
  rw [h1,h2,← sym _,← sym _,or_comm]

theorem raw_vertex {S : Set (Ambient H)} (sym : NegStable S) (p q : Bool × H) :
    raw S (vertex p) (vertex q) ↔ raw S (Base p.2) (Base q.2) := by
  have right (x y : Ambient H) : raw S x (-y) ↔ raw S x y := by
    rw [show raw S x (-y) ↔ raw S (-y) x from ⟨fun h => raw_sym S h,fun h => raw_sym S h⟩,raw_neg sym]
    exact ⟨fun h => raw_sym S h,fun h => raw_sym S h⟩
  rcases p with ⟨c,u⟩
  rcases q with ⟨d,v⟩
  cases c <;> cases d <;> simp [vertex,raw_neg sym,right]

private theorem self_free {S : Set (Ambient H)} {x : Ambient H}
    (h : SumFree (insert x S)) : ¬ raw S x x := by
  have xx : x ∈ insert x S := Set.mem_insert x S
  have no2 := h x xx x xx
  have no0 : (0 : Ambient H) ∉ S := by
    intro zero
    exact h _ (Set.mem_insert_of_mem _ zero) x xx (by simp)
  have ns : x+x ∉ S := fun hx => no2 (Set.mem_insert_of_mem _ hx)
  simp [raw,no0,ns]

theorem count_congr {V : Type*} [DecidableEq V] {r t : V → V → Prop} {s : Finset V}
    (he : ∀ x ∈ s, ∀ y ∈ s, r x y ↔ t x y) : mis r s = mis t s := by
  have mono {p q : V → V → Prop} (e : ∀ x ∈ s, ∀ y ∈ s, p x y ↔ q x y) :
      family p s ⊆ family q s := by
    intro I hi
    obtain ⟨sub,ind,dom⟩ := mem_family.mp hi
    refine mem_family.mpr ⟨sub, fun x hx y hy h => ind _ hx _ hy ((e x (sub hx) y (sub hy)).2 h), ?_⟩
    intro x hx xn
    obtain ⟨y,hy,edge⟩ := dom x hx xn
    exact ⟨y,hy,(e x hx y (sub hy)).1 edge⟩
  exact congrArg Finset.card (Finset.Subset.antisymm (mono he) (mono (fun x hx y hy => (he x hx y hy).symm)))

theorem symmetric_collapse {S : Set (Ambient H)} (sym : NegStable S) :
    mis (Link S) (legal S) = mis (quotient S) (tails S) := by
  classical
  have active : legal S = double (tails S) := by
    ext ⟨c,u⟩
    cases c <;> simp [vertex,legal,tails,neg_legal sym]
  rw [active, ← double_mis (quotient S) (tails S)]
  apply count_congr
  intro p hp q _
  have safe : SumFree (insert (Base p.2) S) := by simpa [tails] using hp
  unfold Link quotient
  rw [raw_vertex sym]
  by_cases eq : p.2 = q.2
  · rw [← eq]
    simp [self_free safe]
  · have ne : p ≠ q := fun e => eq (congrArg Prod.snd e)
    simp [eq,ne]

/-- Theorem B, any finite tail group, hence in particular any finite F₅-vector space. -/
theorem theorem_B {S : Set (Ambient H)} (sym : NegStable S) :
    (mis (Link S) (legal S) : ℝ) ≤ (3 : ℝ)^((Fintype.card H : ℝ)/3) := by
  rw [symmetric_collapse sym]
  have card : (tails S).card ≤ Fintype.card H := card_le_univ _
  exact (moon_moser (R := quotient S)
    (fun _ _ h => ⟨h.1.symm,raw_sym S h.2⟩) (fun _ h => h.1 rfl) _).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by gcongr))

/-- In the zero layer, the contracted graph has Cayley adjacency. -/
theorem quotient_zero {S : Set (Ambient H)} (sym : NegStable S) (zero : ∀ z ∈ S, z.1 = 0)
    (u v : H) : quotient S u v ↔ u ≠ v ∧ ((0,u-v) : Ambient H) ∈ S := by
  have none : Base u + Base v ∉ S := by
    intro h
    have eq := zero _ h
    exact (by decide : (2+2 : ZMod 5) ≠ 0) eq
  unfold quotient
  rw [raw_two sym,or_iff_right none]
  simp [Base,Prod.mk_sub_mk]

theorem theorem_B_zero {S : Set (Ambient H)} (sf : SumFree S)
    (sym : NegStable S) (zero : ∀ z ∈ S, z.1 = 0) :
    (mis (Link S) (legal S) : ℝ) ≤ (2 : ℝ)^((Fintype.card H : ℝ)/2) := by
  rw [symmetric_collapse sym]
  have tri : TriangleFree (quotient S) := by
    intro x y z xy yz xz
    rw [quotient_zero sym zero] at xy yz xz
    apply sf _ xy.2 _ yz.2
    simpa [Prod.mk_add_mk,sub_add_sub_cancel] using xz.2
  have card : (tails S).card ≤ Fintype.card H := card_le_univ _
  apply (hujter_tuza (R := quotient S) (fun _ _ h => ⟨h.1.symm,raw_sym S h.2⟩)
    (fun _ h => h.1 rfl) tri _).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  gcongr

end
end Sumfree
