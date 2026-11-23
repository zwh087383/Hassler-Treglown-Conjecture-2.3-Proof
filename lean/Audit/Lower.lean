import Audit.Link
import Sumfree.Transport
import Sumfree.Counter
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Audit.Lower
open Finset Link Sumfree
variable {H : Type*} [AddCommGroup H] [DecidableEq H]
set_option linter.unusedSectionVars false
abbrev Pt (H : Type*) := Fin 5 × H
def seed : Finset (Pt H) := {(1,0)}
def band (t : Finset H) : Finset (Pt H) := ({2,3} : Finset (Fin 5)) ×ˢ t
@[simp] theorem mem_band {a : Fin 5} {x : H} {t : Finset H} :
    (a,x)∈band t ↔ (a=2 ∨ a=3) ∧ x∈t := by simp [band]

theorem seed_free : Free (seed : Finset (Pt H)) := by
  simp (config := {decide := true}) [seed,Free,Prod.mk_add_mk]
theorem band_free (t : Finset H) : Free (band t) := by
  rintro ⟨a,x⟩ hx ⟨b,y⟩ hy ⟨c,z⟩ hz e
  have no : ∀ a b c : Fin 5, (a=2 ∨ a=3) → (b=2 ∨ b=3) → (c=2 ∨ c=3) → a+b≠c := by decide
  exact no _ _ _ (mem_band.mp hx).1 (mem_band.mp hy).1 (mem_band.mp hz).1 (congrArg Prod.fst e)

section
variable (odd : ∀ x : H, x+x=0 → x=0)
include odd
theorem legal_band (t : Finset H) : legal seed (band t) = band (t.erase 0) := by
  ext ⟨a,x⟩
  simp only [mem_legal,mem_band,mem_erase]
  by_cases can : a=2 ∨ a=3
  · rcases can with rfl | rfl
    · have z2 : (0 : Pt H) ≠ (2,x) := fun h => (by decide : (0:Fin 5) ≠ 2) (congrArg Prod.fst h)
      have z1 : (0 : Pt H) ≠ (1,0) := fun h => (by decide : (0:Fin 5) ≠ 1) (congrArg Prod.fst h)
      simp (config := {decide := true}) [seed,Free,Prod.mk_add_mk,eq_comm,z2,z1,and_comm]
    · have h : x+x=0 ↔ x=0 := ⟨odd _,by rintro rfl; simp⟩
      simp (config := {decide := true}) [seed,Free,Prod.mk_add_mk,h,and_comm]
  · simp [can]

theorem edges {x y : H} (hx : x≠0) (hy : y≠0) (a b : Fin 5)
    (ha : a=2 ∨ a=3) (hb : b=2 ∨ b=3) :
    clash seed (a,x) (b,y) ↔ (a≠b ∧ x=y) ∨ (a=3 ∧ b=3 ∧ x= -y) := by
  have xx : x+x≠0 := fun h => hx (odd _ h)
  have yy : y+y≠0 := fun h => hy (odd _ h)
  have negNe (e : x= -y) : x≠y := by rintro rfl; exact xx (eq_neg_iff_add_eq_zero.mp e)
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
    simp (config := {decide:=true}) [clash,seed,Free,Prod.mk_add_mk,hx,hy,xx,yy,
      add_comm y x,←eq_neg_iff_add_eq_zero,Ne.symm hx,Ne.symm hy,
      show (y=x ↔ x=y) from eq_comm]
  tauto

end

def pathVertex (x : H) : Fin 4 → Pt H := ![(2,x),(3,x),(3,-x),(2,-x)]
def pathEdge (a b : Fin 4) : Bool := decide (a.val+1=b.val ∨ b.val+1=a.val)

theorem path_count : mis (fun a b => pathEdge a b=true) univ = 3 := by
  have exactCount : Counter.solve 4 (Counter.graphFormula 4 pathEdge (fun _ => true) true) = 3 := by decide
  simpa [Counter.solve_mis,Counter.domain] using exactCount

theorem one_pair (odd : ∀ x : H, x+x=0 → x=0) (x : H) (hx : x≠0) :
    mis (clash seed) (band {x,-x}) = 3 := by
  have ne : x≠ -x := fun e => hx (odd _ (eq_neg_iff_add_eq_zero.mp e))
  have nx : -x≠0 := neg_ne_zero.mpr hx
  have imageEq : univ.image (pathVertex x) = band {x,-x} := by
    ext ⟨a,z⟩
    simp only [mem_image,mem_univ,true_and,mem_band,mem_insert,mem_singleton]
    constructor
    · rintro ⟨i,eq⟩; fin_cases i <;> simp [pathVertex] at eq <;> obtain ⟨rfl,rfl⟩ := eq <;> simp
    · rintro ⟨rfl|rfl,rfl|rfl⟩
      · exact ⟨0,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  rw [← imageEq,← path_count]
  symm
  apply mis_image
  · intro a _ b _ e
    fin_cases a <;> fin_cases b <;> simp (config:={decide:=true}) [pathVertex,ne,Ne.symm ne] at *
  · intro a _ b _
    have e (i : Fin 4) : ((pathVertex x i).1=2 ∨ (pathVertex x i).1=3) ∧ (pathVertex x i).2≠0 := by
      fin_cases i <;> simp [pathVertex,hx,nx]
    rw [edges odd (e a).2 (e b).2 _ _ (e a).1 (e b).1]
    fin_cases a <;> fin_cases b <;> simp (config:={decide:=true}) [pathVertex,pathEdge,ne,Ne.symm ne]

theorem pair_decomposition (odd : ∀ x : H, x+x=0 → x=0) (t : Finset H) :
    0∉t → (∀ x∈t, -x∈t) → mis (clash seed) (band t) = 3^(t.card/2) := by
  classical
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    intro nozero stable
    by_cases emp : t=∅
    · subst t
      have e : family (clash (seed : Finset (Pt H))) ∅ = {∅} := by
        ext I; by_cases h : I=∅
        · subst I; simp [IsMIS,Independent]
        · simp [IsMIS,h]
      simp [band,mis,e]
    obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr emp
    have x0 : x≠0 := fun e => nozero (e ▸ hx)
    have opposite := stable x hx
    have ne : x≠ -x := fun e => x0 (odd _ (eq_neg_iff_add_eq_zero.mp e))
    let tail := (t.erase x).erase (-x)
    have sub : tail ⊆ t := (erase_subset _ _).trans (erase_subset _ _)
    have tx : x∉tail := by simp [tail]
    have tnx : -x∉tail := by simp [tail]
    have t0 : 0∉tail := fun h => nozero (sub h)
    have sym (z : H) (hz : z∈tail) : -z∈tail := by
      have back (h : -z=x) : z= -x := by simpa using congrArg Neg.neg h
      have no (h : -z= -x) := tx ((neg_inj.mp h) ▸ hz)
      exact mem_erase.mpr ⟨no,mem_erase.mpr ⟨fun h => tnx (back h ▸ hz),stable z (sub hz)⟩⟩
    have smaller : tail ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => tx (e.symm ▸ hx)⟩
    have ct : tail.card+2=t.card := by
      have a := card_erase_add_one hx
      have b := card_erase_add_one (mem_erase.mpr ⟨Ne.symm ne,opposite⟩ : -x ∈ t.erase x)
      dsimp [tail]; omega
    have cover : {x,-x}∪tail=t := by
      ext z
      by_cases zz : z=x
      · subst z; simp [hx]
      · by_cases zn : z= -x
        · subst z; simp [opposite]
        · simp [tail,zz,zn]
    have separate : Disjoint (band {x,-x}) (band tail) := by
      apply disjoint_left.mpr
      rintro ⟨i,z⟩ h k
      have m := (mem_band.mp k).2
      rcases (show z=x ∨ z= -x by simpa using (mem_band.mp h).2) with rfl|rfl
      · exact tx m
      · exact tnx m
    have cross : ∀ a∈band {x,-x}, ∀ b∈band tail, ¬clash seed a b := by
      rintro ⟨i,z⟩ h ⟨j,w⟩ k
      obtain ⟨hi,zin⟩ := mem_band.mp h
      obtain ⟨hj,win⟩ := mem_band.mp k
      have w0 : w≠0 := fun e => t0 (e ▸ win)
      have inpair : z=x ∨ z= -x := by simpa using zin
      have z0 : z≠0 := inpair.elim (fun e => e ▸ x0) (fun e => e ▸ neg_ne_zero.mpr x0)
      rw [edges odd z0 w0 i j hi hj]
      rintro (⟨_,eq⟩|⟨_,_,eq⟩)
      · have m := eq.symm ▸ win
        exact inpair.elim (fun e => tx (e ▸ m)) (fun e => tnx (e ▸ m))
      · have m := eq.symm ▸ (sym w win)
        exact inpair.elim (fun e => tx (e ▸ m)) (fun e => tnx (e ▸ m))
    have partition : band t = band {x,-x} ∪ band tail := by
      conv_lhs => rw [← cover]
      exact product_union
    rw [partition,disjoint_count (clash_sym seed) _ _ separate cross,one_pair odd x x0,
      ih tail smaller t0 sym,← ct,show (tail.card+2)/2=tail.card/2+1 by omega,pow_succ,mul_comm]

/-- Exact singleton link and a lower bound for the actual global count over
    F5 × (Fin k → F5), including the base case k=0. -/
theorem singleton_lower (k : ℕ) :
    3^((5^k-1)/2) ≤ (maximalSets (univ : Finset (Pt (Fin k → Fin 5)))).card := by
  classical
  let H := Fin k → Fin 5
  let t : Finset H := univ
  have odd : ∀ x : H, x+x=0 → x=0 := by
    intro x h; funext i
    exact (by decide : ∀ a : Fin 5, a+a=0 → a=0) _ (congrFun h i)
  have base := lower_injection (s := (seed : Finset (Pt H))) (b:=band t) seed_free (band_free _)
  rw [legal_band odd,pair_decomposition odd] at base
  · simpa [t,H,card_erase_of_mem] using base
  · simp [t]
  · intro x hx; simpa [t] using hx

end Audit.Lower
