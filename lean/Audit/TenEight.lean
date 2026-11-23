import Audit.TenEightData
import Audit.MixedStrip
import Audit.TriangleTenEightClass

namespace Audit.TenEight
open Finset Link Band Lower Generic Blocks StripFamily
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Module Field5 Plane := inferInstanceAs (Module Field5 (Field5 × Field5))
local instance : Module Field5 Solid := inferInstanceAs (Module Field5 (Plane × Field5))
variable {K L : Type} [AddCommGroup K] [Module Field5 K] [Fintype K] [DecidableEq K]
  [AddCommGroup L] [Module Field5 L] [Fintype L] [DecidableEq L]

theorem image_pat (f : K →ₗ[Field5] L) (a b c : K) :
    embedded f (pat a b c)=pat (f a) (f b) (f c) := by simp [embedded,pat]

private theorem image_free (f : K →ₗ[Field5] L) (s : Finset (Pt K)) (sf : Free (embedded f s)) : Free s := by
  let map (x : Pt K) : Pt L := (x.1,f x.2)
  have keep {p : Pt K} (hp : p∈s) : map p∈embedded f s := mem_image_of_mem _ hp
  intro x hx y hy z hz eq
  apply sf _ (keep hx) _ (keep hy) _ (keep hz)
  rw [←eq]; exact Prod.ext rfl (map_add f _ _).symm

private theorem size_image (f : K →ₗ[Field5] L) (inj : Function.Injective f) (s : Finset (Pt K)) :
    (embedded f s).card=s.card := by
  apply card_image_of_injective
  intro x y h
  exact Prod.ext (congrArg (fun p : Pt L => p.1) h) (inj (congrArg (fun p : Pt L => p.2) h))

private theorem outside (a b c : K) : Disjoint (pat a b c) (full K) := by
  apply disjoint_left.mpr
  rintro ⟨i,x⟩ hp hh
  have head := mem_full.mp hh
  simp only [pat,mem_insert,mem_singleton,Prod.mk.injEq] at hp
  have exclude : ∀ h : Fin 5, (h=0 ∨ h=1 ∨ h=4) → ¬(h=2 ∨ h=3) := by decide
  exact exclude i (by tauto) head

private theorem line_bound (a : K) (ha : a≠0) (b c : Field5) (sf : Free (pat a (b • a) (c • a))) :
    rankCount (pat a (b • a) (c • a))≤3^Fintype.card K := by
  let f : Field5 →ₗ[Field5] K := (LinearMap.id : Field5 →ₗ[Field5] Field5).smulRight a
  have inj : Function.Injective f := by
    intro x y e
    have zero : (x-y) • a=0 := by rw [sub_smul]; exact sub_eq_zero.mpr e
    exact sub_eq_zero.mp ((smul_eq_zero.mp zero).resolve_right ha)
  have image : embedded f (pat 1 b c)=pat a (b • a) (c • a) := by
    simp [image_pat,f,LinearMap.smulRight_apply]
  rw [←image] at sf ⊢
  exact bound_embedding f inj (RankOneBridge.all _ (image_free f _ sf) (outside ..))

def linear3 (f : Plane →ₗ[Field5] K) (z : K) : Solid →ₗ[Field5] K :=
  f.comp (LinearMap.fst Field5 Plane Field5)+(LinearMap.snd Field5 Plane Field5).smulRight z

@[simp] theorem linear3_apply (f : Plane →ₗ[Field5] K) (z : K) (p : Plane) (a : Field5) :
    linear3 f z (p,a)=f p+a • z := rfl

theorem linear3_inj (f : Plane →ₗ[Field5] K) (fi : Function.Injective f) (z : K) (out : ¬∃v, f v=z) :
    Function.Injective (linear3 f z) := by
  have ker (p : Plane) (a : Field5) (h : f p+a • z=0) : p=0 ∧ a=0 := by
    have az : a=0 := by
      by_contra ne
      apply out
      refine ⟨(-a⁻¹) • p,?_⟩
      rw [map_smul,eq_neg_of_add_eq_zero_left h,smul_neg,neg_smul,neg_neg,←mul_smul,inv_mul_cancel₀ ne,one_smul]
    rw [az,zero_smul,add_zero] at h
    exact ⟨fi (h.trans (map_zero f).symm),az⟩
  intro x y e
  have diff : linear3 f z (x-y)=0 := by rw [map_sub,e,sub_self]
  obtain ⟨one,two⟩ := ker (x-y).1 (x-y).2 diff
  exact sub_eq_zero.mp (Prod.ext one two)

private theorem spatial (a b c : K) (ha : a≠0) (hb : ¬∃r : Field5, b=r • a)
    (sf : Free (pat a b c)) (size : (pat a b c).card=5) : rankCount (pat a b c)≤3^Fintype.card K := by
  let f := MixedStrip.linear a b
  have fi : Function.Injective f := MixedStrip.plane_injective a b ha hb
  have a1 : f e1=a := by simp [f,e1]
  have b2 : f e2=b := by simp [f,e2]
  by_cases plane : ∃q : Plane, f q=c
  · obtain ⟨q,hq⟩ := plane
    have eq : embedded f (pat e1 e2 q)=pat a b c := by rw [image_pat,a1,b2,hq]
    rw [←eq] at sf size ⊢
    rw [size_image f fi] at size
    exact bound_embedding f fi (plane_count (image_free f _ sf) size)
  · let g:=linear3 f c
    have gi : Function.Injective g := linear3_inj f fi c plane
    have x1 : g f1=a := by simp [g,f1,a1]
    have x2 : g f2=b := by simp [g,f2,b2]
    have x3 : g f3=c := by simp [g,f3]
    rw [←x1,←x2,←x3,←image_pat]
    exact bound_embedding g gi solid_count

theorem normalized (a b c : K) (sf : Free (pat a b c)) (size : (pat a b c).card=5) :
    rankCount (pat a b c)≤3^Fintype.card K := by
  have ha : a≠0 := by
    rintro rfl
    have contains : 0∈pat (0:K) b c := mem_insert_self ..
    exact sf 0 contains 0 contains 0 contains (zero_add _)
  by_cases bp : ∃u : Field5,b=u • a
  · obtain ⟨u,bu⟩ := bp
    by_cases cp : ∃v : Field5,c=v • a
    · obtain ⟨v,cv⟩ := cp
      rw [bu,cv] at sf ⊢
      exact line_bound a ha u v sf
    · have swap : pat a b c=pat a c b := by ext x; simp [pat,or_comm,or_left_comm,or_assoc]
      rw [swap] at sf size ⊢
      exact spatial a c b ha cp sf size
  · exact spatial a b c ha bp sf size

theorem normal {k : ℕ} (a b c : Space k) (sf : Free (pat a b c)) (size : (pat a b c).card=5) :
    rankCount (pat a b c)≤3^(5^k) := by simpa [Space,Field5] using normalized a b c sf size

theorem crossing {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (size : s.card=5)
    (cross : Mixed.Crossing s) (layers : (Degrees.seedLayer s 1).card=3 ∨ (Degrees.seedLayer s 4).card=3) :
    rankCount s≤3^(5^k) := MixedTenEight.classify normal sf size cross layers

end
end Audit.TenEight
