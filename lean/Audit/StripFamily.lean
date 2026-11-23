import Audit.StripNoZero
import Audit.StripTransport
import Audit.RankOneBridge
import Audit.Defects

namespace Audit.StripFamily
open Finset Lower Link Band Blocks Generic Reduction
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {K L : Type} [AddCommGroup K] [Fintype K] [DecidableEq K] [Module Field5 K]
  [AddCommGroup L] [Fintype L] [DecidableEq L] [Module Field5 L]

def embedded (f : K →ₗ[Field5] L) (s : Finset (Pt K)) : Finset (Pt L) :=
  s.image fun p => (p.1,f p.2)

/-- An ambient embedding produces one copy of the four-layer graph per complementary coset. -/
theorem embedded_count (f : K →ₗ[Field5] L) (inj : Function.Injective f) (s : Finset (Pt K)) :
    ∃ copies : ℕ, Fintype.card L=Fintype.card K*copies ∧ rankCount (embedded f s)=rankCount s^copies := by
  classical
  let U := LinearMap.range f
  obtain ⟨W,comp⟩ := U.exists_isCompl
  let fromK := LinearEquiv.ofInjective f inj
  let iso := (fromK.prodCongr (LinearEquiv.refl Field5 W)).trans (Submodule.prodEquivOfIsCompl U W comp)
  refine ⟨Fintype.card W,?_,?_⟩
  · simpa only [Fintype.card_prod] using (Fintype.card_congr iso.toEquiv).symm
  · have map : (includeSeed W s).image (relabel iso.toAddEquiv)=embedded f s := by
      simp only [includeSeed,embedded,image_image]
      congr 1
      funext p
      refine Prod.ext rfl ?_
      change f p.2+(0:W).val=f p.2
      simp
    rw [←map,←rankCount_relabel,rankCount_directSum]

theorem bound_embedding (f : K →ₗ[Field5] L) (inj : Function.Injective f) {s : Finset (Pt K)}
    (known : rankCount s≤3^(Fintype.card K)) : rankCount (embedded f s)≤3^(Fintype.card L) := by
  obtain ⟨copies,card,count⟩ := embedded_count f inj s
  rw [count,card,pow_mul]
  exact Nat.pow_le_pow_left known copies

/-- Finite base models and transformations which preserve the required count in any rank. -/
inductive Recognized : (r : ℕ) → Finset (Pt (Space r)) → Prop
  | rankOne {s : Finset (Pt (Space 1))} (free : Free s) (outside : Disjoint s (full (Space 1))) :
      Recognized 1 s
  | strip (c : Strip.Model) : Recognized 2 ((Strip.seed c).image (relabel Strip.coordinates))
  | noZero : Recognized 2 (Strip.NoZero.seed.image (relabel Strip.coordinates))
  | matrix {r s} (model : MatrixCovered (k:=r) s) : Recognized r s
  | oneDefect {r} (t : Finset (Pt (Space r))) (z : Pt (Space r))
      (stable : ∀ x,x∈t ↔ -x∈t) (free : Free (insert z t))
      (outside : Disjoint (insert z t) (full (Space r))) : Recognized r (insert z t)
  | oppositeDefects {r} (t : Finset (Pt (Space r))) (b c : Space r)
      (stable : ∀ x,x∈t ↔ -x∈t) (nonzero : 0∉t) (distinct : c≠-b) :
      Recognized r (insert (1,b) (insert (4,c) t))
  | embedding {r t s} (f : Space r →ₗ[Field5] Space t) (inj : Function.Injective f)
      (base : Recognized r s) : Recognized t (embedded f s)
  | coordinate {r s} (e : Pt (Space r) ≃+ Pt (Space r))
      (bands : ∀ x, x∈full (Space r) ↔ e x∈full (Space r)) (base : Recognized r s) :
      Recognized r (s.image e)

theorem recognized_bound {r : ℕ} {s : Finset (Pt (Space r))} (model : Recognized r s) :
    rankCount s ≤ 3^(5^r) := by
  induction model with
  | @rankOne s free outside =>
    let e : Space 1 ≃+ Fin 5 :=
      { toFun := fun x => x 0
        invFun := fun x _ => x
        left_inv := fun x => funext fun i => congrArg x (Subsingleton.elim 0 i)
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
    have sf := (Assembly.free_image (relabel e) s).mpr free
    have ext : Disjoint (s.image (relabel e)) (full (Fin 5)) := by
      apply disjoint_left.mpr
      intro y h hy
      obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      exact disjoint_left.mp outside hp ((mem_full (u:=p)).mpr ((mem_full (u:=relabel e p)).mp hy))
    rw [rankCount_relabel e]
    exact RankOneBridge.all _ sf ext
  | strip c => exact (Strip.model_bound_space c).le
  | noZero => exact Strip.NoZero.model_bound_space.le
  | matrix model => simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using covered_count model
  | oneDefect t z stable sf out =>
    simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using Defects.one_defect t stable z sf out
  | oppositeDefects t b c stable nz distinct =>
    simpa only [Defects.signedSeed,if_true,Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using
      Defects.nonzero t stable nz true true b c (fun _ _ => distinct)
  | embedding f inj _ ih =>
    have result := bound_embedding f inj (s:=_) (by simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using ih)
    simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using result
  | coordinate e bands _ ih => rwa [←transport e bands]

theorem Recognized.shear {r s} (model : Recognized r s) (u : Space r) :
    Recognized r (s.image (StripFamily.shear u)) :=
  .coordinate _ (fun x => (mem_full (u:=x)).trans (mem_full (u:=StripFamily.shear u x)).symm) model

theorem Recognized.negate {r s} (model : Recognized r s) : Recognized r (s.image Neg.neg) := by
  apply Recognized.coordinate (AddEquiv.neg _) _ model
  intro x; simp only [mem_full]
  exact (show ∀ a : Fin 5, (a=2 ∨ a=3) ↔ (-a=2 ∨ -a=3) by decide) x.1

end
end Audit.StripFamily
