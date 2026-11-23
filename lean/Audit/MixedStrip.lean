import Audit.StripFamily

namespace Audit.MixedStrip
open Finset Link Lower Band Generic Blocks StripFamily
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Module Field5 Strip.K := inferInstanceAs (Module Field5 (Field5 × Field5))
variable {K : Type} [AddCommGroup K] [Module Field5 K] [Fintype K] [DecidableEq K]

def linear (u v : K) : Strip.K →ₗ[Field5] K :=
  (LinearMap.fst Field5 Field5 Field5).smulRight u+(LinearMap.snd Field5 Field5 Field5).smulRight v

@[simp] theorem linear_apply (u v : K) (a b : Field5) : linear u v (a,b)=a • u+b • v := rfl

def realize (m : Strip.Model) (u v : K) := embedded (linear u v) (Strip.seed m)

/-- The six algebraic normal forms, retaining actual vectors even when they are dependent. -/
def pattern (m : Strip.Model) (u v : K) : Finset (Pt K) := match m with
  | .sameTriple => {(0,u),(1,0),(1,v)}
  | .oppositeTriple => {(0,u),(1,0),(4,v)}
  | .nestedFour => {(0,u),(1,0),(1,v),(4,0)}
  | .triangleFour => {(0,u),(1,0),(1,v),(4,-u)}
  | .twoZeroFour => {(0,u),(0,-u),(1,0),(1,v)}
  | .triangleFive => {(0,u),(1,0),(1,v),(4,0),(4,-u-v)}

theorem realize_pattern (m : Strip.Model) (u v : K) : realize m u v = pattern m u v := by
  have four : (4:Field5)= -1 := by decide
  cases m <;> simp [realize,embedded,Strip.seed,pattern,linear_apply,four,sub_eq_add_neg]

private theorem map_down (g : Field5 →ₗ[Field5] K) (s : Finset (Pt Field5))
    (sf : Free (embedded g s)) (out : Disjoint (embedded g s) (full K)) :
    Free s ∧ Disjoint s (full Field5) := by
  let f (p : Pt Field5) : Pt K := (p.1,g p.2)
  have mem {p : Pt Field5} (h : p∈s) : f p ∈ embedded g s := mem_image_of_mem _ h
  refine ⟨?_,disjoint_left.mpr ?_⟩
  · intro x hx y hy z hz eq
    apply sf _ (mem hx) _ (mem hy) _ (mem hz)
    rw [←eq]
    exact Prod.ext rfl (map_add g x.2 y.2).symm
  · intro x hx h
    exact disjoint_left.mp out (mem hx) ((mem_full (u:=f x)).mpr ((mem_full (u:=x)).mp h))

private theorem line_count (u : K) (nz : u≠0) (c : Field5) (seed : Strip.Seed)
    (sf : Free (embedded (linear u (c • u)) seed)) (out : Disjoint (embedded (linear u (c • u)) seed) (full K)) :
    rankCount (embedded (linear u (c • u)) seed) ≤ 3^Fintype.card K := by
  let g : Field5 →ₗ[Field5] K := (LinearMap.id : Field5 →ₗ[Field5] Field5).smulRight u
  let f : Strip.K →ₗ[Field5] Field5 := linear (1:Field5) c
  let model := embedded f seed
  have comp : embedded (linear u (c • u)) seed=embedded g model := by
    simp only [embedded,model,image_image]
    congr 1
    funext x; refine Prod.ext rfl ?_
    have scalar (a b : Field5) : a • u+b • (c • u)=(a • (1:Field5)+b • c) • u := by
      rw [smul_eq_mul,smul_eq_mul,mul_one,add_smul,mul_smul]
    exact scalar x.2.1 x.2.2
  rw [comp] at sf out ⊢
  have inj : Function.Injective g := by
    intro a b eq
    have h : (a-b) • u=0 := by rw [sub_smul]; exact sub_eq_zero.mpr eq
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right nz)
  obtain ⟨sf1,out1⟩ := map_down g model sf out
  exact bound_embedding g inj (RankOneBridge.all model sf1 out1)

theorem plane_injective (u v : K) (nz : u≠0) (ind : ¬∃ c : Field5,v=c • u) :
    Function.Injective (linear u v) := by
  have kernel (a b : Field5) (h : linear u v (a,b)=0) : a=0 ∧ b=0 := by
    rw [linear_apply] at h
    have bz : b=0 := by
      by_contra ne
      apply ind
      refine ⟨b⁻¹*(-a),?_⟩
      rw [mul_smul,neg_smul,show -(a • u)=b • v from neg_eq_iff_add_eq_zero.mpr h,
        ←mul_smul,inv_mul_cancel₀ ne,one_smul]
    rw [bz,zero_smul,add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right nz,bz⟩
  intro x y eq
  have diff : linear u v (x-y)=0 := by rw [map_sub,eq,sub_self]
  obtain ⟨a,b⟩ := kernel (x-y).1 (x-y).2 diff
  exact sub_eq_zero.mp (Prod.ext a b)

/-- All dimension-two certificates apply to arbitrary images preserving freeness.
    If the second direction collapses, the rank-one certificate takes over. -/
theorem image_bound (u v : K) (nz : u≠0) (seed : Strip.Seed) (known : rankCount seed≤3^25)
    (sf : Free (embedded (linear u v) seed)) (out : Disjoint (embedded (linear u v) seed) (full K)) :
    rankCount (embedded (linear u v) seed)≤3^Fintype.card K := by
  by_cases line : ∃ c : Field5,v=c • u
  · obtain ⟨c,rfl⟩ := line
    exact line_count u nz c seed sf out
  · exact bound_embedding (linear u v) (plane_injective u v nz line) known

theorem all (m : Strip.Model) (u v : K) (sf : Free (pattern m u v)) :
    rankCount (pattern m u v)≤3^Fintype.card K := by
  have contains : (0,u)∈pattern m u v := by cases m <;> simp [pattern]
  have nz : u≠0 := by
    rintro rfl
    exact sf 0 contains 0 contains 0 contains (zero_add _)
  have out : Disjoint (pattern m u v) (full K) := by
    apply disjoint_left.mpr
    intro x hx hb
    have head := (mem_full (u:=x)).mp hb
    have miss : ∀ a : Fin 5, (a=0 ∨ a=1 ∨ a=4) → ¬(a=2 ∨ a=3) := by decide
    apply miss _ _ head
    cases m <;> simp only [pattern,mem_insert,mem_singleton] at hx <;> rcases x with ⟨i,z⟩ <;>
      simp only [Prod.mk.injEq] at hx <;> tauto
  rw [←realize_pattern] at sf out ⊢
  exact image_bound u v nz _ (Strip.model_bound m).le sf out

end
end Audit.MixedStrip
