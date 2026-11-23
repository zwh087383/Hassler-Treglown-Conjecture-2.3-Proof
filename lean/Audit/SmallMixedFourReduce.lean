import Audit.SmallMixedPure
import Audit.SmallMixedFourBases
import Audit.MixedFive

namespace Audit.SmallMixed
open Finset Lower Link Band Blocks Generic Degrees
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance fourReducePrime : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance fourReducePlaneModule : Module Field5 Strip.K := inferInstanceAs (Module Field5 Plane)
set_option maxRecDepth 12000
variable {V W : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] [Module Field5 V]
  [AddCommGroup W] [Fintype W] [DecidableEq W] [Module Field5 W]

def cubeMap (u v w : V) : Cube →ₗ[Field5] V :=
  (pairMap u v).comp (LinearMap.fst Field5 Plane Field5) + (lineMap w).comp (LinearMap.snd Field5 Plane Field5)

theorem cubeMap_apply (u v w : V) (a b c : Field5) :
    cubeMap u v w ((a,b),c)=a • u+b • v+c • w := rfl

theorem cubeMap_injective {u v w : V} (inj : Function.Injective (pairMap u v))
    (ind : ¬∃ a b : Field5,w=a • u+b • v) : Function.Injective (cubeMap u v w) := by
  classical
  have kernel (x : Cube) (eq : cubeMap u v w x=0) : x=0 := by
    obtain ⟨⟨a,b⟩,c⟩ := x
    rw [cubeMap_apply] at eq
    have cz : c=0 := by
      by_contra ne
      apply ind
      refine ⟨-(c⁻¹*a),-(c⁻¹*b),?_⟩
      have h : c • w= -(a • u+b • v) := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using eq)
      calc
        w = c⁻¹ • (c • w) := by rw [←mul_smul,inv_mul_cancel₀ ne,one_smul]
        _ = _ := by rw [h,smul_neg,smul_add,←mul_smul,←mul_smul,neg_add,neg_smul,neg_smul]
    subst c
    rw [zero_smul,add_zero] at eq
    have ab : (a,b)=(0:Plane) := inj (by rw [map_zero]; exact eq)
    rw [ab]; rfl
  intro x y eq
  apply sub_eq_zero.mp
  apply kernel
  rw [map_sub,eq,sub_self]

theorem free_base (f : W →ₗ[Field5] V) (s : Finset (Pt W)) (sf : Free (StripFamily.embedded f s)) : Free s := by
  let mp (p : Pt W) : Pt V := (p.1,f p.2)
  have hit {p : Pt W} (hp : p∈s) : mp p∈StripFamily.embedded f s := mem_image_of_mem _ hp
  intro a ha b hb c hc eq
  apply sf _ (hit ha) _ (hit hb) _ (hit hc)
  rw [←eq]
  exact Prod.ext rfl (map_add f ..).symm

theorem embedded_size (f : W →ₗ[Field5] V) (inj : Function.Injective f) (s : Finset (Pt W)) :
    (StripFamily.embedded f s).card=s.card := by
  apply card_image_of_injective
  intro x y e
  exact Prod.ext (congrArg (fun p : Pt V => p.1) e) (inj (congrArg (fun p : Pt V => p.2) e))

def legalHead (j : Fin 5) := j=0 ∨ j=1 ∨ j=4

structure FourTables : Prop where
  plane : ∀ j l a b, legalHead j → legalHead l → (shape2 j l a b).card=4 →
    Free (shape2 j l a b) → rankCount (shape2 j l a b)≤3^25
  cube : ∀ j l, legalHead j → legalHead l → (shape3 j l).card=4 →
    Free (shape3 j l) → rankCount (shape3 j l)≤3^125

def marked (u v w : V) (j l : Fin 5) : Finset (Pt V) := {(0,u),(1,0),(j,v),(l,w)}

private theorem with_plane (table : FourTables) (u v w : V) (j l : Fin 5)
    (hj : legalHead j) (hl : legalHead l) (hu : u≠0) (ind : ¬∃a : Field5,v=a • u)
    (size : (marked u v w j l).card=4) (sf : Free (marked u v w j l)) :
    rankCount (marked u v w j l)≤3^Fintype.card V := by
  have inj := pairMap_injective u v hu ind
  by_cases plane : ∃ a b : Field5,w=a • u+b • v
  · obtain ⟨a,b,rfl⟩ := plane
    have model : StripFamily.embedded (pairMap u v) (shape2 j l a b)=marked u v (a • u+b • v) j l := by
      simp only [StripFamily.embedded,shape2,image_insert,image_singleton,marked]
      change {(0,(1:Field5) • u+(0:Field5) • v),(1,(0:Field5) • u+(0:Field5) • v),
        (j,(0:Field5) • u+(1:Field5) • v),(l,a • u+b • v)}=_
      simp
    rw [←model] at sf size ⊢
    rw [embedded_size _ inj] at size
    exact StripFamily.bound_embedding _ inj (table.plane j l a b hj hl size (free_base _ _ sf))
  · have ci := cubeMap_injective inj plane
    have model : StripFamily.embedded (cubeMap u v w) (shape3 j l)=marked u v w j l := by
      simp only [StripFamily.embedded,shape3,image_insert,image_singleton,marked,cubeMap_apply,
        one_smul,zero_smul,add_zero,zero_add]
    rw [←model] at sf size ⊢
    rw [embedded_size _ ci] at size
    exact StripFamily.bound_embedding _ ci (table.cube j l hj hl size (free_base _ _ sf))

theorem marked_four (table : FourTables) (u v w : V) (j l : Fin 5)
    (size : (marked u v w j l).card=4) (sf : Free (marked u v w j l)) (out : Disjoint (marked u v w j l) (full V)) :
    rankCount (marked u v w j l)≤3^Fintype.card V := by
  have un : u≠0 := by
    rintro rfl
    have h : (0:Pt V)∈marked 0 v w j l := mem_insert_self _ _
    exact sf _ h _ h _ h (zero_add _)
  have hj := external_head out (show (j,v)∈marked u v w j l by simp [marked])
  have hl := external_head out (show (l,w)∈marked u v w j l by simp [marked])
  by_cases vind : ∃a : Field5,v=a • u
  · by_cases wind : ∃b : Field5,w=b • u
    · obtain ⟨a,rfl⟩ := vind
      obtain ⟨b,rfl⟩ := wind
      apply line_bound sf out un
      intro x hx
      rcases (show x=(0,u) ∨ x=(1,0) ∨ x=(j,a • u) ∨ x=(l,b • u) by simpa [marked] using hx) with rfl|rfl|rfl|rfl
      · exact ⟨1,(one_smul _ _).symm⟩
      · exact ⟨0,(zero_smul _ _).symm⟩
      · exact ⟨a,rfl⟩
      · exact ⟨b,rfl⟩
    · have sw : marked u v w j l=marked u w v l j := by ext p; simp [marked,or_comm,or_assoc,or_left_comm]
      rw [sw] at sf size ⊢
      exact with_plane table u w v l j hl hj un wind size sf
  · exact with_plane table u v w j l hj hl un vind size sf

end
end Audit.SmallMixed


