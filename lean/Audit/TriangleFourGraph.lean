import Audit.TriangleWitness
import Audit.SmallMixedFourBases

namespace Audit.TriangleFour
open Finset Sumfree Fingerprint Degrees Generic Lower Band Link Blocks
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

def Clean (s : Finset (Pt K)) := ∀x∈s,∀y∈s,-(x+y)∉s
def Crossed (s : Finset (Pt K)) := ∃x∈s,∃y∈s,x.1=0 ∧ y.1=1 ∧ -(y+x)∈s
def Legal (s : Finset (Pt K)) := ∀x∈s,∀y∈s,x+y∉s
instance (s : Finset (Pt K)) : Decidable (Clean s) := by unfold Clean; infer_instance
instance (s : Finset (Pt K)) : Decidable (Crossed s) := by unfold Crossed; infer_instance
instance (s : Finset (Pt K)) : Decidable (Legal s) := by unfold Legal; infer_instance

def population (s : Finset (Pt K)) (h : Fin 5) := (s.filter (fun p => p.1=h)).card
def support (s : Finset (Pt K)) := s∪s.image Neg.neg

def DegreesPass (d l u z : ℕ) (clean cross : Bool) : Prop :=
  (10≤l ∧ d≤2*l-3) ∨
  (clean=true ∧ ((d≤8 ∧ 15≤d+l) ∨ (d≤10 ∧ 17≤d+l) ∨ (d=9 ∧ 15≤d+l ∧ 8≤(u+z)*(d-l)))) ∨
  (d=9 ∧ l=9 ∧ 6≤4+z ∧ cross=true)
instance (d l u z : ℕ) (a b : Bool) : Decidable (DegreesPass d l u z a b) := by
  unfold DegreesPass; infer_instance

def passes (s : Finset (Pt K)) : Bool := Id.run do
  let z:=population s 0
  let p:=population s 1
  let q:=population s 4
  let Z:=population (support s) 0
  let U:=population (support s) 1
  let base:=Z+U+z
  return decide (DegreesPass (base+max p q) (base+min p q) U z (decide (Clean s)) (decide (Crossed s)))

theorem legal_of_free {s : Finset (Pt K)} (sf : Free s) : Legal s :=
  fun x hx y hy hit => sf x hx y hy _ hit rfl

open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false

theorem graph_bound {s : Finset (Pt K)} (sf : Free s) (out : Disjoint s (full K)) (size : s.card=4)
    (yes : passes s=true) : rankCount s≤3^Fintype.card K := by
  let z:=population s 0
  let p:=population s 1
  let q:=population s 4
  let Z:=population (support s) 0
  let U:=population (support s) 1
  have layers (h : Fin 5) (allow : h=0 ∨ h=1) :
      (seedLayer (forward s) h).card=population (support s) h := by
    congr 1
    ext x; simp only [seedLayer,forward,support,mem_filter,Band.signed]
    constructor
    · exact fun t => ⟨t.1.1,t.2⟩
    · exact fun t => ⟨⟨t.1,allow.imp (t.2.trans ·) (t.2.trans ·)⟩,t.2⟩
  obtain ⟨_,_,_,h2,h3⟩:=profiles s out
  rw [layers 0 (Or.inl rfl),layers 1 (Or.inr rfl)] at h2 h3
  change headDegree s 2=Z+U+z+q at h2
  change headDegree s 3=Z+U+z+p at h3
  have hi : Z+U+z+max p q=maximumDegree s := by unfold maximumDegree; omega
  have lo : Z+U+z+min p q=minimumDegree s := by unfold minimumDegree; omega
  have total : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 := max_add_min ..
  change decide (DegreesPass (Z+U+z+max p q) (Z+U+z+min p q) U z (decide (Clean s)) (decide (Crossed s)))=true at yes
  have options := of_decide_eq_true yes
  rw [hi,lo] at options
  rcases options with ⟨ld,rat⟩|⟨cl,spec⟩|⟨dc,lc,ct,cr⟩
  · exact MasterTable.two_degree s sf out ld rat
  · have clean : Clean s := of_decide_eq_true cl
    have tf := Mixed.triangle_free sf (show Mixed.NoZeroSum s by
      intro x hx y hy t ht eq
      exact clean x hx y hy ((eq_neg_of_add_eq_zero_right eq) ▸ ht))
    rcases spec with ⟨c,av⟩|⟨c,av⟩|⟨dc,av,counts⟩
    · exact within_quarter s sf (TriangleEight.dense (within_sym s) (within_irr s) tf _
        (fun x hx => (within_cap sf x hx).trans c) (two_degree_sum s sf 15 (by omega)))
    · exact Mixed.neither_high sf tf (Or.inl ⟨c,by omega⟩)
    · apply within_quarter s sf
      apply TriangleEight.capNine (within_sym s) (within_irr s) tf _
        (fun x hx => (within_cap sf x hx).trans dc.le) _ (two_degree_sum s sf 15 (by omega))
      intro x hx dx
      have eq := (within_degree sf hx).symm.trans (dx.trans dc.symm)
      have hsum := Mixed.high_sum sf hx eq
      rw [layers 1 (Or.inr rfl)] at hsum
      change _+(U+z)*(maximumDegree s-minimumDegree s)≤_ at hsum
      rw [dc] at hsum counts
      change (∑y∈neighbors (within s) Raw.domain x,(neighbors (within s) Raw.domain y).card)≤73
      omega
  · have has : Crossed s := of_decide_eq_true cr
    obtain ⟨⟨h,a⟩,ha,⟨j,b⟩,hb,h0,j1,third⟩:=has
    change h=0 at h0; change j=1 at j1; subst h; subst j
    exact TriangleCoordinates.nine_cross sf out dc.le (by omega) (by rw [size]; exact ct) a b ha hb third

end
end Audit.TriangleFour
