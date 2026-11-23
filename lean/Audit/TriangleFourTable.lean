import Audit.TriangleFourGraph
import Audit.SmallMixedFourExtra

namespace Audit.SmallMixed
open Finset Lower Link Generic Degrees Band Blocks StripFamily TriangleFour
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance tablePlaneModule : Module Field5 Strip.K := inferInstanceAs (Module Field5 (Field5 × Field5))
set_option maxRecDepth 8192

private structure Witness where
  strip : Strip.Model
  flip : Bool
  shift : Plane
  first : Plane
  second : Plane

private def transform (s : Strip.Seed) (w : Witness) : Strip.Seed :=
  (if w.flip then s.image Neg.neg else s).image (shear w.shift)

private def witness (j l : Fin 5) (a b : Field5) : Option Witness :=
  match j.val,l.val,a.val,b.val with
  | 1,0,4,0 => some ⟨.twoZeroFour,false,(0,0),(1,0),(0,1)⟩
  | 1,4,0,0 => some ⟨.nestedFour,false,(0,0),(1,0),(0,1)⟩
  | 1,4,0,4 => some ⟨.nestedFour,false,(0,4),(1,0),(0,4)⟩
  | 1,4,4,0 => some ⟨.triangleFour,false,(0,0),(1,0),(0,1)⟩
  | 1,4,4,4 => some ⟨.triangleFour,false,(0,4),(1,0),(0,4)⟩
  | 4,1,0,4 => some ⟨.nestedFour,false,(0,1),(1,0),(0,1)⟩
  | 4,1,4,4 => some ⟨.triangleFour,false,(1,1),(1,0),(1,1)⟩
  | 4,4,0,0 => some ⟨.nestedFour,true,(0,0),(4,0),(0,4)⟩
  | 4,4,4,0 => some ⟨.triangleFour,true,(4,0),(4,0),(4,4)⟩
  | _,_,_,_ => none

private def matchSeed (s : Strip.Seed) (w : Option Witness) : Bool :=
  match w with
  | none => false
  | some v => decide (transform s v=MixedStrip.pattern v.strip v.first v.second)

private def allowedHead (j : Fin 5) := j=0 ∨ j=1 ∨ j=4
private instance (j : Fin 5) : Decidable (allowedHead j) := by unfold allowedHead; infer_instance

/-- Every entry is checked against its actual four points and its actual coordinate map. -/
private theorem table2 : ∀ (j l : Fin 5) (a b : Field5), allowedHead j → allowedHead l →
    let s:=shape2 j l a b
    s.card=4 → Legal s →
    passes s=true ∨ s=extra false ∨ matchSeed s (witness j l a b)=true := by native_decide

private theorem table3 : ∀ (j l : Fin 5), allowedHead j → allowedHead l →
    let s:=shape3 j l
    s.card=4 → Legal s → passes s=true := by native_decide

noncomputable section
open scoped Classical

private theorem out2 (j l : Fin 5) (a b : Field5) (jh : allowedHead j) (lh : allowedHead l) :
    Disjoint (shape2 j l a b) (full _) := by
  apply disjoint_left.mpr
  intro v hv hd
  have forbidden : ∀ i : Fin 5,allowedHead i → ¬(i=2 ∨ i=3) := by decide
  rcases (show _ ∨ _ ∨ _ ∨ _ by simpa only [shape2,mem_insert,mem_singleton] using hv) with rfl|rfl|rfl|rfl
  · exact forbidden 0 (Or.inl rfl) (mem_full.mp hd)
  · exact forbidden 1 (Or.inr (Or.inl rfl)) (mem_full.mp hd)
  · exact forbidden _ jh (mem_full.mp hd)
  · exact forbidden _ lh (mem_full.mp hd)

private theorem out3 (j l : Fin 5) (jh : allowedHead j) (lh : allowedHead l) :
    Disjoint (shape3 j l) (full _) := by
  apply disjoint_left.mpr
  intro v hv hd
  have forbidden : ∀ i : Fin 5,allowedHead i → ¬(i=2 ∨ i=3) := by decide
  rcases (show _ ∨ _ ∨ _ ∨ _ by simpa only [shape3,mem_insert,mem_singleton] using hv) with rfl|rfl|rfl|rfl
  · exact forbidden 0 (Or.inl rfl) (mem_full.mp hd)
  · exact forbidden 1 (Or.inr (Or.inl rfl)) (mem_full.mp hd)
  · exact forbidden _ jh (mem_full.mp hd)
  · exact forbidden _ lh (mem_full.mp hd)

private theorem model {s : Strip.Seed} (sf : Free s) {w : Witness}
    (match_ : matchSeed s (some w)=true) : rankCount s≤3^25 := by
  let oriented := if w.flip then s.image Neg.neg else s
  have count : rankCount s=rankCount oriented := by
    by_cases flip : w.flip=true
    · simpa [oriented,flip] using negate_count s
    · simp [oriented,flip]
  have f : Free oriented := by
    by_cases flip : w.flip=true
    · simpa [oriented,flip] using (Assembly.free_image (AddEquiv.neg _) s).mpr sf
    · simpa [oriented,flip] using sf
  have data : oriented.image (shear w.shift)=MixedStrip.pattern w.strip w.first w.second := of_decide_eq_true match_
  have ff := (Assembly.free_image (shear w.shift) oriented).mpr f
  rw [data] at ff
  rw [count,shear_count w.shift oriented,data]
  exact (MixedStrip.all w.strip w.first w.second ff).trans_eq (by decide)

theorem shape2_bound (j l : Fin 5) (a b : Field5) (size : (shape2 j l a b).card=4)
    (sf : Free (shape2 j l a b)) (jh : j=0 ∨ j=1 ∨ j=4) (lh : l=0 ∨ l=1 ∨ l=4) :
    rankCount (shape2 j l a b)≤3^25 := by
  rcases table2 j l a b jh lh size (legal_of_free sf) with yes|ex|data
  · exact (graph_bound sf (out2 j l a b jh lh) size yes).trans_eq (by decide)
  · rw [ex]; exact extra_bound false
  · cases e : witness j l a b with
    | none => simp [e,matchSeed] at data
    | some w => rw [e] at data; exact model sf data

theorem shape3_bound (j l : Fin 5) (size : (shape3 j l).card=4)
    (sf : Free (shape3 j l)) (jh : j=0 ∨ j=1 ∨ j=4) (lh : l=0 ∨ l=1 ∨ l=4) :
    rankCount (shape3 j l)≤3^125 :=
  (graph_bound sf (out3 j l jh lh) size (table3 j l jh lh size (legal_of_free sf))).trans_eq
    (by norm_num [Cube,Plane,Field5])

end
end Audit.SmallMixed
