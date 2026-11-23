import Sumfree.Orbit
import Sumfree.CountMemo
import Mathlib.Data.List.Dedup

namespace Sumfree.Pair
open Finset Sumfree.Counter

def freeB {G : Type*} [Add G] [DecidableEq G] (L : List G) : Bool :=
  L.all fun x => L.all fun y => !(L.contains (x+y))
theorem freeB_iff {G : Type*} [Add G] [DecidableEq G] (L : List G) :
    freeB L ↔ SumFree {x | x ∈ L} := by
  simp [freeB,SumFree]
theorem legal_bool {H : Type*} [AddCommGroup H] [DecidableEq H] (s t x : Ambient H) :
    freeB [x,s,t] ↔ legalAt s t x := by
  have same : {p : Ambient H | p ∈ [x,s,t]} = insert x (seedSet s t) := by
    ext p; simp [seedSet]
  exact (freeB_iff [x,s,t]).trans (by rw [same]; rfl)

def edgeB {H : Type*} [AddCommGroup H] [DecidableEq H] (s t x y : Ambient H) :=
  x != y && ([s,t].contains (x+y) || [s,t].contains (x-y) || [s,t].contains (y-x))
theorem edge_bool {H : Type*} [AddCommGroup H] [DecidableEq H] (s t x y : Ambient H) :
    edgeB s t x y ↔ edges s t x y := by simp [edgeB,edges,raw,seedSet,or_assoc]

abbrev Plane := F × F
def shapes : List (Plane × Plane) :=
  [((0,0),(0,0)),((0,0),(1,0)),((1,0),(0,1))] ++ coeffs.map (fun c => ((1,0),(c,0)))

def rooted (s t g : Ambient Plane) := (points s t g).dedup

def localCount (s t g : Ambient Plane) :=
  let L := rooted s t g
  cached L.length (graphFormula L.length
    (fun i j => edgeB s t (L.get i) (L.get j)) (fun i => freeB [L.get i,s,t]))

theorem local_correct (s t g : Ambient Plane) :
    localCount s t g = mis (edges s t) (allowed s t (cell s t g)) := by
  classical
  let L := rooted s t g
  let a := fun (i : Fin L.length) => freeB [L.get i,s,t]
  let e := fun (i j : Fin L.length) => edgeB s t (L.get i) (L.get j)
  have nodup : L.Nodup := List.nodup_dedup _
  have ix : Function.Injective L.get := (List.nodup_iff_injective_get.mp nodup)
  have imageEq : (domain a).image L.get = allowed s t (cell s t g) := by
    ext v
    simp only [mem_image,mem_allowed]
    constructor
    · rintro ⟨i,hi,rfl⟩
      have incl := L.get_mem i
      refine ⟨?_,(legal_bool s t (L.get i)).1 (Finset.mem_filter.mp hi).2⟩
      exact List.mem_toFinset.mpr (List.mem_dedup.mp incl)
    · rintro ⟨hc,safe⟩
      have vl : v ∈ L := by simpa [cell,L,rooted] using hc
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp vl
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(legal_bool s t (L.get i)).2 safe⟩,rfl⟩
  change cached L.length (graphFormula _ e a) = _
  rw [cached_correct,solve_mis, ← imageEq]
  exact mis_image _ _ _ _ ix.injOn (fun i _ j _ => edge_bool s t (L.get i) (L.get j))

def powerFor {A : Type*} [DecidableEq A] (s t : A) : Nat := if s=t then 4 else 50
def baseFor {A : Type*} [DecidableEq A] (s t : A) : Nat := if s=t then 3 else 820694

def allCases (check : Ambient Plane → Ambient Plane → Ambient Plane → Bool) : Bool := [2,3].all fun (c : F) =>
  [0,1,4].all fun (a : F) => [0,1,4].all fun (b : F) =>
    shapes.all fun uv =>
      let s : Ambient Plane := (a,uv.1)
      let t : Ambient Plane := (b,uv.2)
      let g : Ambient Plane := (c,0)
      if freeB [s,t] then check s t g
      else true

def localOK (s t g : Ambient Plane) :=
  decide (localCount s t g ^ powerFor s t ≤ (baseFor s t)^(rooted s t g).length)
def finiteCases := allCases localOK

end Sumfree.Pair
