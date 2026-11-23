import Audit.StripNoZeroData
import Audit.Strip

namespace Audit.Strip.NoZero
open Finset Sumfree Sumfree.Counter Generic Reduction

private theorem adjacency (p q : P) : adj p q=true ↔ Band.edge (plane seed) p q := by
  simp only [adj,inPlane,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,
    decide_eq_true_eq,Band.edge,in_plane]; tauto

private theorem covers : ∀ p : P, p∈Raw.domain → (∃ j : Fin 50, vertex false j.val=p) ∨
    (∃ j : Fin 50, vertex true j.val=p) := by native_decide

private theorem every_row : ∀ (h : Bool) (j : Fin 50), vertex h j.val∈Raw.domain := by native_decide
private theorem bipartite : ∀ h (i j : Fin 50), adj (vertex h i.val) (vertex h j.val)=false := by
  native_decide

private def bits {n : ℕ} (start : ℕ) (I : Finset P) (i : Fin n) : Bool :=
  decide (vertex true (start+i.val)∈I)

private theorem restriction {n start : ℕ} (small : start+n≤50) (cs : List (Clause n))
    (valid : cs.all (checked start)=true) {I : Finset P}
    (hi : IsMIS (Band.edge (plane seed)) Raw.domain I) :
    sat (formula cs) (readBit (bits (n:=n) start I))=true := by
  let row (i : Fin n) := vertex true (start+i.val)
  have get (i : Fin n) : readBit (bits (n:=n) start I) i.val=decide (row i∈I) := by
    simp [readBit,bits,row]
  apply List.all_eq_true.mpr
  intro clause hc
  obtain ⟨⟨i,B⟩,member,rfl⟩ := List.mem_map.mp hc
  by_cases selected : row i∈I
  · refine List.any_eq_true.mpr ⟨(i.val,true),List.mem_cons_self,?_⟩
    simp [get,selected]
  · let k : Fin 50 := ⟨start+i.val,by have := i.isLt; omega⟩
    obtain ⟨p,hp,edge⟩ := hi.2.2 (row i) (every_row true k) selected
    obtain left|right := covers p (hi.1 hp)
    · obtain ⟨j,rfl⟩ := left
      have link := (adjacency ..).mpr edge
      have cert := List.all_eq_true.mp (List.all_eq_true.mp valid _ member) j (List.mem_finRange _)
      change (!adj (row i) (vertex false j.val) || B.any fun z => adj (vertex false j.val) (row z))=true at cert
      rw [link] at cert
      have hB : (B.any fun z => adj (vertex false j.val) (row z))=true := by simpa using cert
      obtain ⟨z,hz,zb⟩ := List.any_eq_true.mp hB
      have absent : row z∉I := fun zi => hi.2.1 _ hp _ zi ((adjacency ..).mp zb)
      refine List.any_eq_true.mpr ⟨(z.val,false),List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨z,hz,rfl⟩),?_⟩
      simp [get,absent]
    · obtain ⟨j,rfl⟩ := right
      have bad := (adjacency ..).mpr edge
      rw [show row i=vertex true k.val from rfl,bipartite true k j] at bad
      contradiction

private theorem right_determines {I J : Finset P}
    (hi : IsMIS (Band.edge (plane seed)) Raw.domain I)
    (hj : IsMIS (Band.edge (plane seed)) Raw.domain J)
    (right : ∀ j : Fin 50, vertex true j.val∈I ↔ vertex true j.val∈J) : I=J := by
  have sub (a b : Finset P) (ha : IsMIS (Band.edge (plane seed)) Raw.domain a)
      (hb : IsMIS (Band.edge (plane seed)) Raw.domain b)
      (keep : ∀ j : Fin 50, vertex true j.val∈b ↔ vertex true j.val∈a) : a⊆b := by
    intro p hp
    rcases covers p (ha.1 hp) with ⟨i,rfl⟩|⟨i,rfl⟩
    · by_contra miss
      obtain ⟨q,hq,edge⟩ := hb.2.2 _ (every_row false i) miss
      rcases covers q (hb.1 hq) with ⟨j,rfl⟩|⟨j,rfl⟩
      · have same := (adjacency ..).mpr edge
        rw [bipartite false i j] at same
        contradiction
      · exact ha.2.1 _ hp _ ((keep j).mp hq) edge
    · exact (keep i).mpr hp
  exact Subset.antisymm (sub I J hi hj (fun _ => (right _).symm)) (sub J I hj hi right)

/-- Bound the sharp component directly from its original sum/difference graph. -/
theorem model_bound : rankCount seed < 3^25 := by
  let fs := family (Band.edge (plane seed)) (Raw.domain : Finset P)
  let pair (I : ↥fs) : Models 20 (formula pairClauses) × Models 30 (formula tripleClauses) :=
    (⟨bits 0 I.val, restriction (by decide) pairClauses pair_sound (mem_family.mp I.property)⟩,
     ⟨bits 20 I.val,restriction (by decide) tripleClauses triple_sound (mem_family.mp I.property)⟩)
  have inj : Function.Injective pair := by
    intro I J eq
    apply Subtype.ext
    apply right_determines (mem_family.mp I.property) (mem_family.mp J.property)
    intro i
    by_cases a : i.val<20
    · let x : Fin 20 := ⟨i.val,a⟩
      have h := congrFun (congrArg (fun z : Models 20 (formula pairClauses) × Models 30 (formula tripleClauses) =>
        z.1.val) eq) x
      simpa [pair,bits,x] using h
    · let x : Fin 30 := ⟨i.val-20,by have := i.isLt; omega⟩
      have h := congrFun (congrArg (fun z : Models 20 (formula pairClauses) × Models 30 (formula tripleClauses) =>
        z.2.val) eq) x
      have back : 20+x.val=i.val := by dsimp [x]; omega
      simpa only [pair,bits,back,decide_eq_decide] using h
  have h := Nat.card_le_card_of_injective pair inj
  rw [Nat.card_prod] at h
  have card : Nat.card ↥fs=rankCount seed := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]; rfl
  rw [card,←solve_correct,←solve_correct,←cached_correct,←cached_correct,pair_count,triple_count] at h
  exact h.trans_lt (by decide)

theorem model_bound_space :
    rankCount (seed.image (relabel Strip.coordinates)) < 3^(5^2) := by
  rw [←rankCount_relabel]; exact model_bound

end Audit.Strip.NoZero
