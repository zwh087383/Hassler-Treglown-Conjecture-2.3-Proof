import Audit.SmallMixedZeroData

namespace Audit.SmallMixed.ZeroTriple
open Finset Sumfree Sumfree.Counter Generic Strip

private theorem adjacency (p q : P) : adj p q=true ↔ Band.edge (plane seed) p q := by
  simp only [adj,isIn,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,
    decide_eq_true_eq,Band.edge,in_plane]
  tauto

private theorem covers : ∀ p : P, p∈Raw.domain → ∃ h i, vertex h i=p := by native_decide
private theorem contains_vertices : ∀ h i, vertex h i∈Raw.domain := by native_decide
private theorem separate : ∀ h i g j, adj (vertex h i) (vertex g j)=true → h=g := by native_decide

private def bits (h : Bool) (I : Finset P) (i : Fin 50) : Bool := decide (vertex h i∈I)

private theorem restriction (h : Bool) (I : Finset P) (hi : IsMIS (Band.edge (plane seed)) Raw.domain I) :
    sat (condition h) (readBit (bits h I))=true := by
  let e (x y : Fin 50) := adj (vertex h x) (vertex h y)
  have clauses : ∀ c ∈ condition h, c ∈ graphFormula 50 e (fun _ => true) true := by
    dsimp only [e]
    cases h <;> native_decide
  have get (i : Fin 50) : i∈selected (bits h I) ↔ vertex h i∈I := by simp [selected,bits]
  have full : sat (graphFormula 50 e (fun _ => true) true) (readBit (bits h I))=true := by
    apply (graph_semantics ..).mpr
    refine ⟨by simp [domain],?_,?_⟩
    · intro x hx y hy edge
      exact hi.2.1 _ ((get x).mp hx) _ ((get y).mp hy) ((adjacency ..).mp edge)
    · intro _ x _ hx
      obtain ⟨y,hy,xy⟩ := hi.2.2 _ (contains_vertices h x) (fun sel => hx ((get x).mpr sel))
      obtain ⟨g,j,rfl⟩ := covers _ (hi.1 hy)
      have linked := (adjacency ..).mpr xy
      obtain rfl := separate _ _ _ _ linked
      exact ⟨j,(get j).mpr hy,linked⟩
  exact List.all_eq_true.mpr (fun c hc => List.all_eq_true.mp full c (clauses c hc))

theorem product_bound : rankCount seed≤solve 50 (condition false)*solve 50 (condition false) := by
  let fs := family (Band.edge (plane seed)) (Raw.domain : Finset P)
  let enc (h : Bool) (I : ↥fs) : Models 50 (condition h) :=
    ⟨bits h I.val,restriction h I.val (mem_family.mp I.property)⟩
  let pair (I : ↥fs) := (enc false I,enc true I)
  have inj : Function.Injective pair := by
    intro I J eq
    have same (h : Bool) (i : Fin 50) : (vertex h i∈I.val) ↔ (vertex h i∈J.val) := by
      have f : (enc h I).val=(enc h J).val := by
        cases h with
        | false => exact congrArg Subtype.val (congrArg Prod.fst eq)
        | true => exact congrArg Subtype.val (congrArg Prod.snd eq)
      have v := congrFun f i
      simpa only [enc,bits,decide_eq_decide] using v
    apply Subtype.ext
    ext p
    by_cases member : p∈(Raw.domain : Finset P)
    · obtain ⟨h,i,rfl⟩ := covers p member
      exact same h i
    · exact ⟨fun hp => False.elim (member ((mem_family.mp I.property).1 hp)),
        fun hp => False.elim (member ((mem_family.mp J.property).1 hp))⟩
  have bound := Nat.card_le_card_of_injective pair inj
  rw [Nat.card_prod] at bound
  have card : Nat.card ↥fs=rankCount seed := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]; rfl
  rw [card,←solve_correct,←solve_correct,←formulas] at bound
  exact bound

end Audit.SmallMixed.ZeroTriple

