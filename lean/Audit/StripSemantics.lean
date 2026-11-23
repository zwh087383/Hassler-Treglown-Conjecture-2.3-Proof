import Audit.StripFormula

namespace Audit.Strip
open Finset Sumfree Sumfree.Counter Generic

theorem adjacency (c : Model) (p q : P) :
    adj c p q=true ↔ Band.edge (plane (seed c)) p q := by
  simp only [adj,inPlane,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,
    decide_eq_true_eq,Band.edge,in_plane]
  tauto

private theorem covers (c : Model) : ∀ p : P, p∈Raw.domain → ∃ h i, vertex c h i=p := by
  cases c <;> native_decide

private theorem contains_vertices (c : Model) : ∀ h i, vertex c h i∈Raw.domain := by
  cases c <;> native_decide

private theorem internal_neighbors (c : Model) :
    ∀ (h : Bool) (i : Fin 50), inside i=true → ∀ h' j,
      adj c (vertex c h i) (vertex c h' j)=true → h'=h := by
  cases c <;> native_decide

private def bits (c : Model) (h : Bool) (I : Finset P) (i : Fin 50) : Bool :=
  decide (vertex c h i∈I)

private theorem restriction (c : Model) (h : Bool) (I : Finset P)
    (hi : IsMIS (Band.edge (plane (seed c))) Raw.domain I) :
    sat (windowFormula c h) (readBit (bits c h I))=true := by
  let v := vertex c h
  let e := fun x y => adj c (v x) (v y)
  have get (i : Fin 50) : readBit (bits c h I) i.val=decide (v i∈I) := by
    simp [readBit,bits,v]
  have positive (i : Fin 50) (hi : v i∈I) : (readBit (bits c h I) i.val == true)=true := by
    simp [get,hi]
  have negative (i : Fin 50) (hi : v i∉I) : (readBit (bits c h I) i.val == false)=true := by
    simp [get,hi]
  apply List.all_eq_true.mpr
  intro clause member
  obtain ⟨x,_,mem⟩ := List.mem_flatMap.mp member
  let neigh := (List.finRange 50).filter (e x)
  let conflicts := (neigh.filter fun y => decide (x<y)).map fun y => [(x.val,false),(y.val,false)]
  have noEdge (hc : clause∈conflicts) :
      clause.any (fun l => readBit (bits c h I) l.1 == l.2)=true := by
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hc
    have linked := (List.mem_filter.mp (List.mem_filter.mp hy).1).2
    by_cases first : v x∈I
    · have second : v y∉I := fun hy => hi.2.1 _ first _ hy ((adjacency ..).mp linked)
      exact List.any_eq_true.mpr ⟨(y.val,false),by simp,negative y second⟩
    · exact List.any_eq_true.mpr ⟨(x.val,false),by simp,negative x first⟩
  change clause∈(if inside x then ((x.val,true)::neigh.map fun y => (y.val,true))::conflicts else conflicts) at mem
  split at mem
  · rename_i internal
    rcases List.mem_cons.mp mem with val|edge
    · subst clause
      by_cases first : v x∈I
      · exact List.any_eq_true.mpr ⟨(x.val,true),by simp,positive x first⟩
      · obtain ⟨y,yi,yedge⟩ := hi.2.2 (v x) (contains_vertices c h x) first
        obtain ⟨s,j,rfl⟩ := covers c y (hi.1 yi)
        have linked := (adjacency ..).mpr yedge
        obtain rfl := internal_neighbors c h x internal s j linked
        have jmem : j∈neigh := List.mem_filter.mpr ⟨List.mem_finRange _,linked⟩
        exact List.any_eq_true.mpr ⟨(j.val,true),
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,jmem,rfl⟩),positive j yi⟩
    · exact noEdge edge
  · exact noEdge mem

theorem window_product (c : Model) :
    rankCount (seed c) ≤ count c false * count c true := by
  let fs := family (Band.edge (plane (seed c))) (Raw.domain : Finset P)
  let enc (h : Bool) (I : ↥fs) : Models 50 (windowFormula c h) :=
    ⟨bits c h I.val,restriction c h I.val (mem_family.mp I.property)⟩
  let pair (I : ↥fs) := (enc false I,enc true I)
  have inj : Function.Injective pair := by
    intro I J eq
    have same (h : Bool) (i : Fin 50) : (vertex c h i∈I.val) ↔ (vertex c h i∈J.val) := by
      have f : (enc h I).val=(enc h J).val := by
        cases h with
        | false => exact congrArg Subtype.val (congrArg Prod.fst eq)
        | true => exact congrArg Subtype.val (congrArg Prod.snd eq)
      have v := congrFun f i
      simpa only [enc,bits,decide_eq_decide] using v
    apply Subtype.ext
    ext p
    by_cases member : p∈(Raw.domain : Finset P)
    · obtain ⟨h,i,rfl⟩ := covers c p member
      exact same h i
    · exact ⟨fun hp => False.elim (member ((mem_family.mp I.property).1 hp)),
        fun hp => False.elim (member ((mem_family.mp J.property).1 hp))⟩
  have bound := Nat.card_le_card_of_injective pair inj
  rw [Nat.card_prod] at bound
  have card : Nat.card ↥fs=rankCount (seed c) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]; rfl
  rw [card,←solve_correct,←solve_correct,←cached_correct,←cached_correct] at bound
  exact bound

end Audit.Strip
