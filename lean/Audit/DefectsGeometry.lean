import Audit.Generic
import Sumfree.TheoremA

namespace Audit.Defects
open Finset Sumfree Lower Generic Band
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {H : Type} [AddCommGroup H] [DecidableEq H]

def rawAtom (z : Ambient H) (x : H) (a : Bool) (y : H) (b : Bool) :=
  raw ({z} : Set (Ambient H)) (Sumfree.vertex (a,x)) (Sumfree.vertex (b,y))

theorem zero_formula (d x y : H) (a b : Bool) : rawAtom (0,d) x a y b ↔
    (y-x=d ∧ (a≠false ∨ b≠true)) ∨ (x-y=d ∧ (a≠true ∨ b≠false)) := by
  have h1 : -x+y=y-x := by abel
  have h2 : -y+x=x-y := by abel
  have h3 : -x- -y=y-x := by abel
  have h4 : -y- -x=x-y := by abel
  have h5 : x+ -y=x-y := by abel
  have h6 : y+ -x=y-x := by abel
  cases a <;> cases b <;>
    simp (config:={decide:=true}) [rawAtom,raw,Sumfree.vertex,Base,Prod.mk_add_mk,Prod.mk_sub_mk,Prod.neg_mk,
      h1,h2,h3,h4,h5,h6,or_comm]

theorem one_formula (d x y : H) (a b : Bool) : rawAtom (1,d) x a y b ↔
    x+y= -d ∧ (a≠false ∨ b≠false) := by
  have h1 : -x- y= -(x+y) := by abel
  have h2 : -y- x= -(x+y) := by abel
  have h3 : -x+ -y= -(x+y) := by abel
  cases a <;> cases b <;>
    simp (config:={decide:=true}) [rawAtom,raw,Sumfree.vertex,Base,Prod.mk_add_mk,Prod.mk_sub_mk,Prod.neg_mk,
      h1,h2,h3,neg_eq_iff_eq_neg] <;>
    rw [show -y+ -x= -(x+y) by abel,neg_eq_iff_eq_neg]

theorem four_formula (d x y : H) (a b : Bool) : rawAtom (4,d) x a y b ↔
    x+y=d ∧ (a≠true ∨ b≠true) := by
  have h1 : x- -y=x+y := by abel
  have h2 : y- -x=x+y := by abel
  cases a <;> cases b <;>
    simp (config:={decide:=true}) [rawAtom,raw,Sumfree.vertex,Base,Prod.mk_add_mk,Prod.mk_sub_mk,Prod.neg_mk,
      h1,h2,add_comm y x]

variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
abbrev Index (K : Type) := K × Bool
def residualSign (b : Bool) : Fin 5 := if b then 4 else 1
def tail (x : Index K) : K × Fin 5 := (x.1,residualSign x.2)
def place (p : Index K × Bool) : Raw.Point K := Sumfree.vertex (p.2,tail p.1)

theorem tail_injective : Function.Injective (@tail K) := by
  rintro ⟨x,b⟩ ⟨y,c⟩ h
  have xy := congrArg Prod.fst h
  have bc := congrArg Prod.snd h
  cases b <;> cases c <;> simp (config:={decide:=true}) [tail,residualSign] at * <;> assumption

theorem place_injective : Function.Injective (@place K _) := by
  rintro ⟨u,b⟩ ⟨v,c⟩ h
  have inj : Function.Injective (@Sumfree.vertex (K × Fin 5) _) := by
    rintro ⟨a,x⟩ ⟨b,y⟩ eq
    cases a <;> cases b <;>
      simp (config:={decide:=true}) [Sumfree.vertex,Base,Prod.neg_mk] at eq ⊢ <;> exact eq
  have e := inj h
  exact Prod.ext (tail_injective (congrArg Prod.snd e)) (congrArg Prod.fst e)

theorem domain_image : (univ.image (@place K _))=Raw.domain := by
  ext p
  obtain ⟨i,k,t⟩ := p
  simp only [mem_image,mem_univ,true_and,Raw.domain,mem_filter]
  constructor
  · rintro ⟨⟨⟨x,sign⟩,b⟩,eq⟩
    have head := congrArg Prod.fst eq
    have last := congrArg (fun q : Raw.Point K => q.2.2) eq
    cases sign <;> cases b <;>
      simp (config:={decide:=true}) [place,Sumfree.vertex,Base,tail,residualSign] at head last <;>
      subst i <;> subst t <;> decide
  · rintro ⟨rfl|rfl,rfl|rfl⟩
    · exact ⟨((k,false),false),rfl⟩
    · exact ⟨((k,true),false),rfl⟩
    · exact ⟨((-k,true),true),by simp [place,Sumfree.vertex,Base,tail,residualSign,Prod.neg_mk]; decide⟩
    · exact ⟨((-k,false),true),by simp [place,Sumfree.vertex,Base,tail,residualSign,Prod.neg_mk]; decide⟩

def projected (s : Finset (Pt K)) (p q : Index K × Bool) := Band.edge (plane s) (place p) (place q)

theorem raw_count (s : Finset (Pt K)) : rankCount s=mis (projected s) univ := by
  unfold rankCount
  rw [←domain_image]
  symm
  apply mis_image _ _ _ _ place_injective.injOn (fun _ _ _ _ => Iff.rfl)

def background (T : Finset (Pt K)) (x y : Index K) :=
  raw (↑(plane T) : Set (Raw.Point K)) (Base (tail x)) (Base (tail y))

theorem bg_sym (T : Finset (Pt K)) : Symmetric (background T) := fun _ _ h => raw_sym _ h

theorem bg_irr (T : Finset (Pt K)) (zero : 0∉T) : Irreflexive (background T) := by
  rintro ⟨k,b⟩ h
  change _ ∈ plane T ∨ _ ∈ plane T ∨ _ ∈ plane T at h
  simp only [sub_self,in_plane] at h
  have nz : residualSign b + residualSign b ≠ 0 := by cases b <;> decide
  exact h.elim (fun hx => nz hx.2) (fun a => a.elim (fun hx => zero hx.1) (fun hx => zero hx.1))

theorem bg_raw (T : Finset (Pt K)) (stable : ∀ x, x∈T ↔ -x∈T) (p q : Index K × Bool) :
    raw (↑(plane T) : Set (Raw.Point K)) (place p) (place q) ↔ background T p.1 q.1 := by
  apply raw_vertex
  intro x
  change (x:Raw.Point K)∈plane T ↔ -(x:Raw.Point K)∈plane T
  rw [in_plane T (x:Raw.Point K),in_plane T (-(x:Raw.Point K))]
  change ((x.1,x.2.1)∈T ∧ x.2.2=0) ↔ (-(x.1,x.2.1)∈T ∧ -x.2.2=0)
  exact and_congr (stable _) (by simp)

theorem insert_atom (z : Pt K) (T : Finset (Pt K)) (p q : Index K × Bool) :
    raw (↑(plane (insert z T)) : Set (Raw.Point K)) (place p) (place q) ↔
      rawAtom (z.1,z.2,0) (tail p.1) p.2 (tail q.1) q.2 ∨
      raw (↑(plane T) : Set (Raw.Point K)) (place p) (place q) := by
  simp only [plane,image_insert,coe_insert,raw,rawAtom,Set.mem_insert_iff,Set.mem_singleton_iff,place]
  tauto

theorem edge_raw (s : Finset (Pt K)) (p q : Index K × Bool) :
    projected s p q ↔ p≠q ∧ raw (↑(plane s) : Set (Raw.Point K)) (place p) (place q) := by
  simp only [projected,Band.edge,place_injective.ne_iff,raw,mem_coe]
  tauto

end
end Audit.Defects
