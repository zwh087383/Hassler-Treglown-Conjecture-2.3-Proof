import Audit.Matrix
import Audit.Link

namespace Audit.Raw
open Finset Bipartite Matrix
set_option linter.unusedSectionVars false
variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]
abbrev Point (K : Type*) := Fin 5 × K × Fin 5

def inSeed (p q : Finset K) (a : Point K) :=
  a.2.2=0 ∧ ((a.1=1 ∧ a.2.1∈p) ∨ (a.1=4 ∧ -a.2.1∈q))
noncomputable def seed (p q : Finset K) : Finset (Point K) := by
  classical exact univ.filter (inSeed p q)
@[simp] theorem mem_seed {p q : Finset K} {a : Point K} : a∈seed p q ↔ inSeed p q a := by
  classical simp [seed]

def domain : Finset (Point K) := univ.filter fun a => (a.1=2 ∨ a.1=3) ∧ (a.2.2=1 ∨ a.2.2=4)
def ordinary (p q : Finset K) (a b : Point K) : Prop :=
  a≠b ∧ (inSeed p q (a+b) ∨ inSeed p q (a-b) ∨ inSeed p q (b-a))

def place (v : Vertex K) : Point K :=
  match v.1,v.2.2 with
  | false,false => (2,v.2.1,1)
  | false,true  => (3,-v.2.1,4)
  | true,false  => (2,-v.2.1,4)
  | true,true   => (3,v.2.1,1)

theorem image_domain : univ.image (@place K _) = domain := by
  ext ⟨a,x,l⟩
  simp only [mem_image,mem_univ,true_and,domain,mem_filter]
  constructor
  · rintro ⟨⟨b,y,c⟩,e⟩; cases b <;> cases c <;> simp [place] at e <;>
      obtain ⟨rfl,rfl,rfl⟩ := e <;> simp
  · rintro ⟨rfl|rfl,rfl|rfl⟩
    · exact ⟨(false,x,false),rfl⟩
    · exact ⟨(true,-x,false),by simp [place]⟩
    · exact ⟨(true,x,true),rfl⟩
    · exact ⟨(false,-x,true),by simp [place]⟩

theorem place_injective : Function.Injective (@place K _) := by
  rintro ⟨a,x,i⟩ ⟨b,y,j⟩ e
  cases a <;> cases b <;> cases i <;> cases j <;>
    simp (config:={decide:=true}) [place] at * <;> assumption

theorem raw_matrix (p q : Finset K) :
    Sumfree.mis (ordinary p q) domain = Sumfree.mis (adj (matrix p q)) univ := by
  rw [← image_domain]; symm
  apply Sumfree.mis_image
  · exact place_injective.injOn
  · rintro ⟨a,x,i⟩ _ ⟨b,y,j⟩ _
    cases a <;> cases b <;> cases i <;> cases j <;>
      simp (config:={decide:=true}) [adj,ordinary,inSeed,matrix,place,Prod.mk_add_mk,
        Prod.mk_sub_mk,sub_eq_add_neg,add_comm,or_comm]

theorem seed_free (p q : Finset K) : Link.Free (seed p q) := by
  have no : ∀ a b c : Fin 5, (a=1 ∨ a=4) → (b=1 ∨ b=4) → (c=1 ∨ c=4) → a+b≠c := by decide
  have heads (z : Point K) (h : z∈seed p q) : z.1=1 ∨ z.1=4 :=
    ((mem_seed.mp h).2).imp And.left And.left
  intro a ha b hb c hc eq
  exact no _ _ _ (heads _ ha) (heads _ hb) (heads _ hc) (congrArg Prod.fst eq)

/-- Testing a single band vertex never creates a Schur triple in this block. -/
theorem no_loops (p q : Finset K) (a : Point K) (ha : a∈domain) :
    Link.Free (insert a (seed p q)) := by
  have absent : (0 : Point K) ∉ seed p q := by
    intro h; rcases (mem_seed.mp h).2 with ap|aq
    · exact (by decide : (0:Fin 5)≠1) ap.1
    · exact (by decide : (0:Fin 5)≠4) aq.1
  have tail (z : Point K) (hz : z∈seed p q) : z.2.2=0 := (mem_seed.mp hz).1
  have nonzero : a.2.2≠0 := by
    obtain h|h := (mem_filter.mp ha).2.2 <;> rw [h] <;> decide
  have dbl : a.2.2+a.2.2 ≠ 0 := by
    obtain h|h := (mem_filter.mp ha).2.2 <;> rw [h] <;> decide
  have project (x y z : Point K) (e : x+y=z) : x.2.2+y.2.2=z.2.2 := congrArg (fun w : Point K => w.2.2) e
  intro x hx y hy z hz e
  have cx := mem_insert.mp hx
  have cy := mem_insert.mp hy
  have cz := mem_insert.mp hz
  clear hx hy hz
  rcases cx with rfl|xs <;> rcases cy with rfl|ys <;> rcases cz with rfl|zs
  · exact nonzero (by simpa using project _ _ _ e)
  · exact dbl ((project _ _ _ e).trans (tail _ zs))
  · exact absent ((add_eq_left.mp e) ▸ ys)
  · exact nonzero (by simpa [tail _ ys,tail _ zs] using project _ _ _ e)
  · exact absent ((add_eq_right.mp e) ▸ xs)
  · exact nonzero (by simpa [tail _ xs,tail _ zs] using project _ _ _ e)
  · exact nonzero (by simpa [tail _ xs,tail _ ys] using (project _ _ _ e).symm)
  · exact seed_free p q _ xs _ ys _ zs e

theorem type_A (t : Fin 4 → K) (h : Function.Injective t) :
    Sumfree.mis (ordinary {t 0,t 1,t 2} {t 3}) domain < 3^(Fintype.card K) := by
  rw [raw_matrix]; exact Matrix.type_A t h
theorem type_C (t : Fin 4 → K) (h : Function.Injective t) :
    Sumfree.mis (ordinary {t 0,t 1,t 2} {t 0,t 3}) domain < 3^(Fintype.card K) := by
  rw [raw_matrix]; exact Matrix.type_C t h
theorem type_B {k : ℕ} (t : Fin 4 → Collisions.Space k) (h : Function.Injective t) :
    Sumfree.mis (ordinary {t 0,t 1} {t 2,t 3}) domain < 3^(Fintype.card (Collisions.Space k)) := by
  rw [raw_matrix]; exact Matrix.type_B t h

end Audit.Raw
