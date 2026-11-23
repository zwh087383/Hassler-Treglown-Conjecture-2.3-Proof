import Audit.Generic
import Audit.SeedFamilies

namespace Audit.TinyGeneric
open Finset Lower Band Link Generic Blocks Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {K : Type} [AddCommGroup K] [DecidableEq K] [Fintype K] [Module Field5 K]
local instance : Module Field5 (K × Fin 5) := inferInstanceAs (Module Field5 (K × Field5))
local instance : Module Field5 (Raw.Point K) := inferInstanceAs (Module Field5 (Field5 × K × Field5))

/-- The original two-seed orbit certificates multiply over any union of whole cells. -/
private theorem assemble {H : Type} [AddCommGroup H] [Module Field5 H] [DecidableEq H] [Fintype H]
    (s t : Sumfree.Ambient H) (os : ¬Pair.band s) (ot : ¬Pair.band t) (sf : SumFree (Pair.seedSet s t))
    (A : Finset (Sumfree.Ambient H)) (banded : ∀x∈A,Pair.band x) (closedA : ∀x∈A,Pair.cell s t x⊆A) :
    mis (Pair.edges s t) (Pair.allowed s t A)^Pair.powerFor s t≤Pair.baseFor s t^A.card := by
  induction A using Finset.strongInductionOn with
  | _ A prev =>
    by_cases empty : A=∅
    · subst A
      have one : family (Pair.edges s t) (Pair.allowed s t ∅)⊆{∅} := by
        intro I hi
        have h := (mem_family.mp hi).1
        simp [Pair.allowed] at h
        simpa using h
      simpa [mis] using Nat.pow_le_pow_left (card_le_card one) (Pair.powerFor s t)
    obtain ⟨g,hg⟩ := nonempty_iff_ne_empty.mpr empty
    let B:=Pair.cell s t g
    let D:=A\B
    have hit : g∈B := Pair.mem_cell.mpr ⟨banded _ hg,Pair.refl_rel ..⟩
    have sub : B⊆A := closedA g hg
    have strict : D⊂A := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun e => (mem_sdiff.mp (e.symm ▸ hg)).2 hit⟩
    have stable (x : Sumfree.Ambient H) (hx : x∈D) : Pair.cell s t x⊆D := by
      intro y hy
      refine mem_sdiff.mpr ⟨closedA _ (mem_sdiff.mp hx).1 hy,fun yb => ?_⟩
      exact (mem_sdiff.mp hx).2 (Pair.mem_cell.mpr ⟨banded _ (mem_sdiff.mp hx).1,
        Pair.trans_rel (Pair.mem_cell.mp yb).2 (Pair.sym_rel (Pair.mem_cell.mp hy).2)⟩)
    have split : Pair.allowed s t A=Pair.allowed s t B∪Pair.allowed s t D := by
      ext x; simp only [Pair.mem_allowed,mem_union,D,mem_sdiff]
      by_cases m : x∈B
      · simp [m,sub m]
      · simp [m]
    have dis : Disjoint (Pair.allowed s t B) (Pair.allowed s t D) := disjoint_left.mpr
      (fun _ hb hd => (mem_sdiff.mp (Pair.mem_allowed.mp hd).1).2 (Pair.mem_allowed.mp hb).1)
    have sep : ∀x∈Pair.allowed s t B,∀y∈Pair.allowed s t D,¬Pair.edges s t x y := by
      intro x hx y hy adj
      have yd := Pair.mem_allowed.mp hy |>.1
      exact (mem_sdiff.mp yd).2 (Pair.mem_cell.mpr ⟨banded _ (mem_sdiff.mp yd).1,
        Pair.trans_rel (Pair.mem_cell.mp (Pair.mem_allowed.mp hx).1).2 (Pair.edge_rel adj)⟩)
    have prod := disjoint_count (R:=Pair.edges s t) (fun _ _ e => ⟨e.1.symm,raw_sym _ e.2⟩) _ _ dis sep
    have bound := Nat.mul_le_mul (Pair.root_bound s t g os ot sf (banded _ hg))
      (prev D strict (fun x hx => banded _ (mem_sdiff.mp hx).1) stable)
    rw [split,prod,Nat.mul_pow]
    rw [←pow_add,Nat.add_comm,card_sdiff_add_card_eq_card sub] at bound
    exact bound

private def lift (p : Pt K) : Raw.Point K := (p.1,p.2,0)

private theorem legal_point {s : Finset (Pt K)} (sf : Free s) {u : Raw.Point K} (hu : u∈Raw.domain) :
    Free (insert u (plane s)) := by
  have absent : (0:Raw.Point K)∉plane s := fun m => sf 0 ((in_plane ..).mp m).1 0 ((in_plane ..).mp m).1
    0 ((in_plane ..).mp m).1 (zero_add _)
  have tail (v : Raw.Point K) (m : v∈plane s) := ((in_plane ..).mp m).2
  have signs := (mem_filter.mp hu).2.2
  have un : u.2.2≠0 := by rcases signs with e|e <;> rw [e] <;> decide
  have dn : u.2.2+u.2.2≠0 := by rcases signs with e|e <;> rw [e] <;> decide
  have last (x y z : Raw.Point K) (e : x+y=z) : x.2.2+y.2.2=z.2.2 := congrArg (fun p : Raw.Point K => p.2.2) e
  intro x hx y hy z hz e
  rcases mem_insert.mp hx with rfl|xs <;> rcases mem_insert.mp hy with rfl|ys <;> rcases mem_insert.mp hz with rfl|zs
  · exact un (by simpa using last _ _ _ e)
  · exact dn ((last _ _ _ e).trans (tail _ zs))
  · exact absent ((add_eq_left.mp e) ▸ ys)
  · exact un (by simpa [tail _ ys,tail _ zs] using last _ _ _ e)
  · exact absent ((add_eq_right.mp e) ▸ xs)
  · exact un (by simpa [tail _ xs,tail _ zs] using last _ _ _ e)
  · exact un (by simpa [tail _ xs,tail _ ys] using (last _ _ _ e).symm)
  · exact sf _ ((in_plane ..).mp xs).1 _ ((in_plane ..).mp ys).1 _ ((in_plane ..).mp zs).1
      (congrArg (fun p : Raw.Point K => (p.1,p.2.1)) e)

private theorem closed_cells (p q : Pt K) (x : Raw.Point K) (hx : x∈Raw.domain) :
    Pair.cell (lift p) (lift q) x⊆Raw.domain := by
  intro y hy
  obtain ⟨band,rel⟩ := Pair.mem_cell.mp hy
  refine mem_filter.mpr ⟨mem_univ _,band,?_⟩
  have signs := (mem_filter.mp hx).2.2
  have tail (a b : Field5) : (a • lift p+b • lift q).2.2=0 := by
    change a*(0:Field5)+b*0=0
    simp
  rcases rel with ⟨a,b,eq⟩|⟨a,b,eq⟩
  · have e : y.2.2-x.2.2=0 := (congrArg (fun z : Raw.Point K => z.2.2) eq).trans (tail a b)
    rwa [sub_eq_zero.mp e]
  · have e : y.2.2+x.2.2=0 := (congrArg (fun z : Raw.Point K => z.2.2) eq).trans (tail a b)
    rw [eq_neg_of_add_eq_zero_left e]
    rcases signs with h|h <;> rw [h] <;> decide

private theorem pair_bound (p q : Pt K) (sf : Free {p,q}) (out : Disjoint {p,q} (full K)) :
    rankCount {p,q}≤3^Fintype.card K := by
  let s:=lift p
  let t:=lift q
  have seeds : (plane {p,q} : Set (Raw.Point K))=Pair.seedSet s t := by
    ext x; simp only [plane,image_insert,image_singleton,coe_insert,coe_singleton,Pair.seedSet,s,t,lift]
  have nband {a : Pt K} (h : a∈({p,q}:Finset (Pt K))) : ¬Pair.band (lift a) :=
    fun b => disjoint_left.mp out h (mem_full.mpr b)
  have freePlane : Free (plane {p,q}) := by
    intro x hx y hy z hz e
    exact sf _ ((in_plane ..).mp hx).1 _ ((in_plane ..).mp hy).1 _ ((in_plane ..).mp hz).1
      (congrArg (fun x : Raw.Point K => (x.1,x.2.1)) e)
  have both : SumFree (Pair.seedSet s t) := seeds ▸ ((SeedFamilies.free_set _).mp freePlane)
  have permitted : Pair.allowed s t Raw.domain=Raw.domain := by
    ext x
    rw [Pair.mem_allowed]
    refine and_iff_left_of_imp ?_
    intro hx
    change SumFree (insert x (Pair.seedSet s t))
    rw [←seeds,←coe_insert,←SeedFamilies.free_set]
    exact legal_point sf hx
  have count : mis (Pair.edges s t) Raw.domain=rankCount {p,q} := by
    apply count_congr
    intro x _ y _
    simp only [Pair.edges,Band.edge,Sumfree.raw,←seeds,mem_coe]
    tauto
  have estimate := assemble s t (nband (mem_insert_self ..)) (nband (mem_insert_of_mem (mem_singleton_self q)))
    both Raw.domain (fun x hx => (mem_filter.mp hx).2.1) (closed_cells p q)
  have size : (Raw.domain (K:=K)).card=4*Fintype.card K := by
    have eq : Raw.domain (K:=K)=({2,3}:Finset (Fin 5)) ×ˢ ((univ:Finset K) ×ˢ ({1,4}:Finset (Fin 5))) := by
      ext x; simp [Raw.domain]
    rw [eq]; simp [show (2:Fin 5)≠3 by decide,show (1:Fin 5)≠4 by decide]; ring
  rw [permitted,count,size] at estimate
  by_cases same : s=t
  · simp only [Pair.powerFor,Pair.baseFor,if_pos same] at estimate
    apply (Nat.pow_le_pow_iff_left (by decide : (4:ℕ)≠0)).mp
    simpa only [←pow_mul,Nat.mul_comm] using estimate
  · simp only [Pair.powerFor,Pair.baseFor,if_neg same] at estimate
    apply (Nat.pow_le_pow_iff_left (by decide : (50:ℕ)≠0)).mp
    apply estimate.trans
    calc
      _ = (820694^2)^(2*Fintype.card K) := by rw [←pow_mul]; congr 1; omega
      _ ≤ (3^25)^(2*Fintype.card K) := Nat.pow_le_pow_left (by decide) _
      _ = (3^Fintype.card K)^50 := by rw [←pow_mul,←pow_mul]; congr 1; omega

theorem all {k : ℕ} (s : Finset (Pt (Space k))) (sf : Free s) (out : Disjoint s (full _)) (small : s.card≤2) :
    rankCount s≤3^(5^k) := by
  by_cases emp : s=∅
  · subst s
    have count : rankCount (∅:Finset (Pt (Space k)))≤1 := by
      unfold rankCount mis
      have only : family (edge (plane (∅:Finset (Pt (Space k))))) Raw.domain⊆{Raw.domain} := by
        intro I hi
        have spec:=mem_family.mp hi
        apply mem_singleton.mpr (Subset.antisymm spec.1 _)
        intro x hx
        by_contra missing
        obtain ⟨y,_,adj⟩ := spec.2.2 _ hx missing
        simp [Band.edge,plane] at adj
      simpa using card_le_card only
    exact count.trans (Nat.one_le_pow _ _ (by decide))
  · obtain ⟨p,q,rfl⟩ : ∃p q : Pt (Space k),s={p,q} := by
      have pos := card_pos.mpr (nonempty_iff_ne_empty.mpr emp)
      rcases (show s.card=1 ∨ s.card=2 by omega) with one|two
      · obtain ⟨p,rfl⟩ := card_eq_one.mp one
        exact ⟨p,p,by simp⟩
      · obtain ⟨p,q,_,eq⟩ := card_eq_two.mp two
        exact ⟨p,q,eq⟩
    simpa [Space,Field5] using pair_bound p q sf out

end
end Audit.TinyGeneric
