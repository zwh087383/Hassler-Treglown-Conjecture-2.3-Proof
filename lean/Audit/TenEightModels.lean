import Audit.TenEightLinks
import Audit.Generic

namespace Audit.TenEight
open Finset Sumfree Fingerprint TriangleBase TenEightLinks Lower Band Link Generic

variable {V : Type} [DecidableEq V]

def inside (n : V → Finset V) (a : Finset V) := ∑ y∈a,((n y)∩a).card
def sumDegree (n : V → Finset V) (a : Finset V) := ∑ y∈a,(n y).card
def common (n : V → Finset V) (x y : V) := (n y∩n x).card

def checkHigh (n : V → Finset V) (g : Finset V) (witness : V → V) (x : V) : Prop :=
    sumDegree n (n x)≤90 ∧ 6 ≤ inside n (n x) ∧
    (∀ y∈n x, (((n x).erase y).filter fun q => (n q).card=10).card≤5 ∧ 2 ≤ inside n ((n x).erase y)) ∧
    let w:=witness x
    w∈g ∧ x≠w ∧ w∉n x ∧ (n w).card=8 ∧ sumDegree n (n w)≤74 ∧ 6 ≤ inside n (n w) ∧
      6≤common n w x ∧
      (∀ y∈insert w (n w), y∈n x ∨ 3≤common n x y ∨
        ∃ q∈n x, (n q).card=10 ∧ y∉n q ∧ 2≤common n x y ∧ 3≤common n q y) ∧
      ∃ q∈n x, (n q).card=10 ∧ ∃z∈n q, (n z).card=10 ∧ z≠x ∧ z≠w ∧ z∉n x ∧ z∉n w ∧
        3≤common n z x+common n z w

def checkX (n : V → Finset V) (g : Finset V) (witness : V → V) (x : V) : Prop :=
  (n x).card=8 ∨ (n x).card=10 ∧ checkHigh n g witness x

instance (n : V → Finset V) (g : Finset V) (witness : V → V) (x : V) : Decidable (checkX n g witness x) := by
  unfold checkX checkHigh; infer_instance

def audit (n : V → Finset V) (g : Finset V) (witness : V → V) :=
  (∀ x∈g,checkX n g witness x) ∧ 18*g.card≤2*sumDegree n g

instance (n : V → Finset V) (g : Finset V) (witness : V → V) : Decidable (audit n g witness) := by
  unfold audit; infer_instance

theorem certified [Fintype V] (g : Finset V) (n : V → Finset V) (witness : V → V)
    (closedN : ∀x,n x⊆g) (sym : Symmetric fun x y => y∈n x) (irr : Irreflexive fun x y => y∈n x)
    (ck : audit n g witness) :
    (mis (fun x y => y∈n x) g:ℝ)≤(3:ℝ)^((g.card:ℝ)/4) := by
  classical
  let r (x y : V) := y∈n x
  have adj (a : Finset V) (x : V) : neighbors r a x=n x∩a := by
    ext y; simp [neighbors,r,and_comm]
  have orig (x : V) : neighbors r g x=n x := (adj _ _).trans (inter_eq_left.mpr (closedN x))
  have dg (x : V) : deg r g x=(n x).card := congrArg Finset.card (orig x)
  have dd (a : Finset V) (x : V) : deg r a x=(n x∩a).card := congrArg Finset.card (adj a x)
  have inside_eq (a : Finset V) : vol r a=inside n a := sum_congr rfl (fun y _ => dd _ _)
  have vol_g : vol r g=sumDegree n g := sum_congr rfl (fun y _ => dg y)
  have sum_eq (x : V) : around r g x=sumDegree n (n x) := by
    unfold around cross sumDegree
    rw [orig]; exact sum_congr rfl (fun y _ => dg y)
  have facts {x : V} (hx : x∈g) (d : deg r g x=10) :
      (n x).card=10 ∧ checkHigh n g witness x := (ck.1 x hx).resolve_left (by rw [←dg,d]; decide)
  apply TenEightLinks.bound (r:=r) sym irr g _ (by rw [vol_g]; exact ck.2)
  constructor
  · intro x hx
    rw [dg]
    exact (ck.1 x hx).imp id And.left
  · intro x hx d
    rw [sum_eq,orig,inside_eq]
    exact ⟨(facts hx d).2.1,(facts hx d).2.2.1⟩
  · intro x hx d y yn
    rw [orig] at yn ⊢
    simp_rw [dg,inside_eq]
    exact (facts hx d).2.2.2.1 y yn
  · intro x hx d
    refine ⟨witness x,?_⟩
    simp only [dg,sum_eq,orig,inside_eq,dd]
    exact (facts hx d).2.2.2.2

variable {K : Type} [AddCommGroup K] [DecidableEq K]
abbrev P (K : Type) := Raw.Point K
def pat (a b c : K) : Finset (Pt K) := {(0,a),(1,0),(1,b),(1,c),(4,-a)}

def valid (x : P K) := (x.1=2 ∨ x.1=3) ∧ (x.2.2=1 ∨ x.2.2=4)
instance (x : P K) : Decidable (valid x) := by unfold valid; infer_instance
def domain (K : Type) [Fintype K] := (univ : Finset (P K)).filter valid
def lift (u : Pt K) : P K := (u.1,u.2,0)
def moves (s : Finset (Pt K)) (x : P K) : Finset (P K) :=
  if valid x then
    ((s.image (fun u => lift u-x) ∪ s.image (fun u => x+lift u) ∪ s.image (fun u => x-lift u)).filter
      (fun y => valid y ∧ x≠y))
  else ∅

theorem in_moves {s : Finset (Pt K)} {x y : P K} :
    y∈moves s x ↔ valid x ∧ valid y ∧ edge (plane s) x y := by
  have seed (w : P K) : w∈plane s ↔ ∃u∈s,lift u=w := mem_image
  by_cases ok : valid x
  · rw [moves,if_pos ok]
    simp only [mem_filter,mem_union,mem_image,edge,seed,ok,true_and]
    constructor
    · rintro ⟨(⟨u,hu,e⟩|⟨u,hu,e⟩)|⟨u,hu,e⟩,yy,ne⟩
      · exact ⟨yy,ne,Or.inl ⟨u,hu,by rw [←e]; abel⟩⟩
      · exact ⟨yy,ne,Or.inr (Or.inl ⟨u,hu,by rw [←e]; abel⟩)⟩
      · exact ⟨yy,ne,Or.inr (Or.inr ⟨u,hu,by rw [←e]; abel⟩)⟩
    · rintro ⟨yy,ne,(⟨u,hu,e⟩|⟨u,hu,e⟩|⟨u,hu,e⟩)⟩
      · exact ⟨Or.inl (Or.inl ⟨u,hu,by rw [e]; abel⟩),yy,ne⟩
      · exact ⟨Or.inl (Or.inr ⟨u,hu,by rw [e]; abel⟩),yy,ne⟩
      · exact ⟨Or.inr ⟨u,hu,by rw [e]; abel⟩,yy,ne⟩
  · simp [moves,ok]

def pass [Fintype K] (s : Finset (Pt K)) := audit (moves s) (domain K) Neg.neg
instance [Fintype K] (s : Finset (Pt K)) : Decidable (pass s) := by unfold pass; infer_instance

theorem base_count [Fintype K] (s : Finset (Pt K)) (test : pass s) :
    rankCount s≤3^Fintype.card K := by
  classical
  have eq : domain K=Raw.domain := rfl
  have valid_in {x : P K} : x∈domain K ↔ valid x := by simp [domain]
  have res := certified (domain K) (moves s) Neg.neg (fun _ _ h => valid_in.mpr (in_moves.mp h).2.1)
    (fun _ _ h => in_moves.mpr ⟨(in_moves.mp h).2.1,(in_moves.mp h).1,edge_sym _ (in_moves.mp h).2.2⟩)
    (fun _ h => (in_moves.mp h).2.2.1 rfl) test
  have same : mis (fun x y => y∈moves s x) (domain K)=rankCount s := by
    apply Sumfree.count_congr
    intro x hx y hy
    simpa [in_moves,valid_in.mp hx,valid_in.mp hy]
  have size : (domain K).card=4*Fintype.card K := by
    rw [eq]
    have f : Raw.domain (K:=K)=({2,3}:Finset (Fin 5)) ×ˢ ((univ:Finset K) ×ˢ ({1,4}:Finset (Fin 5))) := by
      ext x; simp [Raw.domain]
    rw [f]; simp [show (2:Fin 5)≠3 by decide,show (1:Fin 5)≠4 by decide]; ring
  rw [same,size,Nat.cast_mul,Nat.cast_ofNat,show 4*(Fintype.card K:ℝ)/4=(Fintype.card K:ℝ) by ring,Real.rpow_natCast] at res
  exact_mod_cast res

end Audit.TenEight
