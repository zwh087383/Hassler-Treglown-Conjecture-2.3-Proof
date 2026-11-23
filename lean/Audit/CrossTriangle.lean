import Audit.MixedCounts

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees Fingerprint
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev Cell := Fin 5 × Field5
private def coeff (i : Fin 5) : Field5 := i
private def crossSeed : Finset Cell := {(0,1),(1,0),(4,4)}
private def crossEdge (x y : Cell) : Bool :=
  decide ((x.1=2 ∨ x.1=3) ∧ (y.1=2 ∨ y.1=3) ∧ x≠y ∧ (y-x∈crossSeed ∨ x-y∈crossSeed))
private def near (x : Cell) := univ.filter fun y => crossEdge x y=true
private theorem three_edges : ∀ h : Fin 5, h=2 ∨ h=3 →
    6≤∑ y∈near (h,0),((near (h,0)).filter fun t => crossEdge y t=true).card := by native_decide

noncomputable section
open scoped Classical
variable {k : ℕ} {s : Finset (Pt (Space k))}
set_option maxHeartbeats 800000

/-- A zero-sum triple in the three different layers gives three actual undirected edges
    inside every vertex neighborhood, in every ambient dimension. -/
theorem crossing_edges (a p : Space k) (nonzero : a≠0)
    (az : (0,a)∈s) (ps : (1,p)∈s) (qs : (4,-(p+a))∈s)
    (x : Raw.Point (Space k)) (hx : x∈Raw.domain) :
    6≤TriangleBase.vol (within s) (neighbors (within s) Raw.domain x) := by
  let lin : Cell →+ Pt (Space k) :=
    { toFun := fun (y : Cell) => (y.1, y.2 • a + coeff y.1 • p)
      map_zero' := by refine Prod.ext rfl ?_; change (0:Field5) • a+ (0:Field5) • p=0; simp
      map_add' := by intro y z; refine Prod.ext rfl ?_
                     change (y.2+z.2) • a+(coeff y.1+coeff z.1) • p=_
                     simp only [add_smul]; change _=(_+_)+(_+_); abel }
  have li : Function.Injective lin := by
    rintro ⟨h,u⟩ ⟨j,v⟩ eq
    obtain rfl : h=j := congrArg Prod.fst eq
    have t : u • a=v • a := add_right_cancel (congrArg Prod.snd eq)
    have z : (u-v) • a=0 := by rw [sub_smul,t,sub_self]
    exact Prod.ext rfl (sub_eq_zero.mp ((smul_eq_zero.mp z).resolve_right nonzero))
  let base : Cell := (x.1,0)
  let shift := x.2.1-(lin base).2
  let lift (y : Cell) : Raw.Point (Space k) := (y.1,(lin y).2+shift,x.2.2)
  have root : lift base=x := by refine Prod.ext rfl (Prod.ext ?_ rfl); dsimp only [lift,shift]; abel
  have inj : Function.Injective lift := by
    intro u v e
    apply li
    exact Prod.ext (congrArg (fun b : Raw.Point (Space k) => b.1) e) (add_right_cancel (congrArg (fun b : Raw.Point (Space k) => b.2.1) e))
  have into {w : Cell} (m : w∈crossSeed) : lin w∈s := by
    rcases (show w=(0,1) ∨ w=(1,0) ∨ w=(4,4) by simpa [crossSeed] using m) with rfl|rfl|rfl
    · change ((0:Fin 5),(1:Field5) • a+(0:Field5) • p)∈s
      simpa using az
    · change ((1:Fin 5),(0:Field5) • a+(1:Field5) • p)∈s
      simpa using ps
    · change ((4:Fin 5),(4:Field5) • a+(4:Field5) • p)∈s
      simpa only [show (4:Field5)= -1 by decide,neg_one_smul,neg_add_rev] using qs
  have diff (u v : Cell) (m : u-v∈crossSeed) : lift u-lift v∈plane s := by
    apply (in_plane ..).mpr
    refine ⟨?_,sub_self _⟩
    have eq : projection (lift u-lift v)=lin (u-v) := by
      rw [map_sub,map_sub]; refine Prod.ext rfl ?_
      change ((lin u).2+shift)-((lin v).2+shift)=(lin u).2-(lin v).2
      abel
    change projection (lift u-lift v)∈s
    rw [eq]; exact into m
  have edge {u v : Cell} (m : crossEdge u v=true) : within s (lift u) (lift v) := by
    have e := of_decide_eq_true m
    change (_ ∨ _) ∧ (_ ∨ _) ∧ u≠v ∧ _ at e
    have dom {w : Cell} (h : w.1=2 ∨ w.1=3) : lift w∈Raw.domain :=
      mem_filter.mpr ⟨mem_univ _,h,(mem_filter.mp hx).2.2⟩
    refine ⟨dom e.1,dom e.2.1,fun eq => e.2.2.1 (inj eq),Or.inr ?_⟩
    exact e.2.2.2.imp (diff v u) (diff u v)
  let n := neighbors (within s) Raw.domain x
  let t := near base
  have sub (y : Cell) (hy : y∈t) : lift y∈n := by
    have adj := edge (mem_filter.mp hy).2
    rw [root] at adj
    exact mem_filter.mpr ⟨adj.2.1,adj⟩
  have localBound (y : Cell) (_ : y∈t) :
      (t.filter (fun u => crossEdge y u=true)).card≤(neighbors (within s) n (lift y)).card := by
    apply card_le_card_of_injOn lift _ inj.injOn
    intro u hu
    exact mem_filter.mpr ⟨sub u (mem_filter.mp hu).1,edge (mem_filter.mp hu).2⟩
  calc
    _ ≤ ∑ y∈t,(t.filter fun u => crossEdge y u=true).card := three_edges x.1 (mem_filter.mp hx).2.1
    _ ≤ ∑ y∈t,(neighbors (within s) n (lift y)).card := sum_le_sum localBound
    _ = ∑ y∈t.image lift,(neighbors (within s) n y).card :=
      (sum_image (s:=t) (g:=lift) (f:=fun y => (neighbors (within s) n y).card) (fun _ _ _ _ eq => inj eq)).symm
    _ ≤ _ := sum_le_sum_of_subset (image_subset_iff.mpr sub)

end
end Audit.Mixed
