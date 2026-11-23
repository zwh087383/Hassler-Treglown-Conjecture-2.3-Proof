import Audit.PlaneData
import Audit.Hyperplanes

namespace Audit.PlaneFibers
open Finset Link PlaneCert Blocks Hyperplanes
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option linter.unusedSectionVars false

variable {V : Type} [AddCommGroup V] [Module Field5 V] [Fintype V]
abbrev Y := Field5 × Field5

def fiber (φ : V →ₗ[Field5] Y) (a : Finset V) (p : Y) := a.filter fun x => φ x=p

theorem fiber_total (φ : V →ₗ[Field5] Y) (a : Finset V) :
    ∑ i : P, (fiber φ a (point i)).card = a.card := by
  have h := card_eq_sum_card_fiberwise (s:=a) (t:=(univ : Finset P)) (f:=fun x => index (φ x))
    (fun _ _ => mem_univ _)
  convert h.symm using 2 with i
  congr 1
  ext x
  simp only [fiber,mem_filter]
  have eq : index (φ x)=i ↔ φ x=point i := by
    constructor
    · intro e; simpa only [point_index] using congrArg point e
    · intro e; rw [e,index_point]
  tauto

theorem uniform_fiber (φ : V →ₗ[Field5] Y) (surj : Function.Surjective φ) (p : Y) :
    (fiber φ univ p).card=(fiber φ univ 0).card := by
  classical
  obtain ⟨z,hz⟩ := surj p
  apply card_bij (fun x _ => x-z)
  · intro x hx; apply mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [map_sub,(mem_filter.mp hx).2,hz,sub_self]
  · exact fun _ _ _ _ h => sub_left_inj.mp h
  · intro x hx
    refine ⟨x+z,mem_filter.mpr ⟨mem_univ _,?_⟩,add_sub_cancel_right ..⟩
    rw [map_add,(mem_filter.mp hx).2,hz,zero_add]

theorem total_card (φ : V →ₗ[Field5] Y) (surj : Function.Surjective φ) :
    Nat.card V=25*(fiber φ univ 0).card := by
  have h := fiber_total φ univ
  simp_rw [uniform_fiber φ surj] at h
  simpa [Nat.card_eq_fintype_card,P] using h.symm

theorem fiber_le (φ : V →ₗ[Field5] Y) (a : Finset V) (p : Y) :
    fiber φ a p ⊆ fiber φ univ p := by
  intro x hx; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩

private theorem complement_count (φ : V →ₗ[Field5] Y) (surj : Function.Surjective φ)
    (a : Finset V) (i j : Y) (fn : V → V) (inj : Function.Injective fn)
    (valid : ∀ x∈fiber φ a i, fn x∈fiber φ univ j ∧ fn x∉a) :
    (fiber φ a i).card+(fiber φ a j).card ≤ (fiber φ univ 0).card := by
  classical
  have h : (fiber φ a i).card ≤ (fiber φ univ j \ fiber φ a j).card := by
    apply card_le_card_of_injOn fn _ inj.injOn
    intro x hx
    obtain ⟨v,na⟩ := valid x hx
    exact mem_sdiff.mpr ⟨v,fun h => na (mem_filter.mp h).1⟩
  rw [card_sdiff (fiber_le ..)] at h
  have sub := card_le_card (fiber_le φ a j)
  rw [uniform_fiber φ surj] at h sub
  omega

theorem pair_limits (φ : V →ₗ[Field5] Y) (surj : Function.Surjective φ)
    (a : Finset V) (sf : Free a) (i j : Y) :
    (fiber φ a (i+j)).Nonempty ∨ (fiber φ a (i-j)).Nonempty ∨ (fiber φ a (j-i)).Nonempty →
    (fiber φ a i).card+(fiber φ a j).card ≤ (fiber φ univ 0).card := by
  have diff (p r : Y) (z : V) (hz : z∈fiber φ a (r-p)) :
      (fiber φ a p).card+(fiber φ a r).card ≤ (fiber φ univ 0).card := by
    obtain ⟨za,eq⟩ := mem_filter.mp hz
    apply complement_count φ surj a p r (·+z) (add_left_injective _) 
    intro x hx
    obtain ⟨xa,h⟩ := mem_filter.mp hx
    exact ⟨mem_filter.mpr ⟨mem_univ _,by rw [map_add,h,eq]; abel⟩,fun bad => sf _ xa _ za _ bad rfl⟩
  rintro (⟨z,hz⟩|⟨z,hz⟩|⟨z,hz⟩)
  · obtain ⟨za,eq⟩ := mem_filter.mp hz
    apply complement_count φ surj a i j (z-·) (fun _ _ e => sub_right_inj.mp e)
    intro x hx
    obtain ⟨xa,h⟩ := mem_filter.mp hx
    refine ⟨mem_filter.mpr ⟨mem_univ _,by rw [map_sub,eq,h]; abel⟩,?_⟩
    exact fun bad => sf _ bad _ xa _ za (sub_add_cancel _ _)
  · rw [add_comm]; exact diff j i z hz
  · exact diff i j z hz

def projKer (f : V →ₗ[Field5] Field5) (s : V) (hs : f s=1) : V →ₗ[Field5] (LinearMap.ker f) :=
  ((LinearMap.id : V →ₗ[Field5] V) - f.smulRight s).codRestrict (LinearMap.ker f) fun x => by
    change f (x-f x • s)=0; rw [map_sub,map_smul,hs,smul_eq_mul,mul_one,sub_self]

@[simp] theorem projKer_val (f : V →ₗ[Field5] Field5) (s : V) (hs : f s=1) (x : V) :
    (projKer f s hs x).val=x-f x • s := rfl

theorem project_inside (f : V →ₗ[Field5] Field5) (s : V) (hs : f s=1) (x : (LinearMap.ker f)) :
    projKer f s hs x.val=x := by
  apply Subtype.ext
  rw [projKer_val,(show f x.val=0 from x.property),zero_smul,sub_zero]

theorem onto_of_ne {f : V →ₗ[Field5] Field5} (nz : f≠0) : Function.Surjective f :=
  LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero nz)

def Normal (a : Finset V) : Prop :=
  ∃ f : V →ₗ[Field5] Field5, f≠0 ∧ ∀ x∈a, f x=1 ∨ f x=4

theorem lift_dense (a : Finset V) (sf : Free a) (dense : 3*Nat.card V<10*a.card)
    (f : V →ₗ[Field5] Field5) (nz : f≠0) (inK : 3*Nat.card (LinearMap.ker f)<10*(cut f a).card)
    (normal : Normal (cut f a)) : Normal a := by
  classical
  obtain ⟨z,hz⟩ := onto_of_ne nz 1
  obtain ⟨g,ng,gaxis⟩ := normal
  let L := g.comp (projKer f z hz)
  let φ : V →ₗ[Field5] Y := L.prod f
  have surj : Function.Surjective φ := by
    rintro ⟨u,v⟩
    obtain ⟨x,ex⟩ := onto_of_ne ng u
    have Pz : projKer f z hz z=0 := by apply Subtype.ext; simp [hz]
    refine ⟨x.val + v • z,Prod.ext ?_ ?_⟩
    · change g (projKer f z hz (x.val+v • z))=u
      rw [map_add,map_smul,project_inside,Pz,smul_zero,add_zero,ex]
    · change f (x.val+v • z)=v
      rw [map_add,(show f x.val=0 from x.2),map_smul,hz,smul_eq_mul,mul_one,zero_add]
  let w (i : P) := (fiber φ a (point i)).card
  let q := (fiber φ univ 0).card
  have planeCard : Nat.card V=25*q := total_card φ surj
  have kernelSize : Nat.card (LinearMap.ker f)=5*q := by
    have quot := Nat.card_congr (f.quotKerEquivOfSurjective (onto_of_ne nz)).toEquiv
    have size := (LinearMap.ker f).card_eq_card_quotient_mul_card
    rw [quot, Nat.card_eq_fintype_card (α:=Field5),ZMod.card] at size
    omega
  have onAxis (x : V) (xa : x∈a) (xf : f x=0) : L x=1 ∨ L x=4 := by
    let u : (LinearMap.ker f) := ⟨x,xf⟩
    have h := gaxis u (mem_filter.mpr ⟨mem_univ _,xa⟩)
    change g (projKer f z hz u.val)=1 ∨ g (projKer f z hz u.val)=4
    rwa [project_inside]
  have axisSet : a.filter (fun x => f x=0) = fiber φ a (1,0) ∪ fiber φ a (4,0) := by
    ext x
    simp only [fiber,mem_filter,mem_union,Prod.ext_iff]
    change (x∈a ∧ f x=0) ↔ ((x∈a ∧ L x=1 ∧ f x=0) ∨ (x∈a ∧ L x=4 ∧ f x=0))
    constructor
    · rintro ⟨ha,hf⟩; specialize onAxis x ha hf; tauto
    · tauto
  have cutBound : (cut f a).card≤w 1+w 4 := by
    rw [cut_card,axisSet]; exact card_union_le .. 
  have rowZero (i : P) (no : (point i).1≠1 ∧ (point i).1≠4) (row : (point i).2=0) : w i=0 := by
    apply card_eq_zero.mpr; apply eq_empty_iff_forall_not_mem.mpr
    intro x hx; obtain ⟨ha,eq⟩ := mem_filter.mp hx
    have b : f x=0 := (congrArg Prod.snd eq).trans row
    have e : L x=(point i).1 := congrArg Prod.fst eq
    rcases onAxis _ ha b with c|c
    · exact no.1 (e.symm.trans c)
    · exact no.2 (e.symm.trans c)
  have weights : Weights w q := by
    constructor
    · intro i; exact (card_le_card (fiber_le φ a _)).trans_eq (uniform_fiber φ surj _)
    · intro i j obs
      have get (p : Y) (hp : index p ∈ univ.filter (fun i => 0<w i)) :
          (fiber φ a p).Nonempty := by
        have h := (mem_filter.mp hp).2
        change 0 < (fiber φ a (point (index p))).card at h
        rwa [point_index,card_pos] at h
      apply pair_limits φ surj a sf (point i) (point j)
      rcases obs with h|h|h
      · exact Or.inl (get _ h)
      · exact Or.inr (Or.inl (get _ h))
      · exact Or.inr (Or.inr (get _ h))
    · change 15*q < 2*∑ i : P,(fiber φ a (point i)).card
      rw [fiber_total]; omega
    · omega
  obtain ⟨b,all⟩ := PlaneData.normal_plane w q weights (rowZero _ (by decide) (by decide))
    (rowZero _ (by decide) (by decide)) (rowZero _ (by decide) (by decide))
  let t : Field5 := b
  let F : V →ₗ[Field5] Field5 := L + t • f
  have val (x : V) : F x=L x+t*f x := rfl
  have nonzero : F≠0 := by
    obtain ⟨x,hx⟩ := surj (1,0)
    have e : L x=1 := congrArg Prod.fst hx
    have j : f x=0 := congrArg Prod.snd hx
    intro hz
    have fx : F x=0 := by rw [hz]; rfl
    simp [val,e,j] at fx
  refine ⟨F,nonzero,?_⟩
  intro x hx
  have positive : 0<w (index (φ x)) := card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,(point_index _).symm⟩⟩
  have h := all _ positive
  simpa only [line,point_index,decide_eq_true_eq] using h

end
end Audit.PlaneFibers
