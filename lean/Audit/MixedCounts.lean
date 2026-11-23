import Audit.Mixed
import Audit.TriangleEight

namespace Audit.Mixed
open Finset Degrees Generic Band Link Lower Blocks
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem repeated {k : ℕ} {x z : Pt (Space k)} (eq : x+x+z=0) : z+z=x := by
  have scalar : ∀ a b : Field5, a+a+b=0 → b+b=a := by decide
  exact Prod.ext (scalar _ _ (congrArg Prod.fst eq))
    (funext fun i => scalar _ _ (congrArg (fun p : Pt (Space k) => p.2 i) eq))

theorem zero_gain {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) {x : Pt (Space k)}
    (xs : x∈s) (head : x.1=0) : 2≤(seedLayer (forward s) 0).card := by
  have nonzero : (0:Pt (Space k))∉s := fun h => sf 0 h 0 h 0 h (zero_add _)
  have odd : ∀ b : Field5, b= -b → b=0 := by decide
  have no : x≠ -x := fun eq => nonzero ((show x=0 from Prod.ext head
    (funext fun i => odd _ (congrArg (fun p : Pt (Space k) => p.2 i) eq))) ▸ xs)
  have sub : ({x,-x} : Finset (Pt (Space k)))⊆seedLayer (forward s) 0 := by
    intro y hy
    rcases (show y=x ∨ y= -x by simpa using hy) with rfl|rfl
    · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inl xs),Or.inl head⟩,head⟩
    · have h : (-x).1=0 := by change -x.1=0; rw [head,neg_zero]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inr (by simpa using xs)),Or.inl h⟩,h⟩
  simpa only [card_pair no] using card_le_card sub

theorem triangle_gain {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (bad : ¬NoZeroSum s) : s.card+3≤minimumDegree s := by
  unfold NoZeroSum at bad
  push_neg at bad
  obtain ⟨x,hx,y,hy,z,hz,eq⟩ := bad
  have absent (p : Pt (Space k)) (hp : p∈s) : p.1≠2 ∧ p.1≠3 := by
    have h := fun a : p.1=2 ∨ p.1=3 => disjoint_left.mp out hp (mem_full.mpr a)
    exact ⟨fun a => h (Or.inl a),fun a => h (Or.inr a)⟩
  have head : x.1+y.1+z.1=0 := congrArg Prod.fst eq
  have cases : ∀ i j l : Fin 5, (i≠2 ∧ i≠3) → (j≠2 ∧ j≠3) → (l≠2 ∧ l≠3) → i+j+l=0 →
      i=0 ∧ j=0 ∧ l=0 ∨ (i=0 ∨ j=0 ∨ l=0) ∧ (i=1 ∨ j=1 ∨ l=1) ∧ (i=4 ∨ j=4 ∨ l=4) := by decide
  obtain ⟨sc,p,q,h2,h3⟩ := profiles s out
  let Z := seedLayer (forward s) 0
  let U := seedLayer (forward s) 1
  have memZ {u : Pt (Space k)} (hu : u∈s) (h : u.1=0) : u∈Z :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_signed.mpr (Or.inl hu),Or.inl h⟩,h⟩
  rcases cases _ _ _ (absent _ hx) (absent _ hy) (absent _ hz) head with all|crossing
  · have diff {u v : Pt (Space k)} (hu : u∈s) (hv : v∈s) (e : u+u+v=0) : False :=
      sf _ hv _ hv _ hu (repeated e)
    have ne1 : x≠y := fun e => diff hx hz (by simpa only [e] using eq)
    have ne2 : x≠z := fun e => diff hx hy (by rw [e,add_right_comm]; simpa only [e] using eq)
    have ne3 : y≠z := fun e => diff hy hx (by rw [e,add_comm,←add_assoc]; simpa only [e] using eq)
    have lower : 3≤Z.card := by
      have h := card_le_card (show {x,y,z}⊆Z from insert_subset (memZ hx all.1)
        (insert_subset (memZ hy all.2.1) (singleton_subset_iff.mpr (memZ hz all.2.2))))
      simpa [ne1,ne2,ne3] using h
    dsimp only [Z] at lower; unfold minimumDegree; omega
  · have signs (i : Fin 5) (has : x.1=i ∨ y.1=i ∨ z.1=i) :
        ∃u∈s,u.1=i ∧ -u∉s := by
      have he : x+y= -z := eq_neg_of_add_eq_zero_left eq
      have nx : -x∉s := fun t => sf _ hy _ hz _ t ((eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm,add_left_comm,add_assoc] using eq))
      have ny : -y∉s := fun t => sf _ hx _ hz _ t ((eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm,add_left_comm,add_assoc] using eq))
      have nz : -z∉s := fun t => sf _ hx _ hy _ t he
      rcases has with a|a|a
      · exact ⟨x,hx,a,nx⟩
      · exact ⟨y,hy,a,ny⟩
      · exact ⟨z,hz,a,nz⟩
    obtain ⟨az,azs,az0,_⟩ := signs 0 crossing.1
    obtain ⟨u,us,uh,un⟩ := signs 1 crossing.2.1
    obtain ⟨v,vs,vh,vn⟩ := signs 4 crossing.2.2
    let pset := seedLayer s 1
    let qset := (seedLayer s 4).image Neg.neg
    have memU {w : Pt (Space k)} (m : w∈signed s) (h : w.1=1) : w∈U :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨m,Or.inr h⟩,h⟩
    have l : pset⊆U := fun _ h => memU (mem_signed.mpr (Or.inl (mem_filter.mp h).1)) (mem_filter.mp h).2
    have flipHead {t : Pt (Space k)} (h : t.1=4) : (-t).1=1 := by change -t.1=1; rw [h]; decide
    have j : qset⊆U := by
      intro w hw; obtain ⟨t,ht,rfl⟩ := mem_image.mp hw
      exact memU (mem_signed.mpr (Or.inr (by simpa using (mem_filter.mp ht).1))) (flipHead (mem_filter.mp ht).2)
    have lp : pset.card+1≤U.card := by
      have h := card_le_card (insert_subset (memU (w:=-v) (mem_signed.mpr (Or.inr (by simpa using vs))) (flipHead vh)) l)
      rwa [card_insert_of_not_mem (show -v∉pset from fun h => vn (mem_filter.mp h).1)] at h
    have rq : (seedLayer s 4).card+1≤U.card := by
      have missing : u∉qset := by
        intro h
        obtain ⟨t,ht,eq⟩ := mem_image.mp h
        exact un (show -u∈s by rw [←eq,neg_neg]; exact (mem_filter.mp ht).1)
      have h := card_le_card (insert_subset (memU (mem_signed.mpr (Or.inl us)) uh) j)
      rw [card_insert_of_not_mem missing] at h
      simpa only [qset,card_image_of_injective _ neg_injective] using h
    have Z2 := zero_gain sf azs az0
    dsimp only [pset,U] at lp rq; unfold minimumDegree; omega

theorem six_no_zero_sum {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (zero : (seedLayer s 0).Nonempty) (size : 6≤s.card) (clean : NoZeroSum s) :
    rankCount s≤3^(5^k) := by
  have ⟨min,close⟩ := mixed_profile s sf out zero
  have ord : minimumDegree s≤maximumDegree s := min_le_max
  have total : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 := max_add_min ..
  have tf := triangle_free sf clean
  suffices h : rankCount s ≤ 3^Fintype.card (Space k) by simpa [Space,Field5] using h
  by_cases eight : maximumDegree s≤8
  · apply within_quarter s sf
    exact TriangleEight.dense (within_sym _) (within_irr _) tf _
      (fun x hx => (within_cap sf x hx).trans eight) (two_degree_sum s sf 15 (by omega))
  · exact neither_high sf tf (by omega)

theorem seven {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (zero : (seedLayer s 0).Nonempty) (size : 7≤s.card) : rankCount s≤3^(5^k) := by
  by_cases clean : NoZeroSum s
  · exact six_no_zero_sum sf out zero (by omega) clean
  · have high := triangle_gain sf out clean
    have ratio := (mixed_profile s sf out zero).2
    simpa only [Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using MasterTable.two_degree s sf out (by omega) ratio

end
end Audit.Mixed
