import Audit.Generic
import Audit.RankOne
import Mathlib.Data.Nat.Bits

namespace Audit.RankOneBridge
open Finset Generic Band Link Lower
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false

private theorem encode (n : ℕ) (p : ℕ → Bool) :
    ∃ m < 2^n, ∀ i < n, m.testBit i = p i := by
  induction n generalizing p with
  | zero => exact ⟨0,by decide,by omega⟩
  | succ n ih =>
    obtain ⟨m,small,bits⟩ := ih (fun i => p (i+1))
    refine ⟨Nat.bit (p 0) m,?_,?_⟩
    · rw [Nat.bit_val,pow_succ]
      cases p 0 <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
    · intro i hi
      cases i with
      | zero =>
        cases h : p 0 <;> simp [Nat.bit_val,h,Nat.mul_comm,Nat.add_mod]
      | succ i => rw [Nat.testBit_bit_succ]; exact bits i (by omega)

private theorem encodes (s : Finset (Pt (Fin 5))) (sf : Free s) (out : Disjoint s (full (Fin 5))) :
    ∃ m < 16384, (RankOne.seed m).toFinset=plane s := by
  classical
  obtain ⟨m,range,bits⟩ := encode 14 (fun i => decide (RankOne.label i∈plane s))
  refine ⟨m,range,?_⟩
  have enumerate : ∀ x : Pt (Fin 5), x≠0 → x.1≠2 → x.1≠3 →
      ∃ i : Fin 14, RankOne.label i.val=(x.1,x.2,0) := by decide
  ext z
  simp only [List.mem_toFinset,RankOne.seed,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨i,⟨hi,h⟩,rfl⟩
    exact of_decide_eq_true ((bits i hi) ▸ h)
  · intro h
    obtain ⟨mem,tail⟩ := (in_plane ..).mp h
    let x : Pt (Fin 5) := (z.1,z.2.1)
    have member : x∈s := mem
    have nz : x≠0 := by
      intro eq
      have zmem : 0∈s := eq ▸ member
      exact sf _ zmem _ zmem _ zmem (zero_add _)
    have outer := fun a : x.1=2 ∨ x.1=3 => disjoint_left.mp out member (mem_full.mpr a)
    obtain ⟨i,eq⟩ := enumerate x nz (fun a => outer (Or.inl a)) (fun a => outer (Or.inr a))
    have eqz : RankOne.label i.val=z := eq.trans (Prod.ext rfl (Prod.ext rfl tail.symm))
    exact ⟨i.val,⟨i.isLt,(bits _ i.isLt).trans (decide_eq_true (eqz ▸ h))⟩,eqz⟩

theorem all (s : Finset (Pt (Fin 5))) (sf : Free s) (out : Disjoint s (full (Fin 5))) :
    rankCount s ≤ 3^5 := by
  obtain ⟨m,range,model⟩ := encodes s sf out
  let t := RankOne.seed m
  have mem (x : RankOne.Point) : x∈t ↔ x∈plane s := by rw [←model]; exact List.mem_toFinset.symm
  have legal : RankOne.sumFree t=true := by
    apply List.all_eq_true.mpr; intro x hx
    apply List.all_eq_true.mpr; intro y hy
    simp only [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro yes
    have bad := List.contains_iff_mem.mp yes
    have xh := ((in_plane ..).mp ((mem _).mp hx)).1
    have yh := ((in_plane ..).mp ((mem _).mp hy)).1
    have zh := ((in_plane ..).mp ((mem _).mp bad)).1
    exact sf _ xh _ yh _ zh rfl
  have imageDom : (univ : Finset (Fin 20)).image RankOne.vertex=Raw.domain := by decide
  have inj : Function.Injective RankOne.vertex := by decide
  have count : rankCount s = Sumfree.mis (fun x y => RankOne.edge t x y=true) univ := by
    unfold rankCount
    rw [←imageDom]
    symm
    apply Sumfree.mis_image _ _ _ _ inj.injOn
    intro x _ y _
    simp only [RankOne.edge,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,List.contains_iff_mem,
      mem,edge,inj.ne_iff]
    tauto
  rw [count]
  exact RankOne.every_seed m range legal

end
end Audit.RankOneBridge
