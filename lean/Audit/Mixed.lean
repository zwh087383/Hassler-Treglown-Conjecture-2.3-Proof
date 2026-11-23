import Audit.MasterTable

namespace Audit.Mixed
open Finset Sumfree Fingerprint Degrees Generic Band Link Lower Blocks
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]

def projection : Raw.Point K →+ Pt K where
  toFun x := (x.1,x.2.1)
  map_zero' := rfl
  map_add' _ _ := rfl

def oriented (x : Raw.Point K) : Pt K := if x.2.2=1 then projection x else -projection x

theorem oriented_edge {s : Finset (Pt K)} {x y : Raw.Point K} (adj : within s x y) :
    oriented y-oriented x∈signed s := by
  have xt := (mem_filter.mp adj.1).2.2
  have yt := (mem_filter.mp adj.2.1).2.2
  have proj {v : Raw.Point K} (h : v∈plane s) : projection v∈s := ((in_plane ..).mp h).1
  have same (e : x.2.2=y.2.2) :
      projection y-projection x∈signed s := by
    rcases adj.2.2.2 with plus|yx|xy
    · have z := ((in_plane ..).mp plus).2
      change x.2.2+y.2.2=0 at z
      rw [←e] at z
      rcases xt with h|h <;> rw [h] at z <;> contradiction
    · exact mem_signed.mpr (Or.inl (by simpa only [map_sub] using proj yx))
    · exact mem_signed.mpr (Or.inr (by simpa only [neg_sub,map_sub] using proj xy))
  have opposite (e : x.2.2≠y.2.2) : projection y+projection x∈s := by
    rcases adj.2.2.2 with plus|yx|xy
    · simpa only [map_add,add_comm] using proj plus
    · exact (e (sub_eq_zero.mp ((in_plane ..).mp yx).2).symm).elim
    · exact (e (sub_eq_zero.mp ((in_plane ..).mp xy).2)).elim
  rcases xt with a|a <;> rcases yt with b|b
  · simpa [oriented,a,b] using same (a.trans b.symm)
  · have h := opposite (by rw [a,b]; decide)
    apply mem_signed.mpr (Or.inr ?_)
    simpa [oriented,a,b,sub_eq_add_neg,add_comm] using h
  · have h := opposite (by rw [a,b]; decide)
    apply mem_signed.mpr (Or.inl ?_)
    simpa [oriented,a,b] using h
  · have h := same (a.trans b.symm)
    have neg : -(projection y-projection x)∈signed s := (mem_signed.mpr (by
      rcases mem_signed.mp h with z|z
      · exact Or.inr (by simpa using z)
      · exact Or.inl z))
    simpa [oriented,a,b,sub_eq_add_neg,add_comm] using neg

def NoZeroSum (s : Finset (Pt K)) := ∀ u∈s,∀ v∈s,∀ w∈s,u+v+w≠0

theorem signed_free {s : Finset (Pt K)} (free : Free s) (zero : NoZeroSum s) : Free (signed s) := by
  intro x hx y hy z hz eq
  rcases mem_signed.mp hx with ax|ax <;> rcases mem_signed.mp hy with ay|ay <;> rcases mem_signed.mp hz with az|az
  · exact free _ ax _ ay _ az eq
  · apply zero _ ax _ ay _ az; rw [←eq]; abel
  · apply free _ az _ ay _ ax; rw [←eq]; abel
  · apply free _ ax _ az _ ay; rw [←eq]; abel
  · apply free _ az _ ax _ ay; rw [←eq]; abel
  · apply free _ ay _ az _ ax; rw [←eq]; abel
  · apply zero _ ax _ ay _ az; rw [←eq]; abel
  · apply free _ ax _ ay _ az; rw [←eq]; abel

theorem triangle_free {s : Finset (Pt K)} (sf : Free s) (no : NoZeroSum s) : TriangleFree (within s) := by
  intro x y z xy yz xz
  exact signed_free sf no _ (oriented_edge xy) _ (oriented_edge yz) _ (oriented_edge xz) (by abel)

theorem neither_high {s : Finset (Pt K)} (sf : Free s) (tf : TriangleFree (within s))
    (regime : maximumDegree s≤10 ∧ 17≤headDegree s 2+headDegree s 3 ∨
      maximumDegree s≤12 ∧ 18≤headDegree s 2+headDegree s 3 ∨ 12≤maximumDegree s ∧
      maximumDegree s≤2*minimumDegree s) : rankCount s≤3^(Fintype.card K) := by
  apply within_quarter s sf
  rcases regime with ⟨cap,avg⟩|⟨cap,avg⟩|⟨large,diff⟩
  · exact TriangleTen.dense (within_sym _) (within_irr _) tf _ (fun x hx => (within_cap sf x hx).trans cap) (two_degree_sum s sf 17 avg)
  · apply TriangleTwelve.dense (within_sym _) (within_irr _) tf (D:=12) (by decide) _ (fun x hx => (within_cap sf x hx).trans cap)
    have v := two_degree_sum s sf 18 avg
    omega
  · apply TriangleTwelve.dense (within_sym _) (within_irr _) tf large _ (within_cap sf)
    have eq := within_volume s sf
    have ct := (domain_stats s sf).1
    change _≤4*(∑ x∈Raw.domain,(neighbors (within s) Raw.domain x).card)
    rw [ct,eq]
    have e : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 := max_add_min ..
    nlinarith only [Nat.mul_le_mul_right (Fintype.card K) diff,congrArg (fun n : ℕ => n*Fintype.card K) e]

end
end Audit.Mixed
