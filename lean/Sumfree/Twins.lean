import Sumfree.Graph

namespace Sumfree
noncomputable section
open Finset
set_option linter.unusedSectionVars false
variable {V : Type*} [DecidableEq V]

def double (s : Finset V) : Finset (Bool × V) := univ ×ˢ s

@[simp] theorem mem_double {s : Finset V} {p : Bool × V} : p ∈ double s ↔ p.2 ∈ s := by
  simp [double]

theorem double_mis (R : V → V → Prop) (s : Finset V) :
    mis (fun (x y : Bool × V) => R x.2 y.2) (double s) = mis R s := by
  classical
  let D := fun (x y : Bool × V) => R x.2 y.2
  have bridge (J : Finset V) : IsMIS D (double s) (double J) ↔ IsMIS R s J := by
    constructor
    · intro h
      apply isMIS_of_iff
      intro x
      have eq := member_iff h (false,x)
      simpa only [mem_double, D, Prod.forall, Bool.forall_bool, and_self] using eq
    · intro h
      apply isMIS_of_iff
      rintro ⟨c,x⟩
      simpa only [mem_double,D,Prod.forall,Bool.forall_bool,and_self] using member_iff h x
  have recover (I : Finset (Bool × V)) (h : IsMIS D (double s) I) :
      I = double (I.image Prod.snd) := by
    ext ⟨c,x⟩
    rw [mem_double, Finset.mem_image]
    constructor
    · exact fun hi => ⟨(c,x),hi,rfl⟩
    · rintro ⟨⟨d,y⟩, hd, rfl⟩
      apply (member_iff h _).2
      simpa only [D, mem_double] using (member_iff h _).1 hd
  have proj (J : Finset V) : (double J).image Prod.snd = J := by
    ext x
    simp [double, Finset.mem_image, Prod.exists]
  apply Finset.card_bij (fun I _ => I.image Prod.snd)
  · intro I hi
    have h := mem_family.mp hi
    exact mem_family.mpr ((bridge _).1 (recover I h ▸ h))
  · intro I hi J hj eq
    rw [recover I (mem_family.mp hi), recover J (mem_family.mp hj), eq]
  · intro J hj
    exact ⟨double J, mem_family.mpr ((bridge _).2 (mem_family.mp hj)), proj J⟩

end
end Sumfree
