import Audit.SmallMixedThree
import Audit.SmallMixedZeroSemantics
import Audit.SmallMixedZeroCount

namespace Audit.SmallMixed
open Finset Lower Link Band Blocks Generic Degrees
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V] [Module Field5 V]

theorem zero_model : rankCount ZeroTriple.seed ≤ 3^25 := by
  have h := ZeroTriple.product_bound
  rw [ZeroTriple.count] at h
  exact h.trans (by decide)

theorem separate_sum {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) {x y z : Pt (Space k)}
    (hx : x∈s) (hy : y∈s) (hz : z∈s) (eq : x+y+z=0) :
    (x≠y ∧ x≠z ∧ y≠z) ∧ (-x∉s ∧ -y∉s ∧ -z∉s) := by
  have coeff : ∀ a b : Field5, a+a+b=0 → b+b=a := by decide
  have twice {a b : Pt (Space k)} (e : a+a+b=0) : b+b=a := Prod.ext
    (coeff _ _ (congrArg Prod.fst e)) (funext fun i => coeff _ _ (congrArg (fun p : Pt (Space k) => p.2 i) e))
  have diff {u v : Pt (Space k)} (hu : u∈s) (hv : v∈s) (e : u+u+v=0) : False := sf _ hv _ hv _ hu (twice e)
  refine ⟨⟨fun e => diff hx hz (by simpa only [e] using eq),fun e => diff hx hy (by rw [e,add_right_comm]; simpa only [e] using eq),
    fun e => diff hy hx (by rw [e,add_comm,←add_assoc]; simpa only [e] using eq)⟩,?_,?_,?_⟩
  · exact fun t => sf _ hy _ hz _ t (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm,add_left_comm,add_assoc] using eq))
  · exact fun t => sf _ hx _ hz _ t (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm,add_left_comm,add_assoc] using eq))
  · exact fun t => sf _ hx _ hy _ t (eq_neg_of_add_eq_zero_left eq)

theorem pure_profile {s : Finset (Pt V)} (out : Disjoint s (full V)) (zero : ∀p∈s,p.1=0) :
    headDegree s 2=(signed s).card+s.card ∧ headDegree s 3=(signed s).card+s.card := by
  have signedHead {p : Pt V} (hp : p∈signed s) : p.1=0 := by
    rcases mem_signed.mp hp with h|h
    · exact zero p h
    · have a : -p.1=0 := zero (-p) h
      exact neg_eq_zero.mp a
  have front : forward s=signed s := filter_eq_self.mpr (fun _ h => Or.inl (signedHead h))
  have f0 : seedLayer (forward s) 0=signed s := by rw [front]; exact filter_eq_self.mpr (fun _ h => signedHead h)
  have f1 : seedLayer (forward s) 1=∅ := by
    rw [front]; exact filter_eq_empty_iff.mpr (fun x h => by change x.1≠1; rw [signedHead h]; decide)
  have z : seedLayer s 0=s := filter_eq_self.mpr zero
  have other (i : Fin 5) (ne : i≠0) : seedLayer s i=∅ := filter_eq_empty_iff.mpr
    (fun x h => by change x.1≠i; rw [zero x h]; exact Ne.symm ne)
  obtain ⟨_,_,_,a,b⟩ := profiles s out
  simpa only [f0,f1,z,other 1 (by decide),other 4 (by decide),card_empty,add_zero] using And.intro a b

theorem reflect_size {s : Finset (Pt V)} (unpaired : ¬∃x∈s,-x∈s) : (signed s).card=2*s.card := by
  have dis : Disjoint s (s.image Neg.neg) := by
    apply disjoint_left.mpr
    intro x hx h
    obtain ⟨y,hy,rfl⟩ := mem_image.mp h
    exact unpaired ⟨y,hy,hx⟩
  rw [signed,card_union_of_disjoint dis,card_image_of_injective _ neg_injective,two_mul]

theorem pure_three {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (size : s.card=3) (zero : ∀p∈s,p.1=0) : rankCount s≤3^Fintype.card (Space k) := by
  by_cases pair : ∃x∈s,-x∈s
  · obtain ⟨x,hx,hm⟩ := pair
    have odd : ∀a : Field5,a= -a → a=0 := by decide
    have ne : x≠-x := fun h => by
      have orig : x=0 := Prod.ext (zero x hx) (funext fun i => odd _ (congrArg (fun p : Pt (Space k) => p.2 i) h))
      subst x; exact sf _ hx _ hx _ hx (zero_add _)
    obtain ⟨z,eq⟩ := triple_from_members size hx hm ne
    have sform : s=insert z {x,-x} := by rw [eq]; ext p; simp only [mem_insert,mem_singleton]; tauto
    rw [sform] at sf out ⊢
    apply Defects.one_defect {x,-x} _ z sf out
    intro p
    simp only [mem_insert,mem_singleton,neg_eq_iff_eq_neg,neg_neg]
    tauto
  · obtain ⟨a,b⟩ := pure_profile out zero
    rw [reflect_size pair,size] at a b
    by_cases clean : Mixed.NoZeroSum s
    · apply Mixed.neither_high sf (Mixed.triangle_free sf clean)
      unfold maximumDegree; omega
    unfold Mixed.NoZeroSum at clean
    push_neg at clean
    obtain ⟨x,hx,y,hy,z,hz,eq⟩ := clean
    obtain ⟨⟨ne1,ne2,ne3⟩,_⟩ := separate_sum sf hx hy hz eq
    have subset : {x,y,z}⊆s := insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz))
    have full := eq_of_subset_of_card_le subset (by simp [size,ne1,ne2,ne3])
    let u := x.2
    let v := y.2
    have tails : x.2+y.2+z.2=0 := congrArg Prod.snd eq
    have tz : -(u+v)=z.2 := neg_eq_of_add_eq_zero_left (by simpa [u,v,add_comm] using tails)
    have model : StripFamily.embedded (pairMap u v) ZeroTriple.seed=s := by
      rw [←full]
      simp only [StripFamily.embedded,ZeroTriple.seed,image_insert,image_singleton]
      have xx : ((0:Fin 5),pairMap u v (1,0))=x := Prod.ext (zero x hx).symm (by rw [pairMap_apply]; simp [u])
      have yy : ((0:Fin 5),pairMap u v (0,1))=y := Prod.ext (zero y hy).symm (by rw [pairMap_apply]; simp [v])
      have zz : ((0:Fin 5),pairMap u v (4,4))=z := by
        apply Prod.ext (zero z hz).symm
        change pairMap u v (4,4)=z.2
        rw [pairMap_apply,show (4:Field5) = -1 from by decide,neg_one_smul,neg_one_smul,←neg_add,tz]
      rw [xx,yy,zz]
    have un : u≠0 := fun h => by
      have e : x=0 := Prod.ext (zero x hx) h
      subst x; exact sf _ hx _ hx _ hx (zero_add _)
    rw [←model] at sf out ⊢
    exact pair_bound _ zero_model _ _ un sf out

theorem three {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (zero : (seedLayer s 0).Nonempty) (size : s.card=3) : rankCount s≤3^(5^k) := by
  obtain ⟨x,hx⟩ := zero
  by_cases all : ∀p∈s,p.1=0
  · simpa [Space,Field5] using pure_three sf out size all
  · push_neg at all
    obtain ⟨y,hy,hn⟩ := all
    simpa [Space,Field5] using mixed_three sf out size (mem_filter.mp hx).1 hy (mem_filter.mp hx).2 hn

end
end Audit.SmallMixed

