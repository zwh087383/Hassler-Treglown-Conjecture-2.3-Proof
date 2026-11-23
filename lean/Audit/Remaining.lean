import Audit.Reduction
import Audit.RankOneBridge
import Audit.Limit
import Audit.Structure
import Audit.Sparse
import Audit.Degrees
import Audit.Strip
import Audit.StripFamily
import Audit.NoZero
import Audit.SharpFive
import Audit.MixedSix
import Audit.SmallMixedPure

namespace Audit.Remaining
open Finset Generic Reduction Band Blocks Link Lower Assembly Filter
open scoped Classical Topology
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def symmetricSeed {G : Type} [Neg G] (s : Finset G) : Prop := ∀ x, x∈s ↔ -x∈s

/-- A bounded-dimensional finite statement. Every hypothesis narrows the class of graphs
    whose counts are required in the sharp global theorem. -/
def LocalCounts : Prop := ∀ (r : ℕ) (s : Finset (Pt (Space r))),
  2≤r → r≤s.card → Free s → Disjoint s (full (Space r)) →
  (Degrees.seedLayer s 0).Nonempty → ¬symmetricSeed s → ¬StripFamily.Recognized r s →
  s.card=4 → rankCount s ≤ 3^(5^r)

private theorem relabel_data {K L : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
    [AddCommGroup L] [Fintype L] [DecidableEq L] (e : K ≃+ L) {s : Finset (Pt K)}
    (sf : Free s) (outside : Disjoint s (full K)) :
    Free (s.image (relabel e)) ∧ Disjoint (s.image (relabel e)) (full L) := by
  refine ⟨(free_image _ _).mpr sf,disjoint_left.mpr ?_⟩
  intro y mem h
  obtain ⟨x,hx,rfl⟩ := mem_image.mp mem
  have head := (mem_full (u:=relabel e x)).mp h
  exact disjoint_left.mp outside hx ((mem_full (u:=x)).mpr head)

private theorem symmetry_back {k r : ℕ} {s : Finset (group k)}
    (e : spanTails s ≃+ Space r) (h : symmetricSeed ((roots s).image (relabel e))) :
    symmetricSeed s := by
  have mem (x : Pt (spanTails s)) : relabel e x∈(roots s).image (relabel e) ↔ x∈roots s :=
    by simp only [mem_image,(relabel e).injective.eq_iff,exists_eq_right]
  have closed (x : group k) (hx : x∈s) : -x∈s := by
    let v : Pt (spanTails s) := (x.1,⟨x.2,all_tails hx⟩)
    have hv : v∈roots s := mem_filter.mpr ⟨mem_univ _,hx⟩
    have hn := (h _).mp ((mem v).mpr hv)
    rw [←map_neg] at hn
    exact (mem_filter.mp ((mem _).mp hn)).2
  intro x
  exact ⟨closed x, fun hx => by simpa using closed (-x) hx⟩

private theorem zero_rank_small (s : Finset (group 0)) (sf : Free s)
    (out : Disjoint s (full (Space 0))) : s.card≤2 := by
  let allowed := (univ : Finset (group 0)).filter fun x => x≠0 ∧ x.1≠2 ∧ x.1≠3
  have c : allowed.card=2 := by decide
  rw [←c]
  apply card_le_card
  intro x hx
  have nz : x≠0 := by
    rintro rfl
    exact sf 0 hx 0 hx 0 hx (zero_add _)
  have notBand := fun h : x.1=2 ∨ x.1=3 => disjoint_left.mp out hx (mem_full.mpr h)
  exact mem_filter.mpr ⟨mem_univ _,nz,fun h => notBand (Or.inl h),fun h => notBand (Or.inr h)⟩

theorem standard_of_local (localCounts : LocalCounts) : StandardBand := by
  intro k s sf out
  have plus (b : (Sumfree.mis (clash s) (legal s (full (Space k))):ℝ) ≤
      (3:ℝ)^((Fintype.card (Space k):ℝ)/2)) :
      (Sumfree.mis (clash s) (legal s (full (Space k))):ℝ) ≤
      (3:ℝ)^((Fintype.card (Space k):ℝ)/2+errorConstant) := by
    apply b.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
    exact le_add_of_nonneg_right (by unfold errorConstant; positivity)
  by_cases sm : s.card<8192
  · by_cases tiny : s.card≤2
    · exact plus (SeedFamilies.at_most_two sf out tiny)
    by_cases sym : symmetricSeed s
    · exact plus (SeedFamilies.symmetric sym)
    apply small_seed s sm
    intro w nz
    rw [generic_count _ _ nz]
    let U := spanTails s
    let r := Module.finrank Field5 U
    let isometry := LinearEquiv.ofFinrankEq (R:=Field5) U (Space r) (by rw [Module.finrank_fin_fun])
    let e := isometry.toAddEquiv
    let t := (roots s).image (relabel e)
    have hd := roots_data sf out
    have data : Free t ∧ Disjoint t (full (Space r)) := relabel_data e hd.1 hd.2.1
    have ct : t.card=s.card := (card_image_of_injective _ (relabel e).injective).trans hd.2.2
    have rankle : r≤t.card := by
      rw [ct]
      exact (finrank_span_finset_le_card (R:=Field5) (s.image Prod.snd)).trans card_image_le
    have cardU : Nat.card U = 5^r := by
      rw [Module.natCard_eq_pow_finrank (K:=Field5),Nat.card_eq_fintype_card,ZMod.card]
    rw [rankCount_relabel e (roots s),cardU]
    change rankCount t ≤ 3^(5^r)
    have normal (d : ℕ) (a : Finset (Pt (Space d))) (af : Free a)
        (ao : Disjoint a (full (Space d))) (ct' : a.card=s.card) (dr : d≤a.card)
        (asym : ¬symmetricSeed a) : rankCount a ≤ 3^(5^d) := by
      cases d with
      | zero =>
        have h := zero_rank_small a af ao
        omega
      | succ d =>
        cases d with
        | zero =>
          let f : Space 1 ≃+ Fin 5 :=
            { toFun := fun x => x 0
              invFun := fun x _ => x
              left_inv := fun x => funext fun i => congrArg x (Subsingleton.elim 0 i)
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl }
          have da := relabel_data f af ao
          rw [rankCount_relabel f]
          exact RankOneBridge.all _ da.1 da.2
        | succ d =>
          by_cases known : StripFamily.Recognized _ a
          · exact StripFamily.recognized_bound known
          by_cases mixed : (Degrees.seedLayer a 0).Nonempty
          · have finish := localCounts _ a (by omega) dr af ao mixed asym known
            by_cases seven : 7≤a.card
            · exact Mixed.seven af ao mixed seven
            by_cases six : a.card=6
            · exact Mixed.six af ao mixed six
            by_cases five : a.card=5
            · exact Mixed.five af ao mixed five
            by_cases four : a.card=4
            · exact finish four
            · exact SmallMixed.three af ao mixed (by omega)
          · exact NoZero.all a ao mixed
    exact normal r t data.1 data.2 ct rankle (fun h => sym (symmetry_back e h))
  · exact plus (large_seed sf out (by omega))

theorem main_of_local_counts (localCounts : LocalCounts) :
    Tendsto Limit.normalized atTop (𝓝 (1/10:ℝ)) :=
  Limit.limit_of_band Sparse.sparseCovers Structure.largeSetStructure (standard_of_local localCounts)

end
end Audit.Remaining
