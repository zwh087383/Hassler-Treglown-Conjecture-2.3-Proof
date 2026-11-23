import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace Audit.Entropy
open Finset
noncomputable section

variable {O A B C I J X : Type*} [Fintype O] [Fintype A] [Fintype B] [Fintype C]
set_option linter.unusedSectionVars false

/-- Fiber counts for the uniform law on O. Entropies below are in nats
    multiplied by |O|, so no division is needed when adding entropies. -/
def freq (f : O → A) (a : A) : ℝ := by
  classical exact ((univ.filter fun x => f x = a).card : ℝ)

theorem freq_nonneg (f : O → A) (a : A) : 0 ≤ freq f a := by
  classical unfold freq; positivity

theorem freq_pos (f : O → A) (x : O) : 0 < freq f (f x) := by
  classical
  unfold freq
  exact_mod_cast card_pos.mpr (show (univ.filter fun y => f y=f x).Nonempty from
    ⟨x,by simp⟩)

theorem group_sum (f : O → A) (w : A → ℝ) :
    ∑ x, w (f x) = ∑ a, freq f a * w a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := f)
    (fun _ _ => mem_univ _) (fun x => w (f x))]
  apply sum_congr rfl
  intro a _
  calc
    _ = ∑ _x ∈ univ.filter (fun x => f x=a), w a :=
      sum_congr rfl (fun x hx => congrArg w (mem_filter.mp hx).2)
    _ = _ := by simp [freq]

abbrev joint (f : O → A) (g : O → B) (x : O) := (f x,g x)

theorem joint_sum (f : O → A) (g : O → B) (a : A) :
    ∑ b, freq (joint f g) (a,b) = freq f a := by
  classical
  let s := univ.filter fun x => f x=a
  have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := univ) (f := g) (fun _ _ => mem_univ _)
  calc
    _ = ∑ b, ((s.filter fun x => g x=b).card : ℝ) := by
      apply sum_congr rfl
      intro b _
      unfold freq
      congr 2
      ext x; simp [s,joint]
    _ = (s.card : ℝ) := by exact_mod_cast h.symm
    _ = freq f a := by rfl

def info (f : O → A) : ℝ := ∑ x, (Real.log (Fintype.card O) - Real.log (freq f (f x)))

theorem info_congr (f : O → A) (g : O → B)
    (eq : ∀ x y, f x = f y ↔ g x = g y) : info f = info g := by
  classical
  unfold info
  apply sum_congr rfl
  intro y _
  have e : (univ.filter fun x => f x=f y) = univ.filter (fun x => g x=g y) := by
    ext x; simp [eq]
  simp [freq,e]

theorem info_inj (f : O → A) (inj : Function.Injective f) :
    info f = Fintype.card O * Real.log (Fintype.card O) := by
  classical
  have one (y : O) : freq f (f y)=1 := by
    have e : (univ.filter fun x => f x=f y) = {y} := by ext x; simp [inj.eq_iff]
    simp [freq,e]
  simp [info,one]

/-- Cross entropy is minimized at the empirical conditional law. -/
theorem conditional_score (f : O → A) (g : O → B) (w : A → B → ℝ)
    (nonneg : ∀ a b, 0 ≤ w a b) (hit : ∀ x, 0 < w (f x) (g x))
    (mass : ∀ a, ∑ b, w a b ≤ 1) :
    ∑ x, Real.log (w (f x) (g x)) ≤ info f - info (joint f g) := by
  classical
  let ratio (p : A × B) := w p.1 p.2 * freq f p.1 / freq (joint f g) p
  have weight (p : A × B) : freq (joint f g) p * ratio p ≤ w p.1 p.2 * freq f p.1 := by
    by_cases h : freq (joint f g) p = 0
    · simp [h,mul_nonneg (nonneg ..) (freq_nonneg ..)]
    · exact le_of_eq (by dsimp [ratio]; field_simp)
  have total : (∑ x, ratio (joint f g x)) ≤ Fintype.card O := by
    rw [group_sum (joint f g) ratio]
    apply (sum_le_sum (fun p _ => weight p)).trans
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ a, freq f a := by
        apply sum_le_sum; intro a _
        change (∑ b, w a b * freq f a) ≤ freq f a
        rw [← sum_mul]
        simpa using mul_le_mul_of_nonneg_right (mass a) (freq_nonneg f a)
      _ = _ := by simpa using (group_sum f (fun _ => (1:ℝ))).symm
  have logs := sum_le_sum (s:=univ) (fun x _ => Real.log_le_sub_one_of_pos
    (show 0 < ratio (joint f g x) from div_pos (mul_pos (hit x) (freq_pos f x)) (freq_pos (joint f g) x)))
  have expand (x : O) : Real.log (ratio (joint f g x)) =
      Real.log (w (f x) (g x))+Real.log (freq f (f x))-Real.log (freq (joint f g) (joint f g x)) := by
    dsimp [ratio]
    rw [Real.log_div (mul_pos (hit x) (freq_pos f x)).ne' (freq_pos (joint f g) x).ne',
      Real.log_mul (hit x).ne' (freq_pos f x).ne']
  simp only [expand,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one] at logs
  simp only [info,sum_sub_distrib]
  linarith

theorem conditioning (f : O → A) (g : O → B) (h : A → C) :
    info (joint f g) - info f ≤ info (joint (h ∘ f) g) - info (h ∘ f) := by
  classical
  let w (a : A) (b : B) := freq (joint (h ∘ f) g) (h a,b) / freq (h ∘ f) (h a)
  have mass (a : A) : ∑ b, w a b ≤ 1 := by
    dsimp [w]; simp_rw [div_eq_mul_inv]; rw [← sum_mul,joint_sum,← div_eq_mul_inv]
    by_cases zero : freq (h ∘ f) (h a)=0 <;> simp [zero]
  have bound := conditional_score f g w (fun _ _ => div_nonneg (freq_nonneg ..) (freq_nonneg ..))
    (fun x => div_pos (freq_pos (joint (h ∘ f) g) x) (freq_pos (h ∘ f) x)) mass
  have expand (x : O) : Real.log (w (f x) (g x)) =
      Real.log (freq (joint (h ∘ f) g) (joint (h ∘ f) g x))-Real.log (freq (h ∘ f) ((h ∘ f) x)) :=
    Real.log_div (freq_pos (joint (h ∘ f) g) x).ne' (freq_pos (h ∘ f) x).ne'
  simp only [expand,info,sum_sub_distrib] at bound ⊢
  linarith

theorem weighted_bound (f : O → A) (w : A → ℝ) (Z : ℝ) (pos : 0 < Z)
    (nonneg : ∀ a, 0 ≤ w a) (hit : ∀ x, 0 < w (f x))
    (total : ∑ a, w a ≤ Z) (balance : ∑ x, Real.log (w (f x)) = 0) :
    info f ≤ Fintype.card O * Real.log Z := by
  classical
  let unit : O → Unit := fun _ => ()
  have prob := conditional_score unit f (fun _ a => w a/Z)
    (fun _ a => div_nonneg (nonneg a) pos.le) (fun x => div_pos (hit x) pos)
    (fun _ => by
      change (∑ a, w a/Z) ≤ 1
      simp_rw [div_eq_mul_inv]; rw [← sum_mul,← div_eq_mul_inv]; exact (div_le_one pos).2 total)
  have const : info unit = 0 := by simp [info,freq,unit]
  have matchInfo := info_congr (joint unit f) f (by intro x y; simp [joint,unit])
  have ex (x : O) : Real.log (w (f x)/Z)=Real.log (w (f x))-Real.log Z := Real.log_div (hit x).ne' pos.ne'
  simp only [ex,sum_sub_distrib,balance,sum_const,card_univ,nsmul_eq_mul,const,matchInfo] at prob
  linarith

variable [Fintype I] [DecidableEq I] [Fintype X] [Fintype J]
def obs (z : O → I → X) (s : Finset I) (w : O) (i : I) : Option X :=
  if i ∈ s then some (z w i) else none
theorem obs_eq (z : O → I → X) (s : Finset I) (x y : O) :
    obs z s x=obs z s y ↔ ∀ i ∈ s, z x i=z y i := by
  constructor
  · intro e i hi; simpa [obs,hi] using congrFun e i
  · intro h; funext i; by_cases hi : i∈s <;> simp [obs,hi,h]

theorem marginal_mono (z : O → I → X) {s t : Finset I} (sub : s ⊆ t) (i : I) :
    info (obs z (insert i t))-info (obs z t) ≤ info (obs z (insert i s))-info (obs z s) := by
  classical
  let clear (v : I → Option X) (k : I) := if k∈s then v k else none
  have comp : clear ∘ obs z t = obs z s := by
    funext x k; by_cases h : k ∈ s
    · simp [clear,obs,h,sub h,Function.comp_def]
    · simp [clear,h,obs,Function.comp_def]
  have je (v : Finset I) : info (joint (obs z v) (fun x => z x i)) = info (obs z (insert i v)) := by
    apply info_congr
    intro x y
    simp only [joint,Prod.mk.injEq,obs_eq,Finset.forall_mem_insert]
    tauto
  have b := conditioning (obs z t) (fun x => z x i) clear
  rwa [comp,je,je] at b

theorem shearer (z : O → I → X) (windows : J → Finset I) (d : ℕ)
    (regular : ∀ i, (univ.filter fun j => i ∈ windows j).card=d) (s : Finset I) :
    d * info (obs z s) ≤ ∑ j, info (obs z (s ∩ windows j)) := by
  classical
  have obsEmpty : obs z ∅ = fun _ _ => none := by funext x i; simp [obs]
  have baseline : info (obs z ∅) = 0 := by simp [obsEmpty,info,freq]
  induction s using Finset.induction_on with
  | empty => simp [baseline]
  | @insert i s hi ih =>
    let delta := info (obs z (insert i s))-info (obs z s)
    have step (j : J) : info (obs z (s ∩ windows j)) + (if i∈windows j then delta else 0)
        ≤ info (obs z (insert i s ∩ windows j)) := by
      by_cases hit : i∈windows j
      · rw [insert_inter_of_mem hit,if_pos hit]
        have key := marginal_mono z (s:=s∩windows j) (t:=s) inter_subset_left i
        dsimp [delta]; linarith
      · simp [hit,insert_inter_of_not_mem hit]
    have acc := sum_le_sum (s:=univ) (fun j _ => step j)
    rw [sum_add_distrib,← sum_filter, sum_const,regular i,nsmul_eq_mul] at acc
    dsimp [delta] at acc
    linarith

end
end Audit.Entropy
