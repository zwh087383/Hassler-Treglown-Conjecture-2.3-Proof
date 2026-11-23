import Audit.TriangleLocal
import Audit.MasterTable

namespace Audit.TriangleExceptional
open Finset Sumfree Fingerprint TriangleBase TriangleLocal
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop}
variable {s t g : Finset V} {x : V}

def cash (h : ℕ) (r : V → V → Prop) (s : Finset V) : ℤ :=
  (2*((h:ℤ)+1))*s.card-vol r s
def W (h : ℕ) (r : V → V → Prop) (s : Finset V) : ℝ :=
  (3:ℝ)^((cash h r s:ℝ)/(6*h))
def Prev (h : ℕ) (r : V → V → Prop) (s : Finset V) : Prop := ∀ t⊂s,(mis r t:ℝ) ≤ W h r t

theorem full_neighbors {D : ℕ} (ts : t⊆s) (capD : cap r s D) (xt : x∈t) (dx : deg r t x=D) :
    neighbors r t x=neighbors r s x := by
  have ds:=capD x (ts xt)
  exact eq_of_subset_of_card_le (filter_subset_filter _ ts) (by change deg r s x≤deg r t x; omega)

theorem vol_mono (ts : t⊆s) : vol r t≤vol r s := by
  calc
    _ ≤ ∑ x∈t, deg r s x := sum_le_sum (fun u _ => mono ts u)
    _ ≤ _ := sum_le_sum_of_subset ts

theorem cost1 (h : ℕ) (sym : Symmetric r) (xs : x∈s) :
    2*((h:ℤ)+1)-2*deg r s x ≤ cash h r s-cash h r (cut s x) := by
  have c:=single_loss sym xs
  have ct:=card_sdiff_add_card_eq_card (singleton_subset_iff.mpr xs)
  rw [card_singleton] at ct
  have n : ((cut s x).card:ℤ)+1=s.card := by exact_mod_cast ct
  unfold cost at c
  unfold cash
  nlinarith only [c,n,congrArg (fun z : ℤ => z*(h:ℤ)) n]

/-- Removing a closed neighborhood counts the edges between its neighbors once. -/
theorem costN (h : ℕ) (sym : Symmetric r) (irr : Irreflexive r) (xs : x∈s) :
    2*((h:ℤ)+1)*((deg r s x:ℤ)+1)-2*cross r (neighbors r s x) s+vol r (neighbors r s x)
      ≤ cash h r s-cash h r (s\ball r s x) := by
  have ct:=card_sdiff_add_card_eq_card (ball_sub (r:=r) s x)
  have vi:=volume_id sym (ball_sub (r:=r) s x)
  have cs : cross r (ball r s x) s=deg r s x+cross r (neighbors r s x) s := by
    unfold cross; rw [ball_eq sym xs,sum_insert (self_neigh irr s x)]
  have internal : vol r (ball r s x)=vol r (neighbors r s x)+2*deg r s x := by
    rw [ball_eq sym xs]
    have id:=GraphMeasure.volume_insert r sym irr (self_neigh irr s x)
    have nbs : neighbors r (neighbors r s x) x=neighbors r s x := by ext u; simp [neighbors]
    rw [nbs] at id
    exact id
  rw [cs,internal] at vi
  rw [ball_card sym irr xs] at ct
  have nEq : ((s\ball r s x).card:ℤ)+((deg r s x:ℤ)+1)=s.card := by exact_mod_cast ct
  have dv : (vol r s:ℤ)+vol r (neighbors r s x) ≤vol r (s\ball r s x)+2*cross r (neighbors r s x) s := by omega
  unfold cash
  nlinarith only [dv,nEq,congrArg (fun z : ℤ => z*(h:ℤ)) nEq]

theorem scale {h p : ℕ} {f : ℝ} (pos : 0<h) (loss : (p:ℤ)≤cash h r s-cash h r t)
    (num : (3:ℝ)^(-(p:ℝ)/(6*h))≤f) : W h r t≤f*W h r s := by
  have av : (p:ℝ)≤(cash h r s:ℝ)-cash h r t := by exact_mod_cast loss
  have hi : (0:ℝ)<h := by exact_mod_cast pos
  apply le_trans _ (mul_le_mul_of_nonneg_right num (by unfold W; positivity))
  unfold W
  rw [←Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [←add_div]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

macro "exception_numeric" : tactic =>
  `(tactic| first | exact Potential.neg_weight _ _ _ (by decide) (by norm_num) (by norm_num)
                  | norm_num)

theorem combine {h : ℕ} {x : V} {a b f : ℝ}
    (skip : (mis r (cut s x):ℝ)≤a*W h r s) (take : (mis r (s\ball r s x):ℝ)≤b*W h r s)
    (sum : a+b≤f) : (mis r s:ℝ)≤f*W h r s := by
  have u : (mis r s:ℝ)≤mis r (cut s x)+mis r (s\ball r s x) := by exact_mod_cast vertex_branch s x
  apply u.trans ((add_le_add skip take).trans _)
  rw [←add_mul]; exact mul_le_mul_of_nonneg_right sum (by unfold W; positivity)

theorem weighted_base (sym : Symmetric r) (irr : Irreflexive r) {D l h : ℕ}
    (dh : D+l=h+4) (h12 : 12≤h) (check : MasterTable.passes D l=true) (s : Finset V) (c : cap r s D) :
    (mis r s:ℝ)≤W h r s := by
  let n:=MasterTable.denominator D l
  have nEq : n=3*h := by dsimp [n,MasterTable.denominator]; omega
  have nr : (n:ℝ)=3*h := by exact_mod_cast nEq
  have nPos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hh : (36:ℝ)≤n := by exact_mod_cast (show 36≤n by omega)
  have b1 : (1:ℝ)/n≤1/36 := (div_le_iff₀ nPos).mpr (by linarith)
  have small (d : ℕ) (lo : 4≤d) (hi : d≤D) : Master.factor (1/(n:ℝ)) d ≤ 1 := by
    have k:=List.all_eq_true.mp check d (List.mem_range.mpr (by omega))
    exact MasterTable.checked (by omega) (by simpa [show ¬ d<4 by omega] using k)
  apply (Master.master r sym irr (b:=1/n) (by positivity) b1 small s c).trans_eq
  unfold W GraphMeasure.mu cash
  change (3:ℝ)^(_+_*(s.card-(vol r s:ℝ)/2))=(3:ℝ)^_
  congr 1
  push_cast
  rw [nr]
  have hpos : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
  field_simp; ring

theorem quarter {h : ℕ} (pos : 0<h) (av : (h+4)*s.card≤2*vol r s) :
    W h r s≤(3:ℝ)^((s.card:ℝ)/4) := by
  have hi : (0:ℝ)<h := by exact_mod_cast pos
  have avg : ((h:ℝ)+4)*s.card≤2*vol r s := by exact_mod_cast av
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (div_le_iff₀ (show 0<6*(h:ℝ) by positivity)).mpr
  unfold cash; push_cast; nlinarith only [avg]

/-- For a d-degree vertex, at most `k` neighbors of upper degree above 9 remain.
    Every other surviving neighbor costs at most nine. -/
theorem profile_sum (ts : t⊆s) {d k : ℕ} (gt : 9≤d) (c : cap r t d)
    (degree : deg r t x=d)
    (hi : ((neighbors r s x).filter fun y => 9<deg r s y).card≤k) :
    cross r (neighbors r t x) t ≤ 9*d+(d-9)*k := by
  let n:=neighbors r t x
  let high:=n.filter fun y => 9<deg r s y
  have highSize : high.card≤k :=
    (card_le_card (filter_subset_filter _ (filter_subset_filter _ ts))).trans hi
  have each (y : V) (hy : y∈n) : deg r t y≤9+(if 9<deg r s y then d-9 else 0) := by
    have a:=c y (mem_filter.mp hy).1
    have b:=mono (r:=r) ts y
    split <;> omega
  have h:=sum_le_sum each
  rw [sum_add_distrib,sum_const,sum_ite,sum_const_zero,add_zero,sum_const] at h
  simp only [nsmul_eq_mul] at h
  have mult:=Nat.mul_le_mul_left (d-9) highSize
  change (∑ y∈n,deg r t y)≤_
  change _≤n.card*9+high.card*(d-9) at h
  change n.card=d at degree
  rw [degree,Nat.mul_comm _ 9,Nat.mul_comm high.card] at h
  omega

end
end Audit.TriangleExceptional
