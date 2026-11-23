import Audit.Master
import Audit.Degrees

namespace Audit.MasterTable
open Finset Sumfree Fingerprint Potential GraphMeasure Degrees Generic Lower Band Link
open scoped Classical
set_option linter.unusedSectionVars false

def scale : ℕ := 65536
def denominator (D l : ℕ) := 3*(D+l-4)
def leftNumerator (D l d : ℕ) := D+l-3-d
def rightNumerator (D l d : ℕ) := (d+1)*(D+l-3)-d*d
def bisect (x n : ℕ) (lo hi : ℕ) : ℕ → ℕ
  | 0 => hi
  | fuel+1 =>
    let mid := (lo+hi)/2
    if scale^n ≤ 3^x*mid^n then bisect x n lo mid fuel else bisect x n mid hi fuel

def checkStep (D l d : ℕ) : Bool := Id.run do
  let n := denominator D l
  let p := leftNumerator D l d
  let q := rightNumerator D l d
  let m := bisect p n 0 scale 17
  return decide (0<m ∧ m<scale ∧ d≤D+l-3 ∧ d*d≤(d+1)*(D+l-3) ∧
    scale^n≤3^p*m^n ∧ scale^n≤3^q*(scale-m)^n)
def passes (D l : ℕ) : Bool := (List.range (D+1)).all fun d => decide (d<4) || checkStep D l d

set_option maxHeartbeats 0 in
theorem all_profiles : ∀ D l : Fin 36, 10≤l.val → l.val≤D.val → D.val≤2*l.val-3 →
    passes D.val l.val=true := by native_decide

private theorem cert {n p m : ℕ} (np : 0<n) (mp : 0<m) (test : scale^n ≤ 3^p*m^n) :
    (3:ℝ)^(-(p:ℝ)/n) ≤ (m:ℝ)/scale := by
  have sp : (0:ℝ)<scale := by norm_num [scale]
  apply neg_weight _ _ _ np (div_pos (Nat.cast_pos.mpr mp) sp)
  have h : (scale:ℝ)^n ≤ (3:ℝ)^p*(m:ℝ)^n := by exact_mod_cast test
  rw [div_pow,←mul_div_assoc]
  exact (one_le_div (pow_pos sp n)).mpr h

theorem checked {D l d : ℕ} (size : 16≤D+l) (res : checkStep D l d=true) :
    Master.factor (1/(denominator D l:ℝ)) d≤1 := by
  let n := denominator D l
  let p := leftNumerator D l d
  let q := rightNumerator D l d
  let m := bisect p n 0 scale 17
  have hs : 0<m ∧ m<scale ∧ d≤D+l-3 ∧ d*d≤(d+1)*(D+l-3) ∧
      scale^n≤3^p*m^n ∧ scale^n≤3^q*(scale-m)^n := of_decide_eq_true res
  have hn : 0<n := by dsimp [n,denominator]; omega
  have npos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have ne : (n:ℝ)=3*((D:ℝ)+l-4) := by
    dsimp [n,denominator]; rw [Nat.cast_mul,Nat.cast_sub (by omega : 4≤D+l)]; push_cast; ring
  have pe : (p:ℝ)=(D:ℝ)+l-3-d := by
    dsimp [p,leftNumerator]; rw [Nat.cast_sub hs.2.2.1,Nat.cast_sub (by omega : 3≤D+l)]; push_cast; ring
  have qe : (q:ℝ)=((d:ℝ)+1)*(D+l-3)-d*d := by
    dsimp [q,rightNumerator]; rw [Nat.cast_sub hs.2.2.2.1,Nat.cast_mul,Nat.cast_sub (by omega : 3≤D+l)]
    push_cast; ring
  have e1 : -(1/3+(1/(n:ℝ))*(1-d))= -(p:ℝ)/n := by field_simp [npos.ne']; rw [ne,pe]; ring
  have e2 : -(((d:ℝ)+1)/3+(1/(n:ℝ))*(d+1-(d:ℝ)^2))= -(q:ℝ)/n := by
    field_simp [npos.ne']; rw [ne,qe]; ring
  change (3:ℝ)^(-(1/3+(1/(n:ℝ))*(1-d)))+(3:ℝ)^(-(((d:ℝ)+1)/3+(1/(n:ℝ))*(d+1-(d:ℝ)^2)))≤1
  rw [e1,e2]
  apply (add_le_add (cert hn hs.1 hs.2.2.2.2.1) (cert hn (Nat.sub_pos_of_lt hs.2.1) hs.2.2.2.2.2)).trans
  rw [Nat.cast_sub hs.2.1.le,←add_div]
  norm_num [scale]

theorem for_graph {V : Type*} [Fintype V] [DecidableEq V] (r : V → V → Prop)
    (sym : Symmetric r) (irr : Irreflexive r) (s : Finset V) {D l : ℕ} (size : 16≤D+l)
    (test : passes D l=true) (cap : ∀ x∈s,(neighbors r s x).card≤D)
    (vol : (D+l)*s.card≤2*volume r s) : (mis r s:ℝ) ≤ (3:ℝ)^((s.card:ℝ)/4) := by
  let n := denominator D l
  have big : 36≤n := by dsimp [n,denominator]; omega
  have bigR : (36:ℝ)≤n := by exact_mod_cast big
  have pos : (0:ℝ)<n := by linarith
  have one : 1/(n:ℝ)≤1/36 := (div_le_iff₀ pos).mpr (by linarith)
  have scal (d : ℕ) (small : 4≤d) (hi : d≤D) : Master.factor (1/(n:ℝ)) d≤1 := by
    have h := List.all_eq_true.mp test d (List.mem_range.mpr (by omega))
    exact checked size (by simpa [show ¬d<4 by omega] using h)
  apply (Master.master r sym irr (b:=1/n) (by positivity) one scal s cap).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  · have v : ((D:ℝ)+l)*s.card ≤2*volume r s := by exact_mod_cast vol
    have ne : (n:ℝ)=3*((D:ℝ)+l-4) := by
      dsimp [n,denominator]; rw [Nat.cast_mul,Nat.cast_sub (by omega : 4≤D+l)]; push_cast; ring
    apply le_of_mul_le_mul_right _ (show (0:ℝ)<12*n by positivity)
    unfold mu
    rw [add_mul,show (1/(n:ℝ)*((s.card:ℝ)-volume r s/2))*(12*n)=12*((s.card:ℝ)-volume r s/2) by field_simp; ring,ne]
    nlinarith only [v]

theorem degree_case {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
    (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K))
    (size : 16≤maximumDegree s+minimumDegree s) (check : passes (maximumDegree s) (minimumDegree s)=true) :
    rankCount s≤3^(Fintype.card K) := by
  obtain ⟨vc,vv⟩ := domain_stats s sf
  have deg := maximum_stats s sf out
  have volume : (maximumDegree s+minimumDegree s)*(Raw.domain (K:=K)).card ≤
      2*Potential.volume (edge (plane s)) Raw.domain := by
    rw [vc]; change _ ≤ 2*(∑ x∈Raw.domain,(neighbors (edge (plane s)) Raw.domain x).card)
    rw [vv]
    have e : maximumDegree s+minimumDegree s=headDegree s 2+headDegree s 3 :=
      max_add_min .. 
    rw [e]; exact le_of_eq (by ring)
  have h := for_graph (edge (plane s)) (edge_sym _) (fun _ e => e.1 rfl) Raw.domain size check deg.2.1 volume
  rw [vc,Nat.cast_mul,Nat.cast_ofNat,show (4*(Fintype.card K:ℝ))/4=(Fintype.card K:ℝ) by ring,Real.rpow_natCast] at h
  exact_mod_cast h

theorem two_degree {K : Type} [AddCommGroup K] [Fintype K] [DecidableEq K]
    (s : Finset (Pt K)) (sf : Free s) (out : Disjoint s (full K))
    (lo : 10≤minimumDegree s) (ratio : maximumDegree s≤2*minimumDegree s-3) :
    rankCount s ≤ 3^(Fintype.card K) := by
  by_cases big : 36≤maximumDegree s
  · exact of_degree s sf out big
  have order : minimumDegree s≤maximumDegree s := min_le_max
  apply degree_case s sf out (by omega)
  exact all_profiles ⟨maximumDegree s,by omega⟩ ⟨minimumDegree s,by omega⟩ lo order ratio

theorem mixed_eight {k : ℕ} (s : Finset (Pt (Blocks.Space k))) (sf : Free s)
    (out : Disjoint s (full _)) (mixed : (seedLayer s 0).Nonempty) (eight : 8≤s.card) :
    rankCount s ≤ 3^(5^k) := by
  obtain ⟨small,ratio⟩ := mixed_profile s sf out mixed
  simpa only [Blocks.Space,Fintype.card_fun,Fintype.card_fin,ZMod.card] using
    two_degree s sf out (by omega) ratio

end Audit.MasterTable
