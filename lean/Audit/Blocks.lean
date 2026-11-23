import Audit.Band
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Field.ZMod

namespace Audit.Blocks
open Finset Link Lower Band Sumfree
open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false

variable {G W : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup W] [DecidableEq W]

def cell (π : G →+ W) (b : Finset G) (t : Finset W) :=
  b.filter fun x => π x∈t

theorem orbit_edge {π : G →+ W} {s : Finset G} (zero : ∀ x∈s,π x=0)
    {x y : G} (e : edge s x y) : π x=π y ∨ -π x=π y := by
  rcases e.2 with h|h|h
  · have eq := zero _ h
    rw [map_add] at eq
    exact Or.inr ((neg_eq_iff_add_eq_zero).mpr eq)
  · have eq := zero _ h
    rw [map_sub,sub_eq_zero] at eq; exact Or.inl eq.symm
  · have eq := zero _ h
    rw [map_sub,sub_eq_zero] at eq; exact Or.inl eq

theorem cells_multiply {π : G →+ W} {s b : Finset G} (zero : ∀ x∈s,π x=0)
    {a t : Finset W} (apart : Disjoint a t) (stable : ∀ x∈a,-x∈a) :
    mis (edge s) (cell π b (a∪t)) =
      mis (edge s) (cell π b a) * mis (edge s) (cell π b t) := by
  have eq : cell π b (a∪t) = cell π b a ∪ cell π b t := by ext x; simp [cell,and_or_left]
  rw [eq]
  apply disjoint_count (edge_sym s)
  · exact disjoint_left.mpr (fun _ x y =>
      disjoint_left.mp apart (mem_filter.mp x).2 (mem_filter.mp y).2)
  · intro x hx y hy e
    have xIn := (mem_filter.mp hx).2
    have yIn := (mem_filter.mp hy).2
    rcases orbit_edge zero e with eq|eq
    · exact disjoint_left.mp apart (eq ▸ xIn) yIn
    · exact disjoint_left.mp apart (eq ▸ stable _ xIn) yIn

/-- Induction over all unordered pairs of opposite nonzero quotient elements. -/
theorem pair_product {π : G →+ W} {s b : Finset G} (zero : ∀ x∈s,π x=0)
    (odd : ∀ w : W, w = -w → w=0) (u : ℕ)
    (block : ∀ w : W, w≠0 → mis (edge s) (cell π b {w,-w}) ≤ u)
    (t : Finset W) (nozero : 0∉t) (stable : ∀ x∈t, -x∈t) :
    mis (edge s) (cell π b t) ≤ u^(t.card/2) := by
  classical
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    by_cases emp : t=∅
    · subst t
      have fam : family (edge s) ∅ = {∅} := by
        ext i; by_cases h : i=∅
        · subst i; simp [IsMIS,Independent]
        · simp [IsMIS,h]
      simp [cell,mis,fam]
    obtain ⟨w,hw⟩ := nonempty_iff_ne_empty.mpr emp
    have w0 : w≠0 := fun e => nozero (e ▸ hw)
    have opp := stable _ hw
    have ne : w ≠ -w := fun eq => w0 (odd _ eq)
    let tail := (t.erase w).erase (-w)
    have sub : tail ⊆ t := (erase_subset _ _).trans (erase_subset _ _)
    have ex : w∉tail := by simp [tail]
    have enx : -w∉tail := by simp [tail]
    have lower : tail ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => ex (e.symm ▸ hw)⟩
    have stableTail (y : W) (hy : y∈tail) : -y∈tail := by
      refine mem_erase.mpr ⟨fun e => ex ((neg_inj.mp e) ▸ hy),mem_erase.mpr ⟨?_,stable _ (sub hy)⟩⟩
      intro e
      have eq : y = -w := by simpa using congrArg Neg.neg e
      exact enx (eq ▸ hy)
    have split : {w,-w} ∪ tail = t := by
      ext y
      by_cases a : y=w
      · subst y; simp [hw]
      · by_cases b : y= -w
        · subst y; simp [opp]
        · simp [tail,a,b]
    have apart : Disjoint {w,-w} tail := by
      apply disjoint_left.mpr; intro y h hy
      rcases (show y=w ∨ y= -w by simpa using h) with rfl|rfl
      · exact ex hy
      · exact enx hy
    have stablePair : ∀ y∈({w,-w}:Finset W),-y∈({w,-w}:Finset W) := by
      intro y h; rcases (show y=w ∨ y= -w by simpa using h) with rfl|rfl <;> simp
    have ct : tail.card+2=t.card := by
      have p := card_erase_add_one hw
      have q := card_erase_add_one (mem_erase.mpr ⟨ne.symm,opp⟩ : -w∈t.erase w)
      dsimp [tail]; omega
    have step := Nat.mul_le_mul (block w w0) (ih tail lower (fun h => nozero (sub h)) stableTail)
    calc
      _ = mis (edge s) (cell π b {w,-w}) * mis (edge s) (cell π b tail) := by
        conv_lhs => rw [←split]
        exact cells_multiply zero apart stablePair
      _ ≤ _ := step
      _ = _ := by rw [show t.card/2=tail.card/2+1 by omega, pow_succ,mul_comm]

abbrev Field5 := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev Space (k : ℕ) := Fin k → Field5

def spanTails {k : ℕ} (s : Finset (Pt (Space k))) : Submodule Field5 (Space k) :=
  Submodule.span Field5 (↑(s.image Prod.snd) : Set (Space k))

def residual {k : ℕ} (K : Submodule Field5 (Space k)) : Pt (Space k) →+ (Space k ⧸ K) :=
  K.mkQ.toAddMonoidHom.comp (AddMonoidHom.snd _ _)

theorem residual_zero {k : ℕ} {s : Finset (Pt (Space k))} :
    ∀ x∈s, residual (spanTails s) x=0 := by
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span (mem_image_of_mem Prod.snd hx)

theorem span_card {k : ℕ} (s : Finset (Pt (Space k))) :
    Nat.card (spanTails s) ≤ 5^s.card := by
  have rankBound : Module.finrank Field5 (spanTails s) ≤ s.card :=
    (finrank_span_finset_le_card (R:=Field5) (s.image Prod.snd)).trans card_image_le
  rw [Module.natCard_eq_pow_finrank (K:=Field5),Nat.card_eq_fintype_card,ZMod.card]
  exact Nat.pow_le_pow_right (by decide) rankBound

theorem core_card {k : ℕ} (K : Submodule Field5 (Space k)) :
    (cell (residual K) (full (Space k)) {0}).card = 2*Nat.card K := by
  let t := (univ : Finset (Space k)).filter fun x => x∈K
  have eq : cell (residual K) (full (Space k)) {0} = band t := by
    ext ⟨a,x⟩
    simp only [cell,mem_filter,mem_full,mem_singleton,mem_band,t,mem_univ,true_and]
    change (_ ∧ Submodule.Quotient.mk x = (0 : Space k ⧸ K)) ↔ _
    simp [Submodule.Quotient.mk_eq_zero]
  have card : Nat.card K=t.card := by
    classical
    let f : K ≃ ↥t :=
      ⟨fun x => ⟨x.val,mem_filter.mpr ⟨mem_univ _,x.property⟩⟩,
       fun y => ⟨y.val,(mem_filter.mp y.property).2⟩,fun _ => rfl,fun _ => rfl⟩
    simpa using Nat.card_congr f
  rw [eq,card]; simp [band]

def genericCell {k : ℕ} (s : Finset (Pt (Space k))) (w : Space k ⧸ spanTails s) :=
  cell (residual (spanTails s)) (full (Space k)) {w,-w}

/-- The only local input in the bounded-seed proof concerns one nonzero coset pair. -/
def BlockBound : Prop := ∀ (k : ℕ) (s : Finset (Pt (Space k))),
  Free s → Disjoint s (full (Space k)) → s.card<8192 →
    ∀ w : Space k ⧸ spanTails s, w≠0 →
      mis (edge s) (genericCell s w) ≤ 3^(Nat.card (spanTails s))

def errorConstant : ℝ := (5:ℝ)^8191/6

theorem small_seed {k : ℕ} (s : Finset (Pt (Space k))) (small : s.card<8192)
    (blocks : ∀ w : Space k ⧸ spanTails s, w≠0 →
      mis (edge s) (genericCell s w) ≤ 3^(Nat.card (spanTails s))) :
    (mis (clash s) (legal s (full (Space k))):ℝ) ≤
      (3:ℝ)^((Fintype.card (Space k):ℝ)/2+errorConstant) := by
  classical
  let K := spanTails s
  let W := Space k ⧸ K
  let q := Nat.card K
  let b := full (Space k)
  let π := residual K
  have zero : ∀ x∈s,π x=0 := residual_zero
  have odd (w : W) (e : w= -w) : w=0 := by
    have h : (2:Field5) • w = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp e
    exact (smul_eq_zero.mp h).resolve_left (by decide)
  let t := (univ : Finset W).erase 0
  have nozero : (0:W)∉t := by simp [t]
  have stable (w : W) (h : w∈t) : -w∈t :=
    mem_erase.mpr ⟨neg_ne_zero.mpr (mem_erase.mp h).1,mem_univ _⟩
  have eq : ({0}:Finset W)∪t=univ := by
    ext w; by_cases e : w=0 <;> simp [t,e]
  have split : mis (edge s) b = mis (edge s) (cell π b {0}) * mis (edge s) (cell π b t) := by
    have h := cells_multiply (b:=b) zero (a:={0}) (t:=t) (by simpa using nozero) (by simp)
    rwa [eq,show cell π b univ=b by simp [cell]] at h
  have core := moon_moser (edge_sym s) (fun _ h => h.1 rfl) (cell π b {0})
  rw [core_card] at core
  have gen := pair_product zero odd (3^q) blocks t nozero stable
  have tail : (mis (edge s) (cell π b t):ℝ) ≤ (3:ℝ)^((q:ℝ)*(t.card/2:ℕ)) := by
    have h : (mis (edge s) (cell π b t):ℝ) ≤ ((3:ℝ)^q)^(t.card/2) := by exact_mod_cast gen
    rw [←pow_mul] at h
    rw [←Nat.cast_mul,Real.rpow_natCast]; exact h
  have cardN : Fintype.card (Space k)=q*Fintype.card W := by
    simpa only [q,W,Nat.card_eq_fintype_card] using K.card_eq_card_quotient_mul_card
  have tcard : t.card+1=Fintype.card W := by simpa only [card_univ] using card_erase_add_one (mem_univ (0:W))
  have half : 2*(t.card/2) + 1 ≤ Fintype.card W := by omega
  have realHalf : 2*(((t.card/2:ℕ):ℝ))+1 ≤ (Fintype.card W:ℝ) := by exact_mod_cast half
  have sizeBound : s.card≤8191 := Nat.le_of_lt_succ small
  have qc : q ≤ 5^8191 := (span_card s).trans (Nat.pow_le_pow_right (by decide) sizeBound)
  have realQ : (q:ℝ) ≤ (5:ℝ)^(8191:ℕ) := by
    have h := Nat.cast_le (α:=ℝ) |>.mpr qc
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
  have err : (q:ℝ)/6 ≤ errorConstant := div_le_div_of_nonneg_right realQ (by norm_num)
  have hcore : (mis (edge s) (cell π b {0}):ℝ) ≤ (3:ℝ)^(2*(q:ℝ)/3) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using core
  have r := legal_le_edges (s:=s) (band_free (univ : Finset (Space k)))
  calc
    _ ≤ (mis (edge s) b:ℝ) := by exact_mod_cast r
    _ = (mis (edge s) (cell π b {0}):ℝ) * (mis (edge s) (cell π b t):ℝ) := by exact_mod_cast split
    _ ≤ (3:ℝ)^(2*(q:ℝ)/3) * (3:ℝ)^((q:ℝ)*((t.card/2:ℕ):ℝ)) :=
      mul_le_mul hcore tail (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
    _ = _ := (Real.rpow_add (by norm_num : (0:ℝ)<3) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [cardN]; push_cast
      nlinarith only [mul_le_mul_of_nonneg_left realHalf (Nat.cast_nonneg q),err]

theorem all_seeds (gb : BlockBound) {k : ℕ} {s : Finset (Pt (Space k))}
    (sf : Free s) (outside : Disjoint s (full (Space k))) :
    (mis (clash s) (legal s (full (Space k))):ℝ) ≤
      (3:ℝ)^((Fintype.card (Space k):ℝ)/2+errorConstant) := by
  by_cases small : s.card<8192
  · exact small_seed s small (gb _ _ sf outside small)
  · apply (large_seed sf outside (by omega)).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h : 0 ≤ errorConstant := by unfold errorConstant; positivity
    linarith

end
end Audit.Blocks
