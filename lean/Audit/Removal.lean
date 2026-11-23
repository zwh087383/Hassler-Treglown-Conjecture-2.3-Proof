import Audit.Link
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

namespace Audit.Removal

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles
open scoped Classical
set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- We keep both summands, including the diagonal, so these are ordered Schur triples. -/
def triples (s : Finset G) := (s ×ˢ s).filter fun p => p.1+p.2∈s

@[simp] theorem mem_triples {x y : G} {s : Finset G} :
    (x,y)∈triples s ↔ x∈s ∧ y∈s ∧ x+y∈s := by simp [triples, and_assoc]

def meets (p q : G × G) : Prop :=
  p.1=q.1 ∨ p.2=q.2 ∨ p.1+p.2=q.1+q.2

def matching (m : Finset (G × G)) : Prop :=
  ∀ p∈m, ∀ q∈m, meets p q → p=q

def used (m : Finset (G × G)) : Finset G :=
  (m.image Prod.fst ∪ m.image Prod.snd) ∪ m.image (fun p => p.1+p.2)

theorem used_card (m : Finset (G × G)) : (used m).card ≤ 3*m.card := by
  unfold used
  have h₁ := card_union_le (m.image Prod.fst) (m.image Prod.snd)
  have h₂ := card_union_le (m.image Prod.fst ∪ m.image Prod.snd) (m.image fun p => p.1+p.2)
  have h₃ := card_image_le (s:=m) (f:=Prod.fst)
  have h₄ := card_image_le (s:=m) (f:=Prod.snd)
  have h₅ := card_image_le (s:=m) (f:=fun p => p.1+p.2)
  omega

theorem maximal_matching (s : Finset G) :
    ∃ m ⊆ triples s, matching m ∧ Link.Free (s \ used m) := by
  classical
  let candidates := (triples s).powerset.filter matching
  have emp : ∅∈candidates := by simp [candidates, matching]
  obtain ⟨m,hm,best⟩ := exists_max_image candidates Finset.card ⟨_,emp⟩
  obtain ⟨ms,ind⟩ := mem_filter.mp hm
  refine ⟨m,mem_powerset.mp ms,ind,?_⟩
  rintro x hx y hy z hz rfl
  obtain ⟨xs,xu⟩ := mem_sdiff.mp hx
  obtain ⟨ys,yu⟩ := mem_sdiff.mp hy
  obtain ⟨zs,zu⟩ := mem_sdiff.mp hz
  have apart (p : G × G) (hp : p∈m) : ¬ meets (x,y) p := by
    rintro (ex|ey|es)
    · apply xu; exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨p,hp,ex.symm⟩))
    · apply yu; exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨p,hp,ey.symm⟩))
    · apply zu; exact mem_union_right _ (mem_image.mpr ⟨p,hp,es.symm⟩)
  have fresh : (x,y)∉m := fun h => apart _ h (Or.inl rfl)
  have good : matching (insert (x,y) m) := by
    intro p hp q hq eq
    rcases mem_insert.mp hp with rfl|hp <;> rcases mem_insert.mp hq with rfl|hq
    · rfl
    · exact False.elim (apart _ hq eq)
    · apply False.elim; apply apart _ hp
      rcases eq with a|b|c
      · exact Or.inl a.symm
      · exact Or.inr (Or.inl b.symm)
      · exact Or.inr (Or.inr c.symm)
    · exact ind _ hp _ hq eq
  have h := best _ (mem_filter.mpr ⟨mem_powerset.mpr
    (insert_subset (mem_triples.mpr ⟨xs,ys,zs⟩) (mem_powerset.mp ms)),good⟩)
  rw [card_insert_of_not_mem fresh] at h
  omega

/-- A solution with increments u,v gives the triangle with vertices x,x+u,x+u+v. -/
def walk : G × (G × G) ↪ G × G × G where
  toFun p := (p.1,p.1+p.2.1,p.1+p.2.1+p.2.2)
  inj' := by
    rintro ⟨x,u,v⟩ ⟨y,a,b⟩ h
    obtain ⟨rfl, mid, last⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj
    obtain rfl := add_left_cancel mid
    obtain rfl := add_left_cancel last
    rfl

def walks (m : Finset (G × G)) := (univ ×ˢ m).map walk

@[simp] theorem walks_card (m : Finset (G × G)) :
    (walks m).card = Fintype.card G * m.card := by simp [walks]

theorem mem_walks {m : Finset (G × G)} {x y z : G} :
    (x,y,z)∈walks m ↔ (y-x,z-y)∈m := by
  constructor
  · intro h
    obtain ⟨⟨w,u,v⟩,hm,e⟩ := mem_map.mp h
    change (w,w+u,w+u+v)=(x,y,z) at e
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj e |>.imp_right Prod.mk.inj
    simpa [add_sub_cancel_left] using (mem_product.mp hm).2
  · intro h
    refine mem_map.mpr ⟨(x,y-x,z-y),mem_product.mpr ⟨mem_univ _,h⟩,?_⟩
    change (x,x+(y-x),x+(y-x)+(z-y)) = (x,y,z)
    simp [add_comm x,add_comm y]

private theorem diff_sum (x y z : G) : (y-x)+(z-y)=z-x := by abel

theorem disjoint_walks {m : Finset (G × G)} (hm : matching m) :
    ExplicitDisjoint (walks m) where
  inj₀ := by
    intro x y z x' h h'
    have e := hm _ (mem_walks.mp h) _ (mem_walks.mp h') (Or.inr (Or.inl rfl))
    exact sub_right_inj.mp (congrArg Prod.fst e)
  inj₁ := by
    intro x y z y' h h'
    have e := hm _ (mem_walks.mp h) _ (mem_walks.mp h') (Or.inr (Or.inr
      (by change (y-x)+(z-y)=(y'-x)+(z-y'); rw [diff_sum,diff_sum])))
    exact sub_left_inj.mp (congrArg Prod.fst e)
  inj₂ := by
    intro x y z z' h h'
    have e := hm _ (mem_walks.mp h) _ (mem_walks.mp h') (Or.inl rfl)
    exact sub_left_inj.mp (congrArg Prod.snd e)

theorem clique_bound {s : Finset G} {m : Finset (G × G)} (sub : m⊆triples s) :
    ((graph (walks m)).cliqueFinset 3).card ≤ Fintype.card G * (triples s).card := by
  classical
  rw [← walks_card, ← card_map (f:=toTriangle)]
  apply card_le_card
  intro cl hc
  obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := SimpleGraph.is3Clique_iff.mp (mem_cliqueFinset_iff.mp hc)
  obtain ⟨x,y,z,e,hxy,hxz,hyz⟩ := graph_triple hij hik hjk
  obtain ⟨z',p⟩ := Graph.in₀₁_iff.mp hxy
  obtain ⟨y',q⟩ := Graph.in₀₂_iff.mp hxz
  obtain ⟨x',r⟩ := Graph.in₁₂_iff.mp hyz
  have a := mem_triples.mp (sub (mem_walks.mp p))
  have b := mem_triples.mp (sub (mem_walks.mp q))
  have c := mem_triples.mp (sub (mem_walks.mp r))
  refine mem_map.mpr ⟨(x,y,z),mem_walks.mpr (mem_triples.mpr ⟨a.1,c.2.1,?_⟩),e⟩
  rw [diff_sum,← diff_sum x y' z]
  exact b.2.2

/-- A single positive density works for every finite abelian group, including dimension zero. -/
theorem remove (ε : ℝ) (hε : 0<ε) (small : ε≤1) :
    let δ := 27 * triangleRemovalBound (ε/27)
    0<δ ∧ ∀ s : Finset G, ((triples s).card:ℝ) < δ * (Fintype.card G:ℝ)^2 →
      ∃ e ⊆ s, (e.card:ℝ) ≤ ε * Fintype.card G ∧ Link.Free (s \ e) := by
  dsimp only
  have hpos := triangleRemovalBound_pos (show 0<ε/27 by positivity) (show ε/27≤1 by linarith)
  refine ⟨by positivity,?_⟩
  intro s few
  obtain ⟨m,ms,ind,free⟩ := maximal_matching s
  let n : ℝ := Fintype.card G
  have hn : 0<n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have short : (m.card:ℝ) < ε*n/3 := by
    by_contra! large
    letI := disjoint_walks ind
    have far : (graph (walks m)).FarFromTriangleFree (ε/27) := by
      apply farFromTriangleFree
      rw [walks_card]
      push_cast
      change ε/27 * (n+n+n)^2 ≤ n*(m.card:ℝ)
      nlinarith [mul_le_mul_of_nonneg_left large hn.le]
    have lower := far.le_card_cliqueFinset
    have upper : (((graph (walks m)).cliqueFinset 3).card:ℝ) ≤ n*(triples s).card := by
      dsimp [n]
      exact_mod_cast clique_bound ms
    simp only [Fintype.card_sum,Nat.cast_add] at lower
    change triangleRemovalBound (ε/27)*(n+(n+n))^3 ≤ _ at lower
    have bound := lower.trans upper
    have strict := mul_lt_mul_of_pos_left few hn
    change n*(triples s).card < n*(27*triangleRemovalBound (ε/27)*n^2) at strict
    nlinarith only [bound,strict]
  refine ⟨s∩used m,inter_subset_left,?_,?_⟩
  · have inc : ((s∩used m).card:ℝ) ≤ 3*(m.card:ℝ) := by
      exact_mod_cast (card_le_card (inter_subset_right (s₁:=s) (s₂:=used m))).trans (used_card m)
    change _ ≤ ε*n
    linarith
  · exact Link.smaller (by intro x hx; obtain ⟨xs,xn⟩ := mem_sdiff.mp hx
                           exact mem_sdiff.mpr ⟨xs,fun hu => xn (mem_inter.mpr ⟨xs,hu⟩)⟩) free

end Audit.Removal
