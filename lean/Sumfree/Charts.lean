import Sumfree.FiniteCells
import Mathlib.Algebra.Field.ZMod

namespace Sumfree.Pair
open Finset
variable {H : Type*} [AddCommGroup H] [Module F H] [DecidableEq H]
set_option linter.unusedSectionVars false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def chartMap (w u v : H) : Ambient Plane →ₗ[F] Ambient H where
  toFun p := (p.1,p.1 • w+p.2.1 • u+p.2.2 • v)
  map_add' x y := by
    refine Prod.ext (by rfl) ?_
    simp only [Prod.fst_add,Prod.snd_add,add_smul]
    abel
  map_smul' c x := by
    refine Prod.ext (by rfl) ?_
    simp [smul_add,smul_smul,smul_eq_mul]

def coordSpace (x y : Bool) : Submodule F (Ambient Plane) where
  carrier := {p | (x = false → p.2.1 = 0) ∧ (y = false → p.2.2 = 0)}
  zero_mem' := by simp
  add_mem' := fun ha hb => ⟨fun h => by simp [ha.1 h,hb.1 h],fun h => by simp [ha.2 h,hb.2 h]⟩
  smul_mem' := fun c _ ha => ⟨fun h => by simp [ha.1 h],fun h => by simp [ha.2 h]⟩

private theorem independent_coeff {u v : H} (nz : u ≠ 0) (ind : ¬∃ d : F, v = d • u)
    {a b : F} (h : a • u+b • v = 0) : a=0 ∧ b=0 := by
  by_cases hb : b = 0
  · simpa [hb,nz] using h
  · exfalso
    apply ind
    refine ⟨b⁻¹*(-a),?_⟩
    have eq : b • v = -(a • u) := eq_neg_of_add_eq_zero_right h
    calc
      v = b⁻¹ • (b • v) := by rw [smul_smul,inv_mul_cancel₀ hb,one_smul]
      _ = _ := by rw [eq,mul_smul,neg_smul]

structure Chart (s t g : Ambient H) where
  uv : Plane × Plane
  shape : uv ∈ shapes
  f : Ambient Plane →ₗ[F] Ambient H
  D : Submodule F (Ambient Plane)
  head : ∀ x, (f x).1 = x.1
  inj : Set.InjOn f D
  sourceS : (s.1,uv.1) ∈ D
  sourceT : (t.1,uv.2) ∈ D
  sourceG : (g.1,0) ∈ D
  maps : f (s.1,uv.1) = s ∧ f (t.1,uv.2) = t ∧ f (g.1,0) = g

/-- With the root placed on the first axis, only two tail vectors remain.
    A zero pair, one nonzero direction, and two independent directions exhaust them. -/
theorem chart_exists (s t g : Ambient H) (bg : band g) : Nonempty (Chart s t g) := by
  classical
  have gn : g.1 ≠ 0 := by rcases bg with h | h <;> rw [h] <;> decide
  let w := g.1⁻¹ • g.2
  let a := s.2 - s.1 • w
  let b := t.2 - t.1 • w
  have gw : g.1 • w = g.2 := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ gn,one_smul]
  have build (x y : Bool) (u v : H) (p q : Plane) (shape : (p,q) ∈ shapes)
      (hp : (s.1,p) ∈ coordSpace x y) (hq : (t.1,q) ∈ coordSpace x y)
      (sp : p.1 • u+p.2 • v = a) (tq : q.1 • u+q.2 • v = b)
      (zero : ∀ (z : Ambient Plane), z ∈ coordSpace x y →
        z.2.1 • u+z.2.2 • v = 0 → z.2.1=0 ∧ z.2.2=0) : Nonempty (Chart s t g) := by
    let f := chartMap w u v
    refine ⟨⟨(p,q),shape,f,coordSpace x y,fun _ => rfl,?_,hp,hq,by simp [coordSpace],?_,?_,?_⟩⟩
    · intro i hi j hj eq
      have h0 : f (i-j) = 0 := by rw [map_sub,eq,sub_self]
      have hfirst : (i-j).1 = 0 := congrArg Prod.fst h0
      have hs := congrArg Prod.snd h0
      change (i-j).1 • w+(i-j).2.1 • u+(i-j).2.2 • v = 0 at hs
      simp only [hfirst,zero_smul,zero_add] at hs
      obtain ⟨hx,hy⟩ := zero _ ((coordSpace x y).sub_mem hi hj) hs
      apply sub_eq_zero.mp
      exact Prod.ext hfirst (Prod.ext hx hy)
    · refine Prod.ext (by rfl) ?_
      change s.1 • w+p.1 • u+p.2 • v = s.2
      rw [add_assoc,sp]; dsimp [a]; abel
    · refine Prod.ext (by rfl) ?_
      change t.1 • w+q.1 • u+q.2 • v = t.2
      rw [add_assoc,tq]; dsimp [b]; abel
    · refine Prod.ext (by rfl) ?_
      simpa [f,chartMap] using gw
  by_cases ha : a=0
  · by_cases hb : b=0
    · apply build false false 0 0 (0,0) (0,0) (by simp [shapes]) (by simp [coordSpace])
        (by simp [coordSpace]) (by simp [ha]) (by simp [hb])
      intro z hz _
      exact ⟨hz.1 rfl,hz.2 rfl⟩
    · apply build true false b 0 (0,0) (1,0) (by simp [shapes]) (by simp [coordSpace])
        (by simp [coordSpace]) (by simp [ha]) (by simp)
      intro z hz eq
      exact ⟨by simpa [hb] using eq,hz.2 rfl⟩
  · by_cases dep : ∃ d : F, b = d • a
    · obtain ⟨d,hd⟩ := dep
      apply build true false a 0 (1,0) (d,0) (by simp [shapes]) (by simp [coordSpace])
        (by simp [coordSpace]) (by simp) (by simp [hd])
      intro z hz eq
      exact ⟨by simpa [ha] using eq,hz.2 rfl⟩
    · apply build true true a b (1,0) (0,1) (by simp [shapes]) (by simp [coordSpace])
        (by simp [coordSpace]) (by simp) (by simp)
      exact fun _ _ eq => independent_coeff ha dep eq

theorem member_seed_map {s t x : Ambient Plane} {D : Submodule F (Ambient Plane)}
    (f : Ambient Plane →ₗ[F] Ambient H) (inj : Set.InjOn f D)
    (hs : s ∈ D) (ht : t ∈ D) (hx : x ∈ D) :
    f x ∈ seedSet (f s) (f t) ↔ x ∈ seedSet s t := by
  change f x = f s ∨ f x = f t ↔ x = s ∨ x = t
  exact or_congr ⟨inj hx hs,congrArg f⟩ ⟨inj hx ht,congrArg f⟩

theorem legal_map {s t x : Ambient Plane} {D : Submodule F (Ambient Plane)}
    (f : Ambient Plane →ₗ[F] Ambient H) (inj : Set.InjOn f D)
    (hs : s ∈ D) (ht : t ∈ D) (hx : x ∈ D) :
    legalAt (f s) (f t) (f x) ↔ legalAt s t x := by
  let A := insert x (seedSet s t)
  have sub : A ⊆ D := by intro z h; rcases h with rfl|rfl|rfl <;> assumption
  have eq : insert (f x) (seedSet (f s) (f t)) = f '' A := by
    ext z
    simp only [A,seedSet,Set.image_insert_eq,Set.image_singleton]
  unfold legalAt
  rw [eq]
  constructor
  · intro h a ha b hb ab
    exact h _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ⟨a+b,ab,map_add ..⟩
  · rintro h _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ⟨z,hz,eqz⟩
    rw [← map_add] at eqz
    exact h _ ha _ hb (inj (sub hz) (D.add_mem (sub ha) (sub hb)) eqz ▸ hz)

theorem cell_transport {s t g : Ambient Plane} {D : Submodule F (Ambient Plane)}
    (f : Ambient Plane →ₗ[F] Ambient H) (head : ∀ z, (f z).1 = z.1) (inj : Set.InjOn f D)
    (hs : s ∈ D) (ht : t ∈ D) (hg : g ∈ D) :
    (cell (f s) (f t) (f g)).card = (cell s t g).card ∧
    mis (edges (f s) (f t)) (allowed (f s) (f t) (cell (f s) (f t) (f g))) =
      mis (edges s t) (allowed s t (cell s t g)) := by
  classical
  have domain : ∀ z ∈ cell s t g, z ∈ D := by
    intro z hz
    rcases (mem_cell.mp hz).2 with ⟨a,b,e⟩ | ⟨a,b,e⟩
    · have eq : z = (a • s+b • t)+g := sub_eq_iff_eq_add.mp e
      rw [eq]; exact D.add_mem (D.add_mem (D.smul_mem _ hs) (D.smul_mem _ ht)) hg
    · have eq : z = (a • s+b • t)-g := eq_sub_of_add_eq e
      rw [eq]; exact D.sub_mem (D.add_mem (D.smul_mem _ hs) (D.smul_mem _ ht)) hg
  have bandMap (z : Ambient Plane) : band (f z) ↔ band z := by simp [band,head]
  let rawList := [g,-g].flatMap fun h => coeffs.flatMap fun a => coeffs.map fun b => h+a • s+b • t
  have listed : (points s t g).map f = points (f s) (f t) (f g) := by
    calc
      _ = (rawList.map f).filter (fun x => decide (band x)) := by
        rw [List.filter_map]; simp [points,rawList,Function.comp_def,bandMap]
      _ = _ := by simp [points,rawList,List.map_flatMap,List.map_map,Function.comp_def]
  have imageEq : (cell s t g).image f = cell (f s) (f t) (f g) := by
    ext z
    simp only [cell,mem_image,List.mem_toFinset,← listed,List.mem_map]
  have allowedEq : (allowed s t (cell s t g)).image f = allowed (f s) (f t) (cell (f s) (f t) (f g)) := by
    ext y
    rw [mem_allowed,← imageEq,mem_image,mem_image]
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨cz,safe⟩ := mem_allowed.mp hz
      exact ⟨⟨z,cz,rfl⟩,(legal_map f inj hs ht (domain z cz)).2 safe⟩
    · rintro ⟨⟨z,cz,rfl⟩,safe⟩
      exact ⟨z,mem_allowed.mpr ⟨cz,(legal_map f inj hs ht (domain z cz)).1 safe⟩,rfl⟩
  refine ⟨imageEq ▸ Finset.card_image_of_injOn (fun x hx y hy => inj (domain x hx) (domain y hy)),?_⟩
  rw [← allowedEq]
  symm
  apply mis_image _ _ _ _ (fun x hx y hy => inj (domain x (mem_allowed.mp hx).1) (domain y (mem_allowed.mp hy).1))
  intro x hx y hy
  have xd := domain x (mem_allowed.mp hx).1
  have yd := domain y (mem_allowed.mp hy).1
  simp only [edges,raw,← map_add,← map_sub,member_seed_map f inj hs ht (D.add_mem xd yd),
    member_seed_map f inj hs ht (D.sub_mem xd yd),member_seed_map f inj hs ht (D.sub_mem yd xd)]
  exact and_congr_left fun _ => not_congr ⟨congrArg f,inj xd yd⟩

end Sumfree.Pair
