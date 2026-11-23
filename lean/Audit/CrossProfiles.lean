import Audit.MixedFive

namespace Audit.Mixed
open Finset Generic Band Link Lower Blocks Degrees
open scoped Classical
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {k : ℕ} {s : Finset (Pt (Space k))}

def Crossing (s : Finset (Pt (Space k))) :=
  ∃ a p : Space k, a≠0 ∧ (0,a)∈s ∧ (1,p)∈s ∧ (4,-(p+a))∈s

theorem bad_cases (sf : Free s) (out : Disjoint s (full _)) (bad : ¬NoZeroSum s) :
    6≤(seedLayer (forward s) 0).card ∨ Crossing s := by
  unfold NoZeroSum at bad
  push_neg at bad
  obtain ⟨x,hx,y,hy,z,hz,eq⟩ := bad
  have allowed {v : Pt (Space k)} (h : v∈s) : v.1≠2 ∧ v.1≠3 := by
    have no := fun b : v.1=2 ∨ v.1=3 => disjoint_left.mp out h (mem_full.mpr b)
    exact ⟨fun e => no (Or.inl e),fun e => no (Or.inr e)⟩
  have cases : ∀ i j l : Fin 5, (i≠2 ∧ i≠3) → (j≠2 ∧ j≠3) → (l≠2 ∧ l≠3) → i+j+l=0 →
    (i=0 ∧ j=0 ∧ l=0) ∨ (i=0 ∧ j=1 ∧ l=4) ∨ (i=0 ∧ l=1 ∧ j=4) ∨
    (j=0 ∧ i=1 ∧ l=4) ∨ (j=0 ∧ l=1 ∧ i=4) ∨ (l=0 ∧ i=1 ∧ j=4) ∨ (l=0 ∧ j=1 ∧ i=4) := by
      intro i j l; fin_cases i <;> fin_cases j <;> fin_cases l <;> decide
  have ordered {v w t : Pt (Space k)} (vs : v∈s) (ws : w∈s) (ts : t∈s)
      (vh : v.1=0) (wh : w.1=1) (th : t.1=4) (sum : v+w+t=0) : Crossing s := by
    obtain ⟨i,a⟩ := v; obtain ⟨j,p⟩ := w; obtain ⟨l,b⟩ := t
    change i=0 at vh; change j=1 at wh; change l=4 at th
    subst i; subst j; subst l
    have e : a+p+b=0 := congrArg Prod.snd sum
    have beq : b= -(p+a) := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm,add_left_comm,add_assoc] using e)
    have nz : a≠0 := by
      rintro rfl
      exact sf 0 vs 0 vs 0 vs (zero_add _)
    exact ⟨a,p,nz,vs,ws,beq ▸ ts⟩
  rcases cases x.1 y.1 z.1 (allowed hx) (allowed hy) (allowed hz) (congrArg Prod.fst eq) with
    h|h|h|h|h|h|h
  · left
    have diff {u v : Pt (Space k)} (hu : u∈s) (hv : v∈s) (e : u+u+v=0) : False :=
      sf _ hv _ hv _ hu (repeated e)
    have xy : x≠y := fun e => diff hx hz (by simpa only [e] using eq)
    have xz : x≠z := fun e => diff hx hy (by rw [e,add_right_comm]; simpa only [e] using eq)
    have yz : y≠z := fun e => diff hy hx (by rw [e,add_comm,←add_assoc]; simpa only [e] using eq)
    have nx : -x∉s := fun n => sf _ hy _ hz _ n (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm,add_left_comm,add_assoc] using eq))
    have ny : -y∉s := fun n => sf _ hx _ hz _ n (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm,add_left_comm,add_assoc] using eq))
    have nz : -z∉s := fun n => sf _ hx _ hy _ n (eq_neg_of_add_eq_zero_left eq)
    let T : Finset (Pt (Space k)) := {x,y,z}
    have desc (u : Pt (Space k)) (ut : u∈T) : u∈s ∧ -u∉s ∧ u.1=0 := by
      rcases (show u=x ∨ u=y ∨ u=z by simpa [T] using ut) with rfl|rfl|rfl
      · exact ⟨hx,nx,h.1⟩
      · exact ⟨hy,ny,h.2.1⟩
      · exact ⟨hz,nz,h.2.2⟩
    have apart : Disjoint T (T.image Neg.neg) := by
      apply disjoint_left.mpr
      rintro u ut nh
      obtain ⟨v,vt,e⟩ := mem_image.mp nh
      exact (desc v vt).2.1 (e ▸ (desc u ut).1)
    have sub : T∪T.image Neg.neg ⊆ seedLayer (forward s) 0 := by
      intro u hu
      have mem (w : Pt (Space k)) (hs : w∈signed s) (z0 : w.1=0) : w∈seedLayer (forward s) 0 :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨hs,Or.inl z0⟩,z0⟩
      rcases mem_union.mp hu with y|y
      · exact mem _ (mem_signed.mpr (Or.inl (desc u y).1)) (desc u y).2.2
      · obtain ⟨v,vt,rfl⟩ := mem_image.mp y
        exact mem _ (mem_signed.mpr (Or.inr (by simpa using (desc v vt).1))) (by change -v.1=0; rw [(desc v vt).2.2,neg_zero])
    have c := card_le_card sub
    rw [card_union_of_disjoint apart,card_image_of_injective _ neg_injective] at c
    simpa [T,xy,xz,yz] using c
  · exact Or.inr (ordered hx hy hz h.1 h.2.1 h.2.2 eq)
  · exact Or.inr (ordered hx hz hy h.1 h.2.1 h.2.2 (by simpa only [add_right_comm] using eq))
  · exact Or.inr (ordered hy hx hz h.1 h.2.1 h.2.2 (by simpa [add_comm,add_left_comm,add_assoc] using eq))
  · exact Or.inr (ordered hy hz hx h.1 h.2.1 h.2.2 (by simpa [add_comm,add_left_comm,add_assoc] using eq))
  · exact Or.inr (ordered hz hx hy h.1 h.2.1 h.2.2 (by simpa [add_comm,add_left_comm,add_assoc] using eq))
  · exact Or.inr (ordered hz hy hx h.1 h.2.1 h.2.2 (by simpa [add_comm,add_left_comm,add_assoc] using eq))

theorem crossing_gains (sf : Free s) (h : Crossing s) :
    (seedLayer s 0).card < (seedLayer (forward s) 0).card ∧
    (seedLayer s 1).card < (seedLayer (forward s) 1).card ∧
    (seedLayer s 4).card < (seedLayer (forward s) 1).card := by
  obtain ⟨a,p,na,z,u,v⟩ := h
  let x : Pt (Space k) := (0,a)
  let y : Pt (Space k) := (1,p)
  let w : Pt (Space k) := (4,-(p+a))
  have eq : x+y+w=0 := Prod.ext (by decide : (0:Fin 5)+1+4=0) (by change a+p+ -(p+a)=0; abel)
  have nx : -x∉s := fun n => sf y u w v (-x) n (eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm,add_left_comm,add_assoc] using eq))
  have ny : -y∉s := fun n => sf x z w v (-y) n (eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm,add_left_comm,add_assoc] using eq))
  have nw : -w∉s := fun n => sf _ z _ u _ n (eq_neg_of_add_eq_zero_left eq)
  have mem {d : Fin 5} {b : Pt (Space k)} (hs : b∈signed s) (bd : b.1=d) (ok : d=0 ∨ d=1) :
      b∈seedLayer (forward s) d := mem_filter.mpr ⟨mem_filter.mpr ⟨hs,ok.imp (bd.trans ·) (bd.trans ·)⟩,bd⟩
  have sub {d : Fin 5} (ok : d=0 ∨ d=1) : seedLayer s d ⊆ seedLayer (forward s) d :=
    fun _ hb => mem (mem_signed.mpr (Or.inl (mem_filter.mp hb).1)) (mem_filter.mp hb).2 ok
  have plus {d : Fin 5} {t : Pt (Space k)} (raw : t∈s) (abs : -t∉s)
      (head : (-t).1=d) (ok : d=0 ∨ d=1) : (seedLayer s d).card < (seedLayer (forward s) d).card := by
    have c := card_le_card (insert_subset (mem (b:=-t) (mem_signed.mpr (Or.inr (by simpa using raw))) head ok) (sub ok))
    rw [card_insert_of_not_mem (show -t∉seedLayer s d from fun a => abs (mem_filter.mp a).1)] at c
    omega
  refine ⟨plus (d:=0) (t:=x) z nx (by change -(0:Fin 5)=0; decide) (Or.inl rfl),
    plus (d:=1) (t:=w) v nw (by change -(4:Fin 5)=1; decide) (Or.inr rfl),?_⟩
  let Q := (seedLayer s 4).image Neg.neg
  have qs : Q ⊆ seedLayer (forward s) 1 := by
    intro b hb; obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    have h4 := (mem_filter.mp hc).2
    exact mem (mem_signed.mpr (Or.inr (by simpa using (mem_filter.mp hc).1))) (by change -c.1=1; rw [h4]; decide) (Or.inr rfl)
  have miss : y∉Q := by
    intro hy
    obtain ⟨c,hc,e⟩ := mem_image.mp hy
    exact ny (by rw [←e,neg_neg]; exact (mem_filter.mp hc).1)
  have c := card_le_card (insert_subset (mem (b:=y) (mem_signed.mpr (Or.inl u)) rfl (Or.inr rfl)) qs)
  rw [card_insert_of_not_mem miss] at c
  simpa only [Q,card_image_of_injective _ neg_injective] using c

end
end Audit.Mixed
