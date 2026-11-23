import Sumfree.Counter
import Std.Data.DHashMap

namespace Sumfree.Counter

/-- Each cached integer carries its proof of equality to the specification for
    that exact residual formula. Proofs are erased by Lean's evaluator. -/
private abbrev Value (key : Nat × Formula) := {v : Nat // v = solve key.1 key.2}
private abbrev Memo := Std.DHashMap (Nat × Formula) Value

private def calculate : (n : Nat) → (F : Formula) → Memo → Value (n,F) × Memo
  | 0,F,cache => (⟨solve 0 F,rfl⟩,cache)
  | n+1,F,cache =>
    if d : [] ∈ F then (⟨0,by simp [solve,d]⟩,cache)
    else
      match cache.get? (n+1,F) with
      | some v => (v,cache)
      | none =>
        let (a,left) := calculate n (assign false F) cache
        let (b,right) := calculate n (assign true F) left
        let v : Value (n+1,F) := ⟨a.val+b.val,by simp [solve,d,a.property,b.property]⟩
        (v,right.insert (n+1,F) v)

def cached (n : Nat) (F : Formula) := ((calculate n F ∅).1).val
theorem cached_correct (n : Nat) (F : Formula) : cached n F = solve n F :=
  ((calculate n F ∅).1).property

end Sumfree.Counter
