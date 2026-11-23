import Audit.SmallMixedZeroData
namespace Audit.SmallMixed.ZeroTriple
open Sumfree.Counter
set_option maxRecDepth 32768
set_option maxHeartbeats 0
theorem count : solve 50 (condition false)=19245 := by
  rw [←show 34+16=50 from rfl,←parts_correct]
  native_decide
end Audit.SmallMixed.ZeroTriple
