import Audit.StripFormula

namespace Audit.Strip

def windowBound : Model → Nat
  | .sameTriple => 803590
  | .oppositeTriple => 660380
  | .nestedFour => 476800
  | .triangleFour => 641980
  | .twoZeroFour => 267245
  | .triangleFive => 509935

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem count_checked (c : Model) (side : Bool) : count c side=windowBound c := by
  cases c <;> cases side <;> native_decide

end Audit.Strip
