import Sumfree.Blocks
namespace Sumfree.Blocks
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem core_same : count .same false = 2 := by decide
theorem core_opposite : count .opposite false = 1 := by decide
theorem core_different : count .different false = 1 := by decide
theorem core_mixed : count .mixed false = 4 := by decide
theorem core_zeroOpposite : count .zeroOpposite false = 5 := by decide
theorem core_oneNonzero : count .oneNonzero false = 1 := by decide
theorem core_oneZero : count .oneZero false = 10 := by decide
theorem generic_opposite : count .opposite true = 2 := by decide
theorem generic_oneNonzero : count .oneNonzero true = 3 := by decide
theorem generic_same : count .same true = 83 := by native_decide
theorem generic_different : count .different true = 122 := by native_decide
theorem generic_mixed : count .mixed true = 50 := by native_decide
theorem generic_zeroOpposite : count .zeroOpposite true = 25 := by native_decide
theorem generic_oneZero : count .oneZero true = 100 := by native_decide
theorem prism5_mis : prism 5 true = 10 := by decide
theorem prism10_mis : prism 10 true = 122 := by native_decide
theorem prism10_ind : prism 10 false = 6727 := by native_decide
end Sumfree.Blocks
