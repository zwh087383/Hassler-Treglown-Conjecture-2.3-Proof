import Audit.SmallMixedFourGlobal
import Audit.TriangleFourTable

namespace Audit.SmallMixed
open Finset Lower Link Band Blocks Generic Degrees

/-- The checked table supplies every two- and three-dimensional normal form. -/
theorem four_tables : FourTables where
  plane j l a b hj hl size free := shape2_bound j l a b size free hj hl
  cube j l hj hl size free := shape3_bound j l size free hj hl

/-- All four-point exterior seeds meeting the zero layer, in every ambient rank. -/
theorem four {k : ℕ} {s : Finset (Pt (Space k))} (sf : Free s) (out : Disjoint s (full _))
    (zero : (seedLayer s 0).Nonempty) (size : s.card=4) : rankCount s≤3^(5^k) :=
  four_of_tables four_tables sf out zero size

end Audit.SmallMixed
