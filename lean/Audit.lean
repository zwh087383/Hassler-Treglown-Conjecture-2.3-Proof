import Audit.Raw
import Audit.RankOne
import Audit.Asymptotic
import Audit.Coverage
import Audit.Fingerprint
import Audit.Main
import Audit.Unconditional
import Audit.Sharp
import Audit.DefinitionCheck

-- Public entry points for the checked mathematical statements.
#print axioms Audit.Raw.type_A
#print axioms Audit.Raw.type_B
#print axioms Audit.Raw.type_C
#print axioms Audit.Raw.raw_matrix
#print axioms Audit.Raw.no_loops
#print axioms Audit.Collisions.all_dimensions
#print axioms Audit.Collisions.weights_checked
#print axioms Audit.RankOne.every_seed
#print axioms Audit.Entropy.shearer
#print axioms Audit.Coverage.nested_colors
#print axioms Audit.Link.container_count
#print axioms Audit.Fingerprint.large_graph
#print axioms Audit.Asymptotic.lower
#print axioms Audit.Asymptotic.limit_of_upper
#print axioms Audit.Removal.remove
#print axioms Audit.Band.large_seed
#print axioms Audit.Blocks.small_seed
#print axioms Audit.Sparse.sparseCovers
#print axioms Audit.Structure.largeSetStructure
#print axioms Audit.Main.upper_of_generic_blocks
#print axioms Audit.Main.main_of_generic_blocks
#print axioms Audit.Unconditional.exponent_window
#print axioms Audit.RankOneBridge.all
#print axioms Audit.Degrees.many
#print axioms Audit.Strip.model_bound
#print axioms Audit.Strip.NoZero.model_bound
#print axioms Audit.NoZero.all
#print axioms Audit.SmallMixed.three
#print axioms Audit.SmallMixed.four
#print axioms Audit.Mixed.five
#print axioms Audit.Mixed.six
#print axioms Audit.Mixed.seven
#print axioms Audit.TenEight.crossing
#print axioms Audit.GenericTheorem.generic_block
#print axioms Audit.GenericTheorem.original_blocks
#print axioms Audit.StandardCoordinates.fmax_eq
#print axioms Audit.Sharp.standard_band
#print axioms Audit.Sharp.upper
#print axioms Audit.Sharp.log_limit
#print axioms Audit.Sharp.limit_via_generic_blocks
#print axioms Audit.Sharp.main_theorem
#print axioms Audit.DefinitionCheck.paper_statement
#check Audit.Sharp.upper
#check Audit.Sharp.log_limit
#check Audit.Sharp.main_theorem
#check Audit.DefinitionCheck.paper_statement
