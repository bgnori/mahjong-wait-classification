module

public import MahjongTests.WaitDecompositionCode
public meta import MahjongTests.WaitDecompositionCode

@[expose] public section

open MahjongDomain (Tile)

namespace MahjongTests.WaitDecompositionCode

open Internal
open _root_.WaitDecompositionCode
open _root_.WaitCompletionFinder
open _root_.MahjongComputations

/--
Among generated irreducible seven-tile standard-form tenpai hands, equal
decomposition codes and component relations imply equal pathology degree.
-/
theorem sevenTileIrreducibleTenpai_relationClassification_determines_pathologyDegree :
    tenpaiRelationClassificationHasUniformPathologyDegree 2 true = true := by
  native_decide

end MahjongTests.WaitDecompositionCode