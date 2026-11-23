module

public import Mahjong.Hand
public import MahjongDomain.Tenhou

@[expose] public section

namespace Mahjong.TenhouInput

inductive DecodeError where
  | tenhou (error : MahjongDomain.TenhouDecodeError)
  | wrongHandSize (expected actual : Nat)
  | invalidTileCounts
  deriving DecidableEq, Repr

/-- Decode Tenhou IDs at the input boundary into an Int34-based hand. -/
def decodeHand (mentsuCount : Fin (mentsuHandMaxMentsuCount + 1))
    (rawIds : List Nat) : Except DecodeError Hand := do
  let ids ←
    match MahjongDomain.decodeTenhouIds rawIds with
    | .ok ids => pure ids
    | .error error => throw (.tenhou error)
  let expected := mentsuHandTenpaiSize mentsuCount
  if hsize : ids.length = expected then
    let counts := MahjongDomain.TileCounts.ofTenhou ids
    if hvalid : counts.Valid then
      pure
        { mentsuCount := mentsuCount
          counts := counts
          counts_valid := hvalid
          total_tiles := by
            rw [MahjongDomain.TileCounts.ofTenhou_sum]
            exact hsize }
    else
      throw .invalidTileCounts
  else
    throw (.wrongHandSize expected ids.length)

end Mahjong.TenhouInput
