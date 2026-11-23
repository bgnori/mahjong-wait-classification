import Mahjong.WaitCompletionFinder
import Mahjong.Hand
import Mahjong.TenhouInput
import Mathlib.Util.AssertNoSorry

open MahjongDomain (Tile Rank Honor TileFormat)

namespace MahjongTests.WaitCompletionFinder

open _root_.WaitCompletionFinder
open MahjongDomain (MentsuCandidate)

assert_no_sorry MahjongDomain.TileCounts.ofList_apply
assert_no_sorry MahjongDomain.MentsuCandidateList.counts_eq_list_count
assert_no_sorry MahjongDomain.Tile.index_injective
assert_no_sorry WinningPartitionSpec.toDomainStandardCompletion
assert_no_sorry standardCompletion_toStandardAgari
assert_no_sorry IsStandardAgari.toDomainStandardCompletion_of_length

example : IsWaitFor
    [.suited .man 0, .suited .man 0, .suited .man 0, .honor Honor.east]
    (.honor Honor.east) := by
  unfold IsWaitFor IsStandardAgari
  native_decide

/-- Shared suits retain the classification's suit-major order and keys. -/
example :
    MahjongDomain.Suit.all = [.man, .pin, .sou] ∧
    MahjongDomain.Suit.all.map suitOrderKey = [0, 1, 2] := by
  decide

/-- The shared enumeration preserves the former classification key order. -/
example : Tile.all.map (fun tile => tile.index.val) = List.range 34 := by
  decide

private def countBasedHand : Hand :=
  { mentsuCount := 1
    counts := MahjongDomain.TileCounts.ofList
      [.suited .man 4, .suited .man 4, .suited .man 5, .suited .man 6]
    counts_valid := by native_decide
    total_tiles := by
      rw [MahjongDomain.TileCounts.ofList_sum_eq_length]
      rfl }

example : countBasedHand.tileTypes =
    [.suited .man 4, .suited .man 4, .suited .man 5, .suited .man 6] := by
  decide

example :
    (Mahjong.TenhouInput.decodeHand 1 [16, 17, 52, 53]).map Hand.tileTypes =
      .ok [.suited .man 4, .suited .man 4, .suited .pin 4, .suited .pin 4] := by
  decide

example :
    Mahjong.TenhouInput.decodeHand 1 [16, 17, 52] =
      .error (.wrongHandSize 4 3) := by
  rfl

example :
    Mahjong.TenhouInput.decodeHand 1 [16, 16, 52, 53] =
      .error (.tenhou .duplicateId) := by
  rfl

example :
    Mahjong.TenhouInput.decodeHand 1 [16, 17, 52, 136] =
      .error (.tenhou (.idOutOfRange 136)) := by
  rfl

private def testHandA : List Tile := Tile.suitedTiles .man [2, 3, 4, 4, 4] ++
  Tile.suitedTiles .sou [7, 7]
private def testHandB : List Tile := Tile.suitedTiles .man [1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
private def testHandC : List Tile := Tile.suitedTiles .sou [2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
private def testHandD : List Tile := Tile.suitedTiles .man [1, 1, 2, 2, 3, 3, 4, 4] ++
  Tile.suitedTiles .sou [6, 6]
private def testHand3456678 : List Tile := manzu [2, 3, 4, 5, 5, 6, 7]
private def testHand2345678 : List Tile := manzu [1, 2, 3, 4, 5, 6, 7]
private def testHand3334556 : List Tile := manzu [2, 2, 2, 3, 4, 4, 5]
private def testHand3335678 : List Tile := manzu [2, 2, 2, 4, 5, 6, 7]
private def testHand3335567 : List Tile := manzu [2, 2, 2, 4, 4, 5, 6]
private def testHand3335777 : List Tile := manzu [2, 2, 2, 4, 6, 6, 6]
private def testHand2345555678 : List Tile := manzu [1, 2, 3, 4, 4, 4, 4, 5, 6, 7]

private def manzuPair (rank : Rank) : WinningComponent :=
  .pair (.suited .man rank)

private def manzuShuntsu (start : Nat) (valid : start < shuntsuStartCount := by decide) : WinningComponent :=
  .shuntsu .man ⟨start, valid⟩

private def manzuKoutsu (rank : Rank) : WinningComponent :=
  .koutsu (.suited .man rank)

private def manzuWaitCompletion (wait : Rank) (winningComponents : List WinningComponent) : WaitCompletion :=
  { wait := .suited .man wait, winningComponents := CanonicalWinningComponents.ofList winningComponents }

/-- The first and last suited sequences and an honor triplet keep their ordered tile lists. -/
example :
    (WinningComponent.shuntsu .man ⟨0, by decide⟩).tiles = manzu [0, 1, 2] ∧
    (WinningComponent.shuntsu .sou ⟨6, by decide⟩).tiles = souzu [6, 7, 8] ∧
    (WinningComponent.koutsu (.honor Honor.red)).tiles =
      [.honor Honor.red, .honor Honor.red, .honor Honor.red] := by
  decide

/-- Candidate ordering and repeated candidates are observable in the raw decomposition search. -/
example :
    MentsuCandidate.candidates.take 2 =
      [.shuntsu ⟨.man, ⟨0, by decide⟩⟩,
       .shuntsu ⟨.man, ⟨1, by decide⟩⟩] ∧
    (MentsuCandidate.candidates.drop 20).take 2 =
      [.shuntsu ⟨.sou, ⟨6, by decide⟩⟩, .koutsu (.suited .man 0)] ∧
    MentsuCandidate.candidates.getLast? = some (.koutsu (.honor 6)) ∧
    decomposeMentsu 2 (manzu [0, 1, 2, 0, 1, 2]) =
      [[.shuntsu ⟨.man, ⟨0, by decide⟩⟩, .shuntsu ⟨.man, ⟨0, by decide⟩⟩]] ∧
    decomposeMentsu 2 (manzu [0, 1, 2, 3, 4, 5]) =
      [[.shuntsu ⟨.man, ⟨0, by decide⟩⟩, .shuntsu ⟨.man, ⟨3, by decide⟩⟩],
       [.shuntsu ⟨.man, ⟨3, by decide⟩⟩, .shuntsu ⟨.man, ⟨0, by decide⟩⟩]] := by
  native_decide

example :
    waitingTiles testHandA = manzu [1, 4] ++ souzu [7] ∧
    waitingTiles testHandB = manzu [1, 2, 4, 5] ∧
    waitingTiles testHandC = souzu [2, 3, 5, 6] ∧
    waitingTiles testHandD = manzu [1, 4] ++ souzu [6] ∧
    waitingTiles testHand2345555678 = manzu [1, 7] ∧
    waitingTiles (manzu [0, 1]) = [] ∧
    waitingTiles (manzu [0, 0, 0, 0, 0, 1, 2]) = [] ∧
    findWaitCompletions testHand3456678 =
      [manzuWaitCompletion 2 [manzuPair 2, manzuShuntsu 3, manzuShuntsu 5],
       manzuWaitCompletion 5 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 5],
       manzuWaitCompletion 8 [manzuPair 5, manzuShuntsu 2, manzuShuntsu 6]] ∧
    (findWaitCompletions testHand3456678).length = 3 ∧
    findWaitCompletions testHand2345678 =
      [manzuWaitCompletion 1 [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 1, manzuShuntsu 5],
       manzuWaitCompletion 7 [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4]] ∧
    (findWaitCompletions testHand2345678).length = 3 ∧
    findWaitCompletions testHand3334556 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 3],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 3, manzuKoutsu 2],
       manzuWaitCompletion 6 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4]] ∧
    (findWaitCompletions testHand3334556).length = 3 ∧
    findWaitCompletions testHand3335678 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 5],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2],
       manzuWaitCompletion 7 [manzuPair 7, manzuShuntsu 4, manzuKoutsu 2]] ∧
    (findWaitCompletions testHand3335678).length = 3 ∧
    findWaitCompletions testHand3335567 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuShuntsu 4],
       manzuWaitCompletion 4 [manzuPair 4, manzuShuntsu 4, manzuKoutsu 2],
      manzuWaitCompletion 7 [manzuPair 4, manzuShuntsu 5, manzuKoutsu 2]] ∧
    (findWaitCompletions testHand3335567).length = 3 ∧
    findWaitCompletions testHand3335777 =
      [manzuWaitCompletion 3 [manzuPair 2, manzuShuntsu 2, manzuKoutsu 6],
       manzuWaitCompletion 4 [manzuPair 4, manzuKoutsu 2, manzuKoutsu 6],
       manzuWaitCompletion 5 [manzuPair 6, manzuShuntsu 4, manzuKoutsu 2]] ∧
    (findWaitCompletions testHand3335777).length = 3 ∧
    findWaitCompletions testHand2345555678 =
      [manzuWaitCompletion 1
          [manzuPair 1, manzuShuntsu 2, manzuShuntsu 5, manzuKoutsu 4],
        manzuWaitCompletion 7
          [manzuPair 7, manzuShuntsu 1, manzuShuntsu 4, manzuKoutsu 4]] ∧
    (findWaitCompletions testHand2345555678).length = 2 := by
  native_decide

end MahjongTests.WaitCompletionFinder
