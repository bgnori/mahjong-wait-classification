module

public import Mahjong.DirectWaitGeneration
public import Mahjong.WaitCompletionFinder
public import Mahjong.WaitDecompositionCode
public import MahjongComputations.TileMultisets
public import Std.Data.HashMap

@[expose] public section

open MahjongDomain (Tile)

namespace MahjongComputations

open MahjongDomain (MentsuCandidate)
open WaitDecompositionCode
open MahjongComputations.Internal

/-- 牌姿ごとに完成情報を集約する前の1件。 -/
structure WaitCompletionEntry where
  tiles : List Tile
  completion : WaitCompletion
deriving BEq, DecidableEq, Repr

/-- 同じ牌姿から得られた重複のない完成情報群。 -/
structure WaitCompletionGroup where
  tiles : List Tile
  completions : List WaitCompletion
deriving BEq, DecidableEq, Repr

def Internal.waitCompletionEntryKeyLE
    (first second : WaitCompletionEntry) : Bool :=
  decide (tileMultisetKey first.tiles ≤ tileMultisetKey second.tiles)

/-- Insert a completion unless the same normalized completion is already present. -/
def insertCompletion
    (completion : WaitCompletion) (completions : List WaitCompletion) : List WaitCompletion :=
  if completions.contains completion then completions else completion :: completions

def Internal.groupSortedWaitCompletionEntry
    (groups : List WaitCompletionGroup) (entry : WaitCompletionEntry) :
    List WaitCompletionGroup :=
  let key := tileMultisetKey entry.tiles
  match groups with
  | [] => [{ tiles := entry.tiles, completions := [entry.completion] }]
  | group :: rest =>
      if tileMultisetKey group.tiles == key then
        { group with completions := insertCompletion entry.completion group.completions } :: rest
      else
        { tiles := entry.tiles, completions := [entry.completion] } :: groups

/-- 完成情報を牌姿ごとにまとめ、同一牌姿内の重複を除く。 -/
def groupWaitCompletions (entries : List WaitCompletionEntry) : List WaitCompletionGroup :=
  entries.mergeSort waitCompletionEntryKeyLE
    |>.foldl groupSortedWaitCompletionEntry []

/-- 直接導出を、同じ牌姿から得られた完成情報群へまとめる。 -/
def groupWaitDerivations {mentsuCount : Nat}
    (derivations : List (DirectWaitGeneration.WaitDerivation mentsuCount)) :
    List WaitCompletionGroup :=
  derivations
    |>.map (fun derivation =>
      { tiles := DirectWaitGeneration.hand derivation
        completion := DirectWaitGeneration.completion derivation })
    |> groupWaitCompletions

/-!
### 面子の並べ替えだけが違う直接生成の重複を避け、生成結果を一度に保持しない

`DirectWaitGeneration.directWaitDerivations` は `n` 個の面子を `Fin n → MentsuCandidate` という
順序付き関数として生成するため、同じ面子の多重集合でも並べ替えの数（最大 `n !`）だけ重複して
生成し、その大半を `Seed.valid` の正規化条件（`mentsuCanonical`）で捨てている。
さらに、生成した全件を `List` として一度に保持してから牌姿ごとにソート・グループ化する実装は、
面子が増えるほど生成件数（10枚形で数百万件規模）に比例したピークメモリを必要とする。

以下では、`mentsuCanonical` と同じ順序（`WinningComponent.orderKey` の昇順）で最初から
非減少列だけを畳み込みで直接処理し、`Seed.valid` を満たした瞬間に牌姿キーのハッシュマップへ
反映して捨てる。生成した `WaitDerivation` の全件を並べたリストはどこにも保持しないため、
ピークメモリは生成件数ではなく、重複除去後の牌姿の種類数に比例する。
-/

def Internal.canonicalMentsuAlphabet : List MentsuCandidate :=
  MentsuCandidate.candidates.mergeSort fun first second =>
    decide (WinningComponent.orderKey (.inr first) ≤ WinningComponent.orderKey (.inr second))

def Internal.defaultMentsuCandidate : MentsuCandidate := .koutsu (.honor 0)

def Internal.mentsuListToFunction (n : Nat) (mentsuList : List MentsuCandidate) :
    Fin n → MentsuCandidate :=
  fun i => mentsuList.getD i.val defaultMentsuCandidate

open DirectWaitGeneration in
/--
指定した雀頭牌について、面子の割り当てを `mentsuCanonical` と同じ順序で非減少列に限って
直接畳み込み、正規化済みの `WaitDerivation` それぞれを `f` で処理する。
-/
def foldCanonicalDirectWaitDerivationsForPairTiles {n : Nat} {α : Type}
    (pairTiles : List Tile) (init : α) (f : α → WaitDerivation n → α) : α :=
  pairTiles.foldl (init := init) fun acc tile =>
    (WaitDecompositionCode.combinationsWithRepetitionOver canonicalMentsuAlphabet n).foldl
      (init := acc) fun acc mentsuList =>
        let shape : WinningShape n :=
          { pair := ⟨tile⟩, mentsu := mentsuListToFunction n mentsuList }
        (componentIndices n).foldl (init := acc) fun acc selected =>
          ((shape.component selected).tiles.dedup).foldl (init := acc) fun acc wait =>
            let seed : Seed n := { shape, selected, wait }
            if h : seed.valid = true then f acc ⟨seed, h⟩ else acc

open DirectWaitGeneration in
/-- Monadic variant used to stream canonical derivations without retaining them in memory. -/
def foldCanonicalDirectWaitDerivationsForPairTilesM {n : Nat} {α : Type} {m : Type → Type}
    [Monad m] (pairTiles : List Tile) (init : α) (f : α → WaitDerivation n → m α) : m α :=
  pairTiles.foldlM (init := init) fun acc tile =>
    (WaitDecompositionCode.combinationsWithRepetitionOver canonicalMentsuAlphabet n).foldlM
      (init := acc) fun acc mentsuList =>
        let shape : WinningShape n :=
          { pair := ⟨tile⟩, mentsu := mentsuListToFunction n mentsuList }
        (componentIndices n).foldlM (init := acc) fun acc selected =>
          ((shape.component selected).tiles.dedup).foldlM (init := acc) fun acc wait =>
            let seed : Seed n := { shape, selected, wait }
            if h : seed.valid = true then f acc ⟨seed, h⟩ else pure acc

open DirectWaitGeneration in
/--
面子の並べ替えだけが違う重複や、生成結果全体を並べた中間 `List` を保持せず、すべての雀頭牌の
正規化済み `WaitDerivation` を畳み込む。
-/
def foldCanonicalDirectWaitDerivations {n : Nat} {α : Type}
    (init : α) (f : α → WaitDerivation n → α) : α :=
  foldCanonicalDirectWaitDerivationsForPairTiles Tile.all init f

/-!
面子の並べ替えだけが違う重複を生成しない、`directWaitDerivations` と同じ牌姿・待ちの集合を
ストリーミングで集約する。中間 `List (WaitDerivation n)` を保持せず、牌姿キーのハッシュマップへ
1件ずつ反映するため、ピークメモリは牌姿の重複除去後の件数に比例する。
-/
structure CanonicalGenerationResult where
  groups : List WaitCompletionGroup
  enumeratedDerivations : Nat
deriving BEq, DecidableEq, Repr

def canonicalWaitCompletionGroups (n : Nat) : CanonicalGenerationResult :=
  let (groups, count) :=
    foldCanonicalDirectWaitDerivations (n := n)
      ((∅ : Std.HashMap Nat WaitCompletionGroup), 0)
      fun (groups, count) derivation =>
        let tiles := DirectWaitGeneration.hand derivation
        let completion := DirectWaitGeneration.completion derivation
        let key := tileMultisetKey tiles
        let groups' :=
          match groups.get? key with
          | none => groups.insert key { tiles, completions := [completion] }
          | some existing =>
              groups.insert key
                { existing with completions := insertCompletion completion existing.completions }
        (groups', count + 1)
  { groups := groups.values, enumeratedDerivations := count }

end MahjongComputations