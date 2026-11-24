module

public import Mahjong.WaitCompletionFinder
public import Mahjong.WaitDecompositionCode
public import MahjongComputations.TileMultisets
public import Std.Data.HashMap

@[expose] public section

open MahjongDomain (Tile)

namespace MahjongComputations

open WaitDecompositionCode
open MahjongComputations.Internal

/-!
`WaitDecompositionCode.canReduceMentsuPreservingWaitCores` と同じ判定を、元の手牌ぶんの
待ち核だけレポート側がすでに持っている `completions` から求め直し、探索を省略する版。

`canReduceMentsuPreservingWaitCores` は元の手牌の待ち核を `WaitCompletionFinder.findWaitCompletions`
で毎回ゼロから探索し直すが、直接生成のレポートは同じ内容を `WaitCompletionGroup.completions` として
すでに持っている。そこから `WaitDecompositionCode.waitCores` で直接求めれば、元の手牌ぶんの
組合せ探索（`winningPartitions`）を省略できる。面子除去後の手牌は既知データがないため、
そちらは引き続き `WaitDecompositionCode.findWaitCores` で探索する。
-/
def canReduceMentsuPreservingWaitCoresGivenCompletions
    (tiles : List Tile) (completions : List WaitCompletion) : Bool :=
  let originalCores := WaitDecompositionCode.waitCores completions
  1 < tiles.length &&
    !(WaitCompletionFinder.mentsuReductions tiles |>.filter fun remaining =>
        !(WaitCompletionFinder.waitingTiles remaining).isEmpty &&
          WaitDecompositionCode.findWaitCores remaining == originalCores).isEmpty

/-- 除去後の牌姿から得た待ち核集合を、牌姿キーで再利用するキャッシュ。 -/
structure WaitCoreCache where
  values : Std.HashMap Nat (Option (List Nat))
  hits : Nat
  misses : Nat

def emptyWaitCoreCache : WaitCoreCache :=
  { values := ∅, hits := 0, misses := 0 }

def Internal.insertCachedWaitCoreKeys
    (key : Nat) (cores : Option (List Nat)) (cache : WaitCoreCache) : WaitCoreCache :=
  { cache with values := cache.values.insert key cores }

def Internal.cachedWaitCores
    (tiles : List Tile) (cache : WaitCoreCache) :
    Option (List Nat) × WaitCoreCache :=
  let key := tileMultisetKey tiles
  match cache.values.get? key with
  | some cores =>
      (cores, { cache with hits := cache.hits + 1 })
  | none =>
      let completions := WaitCompletionFinder.findWaitCompletions tiles
      let cores := if completions.isEmpty then none
        else some (WaitDecompositionCode.waitCoreKeys (WaitDecompositionCode.waitCores completions))
      (cores, { cache with
        misses := cache.misses + 1 } |> insertCachedWaitCoreKeys key cores)

def canReduceMentsuPreservingWaitCoreKeysWith {m : Type → Type} [Monad m]
    (tiles : List Tile) (completions : List WaitCompletion)
    (lookup : List Tile → m (Option (List Nat))) : m Bool := do
  let originalCores := WaitDecompositionCode.waitCoreKeys (WaitDecompositionCode.waitCores completions)
  let rec loop : List (List Tile) → m Bool
    | [] => pure false
    | remaining :: rest => do
        match ← lookup remaining with
        | some cores =>
            if cores == originalCores then pure true else loop rest
        | none => loop rest
  if 1 < tiles.length then loop (WaitCompletionFinder.mentsuReductions tiles)
  else pure false

/-- 既知の元手牌の完成情報を使い、除去後の待ち核探索だけをキャッシュする判定。 -/
def canReduceMentsuPreservingWaitCoresCached
    (tiles : List Tile) (completions : List WaitCompletion)
    (cache : WaitCoreCache) : Bool × WaitCoreCache :=
  let computation : StateM WaitCoreCache Bool :=
    canReduceMentsuPreservingWaitCoreKeysWith tiles completions fun remaining =>
      get >>= fun cache =>
      let (cores, cache) := cachedWaitCores remaining cache
      set cache *> pure cores
  computation.run cache

end MahjongComputations