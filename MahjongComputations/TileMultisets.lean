module

public import Mahjong.Basic

@[expose] public section

open MahjongDomain (Tile copiesPerTile)

namespace MahjongComputations

/-- 牌種ごとの枚数を、物理上限より1大きい基数で符号化した多重集合キー。 -/
def tileMultisetKey (tiles : List Tile) : Nat :=
  Tile.all.foldl (fun key tile => key * (copiesPerTile + 1) + tiles.count tile) 0

/-- 各牌種を0枚から物理上限まで選ぶ合法牌多重集合の共通畳み込み。 -/
def Internal.foldLegalTileMultisetsOfLength {α : Type}
    (empty : α) (combine : α → α → α)
    (onComplete : α) (prependCopies : Tile → Nat → α → α) :
    Nat → List Tile → α
  | length, [] =>
      if length == 0 then onComplete else empty
  | length, tile :: rest =>
      (List.range (Nat.min copiesPerTile length + 1)).foldl
        (fun result copies =>
          combine result (prependCopies tile copies
            (Internal.foldLegalTileMultisetsOfLength empty combine onComplete prependCopies
              (length - copies) rest)))
        empty
termination_by _ tiles => tiles.length

open MahjongComputations.Internal

/-- 指定した牌種からなる、指定枚数の合法な牌多重集合。 -/
def legalTileMultisetsOfLength (length : Nat) (tiles : List Tile) : List (List Tile) :=
  foldLegalTileMultisetsOfLength [] List.append [[]]
    (fun tile copies tails => tails.map fun tail => List.replicate copies tile ++ tail)
    length tiles

/-- 指定した牌種からなる、指定枚数の合法な牌多重集合の個数。 -/
def countLegalTileMultisetsOfLength (length : Nat) (tiles : List Tile) : Nat :=
  foldLegalTileMultisetsOfLength 0 Nat.add 1 (fun _ _ count => count) length tiles

end MahjongComputations