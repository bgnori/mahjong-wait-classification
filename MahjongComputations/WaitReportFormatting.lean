module

public import Mahjong.WaitDecompositionCode
public import MahjongComputations.WaitDecompositionReporting

@[expose] public section

open MahjongDomain (Tile Rank Honor)

namespace MahjongComputations

open MahjongComputations.Internal

/-- 自然数キーの度数表へ1件加える。 -/
def incrementCount (key : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(key, 1)]
  | entry :: rest =>
      if entry.1 == key then
        (entry.1, entry.2 + 1) :: rest
      else
        entry :: incrementCount key rest

/-- 自然数列を初出順の度数表へ変換する。 -/
def countOccurrences (values : List Nat) : List (Nat × Nat) :=
  values.foldl (fun counts value => incrementCount value counts) []

def Internal.formatNumberedGroup
    (tiles : List Tile) (suit : MahjongDomain.Suit) (suffix : String) : String :=
  let digits := (List.ofFn fun rank : Rank => rank).flatMap fun rank =>
    List.replicate (tiles.count (.suited suit rank)) (toString (rank.val + 1))
  if digits.isEmpty then "" else String.join digits ++ suffix

def Internal.formatHonorGroup (tiles : List Tile) : String :=
  let digits := (List.ofFn fun honor : Honor => honor).flatMap fun honor =>
    List.replicate (tiles.count (.honor honor)) (toString (honor.val + 1))
  if digits.isEmpty then "" else String.join digits ++ "z"

/-- 牌種列をスートごとにまとめた省略表記へ変換する。 -/
def formatTiles (tiles : List Tile) : String :=
  String.join <| [
    formatNumberedGroup tiles .man "m",
    formatNumberedGroup tiles .pin "p",
    formatNumberedGroup tiles .sou "s",
    formatHonorGroup tiles
  ].filter fun group => !group.isEmpty

/-- 待ち分解コードグループをレポートのTSV行へ変換する。 -/
def formatWaitDecompositionCodeGroup (group : WaitDecompositionCodeGroup) : String :=
  String.intercalate "\t" [
    toString group.codes,
    toString (WaitDecompositionCode.waitDecompositionCodesKey group.codes),
    toString group.count,
    formatTiles group.representativeTiles,
    formatTiles group.representativeWaits
  ]

/-- 待ち牌種類数の度数をレポート行へ変換する。 -/
def formatWaitTileCount (counts : List (Nat × Nat)) (waitTileCount : Nat) : String :=
  let count := (counts.find? fun entry => entry.1 == waitTileCount).map Prod.snd |>.getD 0
  s!"{waitTileCount} wait tile kinds: {count}"

end MahjongComputations