module

public import Init
public meta import Init

public import MahjongDomain.Representation

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-!
# 麻雀牌の基礎定義

牌種と物理牌IDはCoreの `MahjongDomain.Tile` と
`MahjongDomain.PhysicalTileId` を直接利用する。
-/

/-- 数牌のランク数。 -/
abbrev numberedRankCount : Nat := 9

deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Suit
deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Tile

/-- 数牌のスート数。 -/
def suitCount : Nat := MahjongDomain.Suit.all.length

/-- 分類の標準列挙順に対応するスートのキー。 -/
def suitOrderKey (suit : MahjongDomain.Suit) : Nat :=
  MahjongDomain.Suit.all.idxOf suit

/-- 牌種の総数。 -/
abbrev tileKindCount : Nat := 34

/-- 同じ牌種ごとの物理牌の枚数。 -/
abbrev copiesPerTile : Nat := 4

/-- 山を構成する物理牌の総数。 -/
abbrev deckSize : Nat := tileKindCount * copiesPerTile

/-- 136枚すべての物理牌からなる山。 -/
def deck : Finset MahjongDomain.PhysicalTileId :=
  Finset.univ

/-- 物理牌の山の枚数は34種類それぞれ4枚である。 -/
theorem deck_cardinality : deck.card = deckSize := by
  simp [deck, deckSize, tileKindCount, copiesPerTile]
