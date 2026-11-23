module

public import Init
public meta import Init

public import MahjongDomain.Tile

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-!
# 麻雀牌の基礎定義

牌種はCoreの `MahjongDomain.Tile` を直接利用する。
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
