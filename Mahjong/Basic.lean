module

public import Init
public meta import Init

public import MahjongDomain.Tile

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

このモジュールでは、以降の待ち分類で使う最小限のドメインモデルを定義する。
牌種としての `Tile` と、同じ牌種が4枚あることを表す `PhysicalTile` を分けることで、
「3mという種類」と「3mの1枚目」のような区別を Lean の型で表せるようにする。

待ちの解析ロジックの多くは牌種 `Tile` の列を扱う。一方、実際の手牌から牌を取り出す
処理では重複を扱う必要があるため、`PhysicalTile` と `Finset` を使う。
-/


/-!
 ## 数牌の定義
 -/
/-- 数牌のランク数。 -/
abbrev numberedRankCount : Nat := 9

/-- 数牌のランク。`0` から `8` が、それぞれ実際の `1` から `9` に対応する。 -/
 abbrev Rank := Fin numberedRankCount

/-- `Rank` を自然数リテラルで書くためのインスタンス。 -/
 instance (n : Nat) [ofNat : OfNat (Fin numberedRankCount) n] : OfNat Rank n where
   ofNat := (OfNat.ofNat n : Fin numberedRankCount)

namespace Rank

/-- 最初の数牌ランク。 -/
def first : Rank := ⟨0, by decide⟩

/-- 2番目の数牌ランク。 -/
def second : Rank := ⟨1, by decide⟩

/-- 最後から2番目の数牌ランク。 -/
def penultimate : Rank := ⟨numberedRankCount - 2, by decide⟩

/-- 最後の数牌ランク。 -/
def last : Rank := ⟨numberedRankCount - 1, by decide⟩

end Rank

/-- 数牌の3種類のスート。 -/
 inductive Suit
 | Manzu
 | Pinzu
 | Souzu
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

instance : Fintype Suit :=
  Fintype.ofList [Suit.Manzu, Suit.Pinzu, Suit.Souzu] (by
    intro suit
    cases suit <;> simp)

namespace Suit

/-- 数牌の全スートを標準順で並べたリスト。 -/
def all : List Suit := [.Manzu, .Pinzu, .Souzu]

/-- 数牌のスート数。 -/
def count : Nat := all.length

/-- 標準列挙順に対応するスートのキー。 -/
def orderKey (suit : Suit) : Nat :=
  all.idxOf suit

end Suit


/-!
 ## 字牌の定義
 -/
/-- 字牌の7種類。 -/
 inductive Honor
 | East
 | South
 | West
 | North
 | White
 | Green
 | Red
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

instance : Fintype Honor :=
  Fintype.ofList
    [Honor.East, Honor.South, Honor.West, Honor.North, Honor.White, Honor.Green, Honor.Red]
    (by
      intro honor
      cases honor <;> simp)

namespace Honor

/-- すべての字牌を標準順で並べたリスト。 -/
def all : List Honor := [.East, .South, .West, .North, .White, .Green, .Red]

/-- 字牌の種類数。 -/
def count : Nat := all.length

/-- 標準列挙順に対応する字牌のキー。 -/
def orderKey (honor : Honor) : Nat :=
  all.idxOf honor

end Honor

/-!
 ## 麻雀牌の種類の定義 -> 萬子・筒子・索子と字牌
 -/
/-- 牌種。数牌はスートとランク、字牌は `Honor` で表す。 -/
 inductive Tile
 | numbered(suit : Suit) (rank : Rank )
 | honor(h : Honor )
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Fintype

namespace Tile

/-- 数牌の牌種数。 -/
def numberedCount : Nat := Suit.count * numberedRankCount

/-- 牌種の総数。 -/
def count : Nat := numberedCount + Honor.count

/-- 指定したスートとランク列から数牌列を作る。 -/
def numberedTiles (suit : Suit) (ranks : List Rank) : List Tile :=
  ranks.map (.numbered suit)

/-- 34種類すべての牌種を標準順で並べたリスト。 -/
def all : List Tile :=
  (Suit.all.flatMap fun suit =>
    List.ofFn fun rank : Rank => Tile.numbered suit rank) ++
  Honor.all.map .honor

/--
すべての牌種は標準列挙 `Tile.all` に含まれる。

この定理は、以降の網羅的な探索や分類が参照する「34種類の牌の一覧」に
抜けがないことを保証する小さな土台である。証明は `Tile` を数牌と字牌に分け、
それぞれが対応する一覧に含まれることを示す。

読むためのLean語彙: `namespace`, `theorem`, `cases`, `simp`, `left`, `exact`, `∈`。
-/
theorem mem_all (tile : Tile) : tile ∈ all := by
  cases tile with
  | numbered suit rank =>
    simp only [all, List.mem_append, List.mem_flatMap]
    left
    exact ⟨suit, by cases suit <;> simp [Suit.all], List.mem_ofFn.mpr ⟨rank, rfl⟩⟩
  | honor honor =>
      cases honor <;> simp [all, Honor.all]

/-- 標準列挙順に対応する牌種のキー。 -/
def orderKey : Tile → Nat
  | Tile.numbered suit rank =>
      Suit.orderKey suit * numberedRankCount + rank.val
  | Tile.honor honorTile => numberedCount + Honor.orderKey honorTile

end Tile

namespace Mahjong.DomainAdapter

def toDomainSuit : Suit → MahjongDomain.Suit
  | .Manzu => .man
  | .Pinzu => .pin
  | .Souzu => .sou

def toDomainHonor : Honor → MahjongDomain.Honor
  | .East => 0
  | .South => 1
  | .West => 2
  | .North => 3
  | .White => 4
  | .Green => 5
  | .Red => 6

def toDomainTile : Tile → MahjongDomain.Tile
  | .numbered suit rank => .suited (toDomainSuit suit) rank
  | .honor honor => .honor (toDomainHonor honor)

end Mahjong.DomainAdapter

/-- 同じ牌種ごとの物理牌の枚数。 -/
abbrev copiesPerTile : Nat := 4

/-- 山を構成する物理牌の総数。 -/
abbrev deckSize : Nat := Tile.count * copiesPerTile

/-- 物理的な1枚の牌。同じ牌種が4枚あることを `Fin 4` で区別する。 -/
abbrev PhysicalTile := Tile × Fin copiesPerTile

/-- 136枚すべての物理牌からなる山。 -/
def deck : Finset PhysicalTile :=
  Finset.univ

/--
麻雀牌の山は `deckSize` 枚、つまり34種類それぞれを `copiesPerTile` 枚ずつ含む。

この定理は、物理牌として扱う山の枚数が通常の麻雀牌の総数と一致することを保証する。
証明では `deck` の定義を展開し、有限型 `PhysicalTile` 全体の個数が `Tile.count * copiesPerTile`
になることを確認する。

読むためのLean語彙: `abbrev`, `Finset`, `.card`, `theorem`, `simp`, `rfl`。
-/
theorem deck_cardinality : deck.card = deckSize := by
  simp [deck]
  rfl

/-!
# 麻雀牌の表記

ここでは、Lean上の牌種 `Tile` を読者が見慣れた文字列へ変換する。

- `unicode`: 麻雀牌のUnicode文字で表す。
- `mpsz`: `1m`、`9p`、`5z` のような牌譜でよく使われる表記で表す。

後続の `Pattern.lean` では、ターツや順子がどの牌種列に対応するかを `mpsz` 表記で確認する。
-/

/-- 牌の表示形式。`mpsz` は `123m55p` のような牌譜でよく使われる表記。 -/
inductive TileFormat
| unicode
| mpsz
deriving BEq, DecidableEq, Repr

namespace Mahjong.DomainAdapter

def toDomainTileFormat : TileFormat → MahjongDomain.TileFormat
  | .unicode => .unicode
  | .mpsz => .mpsz

end Mahjong.DomainAdapter

namespace Tile

/-- 1つの牌種を指定された形式の文字列に変換する。 -/
def format (output : TileFormat) : Tile → String
  | tile =>
      MahjongDomain.Tile.format
        (Mahjong.DomainAdapter.toDomainTileFormat output)
        (Mahjong.DomainAdapter.toDomainTile tile)

example : format .unicode (.numbered .Manzu 0) = "🀇" := rfl
example : format .unicode (.honor .Red) = "🀄" := rfl

end Tile
