import Mahjong.DomainAdapter
import MahjongDomain.Parts
import Mathlib.Tactic.DeriveFintype

/-!
# 牌パターン

このモジュールでは、待ち分類のために共有部品を順序付き牌種列へ展開する。
共有 `Pair`、`Shuntsu`、`MentsuCandidate` を使用する。
和了構成部品 `WinningComponent` は、雀頭と面子候補の直和として表す。
-/

/-!

順子は、開始位置を `Fin` で表す。`Fin n` は `0` 以上 `n` 未満の値なので、
存在しない開始位置を型で除外できる。
-/

/-- 完成面子を構成する牌の枚数。 -/
abbrev mentsuTileCount : Nat := 3

/-- 通常の最大手牌に含まれる面子数。 -/
abbrev standardHandMentsuCount : Nat := 4

/-- 通常形に含まれる雀頭の数。 -/
abbrev standardHandPairCount : Nat := 1

/-- 指定した面子数に対応する通常形聴牌の手牌枚数。 -/
def standardTenpaiHandSize (mentsuCount : Nat) : Nat :=
  mentsuCount * mentsuTileCount + standardHandPairCount

/-- 順子・嵌張ターツの開始位置数。 -/
abbrev shuntsuStartCount : Nat := numberedRankCount - 2

/-- 最初の順子開始位置。 -/
abbrev firstShuntsuStart : Nat := Rank.first.val

/-- 最後の順子開始位置。 -/
abbrev lastShuntsuStart : Nat := shuntsuStartCount - 1

/-- 順子・嵌張ターツの開始位置。 -/
abbrev ShuntsuStart := Fin shuntsuStartCount

namespace ShuntsuStart

/-!
## 順子・嵌張ターツの開始位置からランクを得る

順子や嵌張ターツは実際の1始まりから7始まりまでを扱う。
`isFirst` と `isLast` は、辺張判定で使う端の開始位置を見分ける補助である。
-/

/-- 最初の順子開始位置かどうか。 -/
def isFirst (start : ShuntsuStart) : Bool :=
  start.val == firstShuntsuStart

/-- 最後の順子開始位置かどうか。 -/
def isLast (start : ShuntsuStart) : Bool :=
  start.val == lastShuntsuStart

end ShuntsuStart

/-!
## 和了構成部品で使う小さな牌パターン

ここからは、共有部品と分類側の展開を説明する。

- `MahjongDomain.Pair`: 同じ牌種2枚からなる対子。
- `Shuntsu`: 同じスートで連続する3枚からなる順子。
- `MentsuCandidate`: 通常形で完成面子として扱う候補。順子または刻子。

Coreの順序付き展開を、牌種移行までAdapterで分類側の牌種列に変換する。
-/

deriving instance BEq, ReflBEq, LawfulBEq, Repr, Fintype for MahjongDomain.Pair
deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Shuntsu
deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.MentsuCandidate

open MahjongDomain (Shuntsu MentsuCandidate)

/-!
## メンツ
-/
namespace MahjongDomain.MentsuCandidate

/-!
## 完成面子候補と列挙

`MentsuCandidate` は、通常形で完成面子として扱う候補を順子または刻子として表す。
`candidates` は全順子候補と全刻子候補を並べ、`mem_candidates` がその列挙に
取りこぼしがないことを確認する。
-/

/-- すべての完成面子候補を含む実行可能な列挙。 -/
def candidates : List MentsuCandidate :=
  (MahjongDomain.Suit.all.flatMap fun suit =>
    List.ofFn fun start : ShuntsuStart => MentsuCandidate.shuntsu ⟨suit, start⟩) ++
  _root_.Tile.all.map (fun tile => MentsuCandidate.koutsu (Mahjong.DomainAdapter.toDomainTile tile))

/--
任意の完成面子候補は、実行用候補列 `MentsuCandidate.candidates` に含まれる。

この定理は、完成面子候補を列挙して調べる処理が、順子候補と刻子候補を取りこぼさないことを保証する。
証明では候補を順子の場合と刻子の場合に分ける。順子の場合はスートと開始位置から作った順子候補列に
含まれることを示し、刻子の場合は `Tile.mem_all` を使って、刻子に使う牌種が標準牌種列に含まれることを示す。

読むためのLean語彙: `inductive`, `namespace`, `theorem`, `cases`, `rcases`, `simp`, `left`, `refine`, `?_`, `exact`, `∈`。
-/
theorem mem_candidates (mentsu : MentsuCandidate) :
    mentsu ∈ candidates := by
  cases mentsu with
  | shuntsu shuntsuPattern =>
      rcases shuntsuPattern with ⟨suit, start⟩
      simp only [candidates, List.mem_append, List.mem_flatMap]
      left
      refine ⟨suit, ?_, ?_⟩
      · cases suit <;> simp [MahjongDomain.Suit.all]
      · apply List.mem_ofFn.mpr
        exact ⟨start, rfl⟩
  | koutsu tile =>
      simp only [candidates, List.mem_append, List.mem_map]
      right
      exact ⟨Mahjong.DomainAdapter.ofDomainTile tile, _root_.Tile.mem_all _, by
        simp [Mahjong.DomainAdapter.toDomainTile_ofDomainTile]⟩

/-- 完成面子候補が順子であることを表す述語。 -/
def IsShuntsu : MentsuCandidate → Prop
  | .shuntsu _ => True
  | _ => False

/--
字牌を含む完成面子候補は順子ではない。

この定理は、順子が同じスートの連続する数牌だけからなる、という麻雀上の制約をLean上の
`MentsuCandidate` に対して確認する。候補が刻子なら順子ではない。候補が順子なら、
`Shuntsu.orderedTiles` は数牌だけを返すため、字牌が含まれるという仮定と矛盾する。

読むためのLean語彙: `Prop`, `theorem`, `∈`, `¬`, `cases`, `simp`, `at`。
-/
theorem honor_not_in_shuntsu (candidate : MentsuCandidate) (honor : _root_.Honor)
    (honor_mem : _root_.Tile.honor honor ∈ Mahjong.DomainAdapter.mentsuTiles candidate) : ¬candidate.IsShuntsu := by
  cases candidate with
  | koutsu tile => simp [IsShuntsu]
  | shuntsu shuntsuPattern =>
      cases shuntsuPattern
      simp [Mahjong.DomainAdapter.mentsuTiles, orderedTiles, Shuntsu.orderedTiles,
        Mahjong.DomainAdapter.ofDomainTile] at honor_mem

end MahjongDomain.MentsuCandidate

/-!
## 雀頭と完成面子を同じ和了構成部品として扱う

通常形の和了分割では、雀頭と完成面子をどちらも「完成した部品」として並べて扱う。
`WinningComponent` は、共有雀頭または完成面子候補を持つ型である。

`pair`、`shuntsu`、`koutsu` は、麻雀上の呼び名から `WinningComponent` を作る入口である。
`WinningComponent.tiles` は、どちらの部品であっても構成する牌種列を返す。
-/

/-- 通常形の和了分割に現れる和了構成部品。雀頭または完成面子。 -/
abbrev WinningComponent := MahjongDomain.Pair ⊕ MentsuCandidate

namespace WinningComponent

/-- 指定した牌種の雀頭を和了構成部品として作る。 -/
def pair (tile : Tile) : WinningComponent :=
  .inl ⟨Mahjong.DomainAdapter.toDomainTile tile⟩

/-- 指定した順子を和了構成部品として作る。 -/
def shuntsu (suit : MahjongDomain.Suit) (start : ShuntsuStart) : WinningComponent :=
  .inr (.shuntsu ⟨suit, start⟩)

/-- 指定した牌種の刻子を和了構成部品として作る。 -/
def koutsu (tile : Tile) : WinningComponent :=
  .inr (.koutsu (Mahjong.DomainAdapter.toDomainTile tile))

/-- 和了構成部品を構成する牌種列。 -/
def tiles : WinningComponent → List Tile
  | .inl pair => Mahjong.DomainAdapter.pairTiles pair
  | .inr mentsu => Mahjong.DomainAdapter.mentsuTiles mentsu

example : (WinningComponent.pair (.numbered .man 4)).tiles.map (Tile.format .mpsz) = ["5m", "5m"] := rfl
example : (WinningComponent.shuntsu .pin ⟨3, by decide⟩).tiles.map (Tile.format .mpsz) = ["4p", "5p", "6p"] := rfl
example : (WinningComponent.koutsu (.honor .Red)).tiles.map (Tile.format .mpsz) = ["7z", "7z", "7z"] := rfl

end WinningComponent
