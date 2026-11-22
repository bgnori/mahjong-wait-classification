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
`firstRank`、`middleRank`、`lastRank` は、開始位置に対応する3つのランクを返す。
`isFirst` と `isLast` は、辺張判定で使う端の開始位置を見分ける補助である。
-/

/-- 順子の先頭ランク。 -/
def firstRank (start : ShuntsuStart) : Rank :=
  ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩

/-- 順子の中央ランク。 -/
def middleRank (start : ShuntsuStart) : Rank :=
  ⟨start.val + 1, Nat.lt_trans (Nat.add_lt_add_right start.isLt 1) (by decide)⟩

/-- 順子の終端ランク。 -/
def lastRank (start : ShuntsuStart) : Rank :=
  ⟨start.val + 2, Nat.add_lt_add_right start.isLt 2⟩

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

分類側の `tiles`／`orderedTiles` は必要な牌種列を返す。
-/

deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Suit
deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Tile
deriving instance BEq, ReflBEq, LawfulBEq, Repr, Fintype for MahjongDomain.Pair
deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Shuntsu
deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.MentsuCandidate

open MahjongDomain (Shuntsu MentsuCandidate)

namespace ClassificationPair

/-!
## 対子と牌種列

`tiles` は、共有対子を分類側の牌種で順序付き列に展開する。
-/

/-- 対子を構成する2枚の牌種列。 -/
def tiles (pair : MahjongDomain.Pair) : List Tile :=
  let tile := Mahjong.DomainAdapter.ofDomainTile pair.tile
  [tile, tile]

theorem tiles_toDomain (pair : MahjongDomain.Pair) :
    Multiset.ofList ((tiles pair).map Mahjong.DomainAdapter.toDomainTile) = pair.tiles := by
  simp [tiles, Mahjong.DomainAdapter.toDomainTile_ofDomainTile, MahjongDomain.Pair.tiles,
    Multiset.replicate]

end ClassificationPair

/-!
## 順子
-/
namespace MahjongDomain.Shuntsu

/-!
## 順子と牌種列

`Shuntsu.orderedTiles` は、開始位置から先頭・中央・終端の3ランクを計算し、
同じスートの連続する3枚の牌種列を返す。
-/

/-- 順子を構成する3枚の牌種列。 -/
def orderedTiles (shuntsu : Shuntsu) : List _root_.Tile :=
  let suit := Mahjong.DomainAdapter.ofDomainSuit shuntsu.suit
  [.numbered suit (ShuntsuStart.firstRank shuntsu.start),
   .numbered suit (ShuntsuStart.middleRank shuntsu.start),
   .numbered suit (ShuntsuStart.lastRank shuntsu.start)]

theorem orderedTiles_toDomain (shuntsu : Shuntsu) :
    Multiset.ofList (shuntsu.orderedTiles.map Mahjong.DomainAdapter.toDomainTile) =
      shuntsu.tiles := by
  cases shuntsu with
  | mk suit start =>
      cases suit <;> simp [orderedTiles, Mahjong.DomainAdapter.ofDomainSuit,
        Mahjong.DomainAdapter.toDomainTile, Mahjong.DomainAdapter.toDomainSuit, ShuntsuStart.firstRank,
        ShuntsuStart.middleRank, ShuntsuStart.lastRank, MahjongDomain.Shuntsu.tiles]

end MahjongDomain.Shuntsu

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
  (_root_.Suit.all.flatMap fun suit =>
    List.ofFn fun start : ShuntsuStart => MentsuCandidate.shuntsu ⟨Mahjong.DomainAdapter.toDomainSuit suit, start⟩) ++
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
      refine ⟨Mahjong.DomainAdapter.ofDomainSuit suit, ?_, ?_⟩
      · cases suit <;> simp [Mahjong.DomainAdapter.ofDomainSuit, _root_.Suit.all]
      · apply List.mem_ofFn.mpr
        exact ⟨start, by simp [Mahjong.DomainAdapter.toDomainSuit_ofDomainSuit]⟩
  | koutsu tile =>
      simp only [candidates, List.mem_append, List.mem_map]
      right
      exact ⟨Mahjong.DomainAdapter.ofDomainTile tile, _root_.Tile.mem_all _, by
        simp [Mahjong.DomainAdapter.toDomainTile_ofDomainTile]⟩

/-- 完成面子候補を構成する3枚の牌種列。 -/
def orderedTiles : MentsuCandidate → List _root_.Tile
  | .shuntsu shuntsuPattern => shuntsuPattern.orderedTiles
  | .koutsu tile =>
      let localTile := Mahjong.DomainAdapter.ofDomainTile tile
      [localTile, localTile, localTile]

theorem orderedTiles_toDomain (candidate : MentsuCandidate) :
    Multiset.ofList (candidate.orderedTiles.map Mahjong.DomainAdapter.toDomainTile) =
      candidate.tiles := by
  cases candidate with
  | shuntsu shuntsu =>
      exact shuntsu.orderedTiles_toDomain
  | koutsu tile =>
      simp [orderedTiles, Mahjong.DomainAdapter.toDomainTile_ofDomainTile,
        MahjongDomain.MentsuCandidate.tiles, Multiset.replicate]

/-- 完成面子候補を構成する牌は常に `mentsuTileCount` 枚である。 -/
theorem tiles_length (candidate : MentsuCandidate) :
    candidate.orderedTiles.length = mentsuTileCount := by
  cases candidate with
  | shuntsu pattern => cases pattern; rfl
  | koutsu tile => rfl

/-- 完成面子候補列を牌へ戻した列の長さは、面子数の `mentsuTileCount` 倍である。 -/
theorem flatMap_tiles_length (candidates : List MentsuCandidate) :
    (candidates.flatMap MentsuCandidate.orderedTiles).length =
      candidates.length * mentsuTileCount := by
  induction candidates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [first.tiles_length, inductionHypothesis]
      simp [Nat.add_mul, Nat.add_comm]

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
    (honor_mem : _root_.Tile.honor honor ∈ candidate.orderedTiles) : ¬candidate.IsShuntsu := by
  cases candidate with
  | koutsu tile => simp [IsShuntsu]
  | shuntsu shuntsuPattern =>
      cases shuntsuPattern
      simp [orderedTiles, Shuntsu.orderedTiles] at honor_mem

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
def shuntsu (suit : Suit) (start : ShuntsuStart) : WinningComponent :=
  .inr (.shuntsu ⟨Mahjong.DomainAdapter.toDomainSuit suit, start⟩)

/-- 指定した牌種の刻子を和了構成部品として作る。 -/
def koutsu (tile : Tile) : WinningComponent :=
  .inr (.koutsu (Mahjong.DomainAdapter.toDomainTile tile))

/-- 和了構成部品を構成する牌種列。 -/
def tiles : WinningComponent → List Tile
  | .inl pair => ClassificationPair.tiles pair
  | .inr mentsu => mentsu.orderedTiles

example : (WinningComponent.pair (.numbered .Manzu 4)).tiles.map (Tile.format .mpsz) = ["5m", "5m"] := rfl
example : (WinningComponent.shuntsu .Pinzu ⟨3, by decide⟩).tiles.map (Tile.format .mpsz) = ["4p", "5p", "6p"] := rfl
example : (WinningComponent.koutsu (.honor .Red)).tiles.map (Tile.format .mpsz) = ["7z", "7z", "7z"] := rfl

end WinningComponent

namespace Mahjong.DomainAdapter

def tileListCounts (tiles : List Tile) : MahjongDomain.TileCounts :=
  fun tile => (tiles.map toDomainTile).count tile

theorem toDomainTileList_count (tiles : List Tile) (tile : MahjongDomain.Tile) :
    (tiles.map toDomainTile).count tile = tiles.count (ofDomainTile tile) := by
  induction tiles with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have mappedEq : toDomainTile first = tile ↔ first = ofDomainTile tile := by
        constructor
        · intro equality
          calc
            first = ofDomainTile (toDomainTile first) :=
              (ofDomainTile_toDomainTile first).symm
            _ = ofDomainTile tile := congrArg ofDomainTile equality
        · intro equality
          subst first
          exact toDomainTile_ofDomainTile tile
      simp [List.count_cons, mappedEq, inductionHypothesis]

theorem ofList_count_eq_list_count {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (tiles : List α) (tile : α) :
    (Multiset.ofList tiles).count tile = tiles.count tile := by
  induction tiles with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change Multiset.count tile (first ::ₘ Multiset.ofList rest) = _
      rw [Multiset.count_cons, List.count_cons, inductionHypothesis]
      by_cases equal : tile = first
      · subst first
        simp
      · have unequal : first ≠ tile := Ne.symm equal
        simp [equal, unequal]

theorem pair_count (pair : MahjongDomain.Pair) (tile : MahjongDomain.Tile) :
    pair.tiles.count tile = (ClassificationPair.tiles pair).count (ofDomainTile tile) := by
  rw [← ClassificationPair.tiles_toDomain]
  rw [ofList_count_eq_list_count, toDomainTileList_count]

theorem mentsuCandidate_count (candidate : MahjongDomain.MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    candidate.tiles.count tile = candidate.orderedTiles.count (ofDomainTile tile) := by
  rw [← candidate.orderedTiles_toDomain]
  rw [ofList_count_eq_list_count, toDomainTileList_count]

theorem mentsuCandidates_count (candidates : List MahjongDomain.MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    MahjongDomain.MentsuCandidateList.counts candidates tile =
      (candidates.flatMap MahjongDomain.MentsuCandidate.orderedTiles).count (ofDomainTile tile) := by
  induction candidates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      rw [MahjongDomain.MentsuCandidateList.counts_cons]
      simp only [List.flatMap_cons, List.count_append]
      rw [mentsuCandidate_count, inductionHypothesis]

end Mahjong.DomainAdapter
