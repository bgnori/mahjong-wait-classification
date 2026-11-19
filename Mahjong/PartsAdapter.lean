import Mahjong.DomainAdapter
import Mahjong.Pattern
import MahjongDomain.Parts

/-!
# Adapter for shared standard-hand parts

These conversions preserve the classification-side constructors and ordering
while relating each pair and meld to the shared domain types.
-/

namespace Mahjong.DomainAdapter

def toDomainPair (pair : Toitsu) : MahjongDomain.Pair :=
  match pair with
  | .toitsu tile => ⟨toDomainTile tile⟩

def ofDomainPair (pair : MahjongDomain.Pair) : Toitsu :=
  .toitsu (ofDomainTile pair.tile)

@[simp] theorem ofDomainPair_toDomainPair (pair : Toitsu) :
    ofDomainPair (toDomainPair pair) = pair := by
  cases pair with
  | toitsu tile => simp [toDomainPair, ofDomainPair, ofDomainTile_toDomainTile]

@[simp] theorem toDomainPair_ofDomainPair (pair : MahjongDomain.Pair) :
    toDomainPair (ofDomainPair pair) = pair := by
  cases pair with
  | mk tile => simp [toDomainPair, ofDomainPair, toDomainTile_ofDomainTile]

def toDomainMeld : MentsuCandidate → MahjongDomain.Meld
  | .shuntsu (.shuntsu suit start) =>
      .sequence (toDomainSuit suit) start
  | .koutsu tile => .triplet (toDomainTile tile)

def ofDomainMeld : MahjongDomain.Meld → MentsuCandidate
  | .sequence suit start =>
      .shuntsu (.shuntsu (ofDomainSuit suit) start)
  | .triplet tile => .koutsu (ofDomainTile tile)

@[simp] theorem ofDomainMeld_toDomainMeld (meld : MentsuCandidate) :
    ofDomainMeld (toDomainMeld meld) = meld := by
  cases meld with
  | shuntsu shuntsu =>
      cases shuntsu with
      | shuntsu suit start => cases suit <;> rfl
  | koutsu tile => simp [toDomainMeld, ofDomainMeld, ofDomainTile_toDomainTile]

@[simp] theorem toDomainMeld_ofDomainMeld (meld : MahjongDomain.Meld) :
    toDomainMeld (ofDomainMeld meld) = meld := by
  cases meld with
  | sequence suit start => cases suit <;> rfl
  | triplet tile => simp [toDomainMeld, ofDomainMeld, toDomainTile_ofDomainTile]

def toDomainMelds (melds : List MentsuCandidate) : List MahjongDomain.Meld :=
  melds.map toDomainMeld

def ofDomainMelds (melds : List MahjongDomain.Meld) : List MentsuCandidate :=
  melds.map ofDomainMeld

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

theorem toDomainPair_tiles (pair : Toitsu) :
    (toDomainPair pair).tiles =
      Multiset.ofList (pair.tiles.map toDomainTile) := by
  cases pair with
  | toitsu localTile =>
      simp [toDomainPair, Toitsu.tiles, MahjongDomain.Pair.tiles,
        Multiset.replicate]

theorem toDomainPair_count (pair : Toitsu) (tile : MahjongDomain.Tile) :
    (toDomainPair pair).tiles.count tile = pair.tiles.count (ofDomainTile tile) := by
  rw [toDomainPair_tiles]
  calc
    (Multiset.ofList (pair.tiles.map toDomainTile)).count tile =
        (pair.tiles.map toDomainTile).count tile :=
      ofList_count_eq_list_count _ _
    _ = pair.tiles.count (ofDomainTile tile) := toDomainTileList_count _ _

theorem toDomainMeld_tiles (meld : MentsuCandidate) :
    (toDomainMeld meld).tiles =
      Multiset.ofList (meld.tiles.map toDomainTile) := by
  cases meld with
  | shuntsu shuntsu =>
      cases shuntsu with
      | shuntsu suit start =>
          cases suit <;>
            simp [toDomainMeld, MentsuCandidate.tiles, Shuntsu.tiles,
              ShuntsuStart.firstRank, ShuntsuStart.middleRank,
              ShuntsuStart.lastRank, MahjongDomain.Meld.tiles,
              toDomainTile, toDomainSuit]
  | koutsu localTile =>
      simp [toDomainMeld, MentsuCandidate.tiles, MahjongDomain.Meld.tiles,
        Multiset.replicate]

theorem toDomainMeld_count (meld : MentsuCandidate) (tile : MahjongDomain.Tile) :
    (toDomainMeld meld).tiles.count tile = meld.tiles.count (ofDomainTile tile) := by
  rw [toDomainMeld_tiles]
  calc
    (Multiset.ofList (meld.tiles.map toDomainTile)).count tile =
        (meld.tiles.map toDomainTile).count tile :=
      ofList_count_eq_list_count _ _
    _ = meld.tiles.count (ofDomainTile tile) := toDomainTileList_count _ _

theorem toDomainMelds_count (melds : List MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    MahjongDomain.MeldList.counts (toDomainMelds melds) tile =
      (melds.flatMap MentsuCandidate.tiles).count (ofDomainTile tile) := by
  induction melds with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change MahjongDomain.MeldList.counts
          (toDomainMeld first :: toDomainMelds rest) tile = _
      rw [MahjongDomain.MeldList.counts_cons]
      simp only [List.flatMap_cons, List.count_append]
      rw [toDomainMeld_count, inductionHypothesis]

@[simp] theorem ofDomainMelds_toDomainMelds (melds : List MentsuCandidate) :
    ofDomainMelds (toDomainMelds melds) = melds := by
  simp [ofDomainMelds, toDomainMelds, List.map_map, Function.comp_def]

@[simp] theorem toDomainMelds_ofDomainMelds (melds : List MahjongDomain.Meld) :
    toDomainMelds (ofDomainMelds melds) = melds := by
  simp [ofDomainMelds, toDomainMelds, List.map_map, Function.comp_def]

def toDomainDecomposition (pair : Toitsu) (melds : List MentsuCandidate) :
    MahjongDomain.StandardDecomposition :=
  { pair := toDomainPair pair
    melds := toDomainMelds melds }

def ofDomainDecomposition (decomposition : MahjongDomain.StandardDecomposition) :
    Toitsu × List MentsuCandidate :=
  (ofDomainPair decomposition.pair, ofDomainMelds decomposition.melds)

@[simp] theorem ofDomainDecomposition_toDomainDecomposition
    (pair : Toitsu) (melds : List MentsuCandidate) :
    ofDomainDecomposition (toDomainDecomposition pair melds) = (pair, melds) := by
  simp [ofDomainDecomposition, toDomainDecomposition]

@[simp] theorem toDomainDecomposition_ofDomainDecomposition
    (decomposition : MahjongDomain.StandardDecomposition) :
    toDomainDecomposition (ofDomainDecomposition decomposition).1
      (ofDomainDecomposition decomposition).2 = decomposition := by
  cases decomposition with
  | mk pair melds => simp [ofDomainDecomposition, toDomainDecomposition]

end Mahjong.DomainAdapter
