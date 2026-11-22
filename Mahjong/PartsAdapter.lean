import Mahjong.DomainAdapter
import Mahjong.Pattern
import MahjongDomain.Parts

/-!
# Adapter for shared standard-hand parts

These conversions preserve the classification-side constructors and ordering
while relating each pair and mentsu candidate to the shared domain types.
-/

namespace Mahjong.DomainAdapter

def toDomainMentsuCandidate : MentsuCandidate → MahjongDomain.MentsuCandidate
  | .shuntsu (.shuntsu suit start) =>
      .shuntsu ⟨toDomainSuit suit, start⟩
  | .koutsu tile => .koutsu (toDomainTile tile)

def ofDomainMentsuCandidate : MahjongDomain.MentsuCandidate → MentsuCandidate
  | .shuntsu shuntsu =>
      .shuntsu (.shuntsu (ofDomainSuit shuntsu.suit) shuntsu.start)
  | .koutsu tile => .koutsu (ofDomainTile tile)

@[simp] theorem ofDomainMentsuCandidate_toDomainMentsuCandidate
    (candidate : MentsuCandidate) :
    ofDomainMentsuCandidate (toDomainMentsuCandidate candidate) = candidate := by
  cases candidate with
  | shuntsu shuntsu =>
      cases shuntsu with
      | shuntsu suit start => cases suit <;> rfl
  | koutsu tile =>
      simp [toDomainMentsuCandidate, ofDomainMentsuCandidate, ofDomainTile_toDomainTile]

@[simp] theorem toDomainMentsuCandidate_ofDomainMentsuCandidate
    (candidate : MahjongDomain.MentsuCandidate) :
    toDomainMentsuCandidate (ofDomainMentsuCandidate candidate) = candidate := by
  cases candidate with
  | shuntsu shuntsu =>
      cases shuntsu with
      | mk suit start => cases suit <;> rfl
  | koutsu tile =>
      simp [toDomainMentsuCandidate, ofDomainMentsuCandidate, toDomainTile_ofDomainTile]

def toDomainMentsuCandidates (candidates : List MentsuCandidate) :
    List MahjongDomain.MentsuCandidate :=
  candidates.map toDomainMentsuCandidate

def ofDomainMentsuCandidates (candidates : List MahjongDomain.MentsuCandidate) :
    List MentsuCandidate :=
  candidates.map ofDomainMentsuCandidate

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
  calc
    (Multiset.ofList ((ClassificationPair.tiles pair).map toDomainTile)).count tile =
        ((ClassificationPair.tiles pair).map toDomainTile).count tile :=
      ofList_count_eq_list_count _ _
    _ = (ClassificationPair.tiles pair).count (ofDomainTile tile) := toDomainTileList_count _ _

theorem toDomainMentsuCandidate_tiles (candidate : MentsuCandidate) :
    (toDomainMentsuCandidate candidate).tiles =
      Multiset.ofList (candidate.tiles.map toDomainTile) := by
  cases candidate with
  | shuntsu shuntsu =>
      cases shuntsu with
      | shuntsu suit start =>
          cases suit <;>
            simp [toDomainMentsuCandidate, MentsuCandidate.tiles, Shuntsu.tiles,
              ShuntsuStart.firstRank, ShuntsuStart.middleRank,
              ShuntsuStart.lastRank, MahjongDomain.MentsuCandidate.tiles,
              MahjongDomain.Shuntsu.tiles,
              toDomainTile, toDomainSuit]
  | koutsu localTile =>
      simp [toDomainMentsuCandidate, MentsuCandidate.tiles,
        MahjongDomain.MentsuCandidate.tiles,
        Multiset.replicate]

theorem toDomainMentsuCandidate_count (candidate : MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    (toDomainMentsuCandidate candidate).tiles.count tile =
      candidate.tiles.count (ofDomainTile tile) := by
  rw [toDomainMentsuCandidate_tiles]
  calc
    (Multiset.ofList (candidate.tiles.map toDomainTile)).count tile =
        (candidate.tiles.map toDomainTile).count tile :=
      ofList_count_eq_list_count _ _
    _ = candidate.tiles.count (ofDomainTile tile) := toDomainTileList_count _ _

theorem toDomainMentsuCandidates_count (candidates : List MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    MahjongDomain.MentsuCandidateList.counts (toDomainMentsuCandidates candidates) tile =
      (candidates.flatMap MentsuCandidate.tiles).count (ofDomainTile tile) := by
  induction candidates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change MahjongDomain.MentsuCandidateList.counts
          (toDomainMentsuCandidate first :: toDomainMentsuCandidates rest) tile = _
      rw [MahjongDomain.MentsuCandidateList.counts_cons]
      simp only [List.flatMap_cons, List.count_append]
      rw [toDomainMentsuCandidate_count, inductionHypothesis]

@[simp] theorem ofDomainMentsuCandidates_toDomainMentsuCandidates
    (candidates : List MentsuCandidate) :
    ofDomainMentsuCandidates (toDomainMentsuCandidates candidates) = candidates := by
  simp [ofDomainMentsuCandidates, toDomainMentsuCandidates, List.map_map, Function.comp_def]

@[simp] theorem toDomainMentsuCandidates_ofDomainMentsuCandidates
    (candidates : List MahjongDomain.MentsuCandidate) :
    toDomainMentsuCandidates (ofDomainMentsuCandidates candidates) = candidates := by
  simp [ofDomainMentsuCandidates, toDomainMentsuCandidates, List.map_map, Function.comp_def]

def toDomainDecomposition (pair : MahjongDomain.Pair) (candidates : List MentsuCandidate) :
    MahjongDomain.StandardDecomposition :=
  { pair := pair
    mentsuCandidates := toDomainMentsuCandidates candidates }

end Mahjong.DomainAdapter
