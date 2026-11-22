module

public import Mahjong.Basic
public import MahjongDomain.Representation
public import MahjongDomain.Parts
import Mathlib.Tactic.FinCases

/-!
# Adapter for the shared Mahjong domain

The classification API keeps its named rank and honor types. These conversions
make the correspondence with the shared normalized tile model explicit.
-/

@[expose] public section

deriving instance BEq, ReflBEq, LawfulBEq, Repr for MahjongDomain.Tile

namespace Mahjong.DomainAdapter

def ofDomainHonor (rank : MahjongDomain.Honor) : Honor :=
  match rank.val with
  | 0 => .East
  | 1 => .South
  | 2 => .West
  | 3 => .North
  | 4 => .White
  | 5 => .Green
  | _ => .Red

theorem ofDomainHonor_toDomainHonor (honor : Honor) :
    ofDomainHonor (toDomainHonor honor) = honor := by
  cases honor <;> rfl

theorem toDomainHonor_ofDomainHonor (honor : MahjongDomain.Honor) :
    toDomainHonor (ofDomainHonor honor) = honor := by
  fin_cases honor <;> rfl

def ofDomainTile : MahjongDomain.Tile → Tile
  | .suited suit rank => .numbered suit rank
  | .honor honor => .honor (ofDomainHonor honor)

theorem ofDomainTile_toDomainTile (tile : Tile) :
    ofDomainTile (toDomainTile tile) = tile := by
  cases tile with
  | numbered suit rank => rfl
  | honor honor => cases honor <;> rfl

theorem toDomainTile_ofDomainTile (tile : MahjongDomain.Tile) :
    toDomainTile (ofDomainTile tile) = tile := by
  cases tile with
  | suited suit rank => rfl
  | honor honor => simp [toDomainTile, ofDomainTile, toDomainHonor_ofDomainHonor]

/-- Adapt Core's ordered pair expansion while classification still uses local tiles. -/
def pairTiles (pair : MahjongDomain.Pair) : List Tile :=
  pair.orderedTiles.map ofDomainTile

/-- Adapt Core's ordered meld expansion while classification still uses local tiles. -/
def mentsuTiles (candidate : MahjongDomain.MentsuCandidate) : List Tile :=
  candidate.orderedTiles.map ofDomainTile

theorem mentsuTiles_length (candidate : MahjongDomain.MentsuCandidate) :
    (mentsuTiles candidate).length = 3 := by
  cases candidate with
  | shuntsu pattern => cases pattern; rfl
  | koutsu tile => rfl

theorem flatMap_mentsuTiles_length (candidates : List MahjongDomain.MentsuCandidate) :
    (candidates.flatMap mentsuTiles).length = candidates.length * 3 := by
  induction candidates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [mentsuTiles_length, inductionHypothesis]
      simp [Nat.add_mul, Nat.add_comm]

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

theorem orderedTiles_count (tiles : List MahjongDomain.Tile) (tile : MahjongDomain.Tile) :
    (Multiset.ofList tiles).count tile = (tiles.map ofDomainTile).count (ofDomainTile tile) := by
  rw [← toDomainTileList_count, ofList_count_eq_list_count]
  simp [List.map_map, Function.comp_def, toDomainTile_ofDomainTile]

theorem pair_count (pair : MahjongDomain.Pair) (tile : MahjongDomain.Tile) :
    pair.tiles.count tile = (pairTiles pair).count (ofDomainTile tile) :=
  orderedTiles_count pair.orderedTiles tile

theorem mentsuCandidate_count (candidate : MahjongDomain.MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    candidate.tiles.count tile = (mentsuTiles candidate).count (ofDomainTile tile) :=
  orderedTiles_count candidate.orderedTiles tile

theorem mentsuCandidates_count (candidates : List MahjongDomain.MentsuCandidate)
    (tile : MahjongDomain.Tile) :
    MahjongDomain.MentsuCandidateList.counts candidates tile =
      (candidates.flatMap mentsuTiles).count (ofDomainTile tile) := by
  induction candidates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      rw [MahjongDomain.MentsuCandidateList.counts_cons]
      simp only [List.flatMap_cons, List.count_append]
      rw [mentsuCandidate_count, inductionHypothesis]

def toDomainCounts (counts : Tile → Nat) : MahjongDomain.TileCounts :=
  fun tile => counts (ofDomainTile tile)

def ofDomainCounts (counts : MahjongDomain.TileCounts) : Tile → Nat :=
  fun tile => counts (toDomainTile tile)

theorem ofDomainCounts_toDomainCounts (counts : Tile → Nat) :
    ofDomainCounts (toDomainCounts counts) = counts := by
  funext tile
  simp [ofDomainCounts, toDomainCounts, ofDomainTile_toDomainTile]

theorem toDomainCounts_ofDomainCounts (counts : MahjongDomain.TileCounts) :
    toDomainCounts (ofDomainCounts counts) = counts := by
  funext tile
  simp [toDomainCounts, ofDomainCounts, toDomainTile_ofDomainTile]

theorem tileIndex_val (tile : Tile) :
    (MahjongDomain.Tile.index (toDomainTile tile)).val = Tile.orderKey tile := by
  cases tile with
  | numbered suit rank =>
      cases suit <;>
        simp [toDomainTile, MahjongDomain.Tile.index, Tile.orderKey,
          suitOrderKey, MahjongDomain.Suit.all, numberedRankCount]
  | honor honor =>
      cases honor <;>
        simp [toDomainTile, toDomainHonor, MahjongDomain.Tile.index, Tile.orderKey,
          Tile.numberedCount, suitCount, MahjongDomain.Suit.all, Honor.orderKey, Honor.all,
          numberedRankCount]

/-- Convert a local physical tile to its stable 0-based Tenhou ID. -/
def toDomainPhysicalTileId (physical : PhysicalTile) : MahjongDomain.PhysicalTileId :=
  let index := MahjongDomain.Tile.index (toDomainTile physical.1)
  ⟨index.val * 4 + physical.2.val, by
    have hindex := index.isLt
    have hcopy : physical.2.val < 4 := by
      simpa only [copiesPerTile] using physical.2.isLt
    omega⟩

theorem toDomainPhysicalTileId_copy (physical : PhysicalTile) :
    (toDomainPhysicalTileId physical).val % 4 = physical.2.val := by
  simp [toDomainPhysicalTileId]

theorem toDomainPhysicalTileId_preserves_tile (physical : PhysicalTile) :
    MahjongDomain.PhysicalTileId.tile (toDomainPhysicalTileId physical) =
      toDomainTile physical.1 := by
  have hcopy : physical.2.val < 4 := by
    simpa only [copiesPerTile] using physical.2.isLt
  apply MahjongDomain.Tile.index_injective
  apply Fin.ext
  rw [MahjongDomain.PhysicalTileId.tile_index]
  simp [toDomainPhysicalTileId]
  omega

end Mahjong.DomainAdapter
