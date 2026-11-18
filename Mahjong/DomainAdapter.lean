import Mahjong.Basic
import MahjongDomain.Tile
import Mathlib.Tactic.FinCases

/-!
# Adapter for the shared Mahjong domain

The classification API keeps its named rank and honor types. These conversions
make the correspondence with the shared normalized tile model explicit.
-/

namespace Mahjong.DomainAdapter

def toDomainSuit : Suit → MahjongDomain.Suit
  | .Manzu => .man
  | .Pinzu => .pin
  | .Souzu => .sou

def ofDomainSuit : MahjongDomain.Suit → Suit
  | .man => .Manzu
  | .pin => .Pinzu
  | .sou => .Souzu

theorem ofDomainSuit_toDomainSuit (suit : Suit) :
    ofDomainSuit (toDomainSuit suit) = suit := by
  cases suit <;> rfl

theorem toDomainSuit_ofDomainSuit (suit : MahjongDomain.Suit) :
    toDomainSuit (ofDomainSuit suit) = suit := by
  cases suit <;> rfl

def toDomainHonor : Honor → MahjongDomain.Honor
  | .East => 0
  | .South => 1
  | .West => 2
  | .North => 3
  | .White => 4
  | .Green => 5
  | .Red => 6

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

def toDomainTile : Tile → MahjongDomain.Tile
  | .numbered suit rank => .suited (toDomainSuit suit) rank
  | .honor honor => .honor (toDomainHonor honor)

def ofDomainTile : MahjongDomain.Tile → Tile
  | .suited suit rank => .numbered (ofDomainSuit suit) rank
  | .honor honor => .honor (ofDomainHonor honor)

theorem ofDomainTile_toDomainTile (tile : Tile) :
    ofDomainTile (toDomainTile tile) = tile := by
  cases tile with
  | numbered suit rank => cases suit <;> rfl
  | honor honor => cases honor <;> rfl

theorem toDomainTile_ofDomainTile (tile : MahjongDomain.Tile) :
    toDomainTile (ofDomainTile tile) = tile := by
  cases tile with
  | suited suit rank => cases suit <;> rfl
  | honor honor => simp [toDomainTile, ofDomainTile, toDomainHonor_ofDomainHonor]

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
        simp [toDomainTile, toDomainSuit, MahjongDomain.Tile.index, Tile.orderKey,
          Suit.orderKey, Suit.all, numberedRankCount]
  | honor honor =>
      cases honor <;>
        simp [toDomainTile, toDomainHonor, MahjongDomain.Tile.index, Tile.orderKey,
          Tile.numberedCount, Suit.count, Suit.all, Honor.orderKey, Honor.all,
          numberedRankCount]

end Mahjong.DomainAdapter
