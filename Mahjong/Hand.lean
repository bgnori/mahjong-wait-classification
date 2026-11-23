import Mahjong.Pattern

open MahjongDomain (Tile Rank Honor TileFormat)

/-!
# 手牌

このモジュールでは、牌種ごとのカウントとしての手牌と、通常形の意味論が扱う
牌種列への変換を定義する。

通常形では、聴牌時の手牌枚数は `3n + 1` になる。ここでは学習対象として
1枚、4枚、7枚、10枚、13枚の手牌だけを扱う。
-/
/-- Int34相当の牌種カウントで表す通常形の聴牌手牌。 -/
structure Hand where
  mentsuCount : Fin (standardHandMentsuCount + 1)
  counts : MahjongDomain.TileCounts
  counts_valid : counts.Valid
  total_tiles :
    (∑ tile : Tile, counts tile) = standardTenpaiHandSize mentsuCount

namespace Hand

/-- Count-based handを通常形の意味論が扱う標準順の牌種列へ変換する。 -/
def tileTypes (hand : Hand) : List MahjongDomain.Tile :=
  Tile.all.flatMap fun tile => List.replicate (hand.counts tile) tile

end Hand
