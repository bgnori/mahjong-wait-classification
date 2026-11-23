module

public import Mahjong.Hand
public import Mahjong.WaitCompletionFinder

@[expose] public section

/-!
# 聴牌の証拠

`Tenpai hand` は、手牌を牌種列へ写した上で `WaitCompletionFinder.Wait` に結び付ける。
待ちの意味論は手牌枚数によらず共通であり、4枚・7枚専用の証拠型は使わない。
-/

/-- カウント表現の手牌に結び付いた、通常形の待ちの証拠。 -/
abbrev Tenpai (hand : Hand) := WaitCompletionFinder.Wait hand.tileTypes
