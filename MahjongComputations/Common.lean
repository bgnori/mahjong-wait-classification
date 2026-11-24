module

public import Mahjong.DirectWaitGeneration
public import Std.Data.HashMap
public import MahjongComputations.TileMultisets
public import MahjongComputations.WaitCompletionGrouping
public import MahjongComputations.WaitCoreReduction
public import MahjongComputations.WaitPathology
public import MahjongComputations.WaitDecompositionReporting
public import MahjongComputations.WaitReportFormatting

public meta import Mahjong.DirectWaitGeneration
public meta import Std.Data.HashMap
public meta import MahjongComputations.TileMultisets
public meta import MahjongComputations.WaitCompletionGrouping
public meta import MahjongComputations.WaitCoreReduction
public meta import MahjongComputations.WaitPathology
public meta import MahjongComputations.WaitDecompositionReporting
public meta import MahjongComputations.WaitReportFormatting

@[expose] public section

/-!
# 麻雀計算モジュールの共通import

既存の計算モジュール向けに、共有される牌姿生成・分類・レポート処理を再exportする。
個別の依存を明確にする新しいコードでは、責務ごとのモジュールを直接importする。
-/