# wait-classification Lean回帰テスト分離の実施計画

作成日: 2026-11-24

この文書は、統括repoの[Lean回帰テスト階層化方針](https://github.com/bgnori/mahjong-workspace/blob/main/docs/lean-regression-test-policy-2026-11-24.md)をwait-classificationへ適用する具体計画です。suite分類、CI完全性、計測の共通原則は統括文書を正本とし、ここではこのrepoの対象・計測値・target・手順を記録します。

## 現状と計測

- [`MahjongTests.lean`](../MahjongTests.lean) は `MahjongTests.WaitDecompositionCode` を通常のsuiteへimportしています。
- [CI workflow](../.github/workflows/checks.yml) は `lake build Mahjong MahjongTests` を実行します。
- [`MahjongTests/WaitDecompositionCode.lean`](../MahjongTests/WaitDecompositionCode.lean) には小さい境界例のほか、4牌・7牌・10牌の分類・病理条件を`native_decide`で評価する例があります。7牌の全列挙や10牌の反例などが含まれます。ファイル全体の3分41秒をどの宣言が占めるかは未計測です。
- Lean serverを停止し、既存依存成果物を使って当該ファイルを未キャッシュの出力先へ新規コンパイル・評価した時間は**3分41.064秒**でした。コマンドは `lake env lean MahjongTests/WaitDecompositionCode.lean -o /tmp/WaitDecompositionCode-fresh.olean`、終了コードは0です。
- その後の`lake build MahjongTests.WaitDecompositionCode`は既存成果物を再利用して**1.229秒**でした。これはwarm-cache時間で、cold評価とは区別します。
- Pagesに表示された約4.2秒はレポート生成時の別のruntime計測であり、このLeanファイルのcold compile/evaluation時間とは比較しません。

## 対象と構成案

まず`WaitDecompositionCode.lean`内の`native_decide`を宣言単位または小さなまとまり単位で計測し、fastに残す境界例とexhaustiveへ移す宣言を確定します。移動候補は、7牌全列挙に依存する一様性・病理分類、10牌の全反例条件、列挙から作る代表例・クラス数のassertionです。実測が短い例は通常suiteに残します。

推奨するLean module構成:

- `MahjongTests.WaitDecompositionCode`: 小さな例と局所的な回帰確認。
- `MahjongTests.WaitDecompositionCodeExhaustive`: 高コストの全列挙・`native_decide`検査。
- 必要な場合だけ`MahjongTests.WaitDecompositionFixtures`を追加し、共用牌姿・補助定義を最小限まとめます。

`MahjongTests.lean`はfast suiteのみをimportし、exhaustive moduleは独立してbuildできるようにします。計算本体、公開API、定理の意味、期待値は変更しません。

## 実施手順

1. `WaitDecompositionCode.lean`の高コスト候補を個別に測り、3分41秒の内訳を取ります。計測条件は統括方針に従い、Lean version、cache状態、Lean serverの有無、CPU/worker数、memory limit、swapを記録します。
2. fastに残す例とexhaustiveへ移す検査を確定し、必要最小限のfixtureとともに移動します。
3. `MahjongTests.lean`からexhaustive moduleへの依存を外し、`lake build Mahjong MahjongTests`が日常のfast suiteになるようにします。
4. CIにexhaustive moduleを明示的に追加します。既存workflowのproof-hole検査、Lean toolchain pin、Core依存検査は維持します。
5. `MahjongTests/ParallelComputation.lean`と`MahjongTests/ExternalWaitCompletion.lean`のIOテストはbuildだけで実行済みとせず、CIで次のexecutableも起動します。

```sh
lake exe external-wait-completion-test
lake exe parallel-computation-test
```

## 実行入口

日常のfast確認:

```sh
lake build Mahjong MahjongTests
```

exhaustiveを含む完全確認:

```sh
lake build Mahjong MahjongTests MahjongTests.WaitDecompositionCodeExhaustive
lake exe external-wait-completion-test
lake exe parallel-computation-test
```

exhaustive moduleだけを変更した場合は、fast suiteのbuildだけでその変更を検証済みとは扱わず、exhaustive targetも実行します。

## 完了条件

- `lake build Mahjong MahjongTests`の依存グラフに高コストの全列挙検査が含まれない。
- 現在の全assertionをfast/exhaustiveのどちらかで維持し、削除・弱化しない。
- CIがfast suite、exhaustive module、外部形式と並列計算のIO executableを検査する。
- 同じ環境でcold/warmを分けて計測し、fast suiteのcold feedbackが現状の3分41秒より明確に短い。統括方針の目安である約60秒以内を目標とする。
- CIで完全回帰が成功し、wait-core・可約性・病理分類の意味と出力が不変である。

## 対象外

- `WaitCore`、可約性、病理分類の意味や計算アルゴリズムの変更。
- `native_decide`を削除し、保証を弱めた通常例へ置き換えること。
- suite分離後の計測で必要性が確認される前の探索順・性能最適化。
