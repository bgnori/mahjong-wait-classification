# wait-classification Lean回帰テスト分離の実施計画

作成日: 2026-11-24

この文書は、統括repoの[Lean回帰テスト階層化方針](https://github.com/bgnori/mahjong-workspace/blob/main/docs/lean-regression-test-policy-2026-11-24.md)をwait-classificationへ適用する具体計画です。suite分類、CI完全性、計測の共通原則は統括文書を正本とし、ここではこのrepoの対象・計測値・target・手順を記録します。

## 現状と計測

- [`MahjongTests.lean`](../MahjongTests.lean) は `MahjongTests.WaitDecompositionCode` を通常のsuiteへimportしています。
- [CI workflow](../.github/workflows/checks.yml) は `lake build Mahjong MahjongTests` に加えてexhaustive targetをbuildし、IO executableを実行します。
- 分離前の[`MahjongTests/WaitDecompositionCode.lean`](../MahjongTests/WaitDecompositionCode.lean)は、小さい境界例と4牌・7牌・10牌の分類・病理条件を同じmoduleで評価していました。
- Lean serverを停止し、既存依存成果物を使って当該ファイルを未キャッシュの出力先へ新規コンパイル・評価した時間は**3分41.064秒**でした。コマンドは `lake env lean MahjongTests/WaitDecompositionCode.lean -o /tmp/WaitDecompositionCode-fresh.olean`、終了コードは0です。
- その後の`lake build MahjongTests.WaitDecompositionCode`は既存成果物を再利用して**1.229秒**でした。これはwarm-cache時間で、cold評価とは区別します。
- 分離後、fresh outputへのfast module直接compileは**21.750秒**、exhaustive targetのbuildは**3分27.216秒**でした。いずれもLean 4.35.0、`LEAN_NUM_THREADS=2`、4 vCPU、Lean serverなし、既存依存成果物ありで計測しました。cgroup上限はRAM 6 GiB・swap 6 GiB、計測時の使用量はRAM約2.91 GiB・swap 0でした。
- profiler計測では、7牌の一様性証明が**195.178秒**、7牌の具体的反例が**0.139秒**、10牌の反例条件が**4.939秒**、生成例・クラス数のassertionが**7.604秒**でした。宣言別時間はprofilerの累積表示の差分です。
- Pagesに表示された約4.2秒はレポート生成時の別のruntime計測であり、このLeanファイルのcold compile/evaluation時間とは比較しません。

## 分離後の構成

profiler実測に基づき、約195秒を要する「生成された既約7牌すべてで分類が病理度を決定する」命題だけをexhaustive suiteへ移しました。短い7牌反例、10牌の反例条件、生成例・クラス数assertion、4牌の一様性命題はfast suiteに残しています。証明内容、assertion、期待値は変更していません。

Lean module構成:

- `MahjongTests.WaitDecompositionCode`: 局所例と、実測で短かった分類検査。
- `MahjongTests.WaitDecompositionCodeExhaustive`: 約195秒の全列挙一様性検査。
- exhaustive moduleはfast moduleをimportし、追加fixture moduleは設けていません。

`MahjongTests.lean`はfast suiteのみをimportし、exhaustive moduleは独立してbuildできるようにします。計算本体、公開API、定理の意味、期待値は変更しません。

## CI

CIでは従来のtoolchain pin、proof-hole検査、Core依存検査を維持したうえで、fast suiteのbuild後にexhaustive moduleを独立buildします。また、Lean moduleのbuildだけでは実行されないIOテストをexecutableとして起動します。

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
- fresh outputへのfast module compileが約22秒で、統括方針の目安である約60秒以内。
- cold/warmを区別して記録する。fastはfresh module output、exhaustiveは独立target buildとして計測する。
- CIで完全回帰が成功し、wait-core・可約性・病理分類の意味と出力が不変である。

## 対象外

- `WaitCore`、可約性、病理分類の意味や計算アルゴリズムの変更。
- `native_decide`を削除し、保証を弱めた通常例へ置き換えること。
- suite分離後の計測で必要性が確認される前の探索順・性能最適化。
