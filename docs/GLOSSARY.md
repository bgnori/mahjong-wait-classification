# Mahjong Wait Classification Glossary / 麻雀待ち分類用語集

This glossary records terminology specific to wait classification, including
decomposition, ordering, and reducibility. Shared tile and standard-hand
definitions are canonical in the [Mahjong Domain Core glossary](https://github.com/bgnori/mahjong-domain-core/blob/main/docs/GLOSSARY.md).

この文書は、待ち分類固有の分解・順序・可約性の語彙と、共通用語との意味差を記録します。
Leanの構文やタクティクは [lean-vocabulary.md](lean-vocabulary.md) を参照してください。

牌種、136物理牌ID、Int37／34種表現、カウント集約、牌種容量の共通定義は、
[Mahjong Domain Coreの用語集](https://github.com/bgnori/mahjong-domain-core/blob/main/docs/GLOSSARY.md)
を正本とします。
分類はCoreのスート、牌種、表示形式と `PhysicalTileId` を直接利用する。
物理牌IDはTenhou順で、商が牌種index、余りがcopy番号である。
牌種の4枚則はCoreの`copiesPerTile`、`TileCounts.Valid`と`TileCounts.CanAdd`を使い、
この分類に渡された牌列を対象に適用する。

## Canonical shared-domain terms / 共通ドメイン用語の正本

対子・順子・刻子と雀頭1つ＋指定数の面子による通常形完成は、共通核の
`Pair`、`Shuntsu`、`MentsuCandidate`、`StandardDecomposition`、`StandardCompletion`を
正本とする。分類側は共有`Pair`、`Shuntsu`、`MentsuCandidate`を直接利用する。
順序付き展開はCoreの`Pair.orderedTiles`、`Shuntsu.orderedTiles`、
`MentsuCandidate.orderedTiles`を正本とし、順子はランク昇順とする。分類固有の
候補列挙は分類側に残す。牌種も共有型を直接使うため、展開時の牌種変換はない。
共有仕様との牌種多重度の一致と、分類の牌列順・候補列挙順・結果・重複数の維持を
別々に検証する。共有仕様への接続のために分類の列挙結果を正規化・重複除去しない。
`WinningPartitionSpec`は分類固有の分割仕様であり、単に名前を
揃えるためにCoreの完成仕様へ統合しない。

## Consumer-specific terms / 利用側固有用語

### Winning components / 和了構成部品

和了構成部品は、通常形の和了を雀頭1つと面子4つに分けたときの、分割済みの各部品を指す
このプロジェクトの説明語彙である。コード上では `WinningComponent` に対応する。

`WinningComponent := MahjongDomain.Pair ⊕ MahjongDomain.MentsuCandidate` なので、値は次のどれかである。

- 雀頭となる対子
- 完成面子となる順子
- 完成面子となる刻子

`Winning` は「その部品だけで和了している」という意味ではなく、通常形の和了分割を構成する側に
属することを示す。待ち牌を除いた後の単騎・対子・ターツのような観測成分は含まない。

### Canonical winning-component list / 和了構成部品列の標準順表現

和了分割は、内部探索では和了構成部品を並べた `List WinningComponent` として扱われる。
同じ和了構成部品を同じ個数だけ含むなら、リスト上の順番が違っても同じ和了分割として扱いたい。
この関係はコード上の `List.Perm` に対応する。

このプロジェクトで和了構成部品列の「標準順表現」というときは、次の範囲だけを指す。

- 対象: 和了分割を表す `List WinningComponent`
- 同一視する差: 和了構成部品のリスト上の順番
- 保存する情報: 各和了構成部品とその個数
- 代表の選び方: `WinningComponent.orderKey` の昇順
- 変換する関数: `WinningComponent.canonicalize`
- 公開結果の型: `CanonicalWinningComponents`

したがって、牌姿、待ち牌、和了分割の選び方まで同一視する一般的な「正規形」ではない。
`WinningComponent.canonicalize_eq_of_perm` が保証するのは、`List.Perm` の関係にある2列が同じ標準順表現へ
変換されることだけである。

`WaitCompletion.winningComponents` は `CanonicalWinningComponents` として保持される。
この型は、リスト本体と「そのリストが `WinningComponent.canonicalize` の結果と一致する」という証拠を持つ。
通常のリストとして処理したい場合は `CanonicalWinningComponents.toList` で取り出す。

### Wait decomposition / 待ち分解

待ち分解は、1つの待ち牌と、その牌を和了分割から1枚除いた後の部品列を表す。
コード上では `WaitDecomposition` に対応する。

名前の変換関係は次のように読む。

- `WinningComponent`: 待ち牌を除く前の、和了分割を構成する対子・順子・刻子。
- `WaitComponent`: 1つの `WinningComponent` から待ち牌を除いた結果、または除去せず完成形のまま保持した結果。
- `WaitComponentKind`: `WaitComponent` から具体的な牌種列を忘れた種別。
- `WaitDecomposition`: 待ち牌と、具体牌付きの `List WaitComponent` を持つ待ち分解。
- `WaitKindDecomposition`: 待ち牌と `List WaitComponentKind` を持つ、部品種別だけの待ち分解。
- `WaitCoreExtraction`: `WaitDecomposition` から完成面子を分離し、核成分列と除去した面子を保持した結果。

`WaitKindDecomposition` で忘れるのは `WaitComponent.tiles` だけであり、待ち牌と部品種別列は残る。

### Wait derivation / 待ち導出

待ち導出は、通常和了形、待ち牌を除く和了構成部品の位置、待ち牌を保持し、
完成形からテンパイ牌姿を得る根拠を表す。コード上では `DirectWaitGeneration.WaitDerivation` に対応する。

待ち分解が `WaitCompletion` を観測して得る結果であるのに対し、待ち導出は `WinningShape` から
`WaitCompletion` とテンパイ牌姿の両方を作れる生成証人である。この2つを同じ型や用語では扱わない。

変換の向きは次のようになる。

```text
WinningShape + selected WinningComponent + wait
	-> WaitDerivation
	-> WaitCompletion
	-> WaitDecomposition
	-> WaitKindDecomposition
	-> WaitDecompositionCode
```

### Wait decomposition code / 待ち分解コード

待ち分解コードは、待ち分解に含まれる部品種別の多重集合を1つの自然数で表す内部表現である。
コード上では `WaitDecompositionCodeEntry.code` に対応する。

各 `WaitComponentKind` に異なる素数を割り当て、待ち分解に現れるすべての部品の素数を掛け合わせる。
積は部品の並び順を区別しないが、同じ種別が複数あれば、その個数は対応する素因数の指数として残る。

例:

- 単騎と順子1つ: $2 \times 13 = 26$
- 単騎と順子2つ: $2 \times 13^2 = 338$

`WaitDecompositionCodeEntry` は、このコードと待ち牌を組にして保持する。
`waitDecompositionCodes` でコード単体へ変換すると待ち牌も忘れるため、両者を区別して読む。
コード単体の一致が表すのは部品種別の多重集合の一致だけであり、待ち牌、具体牌、元の牌姿の一致ではない。
同じ待ち牌とコードの組は重複除去されるが、異なる待ち牌から同じコードが得られた場合は、
その重複が `waitDecompositionCodes` のコード列に残る。したがって、このコード列は集合ではなく多重集合である。

### Wait core / 待ち核

待ち核は、このプロジェクトで「1つの待ち牌」と「完成面子を除いたあとに残る核成分列」の組を指す説明語彙である。
コード上では `WaitCore` に対応する。`WaitCore` は `WaitDecomposition` の型別名であり、
完成面子を除去済みであることは `waitCores` までの生成経路が保証する。

数学でいう kernel ではなく、完成面子を削ったあとにも保存される、分類上の本質部分を表すために `core` という語を使う。

コード上の対応:

- `WaitCore.wait`: 待ち核に対応する待ち牌。
- `WaitCore.components`: 待ち牌を除いたあとに残る核成分列。
- `WaitCoreExtraction.core`: `WaitCore.components` に対応する核成分列。名前は `core` だが、待ち牌は含まない。
- `WaitCoreExtraction.removedMentsu`: 核から分離された完成面子。

例:

- 待ち牌 `1m` と核成分 `[単騎 1m]` の組は、1つの待ち核である。
- 待ち牌 `4m` と核成分 `[単騎 4m]` の組も、別の待ち核である。
- 待ち牌 `1m` と核成分 `[対子 55m, 両面ターツ 23m]` の組は、4枚の核成分列を持つ待ち核である。

`1/234` のような表記は、待ち核そのものではなく、完成面子 `234m` を分離して待ち牌 `1m` の待ち核を得る分解を表す。

### Wait-core set / 待ち核集合

1つの牌姿からは、複数の待ち核が得られることがある。
待ち核集合は、牌姿から得られる `WaitCore` の重複なし集合である。
同じ待ち牌に異なる核成分列が対応する場合もあり、それらは重複ではなく待ちの別解釈を表す。
たとえば `1223m` の `2m` 待ちは、単騎の核と、`22m` の雀頭および `13m` の嵌張からなる核を持つ。

コード上の対応:

- `findWaitCores`: 牌姿から得られる待ち核集合を計算する。
- `canReduceMentsuPreservingWaitCores`: 完成面子を取り除いても待ち核集合が変わらないかを判定する。

例:

`1234m` の待ち核集合には、次の2つが含まれる。

- 待ち牌 `1m`、核成分 `[単騎 1m]`
- 待ち牌 `4m`、核成分 `[単騎 4m]`

つまり、`1/234` と `123/4` は待ち核そのものではなく、2つの待ち核を得るための2つの分解である。

### Reducibility and irreducibility / 可約と既約

可約とは、完成面子を取り除いても待ち核集合が変わらないことを指す。
既約とは、そのような完成面子除去ができないことを指す。

対応するコード:

- `WaitReducibility`: 可約か既約かを表す分類ラベル。
- `WaitDecompositionCode.reducibility`: 聴牌の証拠を前提に可約性を計算する。
- `WaitDecompositionCode.canReduceMentsuPreservingWaitCores`: 待ち核集合を保ったまま完成面子を除去できるかをBoolで判定する。