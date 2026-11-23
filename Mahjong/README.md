# Mahjong Modules

This directory contains the Mahjong formalization used as the main Lean study exercise in this repository.

## Reading Order

1. `Basic.lean`
   - Mahjong tile kinds: suits, ranks, honors, and tile formatting.
   - Tile formatting helpers.

2. `Pattern.lean`
   - Shared tile-pattern machinery.
   - Shared pairs, shuntsu, mentsu candidates, and winning components.

3. `Hand.lean`
   - Hand sizes and Int34-equivalent tile-kind counts.
   - Projection from counts to the canonical tile-type list.

4. `WaitCompletion.lean`
   - The `WaitCompletion` data type: one wait tile and one winning partition.
   - Winning components and their canonical ordering.

5. `WaitCompletionFinder.lean`
   - Shared semantics: `IsStandardAgari`, `IsWaitFor`, `IsTenpai`, and `Wait`.
   - Legal tenpai sizes and physical copy-count validation.
   - `WaitCompletionFinder.findWaitCompletions` and executable completion discovery.

6. `WaitDecompositionCode.lean`
   - Decomposes and codes already-found `List WaitCompletion` values without performing discovery.
   - `find...` convenience functions explicitly compose `WaitCompletionFinder` with coding.
   - Computes evidence-indexed reducibility for concrete tenpai hands.
   - The 53 one-suit irreducible seven-tile examples.

7. `DirectWaitGeneration.lean`
   - Generates normalized wait derivations directly from completed winning shapes.
   - Proves exact correspondence with `WaitCompletionFinder` in the standard-hand range.
   - Provides a noncomputable perfect-hash specification between all derivations and finite indices.

8. `Tenpai.lean`
   - A thin bridge from count-based `Hand` values to the single semantic `Wait` type.

`TenhouInput.lean` is an optional input-boundary module. It decodes raw Tenhou
IDs through `MahjongDomain.Tenhou` and constructs count-based hands; the core
wait-classification modules do not depend on Tenhou IDs.

## Import Entry Points

Use the top-level module when you want the whole Mahjong development:

```lean
import Mahjong
```

For focused work, import the smallest module that contains the definitions you need:

```lean
import Mahjong.WaitCompletionFinder
import Mahjong.WaitDecompositionCode
```

## Validation

```bash
lake build Mahjong
```

The computational regression tests are kept out of the production library so
that normal builds do not repeatedly compile `native_decide` proofs:

```bash
lake build MahjongTests
```

Expensive exhaustive computations are also separated from the production
library:

```bash
lake build MahjongComputations
```

To write the four-tile exhaustive report:

```bash
lake build fourTileReport
```

For a single file:

```bash
lake env lean Mahjong/WaitCompletionFinder.lean
```

## Development Notes

Keep small proof examples near the definitions they explain. Put expensive
`native_decide` regression tests under `MahjongTests/` so they are checked by
the explicit test target without slowing normal library builds. Put broader
enumerations and exploratory computations under `MahjongComputations/`.

For the full documentation policy, see [docs/documentation-policy.md](../docs/documentation-policy.md).
