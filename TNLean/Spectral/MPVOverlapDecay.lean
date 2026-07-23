/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Spectral.TransferOperatorGapInjective

/-!
# MPV overlap decay

Compatibility import for the injective overlap-decay API.  The declarations
`mpvOverlap_tendsto_zero` and `mpvInner_tendsto_zero` now live in the downstream
leaf `TransferOperatorGapInjective`, where they are immediate consequences of
the irreducible-tensor results in `TransferOperatorGapNT`.
-/
