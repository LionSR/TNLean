/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition

/-!
# Cyclic decomposition auxiliary wrapper

This module is a compatibility wrapper that re-exports
`TNLean.Channel.Peripheral.CyclicDecomposition`.

Historically, the peripheral-unitary/corner infrastructure lived here and was
later merged into the main cyclic decomposition file; downstream imports of
`CyclicDecompositionAux` should continue to work unchanged.
-/
