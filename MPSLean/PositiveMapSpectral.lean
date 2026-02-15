/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.Channel.PositiveMap
import MPSLean.Channel.KadisonSchwarz
import MPSLean.Channel.CesaroFixedPoint
import MPSLean.Channel.Irreducible

/-!
# Spectral theory of positive maps — re-export hub

This file re-exports the Channel/ submodules for backwards compatibility.
The actual content lives in:

* `Channel.PositiveMap`: positive maps, density matrices, channels
* `Channel.KadisonSchwarz`: Kadison–Schwarz inequality, HS contraction
* `Channel.CesaroFixedPoint`: Cesàro mean fixed point existence

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6][Wolf2012QChannels]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
-/

/-! ## Existence of PSD eigenvector (Wolf Theorem 6.5 sketch)

For general CP maps (not necessarily trace-preserving), we need a different
approach. The key idea from Wolf is the **density argument**:

1. Perturb `E` to `E_ε = (1-ε)E + ε·D` where `D` is the depolarizing channel.
2. `E_ε` is trace-preserving (if we normalize appropriately) and irreducible.
3. By the Cesàro mean theorem, `E_ε` has a PSD fixed point `ρ_ε`.
4. By our PD theorem (irreducible case), `ρ_ε` is actually PD.
5. Take `ε → 0` and extract a limit.

This will be developed in a future extension.
-/
