/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.StationarySupportCompression
import TNLean.MPS.ParentHamiltonian.FaithfulLocalStateSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalPrimitiveGap

/-!
# Local density supports of stationary MPS states

A normalized tensor and a nonzero positive stationary virtual matrix define a
quasi-local state. Compression to the stationary support gives faithful
normalized generators for the same finite expectations. Consequently each
finite interval restriction of the original state has a density whose range
is exactly the boundary space of the compressed tensor. The same density
represents every translation of that interval, including the empty interval.

**Scope restriction (supplied stationary generating data):** The tensor and
its nonzero positive stationary matrix are supplied. Constructing generating
data from an arbitrary GVBS boundary limit remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
The density range is identified with the compressed tensor boundary space;
no equality with the original tensor's full boundary space is asserted.

Source context: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), and the local density support identification at
lines 1724--1738 in Section 4.
-/

open SpinChain
open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d D : ℕ}

/-- Every translated finite restriction of a stationary MPS state has a density
supported exactly on the boundary space of its faithful support compression.
No ambient positive bond dimension, faithfulness, or primitivity is assumed.
The generating data themselves are supplied.
Source context: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b) and Section 4, lines 1724--1738. -/
theorem exists_faithful_quasiLocalExpectation_density_support_of_leftCanonical
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
    ∃ (E : ℕ) (hE : 0 < E) (V : Matrix (Fin D) (Fin E) ℂ)
      (B : MPSTensor d E) (σ : Matrix (Fin E) (Fin E) ℂ)
      (hB : IsLeftCanonical B),
      let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
      let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
      Vᴴ * V = 1 ∧ V * Vᴴ = hρ.supportProj ∧
      (∀ i, B i = Vᴴ * A i * V) ∧ σ = Vᴴ * ρ * V ∧
      σ.PosDef ∧ (∀ i, A i * V = V * B i) ∧ Kraus.map B σ = σ ∧
      Matrix.trace σ = Matrix.trace ρ ∧
      ∀ k : ℕ, ∃ τ : Matrix (Cfg d k) (Cfg d k) ℂ,
        τ.PosSemidef ∧ Matrix.trace τ = 1 ∧
        (∀ (a : ℤ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
          quasiLocalExpectation A hA hρ hFix htr
            (quasiLocalIntervalObservable d a k X) = Matrix.trace (τ * X)) ∧
        LinearMap.range (Matrix.toEuclideanLin τ) = groundSpaceES B k := by
  obtain ⟨E, hE, V, B, σ, hV, hVrange, hCorner, hσEq, hσ, hB,
    hInt, hσFix, hTrace, hInsertion⟩ :=
    exists_faithful_stationary_supportCompression_of_leftCanonical A hA hρ htr hFix
  let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
  let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
  refine ⟨E, hE, V, B, σ, hB, hV, hVrange, hCorner, hσEq,
    hσ, hInt, hσFix, hTrace, ?_⟩
  intro k
  obtain ⟨τ, hτ, hτTrace, hRep, hRange⟩ :=
    exists_quasiLocalExpectation_density_range_eq_groundSpaceES B hB hσ hσFix k
  refine ⟨τ, hτ, hτTrace, ?_, hRange⟩
  intro a X
  exact (quasiLocalExpectation_quasiLocalIntervalObservable A hA hρ hFix htr a X).trans
    ((hInsertion k X).trans
      ((quasiLocalExpectation_quasiLocalIntervalObservable B hB hσ.posSemidef
        hσFix (ne_of_gt hσ.trace_pos) a X).symm.trans (hRep a X)))

end MPSTensor
