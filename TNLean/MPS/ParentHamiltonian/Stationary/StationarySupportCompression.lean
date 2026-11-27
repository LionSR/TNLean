/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableInsertion
import TNLean.MPS.ParentHamiltonian.Stationary.FaithfulPeriodicGroundSpace
import QICLean.Channel.FixedPoint.Stationary.SupportInvariance
import QICLean.Channel.KrausMap.KrausCornerCompression
import QICLean.Analysis.Support.Compression
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalFaithfulSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalMultiblockGap
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableQuasiLocalState
import TNLean.MPS.Tensor.Defs

/-!
# Faithful generators from stationary support compression

Compressing a normalized tensor to the support of a nonzero positive
stationary matrix yields normalized generators with a faithful stationary
matrix. The support isometry intertwines every letter and every word;
consequently all finite insertion expectations agree before and after
compression. The conclusion concerns the state determined by the supplied
matrix, rather than the full boundary spaces of the original tensor.

**Scope restriction (supplied stationary generating data):** A normalized
tensor and a nonzero positive stationary matrix are supplied. No generating
representation of an arbitrary GVBS boundary limit is constructed here;
that separate passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1394--1467, the normalized generating representation, and Section 4,
lines 1724--1738, the faithful local support representation.
The support restriction is Wolf, restriction to full-rank fixed
points, equations (6.51)--(6.52).

## Local density supports of stationary MPS states

A normalized tensor and a nonzero positive stationary virtual matrix define a
quasi-local state. Compression to the stationary support gives faithful
normalized generators for the same finite expectations. Consequently each
finite interval restriction of the original state has a density whose range
is exactly the boundary space of the compressed tensor. The same density
represents every translation of that interval, including the empty interval.

**Scope restriction (supplied stationary generating data):** The tensor and
its nonzero positive stationary matrix are supplied. Constructing generating
data from an arbitrary GVBS boundary limit remains separate; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
The density range is identified with the compressed tensor boundary space;
no equality with the original tensor's full boundary space is asserted.

Source context: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), and the local density support identification at
lines 1724--1738 in Section 4.

It also contains the following results.

* `MPSTensor.quasiLocalExpectation_eq_of_forall_observableInsertionExpectation_eq`,
  `MPSTensor.exists_faithful_quasiLocalExpectation_supportCompression_of_leftCanonical`: equality of
  quasi-local MPS expectations.
-/

open MPTensor

section StationarySupportCompression

section

open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d D E k : ℕ}

/-- A letter intertwiner preserves expansion of virtual matrices under every
finite observable insertion. No isometry condition is required. Source context: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b). -/
theorem physicalObservableTransfer_intertwine
    (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hInt : ∀ i, A i * V = V * B i)
    (σ : Matrix (Fin E) (Fin E) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    physicalObservableTransfer A k X (V * σ * Vᴴ) =
      V * physicalObservableTransfer B k X σ * Vᴴ := by
  simp only [physicalObservableTransfer_apply, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hTerm :
      Kraus.evalWord A (List.ofFn s) * (V * σ * Vᴴ) *
          (Kraus.evalWord A (List.ofFn t))ᴴ =
        (Kraus.evalWord A (List.ofFn s) * V) * σ *
          (Kraus.evalWord A (List.ofFn t) * V)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hTerm, Kraus.evalWord_intertwine A B V hInt,
    Kraus.evalWord_intertwine A B V hInt]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Isometric intertwining and expansion of the virtual matrix preserve every
finite insertion expectation. No normalization or stationarity assumption is
needed for this identity. Source context: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b). -/
theorem observableInsertionExpectation_eq_of_isometric_intertwine
    (A : MPSTensor d D) (B : MPSTensor d E)
    (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ * V = 1)
    (hInt : ∀ i, A i * V = V * B i)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (σ : Matrix (Fin E) (Fin E) ℂ)
    (hExpand : ρ = V * σ * Vᴴ) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X := by
  rw [hExpand, observableInsertionExpectation,
    physicalObservableTransfer_intertwine A B V hInt, observableInsertionExpectation]
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul,
    Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- Compression to the support of a nonzero positive stationary matrix yields a
faithful stationary matrix for the compressed generators and preserves all finite
insertion expectations. No normalization of the tensor is needed. Only the state
associated with this virtual matrix is retained; no equality of the original and
compressed full boundary spaces is asserted.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 4,
lines 1724--1738; Wolf, restriction to full-rank fixed points,
equations (6.51)--(6.52). -/
theorem exists_faithful_stationary_supportCompression
    (A : MPSTensor d D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
    ∃ E : ℕ, 0 < E ∧ ∃ (V : Matrix (Fin D) (Fin E) ℂ)
      (B : MPSTensor d E) (σ : Matrix (Fin E) (Fin E) ℂ),
      Vᴴ * V = 1 ∧ V * Vᴴ = hρ.supportProj ∧
      (∀ i, B i = Vᴴ * A i * V) ∧ σ = Vᴴ * ρ * V ∧
      σ.PosDef ∧ (∀ i, A i * V = V * B i) ∧ Kraus.map B σ = σ ∧
      Matrix.trace σ = Matrix.trace ρ ∧
      ∀ (k : ℕ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
        observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X := by
  obtain ⟨hP, hLower⟩ := Kraus.lowerZero_of_posSemidef_fixedPoint A ρ hρ hFix
  obtain ⟨E, V, _hDimTrace, hV, hVrange⟩ := hP.exists_support_isometry
  let B : MPSTensor d E := fun i => Vᴴ * A i * V
  let σ : Matrix (Fin E) (Fin E) ℂ := Vᴴ * ρ * V
  have hExpand : V * σ * Vᴴ = ρ := by
    calc
      V * σ * Vᴴ = (V * Vᴴ) * ρ * (V * Vᴴ) := by
        simp only [σ, Matrix.mul_assoc]
      _ = ρ := by rw [hVrange, Kraus.stationaryProj_mul hρ, Kraus.mul_stationaryProj hρ]
  have hTrace : Matrix.trace σ = Matrix.trace ρ := by
    change Matrix.trace (Vᴴ * ρ * V) = Matrix.trace ρ
    rw [Matrix.trace_mul_cycle, hVrange, Kraus.stationaryProj_mul hρ]
  have hE : 0 < E := by
    by_contra hE
    have hZero : E = 0 := Nat.eq_zero_of_not_pos hE
    subst E
    exact htr (by simpa [σ] using hTrace.symm)
  have hPV : Kraus.stationaryProj hρ * V = V := by
    rw [← hVrange, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hInt : ∀ i, A i * V = V * B i := by
    intro i
    have h := congrArg (fun T => T * V) (hLower i)
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPV,
      Matrix.zero_mul] at h
    simpa only [B, ← hVrange, Matrix.mul_assoc] using sub_eq_zero.mp h
  have hσ : σ.PosDef := by
    simpa only [σ, Matrix.conjTranspose_conjTranspose] using
      hρ.compression_on_support_posDef (V := Vᴴ)
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hV)
        (by simpa only [Kraus.stationaryProj, Matrix.conjTranspose_conjTranspose]
          using hVrange)
  have hσFix : Kraus.map B σ = σ :=
    Kraus.map_compressed_fixedPoint A B V (Kraus.stationaryProj hρ) ρ
      (fun _ => rfl) hVrange
      (by rw [Kraus.stationaryProj_mul hρ, Kraus.mul_stationaryProj hρ]) hFix
  refine ⟨E, hE, V, B, σ, hV, hVrange, (fun _ => rfl), rfl, hσ, hInt, hσFix, hTrace, ?_⟩
  exact fun _ X => observableInsertionExpectation_eq_of_isometric_intertwine
    A B V hV hInt ρ σ hExpand.symm X

/-- Compression to the support of a nonzero positive stationary matrix yields
faithful stationary normalized generators and preserves all finite insertion
expectations. Only the state associated with this virtual matrix is retained;
no equality of the original and compressed full boundary spaces is asserted.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1394--1467, and Section 4, lines 1724--1738; Wolf, restriction to full-rank
fixed points, equations (6.51)--(6.52). -/
theorem exists_faithful_stationary_supportCompression_of_leftCanonical
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
    ∃ E : ℕ, 0 < E ∧ ∃ (V : Matrix (Fin D) (Fin E) ℂ)
      (B : MPSTensor d E) (σ : Matrix (Fin E) (Fin E) ℂ),
      Vᴴ * V = 1 ∧ V * Vᴴ = hρ.supportProj ∧
      (∀ i, B i = Vᴴ * A i * V) ∧ σ = Vᴴ * ρ * V ∧
      σ.PosDef ∧ IsLeftCanonical B ∧
      (∀ i, A i * V = V * B i) ∧ Kraus.map B σ = σ ∧
      Matrix.trace σ = Matrix.trace ρ ∧
      ∀ (k : ℕ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
        observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X := by
  obtain ⟨E, hE, V, B, σ, hV, hVrange, hB, hσdef, hσ, hInt, hσFix, hTrace, hObs⟩ :=
    exists_faithful_stationary_supportCompression A hρ htr hFix
  exact ⟨E, hE, V, B, σ, hV, hVrange, hB, hσdef, hσ,
    hA.of_isometry_intertwine B V hV hInt, hInt, hσFix, hTrace, hObs⟩

end MPSTensor

end

section

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
        LinearMap.range (Matrix.toEuclideanLin τ) = ((groundSpace B k).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  obtain ⟨E, hE, V, B, σ, hV, hVrange, hCorner, hσEq, hσ, hB,
    hInt, hσFix, hTrace, hInsertion⟩ :=
    exists_faithful_stationary_supportCompression_of_leftCanonical A hA hρ htr hFix
  let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
  let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
  refine ⟨E, hE, V, B, σ, hB, hV, hVrange, hCorner, hσEq,
    hσ, hInt, hσFix, hTrace, ?_⟩
  intro k
  obtain ⟨τ, hτ, hτTrace, hRep, hRange⟩ :=
    exists_quasiLocalExpectation_density_range_eq_map_groundSpace B hB hσ hσFix k
  refine ⟨τ, hτ, hτTrace, ?_, hRange⟩
  intro a X
  exact (quasiLocalExpectation_quasiLocalIntervalObservable A hA hρ hFix htr a X).trans
    ((hInsertion k X).trans
      ((quasiLocalExpectation_quasiLocalIntervalObservable B hB hσ.posSemidef
        hσFix (ne_of_gt hσ.trace_pos) a X).symm.trans (hRep a X)))

end MPSTensor

end

end StationarySupportCompression

section QuasiLocalExpectationEquality

/-!
## Equality of quasi-local MPS expectations

Equality of all finite insertion expectations for two normalized stationary
positive generating data sets implies equality of their continuous quasi-local
functionals. The bond dimensions may differ. In particular, compression to
the support of a nonzero positive stationary matrix preserves the actual
quasi-local state, as well as its finite insertion expectations.

**Scope restriction (supplied stationary generating data):** The support
compression consequence assumes a tensor and a nonzero positive stationary
matrix. It does not construct these generators from an arbitrary GVBS
boundary limit; that passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), and lines 1394--1467, the generating representation.
The functional equality is the uniqueness of continuous extension from the
finite observable algebras.
-/

open SpinChain
open scoped Matrix ComplexOrder BigOperators
namespace MPSTensor
variable {d D E : ℕ}

/-- Equality of every finite insertion expectation implies equality of the
continuous quasi-local state functionals, for possibly different bond
dimensions. No faithfulness or purity is required.
Source context: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), and uniqueness of continuous extension. -/
theorem quasiLocalExpectation_eq_of_forall_observableInsertionExpectation_eq
    [NeZero d] (A : MPSTensor d D) (hA : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hFix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (B : MPSTensor d E) (hB : ∑ i, (B i)ᴴ * B i = 1)
    {σ : Matrix (Fin E) (Fin E) ℂ} (hσ : σ.PosSemidef)
    (hσFix : Kraus.transferMap B σ = σ) (hσtr : Matrix.trace σ ≠ 0)
    (hInsertion : ∀ (k : ℕ) (X : Matrix (Cfg d k) (Cfg d k) ℂ),
      observableInsertionExpectation A ρ X = observableInsertionExpectation B σ X) :
    quasiLocalExpectation A hA hρ hFix htr =
      quasiLocalExpectation B hB hσ hσFix hσtr := by
  apply (localMPSState B hB hσ hσFix hσtr).quasiLocalFunctional_unique
    (quasiLocalExpectation A hA hρ hFix htr)
  intro Λ X
  rw [quasiLocalExpectation_quasiLocalObservable]
  exact hInsertion _ _

/-- Compression to the support of a nonzero positive stationary matrix gives
faithful normalized generators for the identical continuous quasi-local state.
The support isometry and exact compressed data are retained. No purity or
minimality is assumed.
Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.1)--(3.2b), and Wolf, restriction to full-rank fixed points. -/
theorem exists_faithful_quasiLocalExpectation_supportCompression_of_leftCanonical
    (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (htr : Matrix.trace ρ ≠ 0) (hFix : Kraus.map A ρ = ρ) :
    ∃ (E : ℕ) (hE : 0 < E) (V : Matrix (Fin D) (Fin E) ℂ)
      (B : MPSTensor d E) (σ : Matrix (Fin E) (Fin E) ℂ)
      (hB : IsLeftCanonical B) (hσ : σ.PosDef) (hσFix : Kraus.map B σ = σ),
      let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
      let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
      Vᴴ * V = 1 ∧ V * Vᴴ = hρ.supportProj ∧
      (∀ i, B i = Vᴴ * A i * V) ∧ σ = Vᴴ * ρ * V ∧
      (∀ i, A i * V = V * B i) ∧ Matrix.trace σ = Matrix.trace ρ ∧
      quasiLocalExpectation A hA hρ hFix htr =
        quasiLocalExpectation B hB hσ.posSemidef hσFix (ne_of_gt hσ.trace_pos) := by
  obtain ⟨E, hE, V, B, σ, hV, hVrange, hCorner, hσEq, hσ, hB,
    hInt, hσFix, hTrace, hInsertion⟩ :=
    exists_faithful_stationary_supportCompression_of_leftCanonical A hA hρ htr hFix
  let _ : NeZero E := ⟨Nat.ne_of_gt hE⟩
  let _ : NeZero d := ⟨hB.physDim_ne_zero⟩
  refine ⟨E, hE, V, B, σ, hB, hσ, hσFix, hV, hVrange,
    hCorner, hσEq, hInt, hTrace, ?_⟩
  exact quasiLocalExpectation_eq_of_forall_observableInsertionExpectation_eq
    A hA hρ hFix htr B hB hσ.posSemidef hσFix (ne_of_gt hσ.trace_pos) hInsertion

end MPSTensor

end QuasiLocalExpectationEquality
