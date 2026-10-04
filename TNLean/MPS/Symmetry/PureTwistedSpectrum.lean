/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StringOrder
import TNLean.MPS.Core.PhysicalRotation
import QICLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary
import QICLean.Channel.Peripheral.SpectralRadius
import QICLean.Channel.Irreducible.FromSpectral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Twisted transfer spectrum of pure canonical finitely correlated states

This module proves the spectral statement of Pérez-García–Wolf–Sanz–Verstraete–Cirac,
arXiv:0802.0447, Lemma 1. Irreducibility supplies the one-dimensional fixed space;
peripheral primitivity excludes additional unit-modulus eigenvalues. These are separate
hypotheses: the project's `IsPrimitive` predicate alone does not imply irreducibility.
No one-site injectivity assumption is imposed.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

open scoped TNOperatorSpace in
/-- Faithfulness of the stationary dual state and simplicity of the unital
fixed eigenspace imply irreducibility. These are the canonical pure-FCS
conditions used in arXiv:0802.0447, Lemma 1; the implication is Wolf's
spectral characterization of irreducibility, Theorem 6.4. -/
theorem isIrreducibleMap_of_canonical_fixedSpace
    [NeZero D] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hFix : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Kraus.transferMap A X = X → ∃ c : ℂ, X = c • 1) :
    IsIrreducibleMap (Kraus.transferMap A) := by
  have hpos : IsPositiveMap (Kraus.transferMap A) := Kraus.isPositiveMap_mapLM A
  apply isIrreducibleMap_of_hasSpectralProperties
  refine ⟨{
    n := d
    K := A
    map_eq := rfl
    ρ := 1
    σ := Λ
    r := 1
    ρ_posDef := Matrix.PosDef.one
    σ_posDef := hΛpos
    hr_pos := zero_lt_one
    right_eig := by simpa using hNorm
    left_eig := by simpa using hΛfix
    unique_psd_eigenvector := ?_
    spectralRadius_eq := ?_ }⟩
  · intro X _ hX
    exact hFix X (by simpa using hX)
  · simp only [ENNReal.ofReal_one]
    apply le_antisymm
    · exact spectralRadius_le_one_of_forall_eigenvalue_norm_le_one
        (Kraus.transferMap A)
        (hpos.eigenvalue_norm_le_one_of_map_one_eq_one hNorm)
    · have hOne : (1 : ℂ) ∈ spectrum ℂ
          (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
            (Kraus.transferMap A)) := by
        rw [AlgEquiv.spectrum_eq]
        exact (eigenvalue_one_of_map_one_eq_one hNorm).mem_spectrum
      rw [spectralRadius_eq_of_unital]
      simpa using (@le_iSup₂ ENNReal ℂ
        (· ∈ spectrum ℂ (Module.End.toContinuousLinearMap
          (Matrix (Fin D) (Fin D) ℂ) (Kraus.transferMap A))) _
        (fun z _ => (‖z‖₊ : ENNReal)) 1 hOne)


/-- The actual spectral radius of a physical-unitary twisted transfer map is at
most one for an irreducible canonical tensor. One-site injectivity is unnecessary. -/
theorem twistedTransfer_spectralRadius_le_one_of_irreducible
    (A : MPSTensor d D) (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (hNorm : Kraus.transferMap A 1 = 1) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) ≤
      1 := by
  apply spectralRadius_le_one_of_forall_eigenvalue_norm_le_one
  intro μ hμ
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  exact twistedTransfer_eigenvalue_norm_le_one_of_irreducible A hIrr u hu hNorm μ X
    hX.2 hX.apply_eq_smul

/-- Equality in the twisted spectral-radius bound is equivalent to a unitary
virtual intertwiner for the physical action. This is the basis-independent
form of PGWSVC08 Lemma 1, valid without one-site injectivity. -/
theorem twistedTransfer_spectralRadius_eq_one_iff_intertwiner
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (hNorm : Kraus.transferMap A 1 = 1) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) = 1 ↔
      ∃ (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ),
        V * Vᴴ = 1 ∧ ‖μ‖ = 1 ∧
        ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ) := by
  let F := Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)
  have hSpec : spectrum ℂ F = spectrum ℂ (twistedTransferMap A u) :=
    AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) _
  constructor
  · intro hRad
    obtain ⟨μ, hμspec, hμrad⟩ := spectrum.exists_nnnorm_eq_spectralRadius F
    have hμ : ‖μ‖ = 1 := by
      have h : (‖μ‖₊ : ENNReal) = 1 := hμrad.trans hRad
      exact_mod_cast h
    have hEig := Module.End.hasEigenvalue_iff_mem_spectrum.mpr (hSpec ▸ hμspec)
    obtain ⟨X, hX⟩ := hEig.exists_hasEigenvector
    have hGauge := twistedTransfer_modulus_one_implies_gaugePhase_of_irreducible
      A hIrr u hu hNorm μ X hX.2 hX.apply_eq_smul hμ
    obtain ⟨V, ν, hV, _, hν, hInter⟩ :=
      virtualUnitary_of_gaugePhaseEquiv_twisted_of_irreducible A hIrr u hu hNorm hGauge
    exact ⟨V, ν, hV, hν, hInter⟩
  · rintro ⟨V, μ, hV, hμ, hInter⟩
    have hVne : V ≠ 0 := by
      intro hV0
      have h : (0 : Matrix (Fin D) (Fin D) ℂ) = 1 := by simpa [hV0] using hV
      exact zero_ne_one h
    have hEig : Module.End.HasEigenvalue (twistedTransferMap A u) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr
          (twistedTransfer_eigen_of_virtualUnitary A u V μ hNorm hV hInter), hVne⟩
    have hμspec : μ ∈ spectrum ℂ F :=
      hSpec.symm ▸ Module.End.hasEigenvalue_iff_mem_spectrum.mp hEig
    apply le_antisymm (twistedTransfer_spectralRadius_le_one_of_irreducible A hIrr u hu hNorm)
    change 1 ≤ spectralRadius ℂ F
    rw [spectralRadius_eq_of_unital]
    have h := le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ F) => (‖z‖₊ : ENNReal)) μ hμspec
    simpa [show ‖μ‖₊ = 1 by exact_mod_cast hμ] using h

/-- A virtual intertwiner conjugates the twisted transfer action to a phase times
the ordinary transfer action. This identity retains the peripheral phase. -/
theorem twistedTransfer_eq_phase_mul_transfer
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    twistedTransferMap A u X = μ • (V * Kraus.transferMap A (Vᴴ * X)) := by
  calc
    twistedTransferMap A u X =
        ∑ i, (∑ j, u i j • A j) * X * (A i)ᴴ := by
      rw [twistedTransferMap_apply, Finset.sum_comm]
      simp only [Finset.sum_mul, smul_mul_assoc]
    _ = ∑ i, (μ • (V * A i * Vᴴ)) * X * (A i)ᴴ := by
      simp_rw [hInter]
    _ = μ • (V * Kraus.transferMap A (Vᴴ * X)) := by
      simp [Matrix.mul_assoc, Matrix.mul_sum, Finset.smul_sum]

/-- Purity forces every peripheral twisted eigenmatrix into the single virtual
intertwiner direction. In particular its eigenvalue equals the intertwiner phase. -/
theorem twistedTransfer_peripheral_eq_of_primitive
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ))
    (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ≠ 0) (hev : ‖ev‖ = 1)
    (hEig : twistedTransferMap A u X = ev • X) :
    ev = μ ∧ ∃ c : ℂ, c ≠ 0 ∧ X = c • V := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have hμne : μ ≠ 0 := Complex.ne_zero_of_norm_eq_one hμ
  have hYne : Vᴴ * X ≠ 0 := by
    intro hY
    apply hX
    calc
      X = V * (Vᴴ * X) := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
      _ = 0 := by rw [hY, Matrix.mul_zero]
  have hY : Kraus.transferMap A (Vᴴ * X) = (μ⁻¹ * ev) • (Vᴴ * X) := by
    have h := congrArg (fun Z => μ⁻¹ • (Vᴴ * Z)) hEig
    rw [twistedTransfer_eq_phase_mul_transfer A u V μ hInter] at h
    simpa [← Matrix.mul_assoc, hV', smul_smul, hμne] using h
  have hPhase : μ⁻¹ * ev = 1 := hPrim.unique_peripheral _
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hY, hYne⟩)
    (by simp [norm_inv, hμ, hev])
  have hevμ : ev = μ := by
    have h := congrArg (μ * ·) hPhase
    simpa [← mul_assoc, hμne] using h
  have hFix : Kraus.transferMap A (Vᴴ * X) = Vᴴ * X := by
    simpa [hPhase] using hY
  obtain ⟨c, hc⟩ := Kraus.fixed_eq_scalar_of_irreducible_unital A
    (by simpa [KadisonSchwarz.IsUnitalKraus] using hNorm) hIrr (Vᴴ * X) hFix
  have hcne : c ≠ 0 := by
    intro hc0
    exact hYne (by simpa [hc0] using hc)
  refine ⟨hevμ, c, hcne, ?_⟩
  calc
    X = V * (Vᴴ * X) := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
    _ = c • V := by rw [hc, Matrix.mul_smul, Matrix.mul_one]

/-- A pure canonical transfer map has at most one peripheral twisted eigenvalue,
and its eigenspace is one-dimensional whenever it exists. Eigenmatrices are
unique up to a nonzero scalar, rather than literally equal. -/
theorem twistedTransfer_peripheral_unique
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (hNorm : Kraus.transferMap A 1 = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (ev ν : ℂ) (X Y : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hev : ‖ev‖ = 1) (hν : ‖ν‖ = 1)
    (hEX : twistedTransferMap A u X = ev • X)
    (hEY : twistedTransferMap A u Y = ν • Y) :
    ev = ν ∧ ∃ c : ℂ, c ≠ 0 ∧ X = c • Y := by
  have hGauge := twistedTransfer_modulus_one_implies_gaugePhase_of_irreducible
    A hIrr u hu hNorm ev X hX hEX hev
  obtain ⟨V, μ, hV, _, hμ, hInter⟩ :=
    virtualUnitary_of_gaugePhaseEquiv_twisted_of_irreducible A hIrr u hu hNorm hGauge
  obtain ⟨hevμ, c, hc, hXV⟩ := twistedTransfer_peripheral_eq_of_primitive
    A hIrr hPrim hNorm u V μ hV hμ hInter ev X hX hev hEX
  obtain ⟨hνμ, e, he, hYV⟩ := twistedTransfer_peripheral_eq_of_primitive
    A hIrr hPrim hNorm u V μ hV hμ hInter ν Y hY hν hEY
  refine ⟨hevμ.trans hνμ.symm, c / e, div_ne_zero hc he, ?_⟩
  rw [hXV, hYV, smul_smul, div_mul_cancel₀ _ he]

/-- Canonical-density form of the equality clause of PGWSVC08 Lemma 1.
It includes invariance of the faithful normalized dual density, hence supplies
the existing virtual local-covariance predicate with its original meaning. -/
theorem pureCanonical_spectralRadius_eq_one_iff_localSymmetry
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) = 1 ↔
      IsLocalSymmetry A u Λ := by
  rw [twistedTransfer_spectralRadius_eq_one_iff_intertwiner A hIrr u hu hNorm]
  constructor
  · rintro ⟨V, μ, hV, hμ, hInter⟩
    have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
    exact ⟨V, μ, hV, hV', hμ,
      boundaryState_invariant_of_virtualUnitary_of_irreducible
        A hIrr u hu Λ hΛpos hΛtr hΛfix V μ hV hV' hμ hInter,
      hInter⟩
  · rintro ⟨V, μ, hV, _, hμ, _, hInter⟩
    exact ⟨V, μ, hV, hμ, hInter⟩

/-- PGWSVC08 Lemma 1 in the source's canonical spectral-purity regime.
The hypothesis explicitly includes the one-dimensional peripheral eigenspace,
not merely uniqueness of its eigenvalue as a set. Irreducibility is derived
from the faithful dual density and scalar fixed space, rather than assumed.
The physical endpoint and reduced-state symmetry theorems are separate results. -/
theorem pureCanonical_twistedTransfer_spectral_lemma
    [NeZero D] (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1)
    (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
      ev = 1 ∧ ∃ c : ℂ, X = c • 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) ≤ 1 ∧
    (spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) = 1 ↔
      IsLocalSymmetry A u Λ) ∧
    ∀ (ev ν : ℂ) (X Y : Matrix (Fin D) (Fin D) ℂ),
      X ≠ 0 → Y ≠ 0 → ‖ev‖ = 1 → ‖ν‖ = 1 →
      twistedTransferMap A u X = ev • X → twistedTransferMap A u Y = ν • Y →
      ev = ν ∧ ∃ c : ℂ, c ≠ 0 ∧ X = c • Y := by
  have hIrr : IsIrreducibleMap (Kraus.transferMap A) :=
    isIrreducibleMap_of_canonical_fixedSpace A Λ hΛpos hΛfix hNorm fun X hX => by
      rcases eq_or_ne X 0 with rfl | hXne
      · exact ⟨0, by simp⟩
      · exact (hPure 1 X hXne (by simp) (by simpa using hX)).2
  have hPrim : IsPrimitive (Kraus.transferMap A) := by
    apply isPrimitive_of_unique_norm_one (Kraus.transferMap A) 1 hNorm one_ne_zero
    intro ev hEig hev
    obtain ⟨X, hX⟩ := hEig.exists_hasEigenvector
    exact (hPure ev X hX.2 hev hX.apply_eq_smul).1
  exact ⟨twistedTransfer_spectralRadius_le_one_of_irreducible A hIrr u hu hNorm,
    pureCanonical_spectralRadius_eq_one_iff_localSymmetry
      A hIrr u hu Λ hΛpos hΛtr hΛfix hNorm,
    twistedTransfer_peripheral_unique A hIrr hPrim hNorm u hu⟩

private theorem rotatePhysical_virtual_conjugation
    (A : MPSTensor d D) (W : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ) (i : Fin d) :
    rotatePhysical W (fun j => μ • (V * A j * Vᴴ)) i =
      μ • (V * rotatePhysical W A i * Vᴴ) := by
  simp [rotatePhysical, Matrix.mul_sum, Finset.sum_mul, Finset.smul_sum,
    smul_smul, mul_comm]

/-- In a physical eigenbasis, the basis-independent covariance relation is
exactly the source's phased intertwining relation. `W` contains the eigenbasis
bras, so `W u = diag(ζ) W` and the transformed letters are `rotatePhysical W A`. -/
theorem physicalEigenbasis_intertwining_iff
    (A : MPSTensor d D) (u W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W * Wᴴ = 1) (ζ : Fin d → ℂ) (hζ : ∀ i, ζ i ≠ 0)
    (hDiag : W * u = Matrix.diagonal ζ * W)
    (V : Matrix (Fin D) (Fin D) ℂ) (hV : V * Vᴴ = 1) (μ : ℂ) :
    (∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) ↔
      ∀ i, Vᴴ * rotatePhysical W A i =
        (μ / ζ i) • (rotatePhysical W A i * Vᴴ) := by
  have hW' : Wᴴ * W = 1 := mul_eq_one_comm.mp hW
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  have hRot : rotatePhysical W (rotatePhysical u A) =
      fun i => ζ i • rotatePhysical W A i := by
    rw [rotatePhysical_rotatePhysical, hDiag, ← rotatePhysical_rotatePhysical]
    funext i
    simp [rotatePhysical, Matrix.diagonal_apply]
  have hBasis : (∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) ↔
      ∀ i, ζ i • rotatePhysical W A i =
        μ • (V * rotatePhysical W A i * Vᴴ) := by
    constructor
    · intro h i
      have hf : rotatePhysical u A = fun j => μ • (V * A j * Vᴴ) := funext h
      have hi := congrFun hRot i
      rw [hf, rotatePhysical_virtual_conjugation] at hi
      exact hi.symm
    · intro h
      have hf : rotatePhysical W (rotatePhysical u A) =
          rotatePhysical W (fun j => μ • (V * A j * Vᴴ)) := by
        funext i
        rw [hRot, rotatePhysical_virtual_conjugation]
        exact h i
      have hi := congrArg (rotatePhysical Wᴴ) hf
      simp only [rotatePhysical_rotatePhysical, ← Matrix.mul_assoc, hW',
        Matrix.one_mul, rotatePhysical_one] at hi
      exact fun i => congrFun hi i
  rw [hBasis]
  apply forall_congr'
  intro i
  constructor
  · intro h
    have hi := congrArg (fun X => (ζ i)⁻¹ • (Vᴴ * X)) h
    simpa [← Matrix.mul_assoc, hV', smul_smul, hζ i, div_eq_mul_inv, mul_comm] using hi
  · intro h
    have hi := congrArg (fun X => ζ i • (V * X)) h
    simpa [← Matrix.mul_assoc, hV, smul_smul, hζ i, div_eq_mul_inv,
      mul_comm, mul_left_comm] using hi

/-- The literal exponential-phase form of the source's eigenbasis equation.
The angle representatives may be chosen modulo `2π`; the identity depends
only on their unit-circle phases. -/
theorem physicalEigenbasis_exp_intertwining_iff
    (A : MPSTensor d D) (u W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W * Wᴴ = 1) (θj : Fin d → ℝ)
    (hDiag : W * u = Matrix.diagonal (fun j => Complex.exp (θj j * Complex.I)) * W)
    (V : Matrix (Fin D) (Fin D) ℂ) (hV : V * Vᴴ = 1) (θ : ℝ) :
    (∀ i, ∑ j, u i j • A j = Complex.exp (θ * Complex.I) • (V * A i * Vᴴ)) ↔
      ∀ i, Vᴴ * rotatePhysical W A i =
        Complex.exp (((θ - θj i : ℝ) : ℂ) * Complex.I) •
          (rotatePhysical W A i * Vᴴ) := by
  simpa only [Complex.ofReal_sub, sub_mul, Complex.exp_sub] using
    physicalEigenbasis_intertwining_iff A u W hW
      (fun j => Complex.exp (θj j * Complex.I))
      (fun j => Complex.exp_ne_zero _) hDiag V hV (Complex.exp (θ * Complex.I))

private theorem exists_unitPhase_angle (μ : ℂ) (hμ : ‖μ‖ = 1) :
    ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), Complex.exp (θ * Complex.I) = μ := by
  have harg : Complex.exp (μ.arg * Complex.I) = μ := by
    simpa [hμ] using Complex.norm_mul_exp_arg_mul_I μ
  by_cases hneg : μ.arg < 0
  · refine ⟨μ.arg + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [Complex.neg_pi_lt_arg μ, Real.pi_pos]
    · linarith
    · simpa [Complex.ofReal_add, add_mul, Complex.ofReal_mul, Complex.exp_add,
        Complex.exp_two_pi_mul_I] using harg
  · exact ⟨μ.arg, ⟨le_of_not_gt hneg,
      by linarith [Complex.arg_le_pi μ, Real.pi_pos]⟩, harg⟩

/-- The literal source equality criterion in any physical unitary eigenbasis,
including the principal phase representative `0 ≤ θ < 2π`. -/
theorem twistedTransfer_spectralRadius_eq_one_iff_eigenbasis
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hNorm : Kraus.transferMap A 1 = 1)
    (u W : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) (hW : W * Wᴴ = 1)
    (θj : Fin d → ℝ)
    (hDiag : W * u = Matrix.diagonal (fun j => Complex.exp (θj j * Complex.I)) * W) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) (twistedTransferMap A u)) = 1 ↔
      ∃ (V : Matrix (Fin D) (Fin D) ℂ) (θ : ℝ),
        θ ∈ Set.Ico 0 (2 * Real.pi) ∧ V * Vᴴ = 1 ∧
        ∀ i, Vᴴ * rotatePhysical W A i =
          Complex.exp (((θ - θj i : ℝ) : ℂ) * Complex.I) •
            (rotatePhysical W A i * Vᴴ) := by
  rw [twistedTransfer_spectralRadius_eq_one_iff_intertwiner A hIrr u hu hNorm]
  constructor
  · rintro ⟨V, μ, hV, hμ, hInter⟩
    obtain ⟨θ, hθ, hθμ⟩ := exists_unitPhase_angle μ hμ
    refine ⟨V, θ, hθ, hV, ?_⟩
    apply (physicalEigenbasis_exp_intertwining_iff A u W hW θj hDiag V hV θ).mp
    simpa only [hθμ] using hInter
  · rintro ⟨V, θ, _, hV, hInter⟩
    exact ⟨V, Complex.exp (θ * Complex.I), hV, Complex.norm_exp_ofReal_mul_I θ,
      (physicalEigenbasis_exp_intertwining_iff A u W hW θj hDiag V hV θ).mpr hInter⟩

end MPSTensor
