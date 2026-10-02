/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockedGroundSpace
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Residual boundary spaces after physical blocking

A length-\(NL+r\) chain consists of a blocked prefix and an original
\(r\)-site tail. The compressed-sector coefficients are
\(\operatorname{tr}(B_a^u V_a^\dagger A^\tau Y)\), with a rectangular
boundary \(Y\in M_{D\times D_a}(\mathbb C)\). The tail remains correlated
with the virtual boundary. Resolving the virtual identity gives the original
open MPS space as the sum of these rectangular ranges.

For a periodic tensor, step-orbit compression derives both letter
intertwinings, the isometric resolution, positive sector dimensions, and the
compressed-sector periods. The exact range identity holds at every prefix
and tail length, including zero. The generic identities require no positivity
or normalization assumption; the periodic consequence requires only the
periodic tensor and a positive blocking length. No quantitative projection
estimate or all-residue spectral-gap conclusion is asserted here.

Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
local support spaces and intersection property at lines 1504--1538.

**Local fix (powered roots):** The compressed-sector period is
`m / gcd(m,L)`. The peripheral-root correction used in its derivation is
recorded in `docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d D E L : ℕ}

/-- The rectangular residual boundary contraction has coefficient
`tr(B^u * Vᴴ * A^τ * Y)`, with a decoded blocked prefix and an original tail.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
noncomputable def blockedResidualBoundaryMap (A : MPSTensor d D)
    (L : ℕ) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ) :
    Matrix (Fin D) (Fin E) ℂ →ₗ[ℂ] NSiteSpace d (N * L + r) where
  toFun Y σ := Matrix.trace
    (Kraus.evalWord B (List.ofFn ((blockedConfigEquiv d N L).symm (σ ∘ Fin.castAdd r))) *
      Vᴴ * Kraus.evalWord A (List.ofFn (σ ∘ Fin.natAdd (N * L))) * Y)
  map_add' Y Z := by ext σ; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Y := by ext σ; simp [Matrix.trace_smul]

/-- A left letter intertwiner identifies the residual vector with the
original boundary map at `Y * Vᴴ`, including zero prefix and tail lengths.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
theorem blockedResidualBoundaryMap_eq_groundSpaceMap_mul_conjTranspose
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ)
    (hInt : ∀ i, Vᴴ * blockTensor A L i = B i * Vᴴ)
    (N r : ℕ) (Y : Matrix (Fin D) (Fin E) ℂ) :
    blockedResidualBoundaryMap A L B V N r Y =
      groundSpaceMap A (N * L + r) (Y * Vᴴ) := by
  have hWord (u : Cfg d (N * L)) :
      Kraus.evalWord B (List.ofFn ((blockedConfigEquiv d N L).symm u)) * Vᴴ =
        Vᴴ * Kraus.evalWord A (List.ofFn u) := by
    have h := Kraus.evalWord_intertwine B (blockTensor A L) Vᴴ (fun i => (hInt i).symm)
      (List.ofFn ((blockedConfigEquiv d N L).symm u))
    rw [evalWord_blockTensor, ← ofFn_blockedConfigEquiv, Equiv.apply_symm_apply] at h
    exact h
  ext σ
  rw [← leftBoundaryMap_factorization A (N * L) r, leftBoundaryMap_apply]
  change Matrix.trace
    (Kraus.evalWord B (List.ofFn ((blockedConfigEquiv d N L).symm (σ ∘ Fin.castAdd r))) *
      Vᴴ * Kraus.evalWord A (List.ofFn (σ ∘ Fin.natAdd (N * L))) * Y) = _
  rw [hWord]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm Vᴴ
    (Kraus.evalWord A (List.ofFn (σ ∘ Fin.castAdd r)) *
      (Kraus.evalWord A (List.ofFn (σ ∘ Fin.natAdd (N * L))) * Y))

variable {ι : Type*} [Fintype ι] {dim : ι → ℕ}

/-- Resolving the virtual identity splits every original open MPS space
into rectangular residual-sector ranges. No orthogonality or injectivity of
these ranges is required.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
theorem groundSpace_eq_iSup_range_blockedResidualBoundaryMap
    (A : MPSTensor d D) (B : (j : ι) → MPSTensor (blockPhysDim d L) (dim j))
    (V : (j : ι) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) (N r : ℕ) :
    groundSpace A (N * L + r) = ⨆ j, (blockedResidualBoundaryMap A L (B j) (V j) N r).range := by
  classical
  have hSplit (X : Matrix (Fin D) (Fin D) ℂ) :
      groundSpaceMap A (N * L + r) X =
        ∑ j, blockedResidualBoundaryMap A L (B j) (V j) N r (X * V j) := by
    calc
      _ = groundSpaceMap A (N * L + r) (X * (∑ j, V j * (V j)ᴴ)) := by
        rw [hSum, Matrix.mul_one]
      _ = ∑ j, groundSpaceMap A (N * L + r) (X * V j * (V j)ᴴ) := by
        simp only [Matrix.mul_sum, map_sum, ← Matrix.mul_assoc]
      _ = _ := by
        exact Finset.sum_congr rfl fun j _ =>
          (blockedResidualBoundaryMap_eq_groundSpaceMap_mul_conjTranspose A (B j) (V j)
            (hInt j) N r (X * V j)).symm
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [hSplit]
    exact Submodule.sum_mem _ fun j _ =>
      (le_iSup (fun j => (blockedResidualBoundaryMap A L (B j) (V j) N r).range) j)
        ⟨X * V j, rfl⟩
  · refine iSup_le fun j => ?_
    rintro _ ⟨Y, rfl⟩
    exact ⟨Y * (V j)ᴴ,
      (blockedResidualBoundaryMap_eq_groundSpaceMap_mul_conjTranspose A (B j) (V j)
        (hInt j) N r Y).symm⟩


open scoped Matrix.Norms.Frobenius

/-- The residual boundary map in physical Euclidean and virtual
Hilbert--Schmidt coordinates. The virtual coordinates are column index
followed by row index, as in the rectangular Frobenius equivalence.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
noncomputable def blockedResidualBoundaryMapES (A : MPSTensor d D)
    (L : ℕ) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Cfg d (N * L + r)) :=
  LinearMap.toContinuousLinearMap <|
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (N * L + r))).symm.toLinearMap.comp
      ((blockedResidualBoundaryMap A L B V N r).comp
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm.toLinearEquiv.toLinearMap)


/-- Euclidean realization preserves the literal residual boundary vector.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
@[simp] theorem blockedResidualBoundaryMapES_frobeniusEquivEuclidean_apply
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ) (Y : Matrix (Fin D) (Fin E) ℂ) :
    blockedResidualBoundaryMapES A L B V N r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d (N * L + r))).symm
        (blockedResidualBoundaryMap A L B V N r Y) := by
  change (WithLp.linearEquiv 2 ℂ (NSiteSpace d (N * L + r))).symm
    (blockedResidualBoundaryMap A L B V N r
      ((Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y))) = _
  rw [(Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm_apply_apply]

/-- The exact residual-sector range decomposition in the physical
Euclidean space, at every prefix and tail length.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
theorem groundSpaceES_eq_iSup_range_blockedResidualBoundaryMapES
    (A : MPSTensor d D) (B : (j : ι) → MPSTensor (blockPhysDim d L) (dim j))
    (V : (j : ι) → Matrix (Fin D) (Fin (dim j)) ℂ)
    (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, (V j)ᴴ * blockTensor A L i = B j i * (V j)ᴴ) (N r : ℕ) :
    groundSpaceES A (N * L + r) =
      ⨆ j, (blockedResidualBoundaryMapES A L (B j) (V j) N r).range := by
  simp only [groundSpaceES,
    groundSpace_eq_iSup_range_blockedResidualBoundaryMap A B V hSum hInt N r,
    Submodule.map_iSup, blockedResidualBoundaryMapES, LinearMap.coe_toContinuousLinearMap,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]


/-- Periodic compression derives normalized sectors and an isometric
virtual resolution whose rectangular residual ranges give the original
support space at every length `N * L + r`. Both letter intertwinings are
derived from the cyclic projection resolution.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1504--1538. -/
theorem IsPeriodic.exists_stepOrbit_residualGroundSpaceDecomposition {m : ℕ}
    {A : MPSTensor d D} (hA : IsPeriodic m A) (L : ℕ) (hL : 0 < L) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (dim : Fin (m.gcd L) → ℕ)
      (B : (a : Fin (m.gcd L)) → MPSTensor (blockPhysDim d L) (dim a))
      (V : (a : Fin (m.gcd L)) → Matrix (Fin D) (Fin (dim a)) ℂ),
      (∀ a, 0 < dim a) ∧ (∑ a, dim a) = D ∧
      (∀ a, IsLeftCanonical (B a)) ∧ (∀ a, (V a)ᴴ * V a = 1) ∧
      (∑ a, V a * (V a)ᴴ) = 1 ∧
      (∀ a i, blockTensor A L i * V a = V a * B a i) ∧
      (∀ a i, (V a)ᴴ * blockTensor A L i = B a i * (V a)ᴴ) ∧
      (∀ a, IsPeriodic (m / m.gcd L) (B a)) ∧
      (∀ N r, groundSpaceES A (N * L + r) =
        ⨆ a, (blockedResidualBoundaryMapES A L (B a) (V a) N r).range) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, dim, B, V, _hproj, hsum, _hne, hshift, hdim, htotal, hcan,
    hiso, hV, hC, hInt, _hGS, hPeriod⟩ := hA.exists_stepOrbit_groundSpaceDecomposition L hL
  have hCoInt (a : Fin (m.gcd L)) (i : Fin (blockPhysDim d L)) :
      (V a)ᴴ * blockTensor A L i = B a i * (V a)ᴴ := by
    rw [hC, Matrix.mul_assoc, Matrix.mul_assoc, hV,
      ← stepOrbitProjection_mul_blockTensor P A hshift, ← hV,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiso, Matrix.one_mul]
  have hResolution : (∑ a, V a * (V a)ᴴ) = 1 := by
    simp only [hV, sum_stepOrbitProjection, hsum]
  refine ⟨dim, B, V, hdim, htotal, hcan, hiso, hResolution, hInt, hCoInt, hPeriod, ?_⟩
  intro N r
  exact groundSpaceES_eq_iSup_range_blockedResidualBoundaryMapES A B V hResolution hCoInt N r

end MPSTensor
