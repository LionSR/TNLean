/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Irreducible.PerronGauge
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteRangeKnabeGap
import TNLean.Wielandt.Primitivity.Equivalence

/-!
# The normalized primitive gauge of a normal tensor

A normal tensor need not be trace preserving, and its transfer map need not have
spectral radius one.  Both normalizations are taken "without loss of generality"
by the sources: Nachtergaele, arXiv:cond-mat/9410110, rewrites the generalized
valence-bond construction so that equations (3.2a) and (3.2b) hold (lines
1394--1435), and Pérez-García, Verstraete, Wolf, and Cirac, arXiv:quant-ph/0608197,
open the proof of Theorem 4, the translation-invariant canonical form
(statement lines 742--761, proof lines 765--770), by assuming that the spectral
radius of the transfer map is one and gauging by the square root of a positive
fixed point.

This file performs that step. From a normal tensor \(A\) it produces a positive
scalar \(\zeta\), a virtual gauge \(X\), and the rescaled gauged tensor
\(B^i=\zeta\,XA^iX^{-1}\) which carries the trace-preserving normalization
\(\sum_i (B^i)^\dagger B^i=\mathbb 1\) together with a positive definite fixed
point of its transfer map: exactly the data bundled by the complementary
transfer-map gap predicate.  Rescaling and gauging leave the local MPS spaces,
the parent interaction, and the periodic chain ground spaces untouched, so every
consequence of the gap predicate that is phrased through those objects transfers
back to \(A\) verbatim.  The finite-range Knabe gap is one such consequence, and
it is stated here for an arbitrary normal tensor.

The orientation is the mirror of the printed one: the gauge is built from the
Perron eigenvector of the *adjoint* transfer map, so the resulting family is
trace preserving rather than unital.  Both orientations are already in the
sources.  The blocks of the translation-invariant canonical form of
arXiv:quant-ph/0608197, Theorem 4, statement lines 752--758, satisfy
conditions 1 and 2,
\(\sum_i A^iA^{i\dagger}=\mathbb 1\) and
\(\sum_i A^{i\dagger}\Lambda A^i=\Lambda\) with \(\Lambda>0\); the further gauge
by \(\Lambda^{1/2}\) turns condition 2 into the trace-preserving normalization
and condition 1 into the statement that \(\Lambda\) is a positive definite fixed
point of the transfer map.  Nachtergaele's equations (3.2a) and (3.2b) impose
the corresponding two-sided normalization on the rewritten generalized
valence-bond construction.

## Main results

* `MPSTensor.isNBlkInjective_smul_iff`, `MPSTensor.isNormal_smul_iff`: block
  injectivity and normality are invariant under a nonzero rescaling.
* `MPSTensor.exists_apply_ne_zero_of_isNormal`: a normal tensor on a nonzero
  bond space has a nonzero matrix.
* `MPSTensor.exists_isPrimitiveMPS_gauge_of_isNormal`: the normalized primitive
  gauge of a normal tensor.
* `MPSTensor.exists_parentHamiltonianES_gap_of_isNormal`: the finite-range
  Knabe gap for the parent Hamiltonian of an arbitrary normal tensor.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines
  1394--1435.
* D. Pérez-García, F. Verstraete, M. Wolf, J. I. Cirac, arXiv:quant-ph/0608197,
  Theorem 4, lines 742--770.
* M. Sanz, D. Pérez-García, M. Wolf, J. I. Cirac, arXiv:0909.5347,
  Proposition 3.
* J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, arXiv:2011.12127,
  lines 2183--2187.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-! ### Rescaling invariance of block injectivity -/

/-- Rescaling every matrix of a tensor by a nonzero scalar preserves the span of
the length-\(N\) words.

Each length-\(N\) word acquires the common factor \(\zeta^N\), which is a unit,
and the span of a set is unchanged by a unit scalar. -/
theorem wordSpan_smul_eq {ζ : ℂ} (hζ : ζ ≠ 0) (A : MPSTensor d D) (N : ℕ) :
    Kraus.wordSpan (ζ • A) N = Kraus.wordSpan A N := by
  have hword : ∀ σ : Fin N → Fin d,
      Kraus.evalWord (ζ • A) (List.ofFn σ) =
        (ζ ^ N) • Kraus.evalWord A (List.ofFn σ) := fun σ => by
    have h := Kraus.evalWord_smul ζ A (List.ofFn σ)
    rw [List.length_ofFn] at h
    exact h
  simp only [Kraus.wordSpan]
  simp_rw [hword]
  rw [Set.range_smul]
  exact Submodule.span_smul_eq_of_isUnit _ _ (pow_ne_zero N hζ).isUnit

/-- Rescaling every matrix of a tensor by a nonzero scalar preserves block
injectivity at every blocking length. -/
theorem isNBlkInjective_smul_iff {ζ : ℂ} (hζ : ζ ≠ 0) (A : MPSTensor d D) (N : ℕ) :
    Kraus.IsNBlkInjective (ζ • A) N ↔ Kraus.IsNBlkInjective A N := by
  simp only [Kraus.IsNBlkInjective, wordSpan_smul_eq hζ A N]

/-- Rescaling every matrix of a tensor by a nonzero scalar preserves normality.

This is the scalar half of the normalization taken without loss of generality at
arXiv:quant-ph/0608197, proof lines 765--767. -/
theorem isNormal_smul_iff {ζ : ℂ} (hζ : ζ ≠ 0) (A : MPSTensor d D) :
    Kraus.IsNormal (ζ • A) ↔ Kraus.IsNormal A := by
  constructor
  · rintro ⟨N, hN, hInj⟩
    exact ⟨N, hN, (isNBlkInjective_smul_iff hζ A N).1 hInj⟩
  · rintro ⟨N, hN, hInj⟩
    exact ⟨N, hN, (isNBlkInjective_smul_iff hζ A N).2 hInj⟩

/-- A normal tensor on a nonzero bond space has a nonzero matrix.

If every matrix vanished, every positive-length word would vanish and the word
span could not be the full matrix algebra. -/
theorem exists_apply_ne_zero_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) : ∃ i : Fin d, A i ≠ 0 := by
  obtain ⟨N, hN, hInj⟩ := hA
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hsub : (Set.range fun σ : Fin N → Fin d =>
      Kraus.evalWord A (List.ofFn σ)) ⊆ {0} := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    change Kraus.evalWord A (List.ofFn σ) ∈ ({0} : Set (Matrix (Fin D) (Fin D) ℂ))
    rw [Set.mem_singleton_iff, List.ofFn_succ, Kraus.evalWord_cons, hall (σ 0),
      Matrix.zero_mul]
  have hle : (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) ≤ ⊥ := by
    rw [← hInj.span_eq_top, ← Submodule.span_zero_singleton (R := ℂ)
      (M := Matrix (Fin D) (Fin D) ℂ)]
    exact Submodule.span_mono hsub
  have h10 : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
    (Submodule.mem_bot ℂ).mp (hle Submodule.mem_top)
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hentry := congrFun (congrFun h10 ⟨0, hD⟩) ⟨0, hD⟩
  rw [Matrix.one_apply_eq] at hentry
  exact one_ne_zero hentry

/-! ### Transport of the parent Hamiltonian along equal local MPS spaces -/

/-- Two tensors with the same local MPS space at length \(L\) have the same
finite-chain parent Hamiltonian in the Euclidean realization. -/
theorem parentHamiltonianES_eq_of_groundSpace_eq {A B : MPSTensor d D} {L : ℕ}
    (h : groundSpace A L = groundSpace B L) (N : ℕ) :
    parentHamiltonianES A L N = parentHamiltonianES B L N := by
  simp only [parentHamiltonianES, parentHamiltonian_eq_of_groundSpace_eq h N]

/-! ### The normalized primitive gauge -/

/-- **The normalized primitive gauge of a normal tensor.**

For a normal tensor \(A\) there are a nonzero scalar \(\zeta\), a virtual gauge,
and a matrix \(\rho>0\) such that the rescaled gauged tensor \(B\) satisfies
\(\sum_i (B^i)^\dagger B^i=\mathbb 1\) and has \(\rho\) as the distinguished
fixed point of a complementary transfer-map gap.  The matrix product vectors of
\(B\) are those of \(A\) rescaled by \(\zeta^N\), and the local MPS spaces, the
parent interactions, and the periodic chain ground spaces of \(A\) and \(B\)
coincide.

This is the step taken without loss of generality at
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435, and at
arXiv:quant-ph/0608197, Theorem 4, proof lines 765--770: rescale
so that the transfer map has spectral radius one and gauge by the square root of
a positive fixed point.  The gauge here is built from the Perron eigenvector of
the adjoint transfer map, giving the trace-preserving orientation, which is what
conditions 1 and 2 of that theorem (statement lines 752--758) become after the
further gauge by the square root of the matrix \(\Lambda\) appearing in
condition 2.

Normality supplies the irreducibility that the Perron--Frobenius eigenvector
requires, through the direction of arXiv:0909.5347, Proposition 3, that imposes
no normalization on the tensor, and it survives both the rescaling and the
gauge; the trace-preserving representative is therefore normal as well, and the
full equivalence of Proposition 3, which does assume the trace-preserving
normalization, returns the complementary transfer-map gap with a positive
definite fixed point. -/
theorem exists_isPrimitiveMPS_gauge_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) :
    ∃ (B : MPSTensor d D) (ζ : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      ζ ≠ 0 ∧
      GaugeEquiv (ζ • A) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      IsPrimitiveMPS B ρ ∧ ρ.PosDef ∧
      (∀ L : ℕ, groundSpace A L = groundSpace B L) ∧
      (∀ L : ℕ, parentInteraction A L = parentInteraction B L) ∧
      (∀ L N : ℕ, chainGroundSpace A L N = chainGroundSpace B L N) := by
  classical
  have hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) A :=
    isIrreducibleTensor_of_isPrimitivePaper A (isPrimitivePaper_of_isNormal A hA)
  obtain ⟨B, r, σ, _hσ, hr, _hBdef, hBnorm, hBgauge⟩ :=
    exists_tp_data_of_irreducible A hIrr (exists_apply_ne_zero_of_isNormal hA)
  set ζ : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ) with hζ_def
  have hζ : ζ ≠ 0 := by
    have hsqrt : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
    simpa [hζ_def] using inv_ne_zero hsqrt
  have hgauge : GaugeEquiv (ζ • A) B := hBgauge
  have hNormalScaled : Kraus.IsNormal (ζ • A) := (isNormal_smul_iff hζ A).2 hA
  have hNormalB : Kraus.IsNormal B := isNormal_of_gaugeEquiv hNormalScaled hgauge
  obtain ⟨ρ, hPrim, hρ⟩ :=
    isPrimitiveMPS_of_isStronglyIrreduciblePaper B hBnorm
      (isNormal_implies_stronglyIrreducible B hBnorm hNormalB)
  have hGS : ∀ L : ℕ, groundSpace A L = groundSpace B L := by
    intro L
    rw [← groundSpace_smul_eq A ζ hζ L]
    exact hgauge.groundSpace_eq L
  refine ⟨B, ζ, ρ, hζ, hgauge, ?_, hPrim, hρ, hGS, ?_, ?_⟩
  · intro N τ
    rw [← hgauge.sameMPV N τ]
    simp only [mpv, coeff]
    change Matrix.trace (Kraus.evalWord (fun i => ζ • A i) (List.ofFn τ)) = _
    rw [Kraus.evalWord_smul]
    simp [List.length_ofFn, Matrix.trace_smul]
  · exact fun L => parentInteraction_eq_of_groundSpace_eq (hGS L)
  · exact fun L N => chainGroundSpace_eq_of_groundSpace_eq (hGS L)

/-- **The finite-range Knabe gap for an arbitrary normal tensor.**

Every normal tensor has a positive uniform lower bound on the nonzero spectrum
of its canonical range-\(l+1\) parent Hamiltonian on every periodic chain with
\(N\geq 2m\).  This is the matrix-product-state case of the gap statement at
arXiv:2011.12127, lines 2183--2187, with no normalization imposed on the tensor.

The normalized primitive gauge replaces \(A\) by a trace-preserving
representative with a positive definite fixed point, which is where the
finite-range Knabe estimate applies; the parent Hamiltonian is unchanged by that
replacement, and block injectivity transfers back through the rescaling and the
gauge. -/
theorem exists_parentHamiltonianES_gap_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) :
    ∃ l : ℕ, ∃ ε : ℝ, ∃ m : ℕ, ∃ δ : ℝ,
      1 < l ∧ Kraus.IsNBlkInjective A l ∧
      0 ≤ ε ∧ ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) ∧
      l + 1 ≤ m ∧
      δ = ((m : ℝ) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 -
          (l : ℝ) ^ 2) / ((m : ℝ) - (l : ℝ)) ∧
      0 < δ ∧
      ∀ N : ℕ, 2 * m ≤ N → ∀ v ∈
        (LinearMap.ker (parentHamiltonianES A (l + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES A (l + 1) N v‖ := by
  obtain ⟨B, ζ, ρ, hζ, hgauge, _hmpv, hPrim, hρ, hGS, _hPI, _hCGS⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA
  obtain ⟨l, ε, m, δ, hl, hInjB, hε, hεlt, hm, hδ_def, hδ, hGap⟩ :=
    hPrim.exists_parentHamiltonianES_gap_of_finiteRangeKnabe hρ
  have hInjA : Kraus.IsNBlkInjective A l :=
    (isNBlkInjective_smul_iff hζ A l).1
      (isNBlkInjective_of_gaugeEquiv hInjB hgauge.symm)
  refine ⟨l, ε, m, δ, hl, hInjA, hε, hεlt, hm, hδ_def, hδ, ?_⟩
  intro N hN v hv
  rw [parentHamiltonianES_eq_of_groundSpace_eq (hGS (l + 1)) N] at hv ⊢
  exact hGap N hN v hv

end MPSTensor
