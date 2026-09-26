/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.AnticommutingEvenDimension
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.GaugeUniqueness
import TNLean.MPS.Symmetry.StringOrderAux

/-!
# Degeneracy of the entanglement spectrum in a symmetry-protected phase

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
paragraph "Entanglement spectrum and edge modes",
`Papers/2011.12127/TN-Review-main.tex` lines 1171–1172: for an injective MPS in
canonical form with on-site symmetry, the fixed point `ρ` of the transfer map
inherits the symmetry, `X_g ρ X_g† = ρ`, and a projective virtual representation
with no one-dimensional invariant subspaces forces every eigenvalue of `ρ` to be
degenerate.

**Formalized here.** For an injective tensor normalized by `E(1) = 1` with
positive definite fixed point `Λ` of the adjoint transfer map, every virtual
gauge `X` of a unitary on-site symmetry, `∑ⱼ uᵢⱼ Aʲ = ζ X Aⁱ X⁻¹`, is a nonzero
multiple of a unitary `W` with `W Λ W† = Λ`, so `X` commutes with `Λ`.  If two
such gauges anticommute, every eigenspace of `Λ` has even dimension.

The source writes the canonical form with the fixed point of `ρ ↦ ∑ Aⁱ ρ Aⁱ†`;
this development uses the mirror normalization `∑ Aⁱ Aⁱ† = 1` with `Λ` the
fixed point of `ρ ↦ ∑ Aⁱ† ρ Aⁱ`, as in the string-order modules.  Both describe
the half-chain reduced density matrix, whose spectrum is the entanglement
spectrum.  The anticommuting pair is the source's non-abelian projective
representation specialized to its smallest instance; the even dimension of
every eigenspace is the degeneracy the source asserts.

## Main results

* `MPSTensor.exists_unitary_gauge_of_symmetry` : every virtual gauge of a unitary
  on-site symmetry is a nonzero multiple of a unitary fixing `Λ`
* `MPSTensor.commute_boundaryState_of_symmetry` : every such gauge commutes with `Λ`
* `MPSTensor.even_finrank_eigenspace_of_anticommuting_gauges` : two anticommuting
  gauges force every eigenspace of `Λ` to have even dimension
* `MPSTensor.twistedTensor_blockTensor_eq_gauge` : a virtual gauge of an on-site
  symmetry is also a virtual gauge of the blocked symmetry of the blocked tensor

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The companion family attached to `uᴴ` is the physical twist by `u`. -/
private lemma twistedMixedCompanion_conjTranspose (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    twistedMixedCompanion A uᴴ i = ∑ j : Fin d, u i j • A j := by
  simp [twistedMixedCompanion, Matrix.conjTranspose_apply]

/-- **Virtual gauges can be chosen unitary and fix the boundary state.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1083 and 1172): for an injective tensor in canonical form the gauge of an
on-site symmetry is unitary up to a scalar, and by uniqueness of the fixed point
it leaves `Λ` invariant.

Here `A` is injective with `E(1) = 1`, `Λ` is a positive definite fixed point of
the adjoint transfer map, `u` is a unitary on-site operator, and
`∑ⱼ uᵢⱼ Aʲ = ζ X Aⁱ X⁻¹`.  The conclusion is `X = c W` with `W` unitary and
`W Λ W† = Λ`. -/
theorem exists_unitary_gauge_of_symmetry
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    {u : Matrix (Fin d) (Fin d) ℂ} (hu : u * uᴴ = 1)
    {X : GL (Fin D) ℂ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hX : ∀ i, ∑ j : Fin d, u i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ∃ W : Matrix (Fin D) (Fin D) ℂ, W * Wᴴ = 1 ∧ Wᴴ * W = 1 ∧ W * Λ * Wᴴ = Λ ∧
      ∃ c : ℂ, c ≠ 0 ∧ (X : Matrix (Fin D) (Fin D) ℂ) = c • W := by
  classical
  rcases eq_or_ne D 0 with hD | hD
  · subst hD
    exact ⟨1, by simp, by simp, Subsingleton.elim _ _, 1, one_ne_zero,
      Subsingleton.elim _ _⟩
  have : NeZero D := ⟨hD⟩
  -- Normalize the boundary state to trace one.
  have htr_pos : 0 < Λ.trace := hΛpos.trace_pos
  have htr_ne : Λ.trace ≠ 0 := htr_pos.ne'
  set Λ' : Matrix (Fin D) (Fin D) ℂ := (Λ.trace)⁻¹ • Λ with hΛ'
  have hΛ'pos : Λ'.PosDef := hΛpos.smul (inv_pos.mpr htr_pos)
  have hΛ'tr : Λ'.trace = 1 := by
    rw [hΛ', Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr_ne]
  have hΛ'fix : Kraus.transferMap (fun i => (A i)ᴴ) Λ' = Λ' := by
    rw [hΛ', map_smul, hΛfix]
  have hu' : uᴴ * uᴴᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hu
  have hGauge : GaugePhaseEquiv A (twistedMixedCompanion A uᴴ) :=
    ⟨X, ζ, hζ, fun i => by rw [twistedMixedCompanion_conjTranspose, hX i]⟩
  obtain ⟨V, μ, hVV, hVV', hμ, hrel⟩ :=
    virtualUnitary_of_gaugePhaseEquiv_twisted A hA uᴴ hu' hNorm hGauge
  have hinv : Vᴴ * Λ' * V = Λ' :=
    boundaryState_invariant_of_virtualUnitary A hA uᴴ hu' Λ' hΛ'pos hΛ'tr hΛ'fix
      V μ hVV hVV' hμ hrel
  -- Undo the physical twist: `A = μ ζ (V X) A (V X)⁻¹`.
  let Vgl : GL (Fin D) ℂ := ⟨V, Vᴴ, hVV, hVV'⟩
  have hback : ∀ k, A k = (μ * ζ) •
      (((Vgl * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A k *
        (((Vgl * X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro k
    have hmix := unitary_mix_inverse A uᴴ
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hu) k
    calc A k = ∑ i : Fin d, (starRingEnd ℂ) (uᴴ i k) • (∑ j : Fin d, uᴴ i j • A j) :=
          hmix.symm
      _ = ∑ i : Fin d, u k i • (μ • (V * A i * Vᴴ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hrel i, Matrix.conjTranspose_apply]
          simp
      _ = μ • (V * (∑ i : Fin d, u k i • A i) * Vᴴ) := by
          simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, Matrix.mul_smul,
            Matrix.smul_mul, smul_comm μ]
      _ = _ := by
          rw [hX k]
          simp only [Vgl, Units.val_mul, mul_inv_rev, Matrix.mul_smul, Matrix.smul_mul,
            smul_smul, Matrix.mul_assoc]
          congr 3
  obtain ⟨-, a, ha⟩ := gauge_phase_unique hA (X := 1) (Y := (Vgl * X)⁻¹) (c := μ * ζ)
    (fun i => by simpa [Matrix.mul_assoc] using hback i)
  -- `1 = a (V X)⁻¹`, so `X = a V⁻¹ = a V†`.
  have hVX : ((Vgl * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      (a : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have := congrArg (· * ((Vgl * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ha
    simp only [Units.val_one, Matrix.one_mul, Matrix.smul_mul, Units.inv_mul] at this
    exact this
  refine ⟨Vᴴ, by simpa using hVV', by simpa using hVV, ?_, a, a.ne_zero, ?_⟩
  · have h := congrArg (fun M => (Λ.trace) • M) hinv
    simp only [hΛ', Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ htr_ne,
      one_smul] at h
    simpa [Matrix.conjTranspose_conjTranspose] using h
  · have := congrArg (fun M => Vᴴ * M) hVX
    simp only [Units.val_mul, ← Matrix.mul_assoc] at this
    simpa [Vgl, hVV', Matrix.mul_smul] using this

/-- **The virtual gauges commute with the boundary state.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1172): "Because of the uniqueness of the corresponding eigenvalue, `ρ` has
to inherit all symmetries of the MPS and will hence be invariant under the
transformation `X_g ρ X_g† = ρ`." -/
theorem commute_boundaryState_of_symmetry
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    {u : Matrix (Fin d) (Fin d) ℂ} (hu : u * uᴴ = 1)
    {X : GL (Fin D) ℂ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hX : ∀ i, ∑ j : Fin d, u i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    Commute Λ (X : Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨W, hWW, hWW', hWΛ, c, -, hc⟩ :=
    exists_unitary_gauge_of_symmetry hA hNorm hΛpos hΛfix hu hζ hX
  have hcomm : W * Λ = Λ * W := by
    calc W * Λ = W * Λ * (Wᴴ * W) := by rw [hWW', Matrix.mul_one]
      _ = (W * Λ * Wᴴ) * W := by simp only [Matrix.mul_assoc]
      _ = Λ * W := by rw [hWΛ]
  rw [hc]
  exact (Commute.smul_right hcomm.symm c)

/-- **Even degeneracy of the entanglement spectrum.**
Source: arXiv:2011.12127, §III.A, paragraph "Entanglement spectrum and edge
modes" (`Papers/2011.12127/TN-Review-main.tex` line 1172): a non-abelian
projective virtual representation forces every eigenvalue of the fixed point `ρ`
to be degenerate.

For an injective tensor with `E(1) = 1` and positive definite adjoint fixed point
`Λ`, if two unitary on-site symmetries have virtual gauges `X` and `Y` that
anticommute, `X Y = -Y X`, then every eigenspace of `Λ` has even dimension. -/
theorem even_finrank_eigenspace_of_anticommuting_gauges
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (hNorm : Kraus.transferMap A 1 = 1)
    {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛpos : Λ.PosDef)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    {u v : Matrix (Fin d) (Fin d) ℂ} (hu : u * uᴴ = 1) (hv : v * vᴴ = 1)
    {X Y : GL (Fin D) ℂ} {ζ η : ℂ} (hζ : ζ ≠ 0) (hη : η ≠ 0)
    (hX : ∀ i, ∑ j : Fin d, u i j • A j =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    (hY : ∀ i, ∑ j : Fin d, v i j • A j =
      η • ((Y : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    (hXY : (X : Matrix (Fin D) (Fin D) ℂ) * Y = -((Y : Matrix (Fin D) (Fin D) ℂ) * X))
    (μ : ℂ) :
    Even (Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' Λ) μ)) :=
  Matrix.even_finrank_eigenspace_of_anticommute (Units.isUnit X) (Units.isUnit Y)
    (commute_boundaryState_of_symmetry hA hNorm hΛpos hΛfix hu hζ hX)
    (commute_boundaryState_of_symmetry hA hNorm hΛpos hΛfix hv hη hY) hXY μ

/-- A virtual gauge of an on-site symmetry is also a virtual gauge of the
Kronecker-power symmetry of the blocked tensor: if the `g`-twist of `A` is
`R Aⁱ R⁻¹`, then the `g`-twist of `blockTensor A L` is `R (blockTensor A L)ᴵ R⁻¹`. -/
theorem twistedTensor_blockTensor_eq_gauge {G : Type*} [Monoid G] {A : MPSTensor d D}
    {U : G →* Matrix (Fin d) (Fin d) ℂ} {g : G} {R : GL (Fin D) ℂ}
    (hR : ∀ i, twistedTensor A U g i =
      (R : Matrix (Fin D) (Fin D) ℂ) * A i * ((R⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (L : ℕ) (I : Fin (blockPhysDim d L)) :
    twistedTensor (blockTensor A L) (blockKronAction L U) g I =
      (R : Matrix (Fin D) (Fin D) ℂ) * blockTensor A L I *
        ((R⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  rw [twistedTensor_blockTensor_comm]
  exact evalWord_gauge R hR _

end MPSTensor
