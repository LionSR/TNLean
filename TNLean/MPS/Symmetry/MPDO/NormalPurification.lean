/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.NormalTensorDichotomy
import TNLean.MPS.Symmetry.MPDO.Purification

/-!
# Strong on-site symmetry of a matrix product density operator with a normal purification

**Source.** Sun 2025 (arXiv:2504.16985), `References/2504.16985/main.tex` line 182 (strong
symmetry `O ρ^{(L)} = λ^{(L)} ρ^{(L)}`) and Lemma `prop:purification`, lines 183–187 (every
purification satisfies `(O ⊗ 1_anc) Ψ = λ Ψ`), applied to the local purification
`M^{ij} = ∑_k A^{(i,k)} ⊗ \bar A^{(j,k)}` of Cirac, Pérez-García, Schuch, Verstraete 2017
(arXiv:1606.00608), `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 744–751. The local form of
the conclusion is analogous to the strongly symmetric dilations of de Groot, Turzillo, Schuch
2022 (arXiv:2112.04483), `References/2112.04483/source/main.tex` lines 448–452, where the
symmetry acts trivially on the ancilla; that source treats channels, not matrix product
density operators.

**Formalized here.** Bridge: if the spin-ancilla tensor `A^{(i,k)}` of a local purification is
normal and the matrix product density operator is strongly symmetric under a unitary on-site
representation `U_g^{⊗L}`, then acting with `U_g` on the spin leg of `A` is a gauge
transformation up to a unit scalar `ζ_g`, with no action on the ancilla leg. With
`TNLean/MPS/Symmetry/MPDO/Purification.lean` this makes strong on-site symmetry equivalent to
that local covariance, and the strong eigenvalues are `ζ_g^L` at every length where
`ρ^{(L)} ≠ 0`. The proof passes through the purification lemma: `(U_g^{⊗L} ⊗ 1) Ψ_A = c Ψ_A`
at every positive length, the twisted tensor is again normal, and the proportional
fundamental theorem for normal tensors (arXiv:1606.00608, Corollary `eqV`, lines 1121–1128,
and Lemma `equalMPS`, lines 1080–1117) turns proportional purifications into a gauge phase.

The projective virtual representation `g ↦ X_g` and its cocycle are not constructed here;
they need uniqueness of the gauge between normal tensors up to a scalar.

**Scope restriction (boundary `X = 1`):** as in `TNLean/MPS/Symmetry/MPDO/Defs.lean`, the
density operators are the periodic operators `mpo M L`; documented in
`docs/paper-gaps/sun25_mpdo_symmetry_boundary_scope.tex`.

## Main definitions

* `MPOTensor.spinTwist`: the purifying tensor with `u` applied to its spin leg.

## Main results

* `MPOTensor.isNormalTensor_purificationTensor_spinTwist`: a unitary spin twist of a normal
  purifying tensor is normal.
* `MPOTensor.exists_gaugePhase_of_isStrongOnSiteSymmetry_of_isNormalTensor`: strong symmetry
  gives the local gauge phase.
* `MPOTensor.exists_isStrongOnSiteSymmetry_iff_of_isNormalTensor`: the equivalence.
* `MPOTensor.IsStrongOnSiteSymmetry.exists_eq_pow_of_isNormalTensor`: the eigenvalues are
  powers of unit scalars.

## References
- [arXiv:2504.16985](https://arxiv.org/abs/2504.16985) -- X.-Q. Sun, *Anomalous matrix
  product operator symmetries and 1D mixed-state phases*
- [arXiv:2112.04483](https://arxiv.org/abs/2112.04483) -- C. de Groot, A. Turzillo,
  N. Schuch, *Symmetry protected topological order in open quantum systems*
- [arXiv:1606.00608](https://arxiv.org/abs/1606.00608) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product density operators: Renormalization fixed points
  and boundary theories*
-/

open scoped Matrix ComplexOrder BigOperators Kronecker
open Filter MPSTensor

namespace MPOTensor

variable {d D dK D' : ℕ}

/-- **The spin twist of a purifying tensor.** `(spinTwist u A)^{(i,k)} = ∑_j u_{ij} A^{(j,k)}`:
the operator `u` acts on the spin leg and the ancilla leg is untouched. -/
noncomputable def spinTwist (u : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) :
    Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ :=
  fun i k => ∑ j, u i j • A j k

/-- A sum over the combined spin-ancilla index is a double sum. -/
private theorem sum_purificationTensor {β : Type*} [AddCommMonoid β]
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (f : Matrix (Fin D') (Fin D') ℂ → β) :
    ∑ p, f (purificationTensor A p) = ∑ i, ∑ k, f (A i k) := by
  rw [← (finProdFinEquiv : Fin d × Fin dK ≃ Fin (d * dK)).sum_comp, Fintype.sum_prod_type]
  simp [purificationTensor]

/-- A unitary spin twist leaves the transfer map of the purifying tensor unchanged. -/
theorem transferMap_purificationTensor_spinTwist {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : uᴴ * u = 1) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) :
    Kraus.transferMap (purificationTensor (spinTwist u A)) =
      Kraus.transferMap (purificationTensor A) := by
  refine LinearMap.ext fun X => ?_
  rw [Kraus.transferMap_apply, Kraus.transferMap_apply,
    sum_purificationTensor (f := fun B => B * X * Bᴴ),
    sum_purificationTensor (f := fun B => B * X * Bᴴ), Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ =>
    kraus_same_map_of_isometry_combination (fun i => spinTwist u A i k) (fun j => A j k) u hu
      (fun _ => rfl) X

/-- A unitary spin twist of an irreducible purifying tensor is irreducible: the untwisted
tensor is recovered as `A^{(j,k)} = ∑_i (u^†)_{ji} (spinTwist u A)^{(i,k)}`. -/
theorem isIrreducibleFamily_purificationTensor_spinTwist {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : uᴴ * u = 1) {A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ}
    (hA : Kraus.IsIrreducibleFamily (purificationTensor A)) :
    Kraus.IsIrreducibleFamily (purificationTensor (spinTwist u A)) := by
  rintro ⟨P, hP, hP0, hP1, hinv⟩
  refine hA ⟨P, hP, hP0, hP1, fun p => ?_⟩
  have hinv' : ∀ i k, (1 - P) * spinTwist u A i k * P = 0 := fun i k => by
    simpa [purificationTensor] using hinv (finProdFinEquiv (i, k))
  have hrec : ∀ j k, A j k = ∑ i, uᴴ j i • spinTwist u A i k := by
    intro j k
    simp only [spinTwist, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, hu, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (1 - P) * A p.divNat p.modNat * P = 0
  rw [hrec, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_eq_zero fun i _ => by rw [Matrix.mul_smul, Matrix.smul_mul, hinv', smul_zero]

/-- **A unitary spin twist of a normal purifying tensor is normal.** -/
theorem isNormalTensor_purificationTensor_spinTwist {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : uᴴ * u = 1) {A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ}
    (hA : IsNormalTensor (purificationTensor A)) :
    IsNormalTensor (purificationTensor (spinTwist u A)) where
  no_invariant_proj := isIrreducibleFamily_purificationTensor_spinTwist hu hA.no_invariant_proj
  spectral_radius_one := by
    rw [transferMap_purificationTensor_spinTwist hu]
    exact hA.spectral_radius_one
  primitive_transfer := by
    rw [transferMap_purificationTensor_spinTwist hu]
    exact hA.primitive_transfer

/-- **Strong symmetry at one length as proportional purifications.**

Source: arXiv:2504.16985, Lemma `prop:purification`, lines 184–187: if
`u^{⊗L} ρ^{(L)} = c ρ^{(L)}` for the local purification of arXiv:1606.00608 lines 744–751, then
the spin twist of the purifying tensor generates `c` times its matrix product vector at
length `L`. -/
theorem mpv_purificationTensor_spinTwist_of_mpo_mul_eq_smul
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    {u : Matrix (Fin d) (Fin d) ℂ} {L : ℕ} {c : ℂ}
    (h : mpo (onSite u) L * mpo M L = c • mpo M L) (w : Fin L → Fin (d * dK)) :
    mpv (purificationTensor (spinTwist u A)) w = c * mpv (purificationTensor A) w := by
  rw [mpo_onSite, mpo_eq_purificationDensity A e hM, purificationDensity_eq_mul_conjTranspose,
    Matrix.mul_mul_conjTranspose_eq_smul_iff, finKronecker_mul_purificationAmplitude] at h
  have h1 := congrFun (congrFun h fun n => (finProdFinEquiv.symm (w n)).1)
    fun n => (finProdFinEquiv.symm (w n)).2
  simp only [purificationAmplitude, Matrix.of_apply, Prod.mk.eta, Equiv.apply_symm_apply,
    Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

/-- **Strong on-site symmetry with a normal purification is a local gauge phase.**

Bridge: for the local purification of arXiv:1606.00608 lines 744–751 with normal purifying
tensor, strong on-site symmetry under a unitary representation (arXiv:2504.16985, line 182)
forces `∑_j (U_g)_{ij} A^{(j,k)} = ζ_g X_g A^{(i,k)} X_g^{-1}` with `|ζ_g| = 1`: the symmetry
acts on the purification by a virtual gauge and trivially on the ancilla leg, in analogy
with the strongly symmetric dilations of arXiv:2112.04483, lines 448–452. By Lemma
`prop:purification` (arXiv:2504.16985, lines 184–187) the twisted and untwisted purifications
are proportional at every positive length; the proportionality scalar is nonzero at all large
lengths because the twisted tensor is normal, and Corollary `eqV` and Lemma `equalMPS` of
arXiv:1606.00608 (lines 1080–1128) give the gauge phase. -/
theorem exists_gaugePhase_of_isStrongOnSiteSymmetry_of_isNormalTensor [NeZero D']
    {G : Type*} [Monoid G] (U : G →* Matrix (Fin d) (Fin d) ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    {c : G → ℕ → ℂ} (hsym : IsStrongOnSiteSymmetry M U c)
    (hA : IsNormalTensor (purificationTensor A)) (g : G) :
    ∃ (X : GL (Fin D') ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧ ∀ i k, ∑ j, U g i j • A j k =
      ζ • ((X : Matrix (Fin D') (Fin D') ℂ) * A i k *
        ((X⁻¹ : GL (Fin D') ℂ) : Matrix (Fin D') (Fin D') ℂ)) := by
  set B := purificationTensor (spinTwist (U g) A) with hBdef
  have hB : IsNormalTensor B := isNormalTensor_purificationTensor_spinTwist (hU g) hA
  have hrel : ∀ L, 0 < L → ∀ w : Fin L → Fin (d * dK),
      mpv B w = c g L * mpv (purificationTensor A) w := fun L hL w =>
    mpv_purificationTensor_spinTwist_of_mpo_mul_eq_smul A e hM (hsym g L hL) w
  have hProp : EventuallyNonzeroProportionalMPV₂ (purificationTensor A) B := by
    have hev : ∀ᶠ N in atTop, mpvOverlap (d := d * dK) B B N ≠ 0 :=
      hB.selfOverlap_tendsto_one.eventually_ne one_ne_zero
    filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
    have hc : c g N ≠ 0 := by
      intro hc0
      apply hN
      simp only [mpvOverlap]
      simp_rw [hrel N hN0, hc0]
      simp
    refine ⟨(c g N)⁻¹, inv_ne_zero hc, fun σ => ?_⟩
    rw [hrel N hN0, inv_mul_cancel_left₀ hc]
  obtain ⟨a, ha, hpow⟩ := hProp.exists_unit_phase_power_of_isNormalTensor hA hB
  have ha0 : a ≠ 0 := Complex.ne_zero_of_norm_eq_one ha
  have hphase : MPVBlockPhaseEquiv (purificationTensor A) B := by
    refine ⟨a⁻¹, inv_ne_zero ha0, fun N hN σ => ?_⟩
    rw [hpow N hN σ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0, one_pow, one_mul]
  obtain ⟨hdim, X, ζ, _, hX⟩ := hphase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor hA hB
  refine ⟨X, ζ, norm_eq_one_of_gaugePhase_cast_of_isNormalTensor hA hB hdim hX,
    fun i k => ?_⟩
  have h1 := hX (finProdFinEquiv (i, k))
  simpa [hBdef, purificationTensor, spinTwist] using h1

/-- **Strong on-site symmetry is equivalent to a local gauge phase, for normal
purifications.**

Bridge: combines `exists_gaugePhase_of_isStrongOnSiteSymmetry_of_isNormalTensor` with the
sufficient condition `isStrongOnSiteSymmetry_of_gaugePhase_purification`. -/
theorem exists_isStrongOnSiteSymmetry_iff_of_isNormalTensor [NeZero D']
    {G : Type*} [Monoid G] (U : G →* Matrix (Fin d) (Fin d) ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (hA : IsNormalTensor (purificationTensor A)) :
    (∃ c, IsStrongOnSiteSymmetry M U c) ↔
      ∀ g, ∃ (X : GL (Fin D') ℂ) (ζ : ℂ), ‖ζ‖ = 1 ∧ ∀ i k, ∑ j, U g i j • A j k =
        ζ • ((X : Matrix (Fin D') (Fin D') ℂ) * A i k *
          ((X⁻¹ : GL (Fin D') ℂ) : Matrix (Fin D') (Fin D') ℂ)) := by
  constructor
  · rintro ⟨c, hsym⟩ g
    exact exists_gaugePhase_of_isStrongOnSiteSymmetry_of_isNormalTensor U hU A e hM hsym hA g
  · intro h
    choose X ζ _ hX using h
    exact ⟨_, isStrongOnSiteSymmetry_of_gaugePhase_purification U A e hM X ζ hX⟩

/-- **Strong eigenvalues are powers of unit scalars, for normal purifications.**

Bridge: under the hypotheses of `exists_gaugePhase_of_isStrongOnSiteSymmetry_of_isNormalTensor`,
there are unit scalars `ζ_g` with `c_g^{(L)} = ζ_g^L` at every positive length where
`ρ^{(L)} ≠ 0`; at the remaining lengths the eigenvalue of arXiv:2504.16985, line 182, is not
determined. -/
theorem IsStrongOnSiteSymmetry.exists_eq_pow_of_isNormalTensor [NeZero D']
    {G : Type*} [Monoid G] {U : G →* Matrix (Fin d) (Fin d) ℂ} (hU : ∀ g, (U g)ᴴ * U g = 1)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    {c : G → ℕ → ℂ} (hsym : IsStrongOnSiteSymmetry M U c)
    (hA : IsNormalTensor (purificationTensor A)) :
    ∃ ζ : G → ℂ, (∀ g, ‖ζ g‖ = 1) ∧
      ∀ g L, 0 < L → mpo M L ≠ 0 → c g L = ζ g ^ L := by
  choose X ζ hζ hX using
    exists_gaugePhase_of_isStrongOnSiteSymmetry_of_isNormalTensor U hU A e hM hsym hA
  refine ⟨ζ, hζ, fun g L hL hρ => ?_⟩
  have h1 := hsym g L hL
  have h2 := isStrongOnSiteSymmetry_of_gaugePhase_purification U A e hM X ζ hX g L hL
  exact smul_left_injective ℂ hρ (h1.symm.trans h2)

end MPOTensor
