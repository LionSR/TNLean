/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LocalPurificationRFP
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.Symmetry.MPDO.Defs

/-!
# Strong and weak symmetries through local purifications

**Source.** Sun 2025 (arXiv:2504.16985), Lemma `prop:purification`,
`References/2504.16985/main.tex` lines 183–187: if `O ρ = λ ρ`, every state in the support of
`ρ` is an eigenvector, and every purification `Ψ` of `ρ` satisfies
`(O ⊗ 1_anc) Ψ = λ Ψ`. The local purification `M^{ij} = ∑_k A^{(i,k)} ⊗ \bar A^{(j,k)}` and its
global form `ρ^{(L)} = tr_anc |Ψ_A⟩⟨Ψ_A|` are those of Cirac, Pérez-García, Schuch, Verstraete
2017 (arXiv:1606.00608), `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 744–751. The local
sufficient conditions are analogous to the dilation criteria of de Groot, Turzillo, Schuch
2022 (arXiv:2112.04483), `References/2112.04483/source/main.tex` lines 385–403 and 440–452,
where a symmetric unitary dilation with trivial (respectively symmetric) ancilla action gives
a strongly (respectively weakly) symmetric channel; that source states them for channels
only, and has no statement about matrix product density operators.

**Formalized here.** A purification `ρ = Φ Φ^†` of any matrix, with `Φ` indexed by system and
ancilla configurations, satisfies `O ρ = λ ρ` exactly when `O Φ = λ Φ`, that is,
`(O ⊗ 1_anc) Ψ = λ Ψ` (the source's lemma, in both directions). For a locally purified tensor
the purification is the spin-ancilla matrix product state of `A`, and strong symmetry of the
matrix product density operator is equivalent to the eigenvalue equation on that state. A
local gauge-phase covariance of `A` under `U` on the spin leg gives strong on-site symmetry
with eigenvalue `ζ^L`; under `U ⊗ V` with unitary `V` on the ancilla leg it gives weak on-site
symmetry.

**Scope restriction (boundary `X = 1`):** as in `TNLean/MPS/Symmetry/MPDO/Defs.lean`, the
density operators are the periodic operators `mpo M L`; documented in
`docs/paper-gaps/sun25_mpdo_symmetry_boundary_scope.tex`.

## Main definitions

* `MPOTensor.purificationAmplitude`: the purifying state of `A` as a system-by-ancilla matrix.

## Main results

* `Matrix.mul_mul_conjTranspose_eq_smul_iff`: `O (Φ Φ^†) = λ Φ Φ^† ↔ O Φ = λ Φ`.
* `MPOTensor.purificationDensity_eq_mul_conjTranspose`: `ρ = Φ Φ^†`.
* `MPOTensor.mpo_mul_eq_smul_iff_purification`,
  `MPOTensor.isStrongMPOSymmetry_iff_purification`: strong symmetry through the purification.
* `MPOTensor.isStrongOnSiteSymmetry_of_gaugePhase_purification`,
  `MPOTensor.isWeakOnSiteSymmetry_of_gaugePhase_purification`: local sufficient conditions
  (project results, analogous to the channel criteria of arXiv:2112.04483).

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

namespace Matrix

variable {m k : Type*} [Fintype m] [Fintype k]

/-- **The purification form of strong symmetry.**

Source: arXiv:2504.16985, Lemma `prop:purification`, lines 184–187: for a purification
`Ψ = ∑ Φ_{σκ} |σ⟩|κ⟩` of `ρ = Φ Φ^†`, `O ρ = λ ρ` holds exactly when `(O ⊗ 1_anc) Ψ = λ Ψ`,
that is `O Φ = λ Φ`. The forward direction is the source's lemma: `(O - λ) Φ` has vanishing
Gram matrix `(O - λ) ρ (O - λ)^†`. The converse is immediate. -/
theorem mul_mul_conjTranspose_eq_smul_iff (O : Matrix m m ℂ) (Φ : Matrix m k ℂ) (c : ℂ) :
    O * (Φ * Φᴴ) = c • (Φ * Φᴴ) ↔ O * Φ = c • Φ := by
  classical
  constructor
  · intro h
    have h1 : (O - c • 1) * (Φ * Φᴴ) = 0 := by
      rw [Matrix.sub_mul, h, Matrix.smul_mul, Matrix.one_mul, sub_self]
    have h2 : ((O - c • 1) * Φ) * ((O - c • 1) * Φ)ᴴ = 0 := by
      rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ Φ, h1, Matrix.zero_mul]
    have h3 := self_mul_conjTranspose_eq_zero.mp h2
    rwa [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h3
  · intro h
    rw [← Matrix.mul_assoc, h, Matrix.smul_mul]

end Matrix

namespace MPOTensor

variable {d D dK D' : ℕ}

/-- **The purifying state as a matrix.** The spin-ancilla matrix product state of `A`,
`Φ_{σκ} = tr[A^{(σ_1,κ_1)} ⋯ A^{(σ_L,κ_L)}]`, arranged with system configurations as rows and
ancilla configurations as columns.

Source: arXiv:1606.00608, lines 744–751 (the state `|Ψ_A⟩` whose ancillary trace is the
matrix product density operator). -/
noncomputable def purificationAmplitude (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (L : ℕ) : Matrix (Fin L → Fin d) (Fin L → Fin dK) ℂ :=
  Matrix.of fun σ κ =>
    MPSTensor.mpv (purificationTensor A) (fun n => finProdFinEquiv (σ n, κ n))

theorem purificationAmplitude_apply (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    {L : ℕ} (σ : Fin L → Fin d) (κ : Fin L → Fin dK) :
    purificationAmplitude A L σ κ =
      Matrix.trace ((List.ofFn fun l => A (σ l) (κ l)).prod) := by
  have hfun : (fun l : Fin L => purificationTensor A (finProdFinEquiv (σ l, κ l)))
      = fun l => A (σ l) (κ l) :=
    funext fun l => by
      change A (finProdFinEquiv (σ l, κ l)).divNat (finProdFinEquiv (σ l, κ l)).modNat = _
      rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp only [purificationAmplitude, Matrix.of_apply, MPSTensor.mpv_eq, MPSTensor.coeff_eq,
    MPSTensor.evalWord_ofFn_eq_prod, hfun]

/-- The ancillary trace of the purifying state is `Φ Φ^†`.

Bridge: arXiv:1606.00608, line 751, in matrix form. -/
theorem purificationDensity_eq_mul_conjTranspose
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (L : ℕ) :
    purificationDensity A L = purificationAmplitude A L * (purificationAmplitude A L)ᴴ := by
  ext σ τ
  simp [purificationDensity, purificationAmplitude, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- **Strong symmetry at one length through the local purification.**

Source: arXiv:2504.16985, Lemma `prop:purification`, lines 184–187, for the purification of
arXiv:1606.00608 lines 744–751: `O ρ^{(L)} = λ ρ^{(L)}` exactly when, for every ancilla
configuration `κ`, the system vector `Φ_{·κ}` of the purifying state is an eigenvector of `O`
with eigenvalue `λ`, which is `(O ⊗ 1_anc) Ψ_A = λ Ψ_A`. -/
theorem mpo_mul_eq_smul_iff_purification
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    {L : ℕ} (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) (c : ℂ) :
    O * mpo M L = c • mpo M L ↔
      ∀ κ : Fin L → Fin dK,
        O *ᵥ (fun σ => purificationAmplitude A L σ κ) =
          c • fun σ => purificationAmplitude A L σ κ := by
  rw [mpo_eq_purificationDensity A e hM, purificationDensity_eq_mul_conjTranspose,
    Matrix.mul_mul_conjTranspose_eq_smul_iff]
  constructor
  · intro h κ
    funext σ
    have := congrFun (congrFun h σ) κ
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro h
    ext σ κ
    have := congrFun (h κ) σ
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- **Strong symmetry of the family through the local purification.**

Source: arXiv:2504.16985, Lemma `prop:purification`, lines 184–187, at every positive length:
the matrix product density operator is strongly symmetric under the family `O_a` with
eigenvalues `λ_a^{(L)}` exactly when the purifying state satisfies
`(O_a^{(L)} ⊗ 1_anc) Ψ_A = λ_a^{(L)} Ψ_A`. -/
theorem isStrongMPOSymmetry_iff_purification {ι : Type*} {χ : ι → ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (O : ∀ a, MPOTensor d (χ a)) (c : ι → ℕ → ℂ) :
    IsStrongMPOSymmetry O M c ↔
      ∀ a L, 0 < L → ∀ κ : Fin L → Fin dK,
        mpo (O a) L *ᵥ (fun σ => purificationAmplitude A L σ κ) =
          c a L • fun σ => purificationAmplitude A L σ κ := by
  refine forall_congr' fun a => forall_congr' fun L => forall_congr' fun _ => ?_
  exact mpo_mul_eq_smul_iff_purification A e hM _ _

/-! ### Local sufficient conditions -/

/-- Twisting the spin leg of the purifying tensor by `u` acts on the purifying state by
`u^{⊗L} ⊗ 1_anc`. -/
theorem finKronecker_mul_purificationAmplitude
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (u : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) :
    (Matrix.finKronecker fun _ : Fin L => u) * purificationAmplitude A L =
      purificationAmplitude (fun i k => ∑ j, u i j • A j k) L := by
  ext σ κ
  rw [purificationAmplitude_apply, Matrix.trace_prod_ofFn_sum_smul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Matrix.finKronecker_apply, purificationAmplitude_apply]

/-- Twisting the ancilla leg of the purifying tensor by `v` acts on the purifying state by
`1 ⊗ v^{⊗L}`, which multiplies the system-by-ancilla matrix on the right by the transpose. -/
theorem purificationAmplitude_mul_finKronecker_transpose
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (v : Matrix (Fin dK) (Fin dK) ℂ)
    (L : ℕ) :
    purificationAmplitude A L * (Matrix.finKronecker fun _ : Fin L => v)ᵀ =
      purificationAmplitude (fun i k => ∑ l, v k l • A i l) L := by
  ext σ κ
  rw [purificationAmplitude_apply, Matrix.trace_prod_ofFn_sum_smul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Matrix.transpose_apply, Matrix.finKronecker_apply, purificationAmplitude_apply, mul_comm]

/-- A gauge-phase covariant purifying tensor has a rescaled purifying state: if
`B^{(i,k)} = ζ X A^{(i,k)} X^{-1}`, then `Φ_B = ζ^L Φ_A`. -/
theorem purificationAmplitude_of_gaugePhase
    {A B : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ} (X : GL (Fin D') ℂ) (ζ : ℂ)
    (hB : ∀ i k, B i k = ζ • ((X : Matrix (Fin D') (Fin D') ℂ) * A i k *
      ((X⁻¹ : GL (Fin D') ℂ) : Matrix (Fin D') (Fin D') ℂ))) (L : ℕ) :
    purificationAmplitude B L = ζ ^ L • purificationAmplitude A L := by
  ext σ κ
  simp only [purificationAmplitude, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact MPSTensor.mpv_eq_pow_mul_of_gaugePhase (purificationTensor A) (purificationTensor B)
    X ζ (fun p => hB _ _) L _

/-- **Strong on-site symmetry from a trivial ancilla action.**

Bridge: for the local purification of arXiv:1606.00608 lines 744–751, if acting with `U_g`
on the spin leg of the purifying tensor is a gauge transformation up to the scalar `ζ_g`,
`∑_j (U_g)_{ij} A^{(j,k)} = ζ_g X_g A^{(i,k)} X_g^{-1}`, then the matrix product density
operator is strongly symmetric under `U_g^{⊗L}` with eigenvalue `ζ_g^L`
(arXiv:2504.16985, line 182). No normality of `A` is used. This is analogous to, but not a
case of, the channel statement of arXiv:2112.04483, lines 448–452, where a unitary dilation
with `U_g ⊗ 1` covariance gives a strongly symmetric channel. -/
theorem isStrongOnSiteSymmetry_of_gaugePhase_purification {G : Type*} [Monoid G]
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (X : G → GL (Fin D') ℂ) (ζ : G → ℂ)
    (hA : ∀ g i k, ∑ j, U g i j • A j k = ζ g • ((X g : Matrix (Fin D') (Fin D') ℂ) * A i k *
      (((X g)⁻¹ : GL (Fin D') ℂ) : Matrix (Fin D') (Fin D') ℂ))) :
    IsStrongOnSiteSymmetry M U fun g L => ζ g ^ L := by
  intro g L _
  change mpo (onSite (U g)) L * mpo M L = ζ g ^ L • mpo M L
  rw [mpo_onSite, mpo_eq_purificationDensity A e hM, purificationDensity_eq_mul_conjTranspose,
    Matrix.mul_mul_conjTranspose_eq_smul_iff, finKronecker_mul_purificationAmplitude]
  exact purificationAmplitude_of_gaugePhase (X g) (ζ g) (hA g) L

/-- A square matrix with `v^† v = 1` has unitary transpose. -/
private theorem transpose_conjTranspose_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {v : Matrix n n ℂ} (hv : vᴴ * v = 1) : (vᵀ)ᴴ * vᵀ = 1 := by
  have hv' : v * vᴴ = 1 := mul_eq_one_comm.mp hv
  have hT : (vᵀ)ᴴ = (vᴴ)ᵀ := by ext; simp
  rw [hT, ← Matrix.transpose_mul, hv', Matrix.transpose_one]

/-- **Weak on-site symmetry from a symmetric ancilla action.**

Bridge: for the local purification of arXiv:1606.00608 lines 744–751, if acting with
`U_g ⊗ V_g` on the spin and ancilla legs of the purifying tensor, `V_g` unitary, is a gauge
transformation up to a scalar, then the matrix product density operator commutes with
`U_g^{⊗L}` (arXiv:2504.16985, line 182). The scalar has `|ζ_g|^{2L} = 1` whenever
`ρ^{(L)} ≠ 0`, forced by `tr (U ρ U^†) = tr ρ`. This is analogous to the channel statement of
arXiv:2112.04483, lines 440–447, where a unitary dilation covariant under `U_g ⊗ U_g^A` with
an invariant ancilla state `U_g^A |a⟩ = |a⟩` gives a weakly symmetric channel. Here there is
no ancilla state to be invariant, and `g ↦ V_g` need not be a representation. -/
theorem isWeakOnSiteSymmetry_of_gaugePhase_purification {G : Type*} [Monoid G]
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1)
    (V : G → Matrix (Fin dK) (Fin dK) ℂ) (hV : ∀ g, (V g)ᴴ * V g = 1)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (X : G → GL (Fin D') ℂ) (ζ : G → ℂ)
    (hA : ∀ g i k, ∑ l, V g k l • ∑ j, U g i j • A j l =
      ζ g • ((X g : Matrix (Fin D') (Fin D') ℂ) * A i k *
        (((X g)⁻¹ : GL (Fin D') ℂ) : Matrix (Fin D') (Fin D') ℂ))) :
    IsWeakOnSiteSymmetry M U := by
  intro g L _
  change Commute (mpo (onSite (U g)) L) (mpo M L)
  set Φ := purificationAmplitude A L
  set u := Matrix.finKronecker fun _ : Fin L => U g
  set W := (Matrix.finKronecker fun _ : Fin L => V g)ᵀ
  have hu : uᴴ * u = 1 := Matrix.finKronecker_conjTranspose_mul_self (hU g)
  have hW : W * Wᴴ = 1 := by
    have h1 : Wᴴ * W = 1 := by
      simp only [W, Matrix.finKronecker_transpose]
      exact Matrix.finKronecker_conjTranspose_mul_self (transpose_conjTranspose_mul_self (hV g))
    exact mul_eq_one_comm.mp h1
  have hΦ : u * Φ * W = ζ g ^ L • Φ := by
    rw [finKronecker_mul_purificationAmplitude, purificationAmplitude_mul_finKronecker_transpose]
    exact purificationAmplitude_of_gaugePhase (X g) (ζ g) (hA g) L
  have hρ : mpo M L = Φ * Φᴴ := by
    rw [mpo_eq_purificationDensity A e hM, purificationDensity_eq_mul_conjTranspose]
  -- `u ρ u^† = r ρ` with `r = |ζ|^{2L}`.
  have hconj : u * (Φ * Φᴴ) * uᴴ = (ζ g ^ L * star (ζ g ^ L)) • (Φ * Φᴴ) := by
    have h1 : u * (Φ * Φᴴ) * uᴴ = (u * Φ * W) * (u * Φ * W)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc W, hW, Matrix.one_mul]
    rw [h1, hΦ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mpo_onSite, hρ]
  by_cases h0 : Φ = 0
  · rw [h0, Matrix.zero_mul]
    exact Commute.zero_right _
  have htr : (Φ * Φᴴ).trace ≠ 0 := fun h =>
    h0 (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h)
  have hr : ζ g ^ L * star (ζ g ^ L) = 1 := by
    have h1 := congrArg Matrix.trace hconj
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul] at h1
    exact (mul_eq_right₀ htr).mp h1.symm
  rw [hr, one_smul] at hconj
  change u * (Φ * Φᴴ) = (Φ * Φᴴ) * u
  calc u * (Φ * Φᴴ) = u * (Φ * Φᴴ) * uᴴ * u := by
        rw [Matrix.mul_assoc _ uᴴ, hu, Matrix.mul_one]
    _ = (Φ * Φᴴ) * u := by rw [hconj]

end MPOTensor
