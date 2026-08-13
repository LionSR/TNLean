/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVExample411BinarySupport
import TNLean.MPS.MPDO.PhysicalSupportSALTransport

/-!
# Ambient two-qubit-site model for CPSV16 Example 4.11

This module embeds the effective binary-support tensor for CPSV16 Example 4.11
into the source-facing four-dimensional one-site space. The supported binary
label $k$ is sent to the two-qubit basis vector $|k,k\rangle$, indexed by
`finProdFinEquiv (k, k)`. The resulting periodic MPO is the sitewise isometric
congruence of the binary model, so its supported entries and trace are
transported exactly.

**Local fix (support embedding):** the effective physical dimension $2$ is not
identified with the ambient physical dimension $4$. It is included as the span
of $|0,0\rangle$ and $|1,1\rangle$.

**Scope restriction:** CPSV16, Example 4.11, lines 907--924 is cited only for
the four operators $\eta_{k,h}$ and their two-qubit site interpretation. The
embedding consequences below are project derivations recorded in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. No spectrum, entropy,
SAL, ZCL, or unsupported full-MPO entry theorem is asserted here.

## Main definitions

* `siteEmbedding`: the supported-label inclusion $k \mapsto |k,k\rangle$.
* `inclusion`: the corresponding rectangular one-site isometry.
* `ambientM`: the physical-dimension-$4$ tensor obtained from the binary model.
* `embedConfig`: the sitewise inclusion of a binary configuration.

## Main results

* `ambientM_supported`: the exact one-site supported-slice equality.
* `ambientM_left_unsupported` and `ambientM_right_unsupported`: unsupported
  one-site physical legs vanish.
* `mpo_ambientM_eq_singleKrausMap`: the operator-level sitewise congruence.
* `mpo_ambientM_supported_apply`: the positive-length supported MPO entries.
* `trace_mpo_ambientM`: equality of ambient and binary traces.
* `trace_mpo_ambientM_eq_partitionFunction` and
  `trace_mpo_ambientM_closed_form`: exact normalization formulas.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.CPSVExample411Ambient

open PhysicalSectorFactorization

/-- The supported binary label $k$ occupies the ambient two-qubit basis vector
$|k,k\rangle$.

Source for the two-qubit site interpretation: arXiv:1606.00608, Example 4.11,
lines 907--924. -/
def siteEmbedding (k : Fin 2) : Fin 4 := finProdFinEquiv (k, k)

/-- The supported-label map into the ambient two-qubit basis is injective. -/
theorem siteEmbedding_injective : Function.Injective siteEmbedding := by
  intro k h hkh
  exact congrArg Prod.fst (finProdFinEquiv.injective hkh)

/-- The rectangular inclusion of the supported one-site space into the
ambient two-qubit one-site space. -/
def inclusion : Matrix (Fin 4) (Fin 2) ℂ :=
  fun i k ↦ if i = siteEmbedding k then 1 else 0

@[simp] theorem inclusion_apply (i : Fin 4) (k : Fin 2) :
    inclusion i k = if i = siteEmbedding k then 1 else 0 := rfl

@[simp] theorem siteEmbedding_inj {k h : Fin 2} :
    siteEmbedding k = siteEmbedding h ↔ k = h :=
  siteEmbedding_injective.eq_iff

@[simp] theorem inclusion_siteEmbedding (k h : Fin 2) :
    inclusion (siteEmbedding k) h = if k = h then 1 else 0 := by
  rw [inclusion_apply]
  exact if_congr siteEmbedding_inj rfl rfl

/-- The one-site support inclusion is an isometry. -/
theorem inclusion_isometry : inclusionᴴ * inclusion = 1 := by
  ext k h
  rw [Matrix.mul_apply]
  by_cases hkh : k = h
  · subst h
    rw [Fintype.sum_eq_single (siteEmbedding k)]
    · simp
    · intro i hik
      simp only [Matrix.conjTranspose_apply, inclusion_apply]
      rw [if_neg hik]
      simp
  · simp only [Matrix.one_apply, if_neg hkh]
    have hemb : siteEmbedding k ≠ siteEmbedding h := fun h' ↦
      hkh (siteEmbedding_injective h')
    apply Finset.sum_eq_zero
    intro i _
    simp only [Matrix.conjTranspose_apply, inclusion_apply]
    by_cases hik : i = siteEmbedding k
    · rw [if_pos hik, if_neg (hik ▸ hemb)]
      simp
    · rw [if_neg hik]
      simp

/-- The source-facing ambient tensor, obtained by isometrically including the
binary support model in the two-qubit one-site space.

**Local fix (support embedding):** this is a support inclusion, not an equivalence between the
physical dimensions $2$ and $4$.

Source for the local $\eta_{k,h}$ family: arXiv:1606.00608, Example 4.11,
lines 907--924. The embedding is the project derivation documented in
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. -/
def ambientM : MPOTensor 4 4 :=
  changePhysicalBasis inclusion CPSVExample411BinarySupport.M

/-- Exact equality on the supported one-site physical slice. -/
theorem ambientM_supported (k h : Fin 2) :
    ambientM (siteEmbedding k) (siteEmbedding h) =
      CPSVExample411BinarySupport.M k h := by
  ext beta alpha
  simp [ambientM, changePhysicalBasis, physicalSlice, Matrix.mul_apply,
    Matrix.conjTranspose_apply, inclusion_apply]

/-- A physical ket leg outside the supported two-qubit basis slice vanishes. -/
theorem ambientM_left_unsupported (i : Fin 4)
    (hi : ∀ k : Fin 2, i ≠ siteEmbedding k) (j : Fin 4) :
    ambientM i j = 0 := by
  rw [ambientM, changePhysicalBasis_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro p _
  simp [inclusion_apply, hi p.1]

/-- A physical bra leg outside the supported two-qubit basis slice vanishes. -/
theorem ambientM_right_unsupported (j : Fin 4)
    (hj : ∀ k : Fin 2, j ≠ siteEmbedding k) (i : Fin 4) :
    ambientM i j = 0 := by
  rw [ambientM, changePhysicalBasis_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro p _
  simp [inclusion_apply, hj p.2]

/-- Sitewise embedding of a binary physical configuration into the ambient
four-dimensional site space. -/
def embedConfig {N : ℕ} (σ : Fin N → Fin 2) : Fin N → Fin 4 :=
  fun n ↦ siteEmbedding (σ n)

/-- The sitewise inclusion is the rectangular delta matrix on embedded
configurations. -/
@[simp] theorem sitewisePhysicalMatrix_inclusion_embedConfig {N : ℕ}
    (σ τ : Fin N → Fin 2) :
    sitewisePhysicalMatrix inclusion N (embedConfig σ) τ =
      if σ = τ then 1 else 0 := by
  simp only [sitewisePhysicalMatrix, embedConfig, inclusion_siteEmbedding]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

/-- The ambient periodic MPO is the sitewise single-Kraus congruence of the
binary periodic MPO. -/
theorem mpo_ambientM_eq_singleKrausMap (N : ℕ) :
    mpo ambientM N = singleKrausMap (sitewisePhysicalMatrix inclusion N)
      (mpo CPSVExample411BinarySupport.M N) := by
  exact (singleKrausMap_sitewisePhysicalMatrix_mpo inclusion CPSVExample411BinarySupport.M N).symm

/-- Supported positive-length entries of the ambient MPO are exactly the
binary cycle weights. -/
theorem mpo_ambientM_supported_apply {N : ℕ} [NeZero N]
    (σ τ : Fin N → Fin 2) :
    mpo ambientM N (embedConfig σ) (embedConfig τ) =
      if σ = τ then CPSVExample411BinarySupport.cycleWeight σ else 0 := by
  rw [mpo_ambientM_eq_singleKrausMap, singleKrausMap_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    sitewisePhysicalMatrix_inclusion_embedConfig, ite_mul, one_mul, zero_mul,
    Fintype.sum_ite_eq]
  have hstar (q : Fin N → Fin 2) :
      star (if τ = q then (1 : ℂ) else 0) = if τ = q then 1 else 0 := by
    split <;> simp
  simp_rw [hstar]
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
  change mpo CPSVExample411BinarySupport.M N σ τ = _
  exact CPSVExample411BinarySupport.mpo_M_apply σ τ

/-- The ambient and binary periodic MPOs have equal traces at every length. -/
theorem trace_mpo_ambientM (N : ℕ) :
    Matrix.trace (mpo ambientM N) = Matrix.trace (mpo CPSVExample411BinarySupport.M N) := by
  exact trace_mpo_changePhysicalBasis_of_isometry
    inclusion inclusion_isometry CPSVExample411BinarySupport.M N

/-- For positive length, the ambient MPO trace is the binary cycle partition
function. -/
theorem trace_mpo_ambientM_eq_partitionFunction {N : ℕ} [NeZero N] :
    Matrix.trace (mpo ambientM N) = CPSVExample411BinarySupport.partitionFunction N := by
  rw [trace_mpo_ambientM, CPSVExample411BinarySupport.mpo_M_eq_diagonal,
    Matrix.trace_diagonal, CPSVExample411BinarySupport.partitionFunction]

/-- The exact positive-length normalization of the ambient two-qubit-site MPO. -/
theorem trace_mpo_ambientM_closed_form {N : ℕ} [NeZero N] :
    Matrix.trace (mpo ambientM N) = ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N := by
  rw [trace_mpo_ambientM_eq_partitionFunction,
    CPSVExample411BinarySupport.partitionFunction_closed_form]

end MPOTensor.CPSVExample411Ambient
