/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Overlap
import QICLean.Circuit.Compile.ImageReflection
import QICLean.ManyBody.Sites.Support
import QICLean.Circuit.Geometry.Graph
import QICLean.Circuit.Model.CleanWorkspace

/-!
# Logical support is preserved by amplification

Unitary image conjugation, both reflections, their products, and arbitrary
powers remain supported on the same logical sites. The prescribed global
minus sign is a scalar identity and adds no support. These are operator
identities on the complete logical space; sites outside the support need
not be initialized.

The results concern support. Isometry, success probability, clean workspace,
and the physical circuit construction are established separately. Source:
the recursive image-reflection construction in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

It also contains the following results.

* `MPUCircuit.exists_exact_clean_amplification_circuit`: exact amplification circuits with a shared
  initialized workspace.
-/

open Matrix MPSTensor QuantumCircuit

section SupportedAmplification

namespace MPSPreparation

variable {d n : ℕ} {S : Finset (Fin n)}

/-- Reflection about a supported matrix preserves its support. Source:
initialized and success reflections in Section 5 of the circuit audit. -/
theorem subspaceReflection_mem_supportedOperators
    {P : Matrix (Cfg d n) (Cfg d n) ℂ} (hP : P ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    Matrix.subspaceReflection P ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S :=
  sub_mem (one_mem (ManyBody.supportedOperators _ S))
    (SMulMemClass.smul_mem (2 : ℂ) hP)

/-- Powers do not enlarge logical support. Source: repeated amplification
in Section 5 of the circuit audit. -/
theorem pow_mem_supportedOperators
    {X : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hX : X ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) (ℓ : ℕ) :
    X ^ ℓ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S := by
  induction ℓ with
  | zero => simpa only [pow_zero] using (one_mem (ManyBody.supportedOperators _ S))
  | succ ℓ ih => simpa only [pow_succ] using mul_mem ih hX

/-- Conjugating an initialized reflection by a supported unitary preserves
support on every logical input. Source: `Matrix.subspaceReflection_image`
and Section 5 of the circuit audit. -/
theorem subspaceReflection_image_mem_supportedOperators
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hR : Matrix.subspaceReflection (E * Eᴴ) ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    Matrix.subspaceReflection ((Z * E) * (Z * E)ᴴ) ∈ ManyBody.supportedOperators
        (fun _ ↦ Fin d) S := by
  rw [Matrix.subspaceReflection_image Z E hZ]
  have hstar : Zᴴ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S := by
    simpa only [Matrix.star_eq_conjTranspose] using star_mem hZS
  exact mul_mem (mul_mem hZS hR) hstar

/-- Both logical reflections and the scalar minus sign in one amplification
round preserve the same support. Source: phase-exact amplification in
Section 5 of the circuit audit. -/
theorem postselectionAmplificationStep_mem_supportedOperators
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (P : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hR : Matrix.subspaceReflection (E * Eᴴ) ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hP : Matrix.subspaceReflection P ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) :
    Matrix.postselectionAmplificationStep (Z * E) P ∈ ManyBody.supportedOperators
        (fun _ ↦ Fin d) S :=
  neg_mem
    (mul_mem
      (subspaceReflection_image_mem_supportedOperators Z E hZ hZS hR) hP)

/-- The complete logical amplification operator has the original support,
including its exact global phase and all rounds. Source: recursive parent
support in Section 5 of the circuit audit. -/
theorem postselectionAmplification_mem_supportedOperators
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (P : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hR : Matrix.subspaceReflection (E * Eᴴ) ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hP : Matrix.subspaceReflection P ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) (ℓ : ℕ) :
    Matrix.postselectionAmplificationStep (Z * E) P ^ ℓ * Z ∈ ManyBody.supportedOperators
        (fun _ ↦ Fin d) S :=
  mul_mem
    (pow_mem_supportedOperators
      (postselectionAmplificationStep_mem_supportedOperators Z E P hZ hZS hR hP) ℓ) hZS

/-- A supported initial image Gram and supported success matrix suffice for
support of the full amplification operator. No support hypothesis on the
constructed image reflection is supplied. Source: the two-reflection
construction in Section 5 of the circuit audit. -/
theorem postselectionAmplification_mem_supportedOperators_of_projection_support
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (P : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hE : E * Eᴴ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hP : P ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) (ℓ : ℕ) :
    Matrix.postselectionAmplificationStep (Z * E) P ^ ℓ * Z ∈ ManyBody.supportedOperators
        (fun _ ↦ Fin d) S :=
  postselectionAmplification_mem_supportedOperators Z E P hZ hZS
    (subspaceReflection_mem_supportedOperators hE)
    (subspaceReflection_mem_supportedOperators hP) ℓ

end MPSPreparation

end SupportedAmplification

section ExactCleanAmplificationCircuit

/-!
## Exact amplification circuits with a shared initialized workspace

The implementing child circuit and the two reflection circuits are the
induction data. Their common workspace is represented by an isometric
inclusion `J`. Each circuit implements its logical unitary on the entire
initialized logical space. The inverse child call is therefore clean,
and all reflection rounds reuse the same workspace.

The resulting circuit acts exactly as normalized postselection on the
specified input isometry, with its complete global phase retained. The phase
`-1` of each round is a one-site unitary and costs no gate.
Source: the circuit assembly in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

/-- Clean child and reflection circuits assemble into the phase-exact
amplification circuit. The workspace inclusion and each clean action are
the induction data, and the logical child unitarity and inverse cleanup
are derived from them. Source: the circuit assembly in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_exact_clean_amplification_circuit
    {d n K B L : ℕ} {κ m : Type*} [Fintype κ] [Fintype m]
    [DecidableEq κ] [DecidableEq m]
    (hn : 2 ≤ n) (J : Matrix (Cfg d n) κ ℂ) (hJ : J.IsIsometry)
    (E : Matrix κ m ℂ) (hE : E.IsIsometry)
    (Z : Matrix κ κ ℂ) (U R S : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hU : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) K U)
    (hUclean : IsCleanImplementation J U Z)
    (hR : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) B R)
    (hRclean : IsCleanImplementation J R (subspaceReflection (E * Eᴴ)))
    (P : Matrix κ κ ℂ) (hP : IsStarProjection P)
    (hS : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) L S)
    (hSclean : IsCleanImplementation J S (subspaceReflection P))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hprob : (Z * E)ᴴ * P * (Z * E) =
      (Real.sin (Real.pi / (4 * (ℓ : ℝ) + 2)) : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    ∃ W : Matrix (Cfg d n) (Cfg d n) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (ℓ * (2 * K + B + L) + K) W ∧
      IsCleanImplementation J W
        (postselectionAmplificationStep (Z * E) P ^ ℓ * Z) ∧
      W * (J * E) = J * postselectionSuccess (Z * E) P
        (Real.sin (Real.pi / (4 * (ℓ : ℝ) + 2))) := by
  have hZ := hUclean.logical_mem_unitaryGroup hJ hU.mem_unitaryGroup
  have hZgram : Zᴴ * Z = 1 := mem_unitaryGroup_iff'.mp hZ
  have hV : (Z * E)ᴴ * (Z * E) = 1 := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Zᴴ Z, hZgram, Matrix.one_mul, hE]
  let Q : Matrix (Cfg d n) (Cfg d n) ℂ := -(U * R * Uᴴ * S)
  have hQ : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * K + B + L) Q := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have hprod := ((hU.mul hR).mul hU.conjTranspose).mul hS
    have hphase := IsGateProduct.smul_one (Γ := Geometry.graph (SimpleGraph.pathGraph n))
      (X := fun _ : Fin n ↦ Fin d) (μ := -1) (by simp) 0
    have h := hphase.mul hprod
    rw [neg_one_smul, neg_mul, Matrix.one_mul, zero_add,
      show K + B + K + L = 2 * K + B + L by omega] at h
    exact h
  have hQclean : IsCleanImplementation J Q (postselectionAmplificationStep (Z * E) P) := by
    have hprod := ((hUclean.mul hRclean).mul
      (hUclean.conjTranspose_of_isometry hJ hU.mem_unitaryGroup)).mul hSclean
    change (U * R * Uᴴ * S) * J =
      J * (Z * subspaceReflection (E * Eᴴ) * Zᴴ * subspaceReflection P) at hprod
    change -(U * R * Uᴴ * S) * J = J *
      -(subspaceReflection ((Z * E) * (Z * E)ᴴ) * subspaceReflection P)
    rw [Matrix.neg_mul, hprod, Matrix.mul_neg, subspaceReflection_image Z E hZ]
  refine ⟨Q ^ ℓ * U, (hQ.pow ℓ).mul hU,
    (hQclean.pow ℓ).mul hUclean, ?_⟩
  have hclean := (hQclean.pow ℓ).mul hUclean
  change (Q ^ ℓ * U) * J = J * (postselectionAmplificationStep (Z * E) P ^ ℓ * Z)
    at hclean
  rw [← Matrix.mul_assoc, hclean]
  simp only [Matrix.mul_assoc]
  rw [postselectionAmplificationStep_pow_eq_success (Z * E) P hV hP ℓ hℓ hprob]

end MPUCircuit

end ExactCleanAmplificationCircuit
