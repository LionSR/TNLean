/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import TNLean.Circuit.SelectedZeroRegisterSupport
import TNLean.Circuit.ImageReflectionCircuit

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
-/

open Matrix MPSTensor QuantumCircuit

namespace MPSPreparation

variable {d n : ℕ} {S : Set (Fin n)}

/-- Reflection about a supported matrix preserves its support. Source:
initialized and success reflections in Section 5 of the circuit audit. -/
theorem subspaceReflection_mem_supportedOperators
    {P : Matrix (Cfg d n) (Cfg d n) ℂ} (hP : P ∈ supportedOperators d S) :
    Matrix.subspaceReflection P ∈ supportedOperators d S :=
  (supportedOperators d S).sub_mem (one_mem_supportedOperators S)
    ((supportedOperators d S).smul_mem (2 : ℂ) hP)

/-- Powers do not enlarge logical support. Source: repeated amplification
in Section 5 of the circuit audit. -/
theorem pow_mem_supportedOperators
    {X : Matrix (Cfg d n) (Cfg d n) ℂ} (hX : X ∈ supportedOperators d S) (ℓ : ℕ) :
    X ^ ℓ ∈ supportedOperators d S := by
  induction ℓ with
  | zero => simpa only [pow_zero] using one_mem_supportedOperators S
  | succ ℓ ih => simpa only [pow_succ] using mul_mem_supportedOperators ih hX

/-- Conjugating an initialized reflection by a supported unitary preserves
support on every logical input. Source: `Matrix.subspaceReflection_image`
and Section 5 of the circuit audit. -/
theorem subspaceReflection_image_mem_supportedOperators
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ supportedOperators d S)
    (hR : Matrix.subspaceReflection (E * Eᴴ) ∈ supportedOperators d S) :
    Matrix.subspaceReflection ((Z * E) * (Z * E)ᴴ) ∈ supportedOperators d S := by
  rw [Matrix.subspaceReflection_image Z E hZ]
  have hstar : Zᴴ ∈ supportedOperators d S := by
    simpa only [Matrix.star_eq_conjTranspose] using star_mem_supportedOperators hZS
  exact mul_mem_supportedOperators (mul_mem_supportedOperators hZS hR) hstar

/-- Both logical reflections and the scalar minus sign in one amplification
round preserve the same support. Source: phase-exact amplification in
Section 5 of the circuit audit. -/
theorem postselectionAmplificationStep_mem_supportedOperators
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (P : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ supportedOperators d S)
    (hR : Matrix.subspaceReflection (E * Eᴴ) ∈ supportedOperators d S)
    (hP : Matrix.subspaceReflection P ∈ supportedOperators d S) :
    Matrix.postselectionAmplificationStep (Z * E) P ∈ supportedOperators d S :=
  (supportedOperators d S).neg_mem
    (mul_mem_supportedOperators
      (subspaceReflection_image_mem_supportedOperators Z E hZ hZS hR) hP)

/-- The complete logical amplification operator has the original support,
including its exact global phase and all rounds. Source: recursive parent
support in Section 5 of the circuit audit. -/
theorem postselectionAmplification_mem_supportedOperators
    {m : Type*} [Fintype m]
    (Z : Matrix (Cfg d n) (Cfg d n) ℂ) (E : Matrix (Cfg d n) m ℂ)
    (P : Matrix (Cfg d n) (Cfg d n) ℂ)
    (hZ : Z ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ))
    (hZS : Z ∈ supportedOperators d S)
    (hR : Matrix.subspaceReflection (E * Eᴴ) ∈ supportedOperators d S)
    (hP : Matrix.subspaceReflection P ∈ supportedOperators d S) (ℓ : ℕ) :
    Matrix.postselectionAmplificationStep (Z * E) P ^ ℓ * Z ∈ supportedOperators d S :=
  mul_mem_supportedOperators
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
    (hZS : Z ∈ supportedOperators d S)
    (hE : E * Eᴴ ∈ supportedOperators d S)
    (hP : P ∈ supportedOperators d S) (ℓ : ℕ) :
    Matrix.postselectionAmplificationStep (Z * E) P ^ ℓ * Z ∈ supportedOperators d S :=
  postselectionAmplification_mem_supportedOperators Z E P hZ hZS
    (subspaceReflection_mem_supportedOperators hE)
    (subspaceReflection_mem_supportedOperators hP) ℓ

end MPSPreparation
