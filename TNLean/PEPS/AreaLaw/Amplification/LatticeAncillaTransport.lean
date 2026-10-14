/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.AncillaTransport
import TNLean.PEPS.AreaLaw.Amplification.LatticeRestoring
import TNLean.Algebra.MatrixKroneckerContraction
import QICLean.Analysis.RootChannel

/-!
# The restoring operator with the two ancillary copies as spectators

The restoring estimates of the amplification proof are proved in the coordinates
`((s', e'), (X, Y)), Z'` with the target `X` written in the eigenbasis of `ρ_X`. The
constraint products act on the physical configurations of the finite domain, with the two
ancillary copies `s', e'` of the target as spectators. This module transports the
restoring operator `R₀`, the column operator `B₀` and the vectors `φ`, `η`, `Ω ⊗ |00⟩` to
the coordinates `physical × (s', e')`, with the physical system in its original
coordinates, and restates the three estimates there:

* `‖R₀‖, ‖B₀‖ ≤ exp ((𝓘 + 3w)/2)` with `𝓘 = I_Ω(X : Z')`;
* the column identity `R₀ φ = B₀ (Ω ⊗ ξ)` for the transported blank pair `ξ`, which puts
  `R₀ φ` in the form required by the omission estimate of the local-products lemma;
* the physical ground component of `R₀ φ` has norm at most one;
* `‖((L' ⊗ 1) R₀)^† η - φ‖ ≤ 3 √δ + ‖L'^† Ω - Ω‖` for every physical operator `L'`.

In these coordinates `B₀` is a sum of operators `P ⊗ A` with `P` acting on `S₀ = X ∪ Y`,
and `R₀` a sum of operators `P ⊗ (b ⊗ 1)` with `P` acting on `S₀` and `b` acting on `s'`.
The vector `η` is `Ω` tensored with an ancillary vector, and `φ` is `Ω` with its target
read on `e'` and a blank on the physical target.

## Main definitions

* `TNLean.PEPS.AreaLaw.restoringEigenbasis`: the eigenvector unitary of `ρ_X`.
* `TNLean.PEPS.AreaLaw.restoringTransport`: the transport to `physical × (s', e')`.

## Main statements

* `TNLean.PEPS.AreaLaw.restoringTransport_estimates`: the estimates above.
* `TNLean.PEPS.AreaLaw.restoringTransport_copy`, `restoringTransport_restored`: the two
  vectors.
* `TNLean.PEPS.AreaLaw.restoringTransport_restoringGlobal_eq_sum`,
  `restoringTransport_restoringColumnGlobal_eq_sum`: the supports of `R₀` and `B₀`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 324–447
  and 470–473: `eq:amplification-swapped-state`, `eq:amplification-restored-state`,
  `eq:amplification-restoring-operator`, `eq:amplification-column-operator`,
  `eq:amplification-column-identity`, `eq:amplification-operator-norm`,
  `eq:amplification-adjoint-error` and `eq:amplification-ground-component`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

section Isometry

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- A matrix with `Wᴴ W = 1` has operator norm at most one. -/
theorem l2_opNorm_le_one_of_conjTranspose_mul_self {W : Matrix m n ℂ} (hW : Wᴴ * W = 1) :
    ‖W‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have h := l2_opNorm_conjTranspose_mul_self W
  rw [hW] at h
  nlinarith [norm_nonneg W]

/-- A matrix with `Wᴴ W = 1` preserves Euclidean norms. -/
theorem norm_toLp_mulVec_of_conjTranspose_mul_self {W : Matrix m n ℂ} (hW : Wᴴ * W = 1)
    (v : n → ℂ) : ‖WithLp.toLp 2 (W *ᵥ v)‖ = ‖WithLp.toLp 2 v‖ := by
  have hle := l2_opNorm_le_one_of_conjTranspose_mul_self hW
  have hW' : ‖Wᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact hle
  have hA : ‖WithLp.toLp 2 (W *ᵥ v)‖ ≤ ‖W‖ * ‖WithLp.toLp 2 v‖ :=
    W.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have hB : ‖WithLp.toLp 2 (Wᴴ *ᵥ (W *ᵥ v))‖ ≤ ‖Wᴴ‖ * ‖WithLp.toLp 2 (W *ᵥ v)‖ :=
    Wᴴ.l2_opNorm_mulVec (WithLp.toLp 2 (W *ᵥ v))
  have hv : Wᴴ *ᵥ (W *ᵥ v) = v := by rw [mulVec_mulVec, hW, one_mulVec]
  rw [hv] at hB
  apply le_antisymm
  · nlinarith [norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ n), norm_nonneg W]
  · nlinarith [norm_nonneg (WithLp.toLp 2 (W *ᵥ v) : EuclideanSpace ℂ m), norm_nonneg Wᴴ]

/-- Conjugation by a matrix with `Wᴴ W = 1` does not increase the operator norm. -/
theorem l2_opNorm_conj_le {W : Matrix m n ℂ} (hW : Wᴴ * W = 1) (A : Matrix n n ℂ) :
    ‖W * A * Wᴴ‖ ≤ ‖A‖ := by
  have hle := l2_opNorm_le_one_of_conjTranspose_mul_self hW
  calc ‖W * A * Wᴴ‖ ≤ ‖W * A‖ * ‖Wᴴ‖ := l2_opNorm_mul _ _
    _ ≤ (‖W‖ * ‖A‖) * ‖Wᴴ‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ (1 * ‖A‖) * 1 := by
        rw [l2_opNorm_conjTranspose]
        gcongr
    _ = ‖A‖ := by ring

omit [DecidableEq m] in
/-- Applying an operator and then a matrix with `Wᴴ W = 1` equals applying the conjugated
operator to the transported vector. -/
theorem mulVec_mulVec_eq_conj {W : Matrix m n ℂ} (hW : Wᴴ * W = 1) (A : Matrix n n ℂ)
    (v : n → ℂ) : W *ᵥ (A *ᵥ v) = (W * A * Wᴴ) *ᵥ (W *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (W * A), hW, Matrix.mul_one]

end Isometry

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- A local matrix placed on a region is `K ⊗ 1` in the coordinates of that region and its
complement. -/
theorem localLift_eq_kronecker_one_submatrix (S : Finset (Site Λ))
    (K : Matrix (RegionalConfiguration q S) (RegionalConfiguration q S) ℂ) :
    localLift Λ q S K = (K ⊗ₖ (1 : Matrix (RegionalConfiguration q Sᶜ)
      (RegionalConfiguration q Sᶜ) ℂ)).submatrix
        (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) S)
        (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) S) := by
  ext c c'
  simp only [localLift, QuantumCircuit.embedOp_apply, submatrix_apply, kroneckerMap_apply,
    one_apply]
  have hagree : QuantumCircuit.AgreeOff (fun x : ↥S ↦ x.val) c c' ↔
      (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) S c).2 =
        (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) S c').2 := by
    constructor
    · intro h
      funext v
      exact h v fun j hj => (Finset.mem_compl.mp v.2) (hj ▸ j.2)
    · intro h i hi
      have hiS : i ∉ S := fun hiS => hi ⟨i, hiS⟩ rfl
      exact congrFun h ⟨i, Finset.mem_compl.mpr hiS⟩
  by_cases h : QuantumCircuit.AgreeOff (fun x : ↥S ↦ x.val) c c'
  · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), ite_eq_left_iff.mpr
      (fun h' => absurd (hagree.mp h) h'), mul_one]
    rfl
  · simp only [h, hagree.not.mp h, ite_false, mul_zero]

/-- The physical operator obtained from an operator on `X × Y` acts on `X ∪ Y`.
Source: `09-amplification.tex`, lines 348–364. -/
theorem ancillaPhysical_mem_supportedOperators (X Y : Finset (Site Λ)) (hXY : Disjoint X Y)
    (U : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)
    (M : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ) :
    ancillaPhysical U (restoringSplit q X Y hXY) M ∈
      QuantumCircuit.supportedOperators q ((X ∪ Y : Finset (Site Λ)) : Set (Site Λ)) := by
  set uE := FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY
  have h : ancillaPhysical U (restoringSplit q X Y hXY) M =
      localLift Λ q (X ∪ Y) ((((U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y)
        (RegionalConfiguration q Y) ℂ)) * M * (U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y)
          (RegionalConfiguration q Y) ℂ))ᴴ)).submatrix uE uE) := by
    rw [localLift_eq_kronecker_one_submatrix]
    ext c c'
    simp only [ancillaPhysical, submatrix_apply, kroneckerMap_apply]
    rfl
  rw [h]
  exact localLift_mem_supportedOperators Λ q _ _

/-- The eigenvector unitary of the reduced state `ρ_X`, whose columns are the full
eigenbasis `{|x⟩}`. Source: `09-amplification.tex`, lines 324–325. -/
noncomputable abbrev restoringEigenbasis (Ω : StateSpace Λ q) (X : Finset (Site Λ)) :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ :=
  ((reducedState_isHermitian Λ q Ω X).eigenvectorUnitary :
    Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)

theorem restoringEigenbasis_unitary (Ω : StateSpace Λ q) (X : Finset (Site Λ)) :
    restoringEigenbasis Ω X * (restoringEigenbasis Ω X)ᴴ = 1 ∧
      (restoringEigenbasis Ω X)ᴴ * restoringEigenbasis Ω X = 1 := by
  simp only [restoringEigenbasis, ← star_eq_conjTranspose]
  exact ⟨Unitary.coe_mul_star_self _, Unitary.coe_star_mul_self _⟩

/-- The transport from the restoring coordinates `((s', e'), (X, Y)), Z'` to the
coordinates `physical × (s', e')`. Source: `09-amplification.tex`, lines 324–347. -/
noncomputable def restoringTransport (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) :
    Matrix (Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X))
      (((RegionalConfiguration q X × RegionalConfiguration q X) ×
        (RegionalConfiguration q X × RegionalConfiguration q Y)) ×
          RegionalConfiguration q (X ∪ Y)ᶜ) ℂ :=
  ancillaTransport (restoringEigenbasis Ω X) (restoringSplit q X Y hXY)

theorem restoringTransport_unitary (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) :
    restoringTransport Ω X Y hXY * (restoringTransport Ω X Y hXY)ᴴ = 1 ∧
      (restoringTransport Ω X Y hXY)ᴴ * restoringTransport Ω X Y hXY = 1 :=
  ⟨ancillaTransport_mul_conjTranspose (restoringEigenbasis_unitary Ω X).1
      (restoringEigenbasis_unitary Ω X).2 _,
    conjTranspose_mul_ancillaTransport (restoringEigenbasis_unitary Ω X).1
      (restoringEigenbasis_unitary Ω X).2 _⟩

/-- **The copied vector** `φ` in the coordinates `physical × (s', e')`: its value at a
configuration `c` and ancillary pair `(s, e)` is `|0⟩(s) (U |0⟩)(c_X) Ω(c')`, where `c'`
agrees with `c` off `X` and reads `e` on `X`.
Source: `eq:amplification-swapped-state`, `09-amplification.tex`, lines 334–347. -/
theorem restoringTransport_copy (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) (sBlank xBlank : RegionalConfiguration q X → ℂ) :
    restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp =
      fun c => sBlank c.2.1 * (restoringEigenbasis Ω X *ᵥ xBlank)
        (restoringSplit q X Y hXY c.1).1.1 * Ω ((restoringSplit q X Y hXY).symm
          ((c.2.2, (restoringSplit q X Y hXY c.1).1.2), (restoringSplit q X Y hXY c.1).2)) :=
  ancillaTransport_mulVec_copy (restoringEigenbasis_unitary Ω X).1 _ sBlank xBlank
    (fun c => Ω c)

/-- **The restored vector** `η = Ω ⊗ ∑_x √p_x |x⟩_{s'}|x⟩_{e'}` in the coordinates
`physical × (s', e')`, with `e'` read in the original basis.
Source: `eq:amplification-restored-state`, `09-amplification.tex`, lines 338–341. -/
theorem restoringTransport_restored (Ω : StateSpace Λ q) (X Y : Finset (Site Λ))
    (hXY : Disjoint X Y) (p : RegionalConfiguration q X → ℝ) :
    restoringTransport Ω X Y hXY *ᵥ (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp =
      fun c => Ω c.1 * (((1 : Matrix (RegionalConfiguration q X)
        (RegionalConfiguration q X) ℂ) ⊗ₖ restoringEigenbasis Ω X) *ᵥ
          fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0) c.2 :=
  ancillaTransport_mulVec_restored (restoringEigenbasis_unitary Ω X).1 _ p (fun c => Ω c)

/-- **The support of the transported restoring operator**: `R₀` is a sum of operators
`P ⊗ (b ⊗ 1_{e'})` with `P` acting on `X ∪ Y` and `b` acting on `s'`.
Source: `eq:amplification-restoring-operator`, `09-amplification.tex`, lines 350–356. -/
theorem restoringTransport_restoringGlobal_eq_sum (Ω : StateSpace Λ q)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (E : Finset (RegionalConfiguration q X))
    (p : RegionalConfiguration q X → ℝ) (sBlank xBlank : RegionalConfiguration q X → ℂ)
    (Q : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ)
    (T : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ) :
    ∃ P : RegionalConfiguration q X → Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
      (∀ x, P x ∈ QuantumCircuit.supportedOperators q
        ((X ∪ Y : Finset (Site Λ)) : Set (Site Λ))) ∧
      restoringTransport Ω X Y hXY * Entropy.restoringGlobal (Z := RegionalConfiguration q
          (X ∪ Y)ᶜ) E p sBlank xBlank Q T * (restoringTransport Ω X Y hXY)ᴴ =
        ∑ x ∈ E, P x ⊗ₖ (Entropy.basisColumn x sBlank ⊗ₖ
          (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)) := by
  refine ⟨fun x => Entropy.restoringWeight (p x) • ancillaPhysical (restoringEigenbasis Ω X)
    (restoringSplit q X Y hXY) (Q * (Entropy.basisColumn x xBlank ⊗ₖ T)),
    fun x => Submodule.smul_mem _ _ (ancillaPhysical_mem_supportedOperators X Y hXY _ _), ?_⟩
  rw [restoringTransport, ancillaTransport_conj_restoringGlobal
    (restoringEigenbasis_unitary Ω X).1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_kronecker, kronecker_smul]

/-- **The support of the transported column operator**: `B₀` is a sum of operators
`P ⊗ A` with `P` acting on `X ∪ Y` and `A` acting on the ancillas.
Source: `eq:amplification-column-operator`, `09-amplification.tex`, lines 359–364. -/
theorem restoringTransport_restoringColumnGlobal_eq_sum (Ω : StateSpace Λ q)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (E : Finset (RegionalConfiguration q X))
    (p : RegionalConfiguration q X → ℝ) (sBlank eBlank : RegionalConfiguration q X → ℂ)
    (Q : Matrix (RegionalConfiguration q X × RegionalConfiguration q Y)
      (RegionalConfiguration q X × RegionalConfiguration q Y) ℂ)
    (T : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ) :
    ∃ (P : RegionalConfiguration q X × RegionalConfiguration q X →
        Matrix (Configuration Λ q) (Configuration Λ q) ℂ)
      (A : RegionalConfiguration q X × RegionalConfiguration q X →
        Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
          (RegionalConfiguration q X × RegionalConfiguration q X) ℂ),
      (∀ i, P i ∈ QuantumCircuit.supportedOperators q
        ((X ∪ Y : Finset (Site Λ)) : Set (Site Λ))) ∧
      restoringTransport Ω X Y hXY * Entropy.restoringColumnGlobal (Z := RegionalConfiguration q
          (X ∪ Y)ᶜ) E p sBlank eBlank Q T * (restoringTransport Ω X Y hXY)ᴴ =
        ∑ i ∈ E ×ˢ Finset.univ, P i ⊗ₖ A i := by
  refine ⟨fun i => ancillaPhysical (restoringEigenbasis Ω X) (restoringSplit q X Y hXY)
      (Q * (single i.1 i.2 1 ⊗ₖ T)),
    fun i => ((1 : Matrix _ _ ℂ) ⊗ₖ restoringEigenbasis Ω X) *
      (Entropy.restoringWeight (p i.1) • (Entropy.basisColumn i.1 sBlank ⊗ₖ
        Entropy.basisColumn i.2 eBlank)) * ((1 : Matrix _ _ ℂ) ⊗ₖ restoringEigenbasis Ω X)ᴴ,
    fun i => ancillaPhysical_mem_supportedOperators X Y hXY _ _, ?_⟩
  rw [restoringTransport, ancillaTransport_conj_restoringColumnGlobal, Finset.sum_product]

/-- **The restoring estimates with the ancillas as spectators.** Let `Ω` be a unit vector,
`X, Y` disjoint regions with `S₀ = X ∪ Y` and `Z' = Λ ∖ S₀`, and `w, δ` real numbers
bounding the failure probabilities of the typical projections of `X`, `Y` and `S₀` by `δ`.
Transport the restoring operator `R₀`, the column operator `B₀`, the copied vector `φ`
and the restored vector `η` to the coordinates `physical × (s', e')`. Then `φ, η` are unit
vectors, `‖R₀‖, ‖B₀‖ ≤ M₀ = exp ((𝓘 + 3w)/2)` with `𝓘 = I_Ω(X : Z')`, `R₀ φ = B₀ (Ω ⊗ ξ)`
for the transported blank pair `ξ`, the physical ground component of `R₀ φ` has norm at
most one, and `‖((L' ⊗ 1) R₀)^† η - φ‖ ≤ 3 √δ + ‖L'^† Ω - Ω‖` for every physical `L'`.
Source: `09-amplification.tex`, lines 324–447 and 470–473. -/
theorem restoringTransport_estimates (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (X Y : Finset (Site Λ)) (hXY : Disjoint X Y) (w δ : ℝ)
    (hδX : 1 - (reducedState Λ q Ω X * typicalProjection Λ q Ω X w).trace.re ≤ δ)
    (hδY : 1 - (reducedState Λ q Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤ δ)
    (hδS : 1 - (reducedState Λ q Ω (X ∪ Y) * typicalProjection Λ q Ω (X ∪ Y) w).trace.re ≤
      δ)
    (sBlank xBlank eBlank : RegionalConfiguration q X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (he : ‖WithLp.toLp 2 eBlank‖ = 1) :
    let 𝒲 := restoringTransport Ω X Y hXY
    let p := (reducedState_isHermitian Λ q Ω X).eigenvalues
    let E := Entropy.typicalSet p (regionalEntropy Λ q Ω X) w
    let T := typicalProjection Λ q Ω Y w
    let Q := restoringCutProjection Ω X Y hXY w
    let ψ := restoringVector Ω X Y hXY
    let I := FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X (X ∪ Y)ᶜ
    let R := 𝒲 * Entropy.restoringGlobal E p sBlank xBlank Q T * 𝒲ᴴ
    let B := 𝒲 * Entropy.restoringColumnGlobal E p sBlank eBlank Q T * 𝒲ᴴ
    let φ := 𝒲 *ᵥ (Entropy.restoringCopy sBlank xBlank ψ).ofLp
    let η := 𝒲 *ᵥ (Entropy.restoringRestored p ψ).ofLp
    ‖WithLp.toLp 2 φ‖ = 1 ∧ ‖WithLp.toLp 2 η‖ = 1 ∧
      ‖R‖ ≤ Real.exp ((I + 3 * w) / 2) ∧ ‖B‖ ≤ Real.exp ((I + 3 * w) / 2) ∧
      R *ᵥ φ = B *ᵥ (fun c => Ω c.1 *
        (sBlank c.2.1 * (restoringEigenbasis Ω X *ᵥ eBlank) c.2.2)) ∧
      ‖WithLp.toLp 2 ((vecMulVec Ω.ofLp (star Ω.ofLp) ⊗ₖ
        (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
          (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ (R *ᵥ φ))‖ ≤ 1 ∧
      ∀ L : Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
        ‖WithLp.toLp 2 ((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
            (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) * R)ᴴ *ᵥ η) -
          WithLp.toLp 2 φ‖ ≤ 3 * √δ + ‖WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp) - Ω‖ := by
  intro 𝒲 p E T Q ψ I R B φ η
  obtain ⟨hU, hU'⟩ := restoringEigenbasis_unitary Ω X
  obtain ⟨-, h𝒲⟩ := restoringTransport_unitary Ω X Y hXY
  set U := restoringEigenbasis Ω X with hUdef
  set rs := restoringSplit q X Y hXY with hrs
  obtain ⟨hψ, hRn, hBn, hground, hadj⟩ := restoringOperator_estimates Ω hΩ X Y hXY w δ hδX hδY
    hδS sBlank xBlank eBlank hs hx he
  -- The rotation `(Uᴴ ⊗ 1) ⊗ 1` relating `ψ` to `Ω`.
  set Uh := (Uᴴ ⊗ₖ (1 : Matrix (RegionalConfiguration q Y) (RegionalConfiguration q Y) ℂ)) ⊗ₖ
    (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ) (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ)
    with hUhdef
  have hUh : Uhᴴ * Uh = 1 := by
    simp only [hUhdef, conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_one,
      ← mul_kronecker_mul, hU, Matrix.one_mul, one_kronecker_one]
  have hUhH : Uhᴴ = (U ⊗ₖ (1 : Matrix (RegionalConfiguration q Y)
      (RegionalConfiguration q Y) ℂ)) ⊗ₖ (1 : Matrix (RegionalConfiguration q (X ∪ Y)ᶜ)
        (RegionalConfiguration q (X ∪ Y)ᶜ) ℂ) := by
    simp only [hUhdef, conjTranspose_kronecker, conjTranspose_conjTranspose, conjTranspose_one]
  have hψdef : ψ.ofLp = Uh *ᵥ fun i => Ω (rs.symm i) := rfl
  -- The physical operators in the eigenbasis coordinates.
  have hphys (L : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      𝒲 * Entropy.restoringPhysicalLift (Uh * L.submatrix rs.symm rs.symm * Uhᴴ) * 𝒲ᴴ =
        L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
          (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) := by
    rw [hUhH]
    exact ancillaTransport_conj_physicalLift hU rs L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_toLp_mulVec_of_conjTranspose_mul_self h𝒲]
    exact (Entropy.restoringCopy_norm sBlank xBlank hs hx ψ).trans hψ
  · -- `η` is `Ω` tensored with a unit ancillary vector.
    have hη : η = fun c => Ω c.1 * (((1 : Matrix (RegionalConfiguration q X)
        (RegionalConfiguration q X) ℂ) ⊗ₖ U) *ᵥ
          fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0) c.2 :=
      restoringTransport_restored Ω X Y hXY p
    have hp0 : ∀ x, 0 ≤ p x := (reducedState_posSemidef Λ q Ω X).eigenvalues_nonneg
    have hpsum : ∑ x, p x = 1 := by
      have h := (reducedState_isHermitian Λ q Ω X).trace_eq_sum_eigenvalues
      rw [trace_reducedState Ω hΩ X] at h
      have h' : ((∑ x, p x : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
      exact_mod_cast h'
    have hU1 : ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ U)ᴴ *
        ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ U) = 1 := by
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hU']
      simp
    have hχ : ‖WithLp.toLp 2 (fun a : RegionalConfiguration q X × RegionalConfiguration q X =>
        if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0)‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type]
      rw [← hpsum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single x (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [Complex.norm_real, Real.sq_sqrt (hp0 x), abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hη]
    have := EuclideanSpace.norm_vecKron Ω (WithLp.toLp 2 (((1 : Matrix (RegionalConfiguration q X)
      (RegionalConfiguration q X) ℂ) ⊗ₖ U) *ᵥ fun a : RegionalConfiguration q X ×
        RegionalConfiguration q X => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0))
    rw [norm_toLp_mulVec_of_conjTranspose_mul_self hU1, hχ, hΩ, mul_one] at this
    exact this
  · calc ‖R‖ ≤ ‖Entropy.restoringGlobal E p sBlank xBlank Q T‖ := l2_opNorm_conj_le h𝒲 _
      _ ≤ ‖Entropy.restoringOperatorWithAncilla E p sBlank xBlank Q T‖ :=
          l2_opNorm_kronecker_one_le _
      _ ≤ ‖Entropy.restoringOperator E p sBlank xBlank Q T ⊗ₖ
            (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)‖ :=
          norm_submatrix_equiv_le _ _
      _ ≤ ‖Entropy.restoringOperator E p sBlank xBlank Q T‖ := l2_opNorm_kronecker_one_le _
      _ ≤ _ := hRn
  · calc ‖B‖ ≤ ‖Entropy.restoringColumnGlobal E p sBlank eBlank Q T‖ := l2_opNorm_conj_le h𝒲 _
      _ ≤ ‖Entropy.columnOperator E p sBlank eBlank Q T‖ := l2_opNorm_kronecker_one_le _
      _ ≤ _ := hBn
  · have hinit : 𝒲 *ᵥ (Entropy.restoringInitial sBlank eBlank ψ).ofLp =
        fun c => Ω c.1 * (sBlank c.2.1 * (U *ᵥ eBlank) c.2.2) :=
      ancillaTransport_mulVec_initial hU rs sBlank eBlank (fun c => Ω c)
    rw [← hinit, ← mulVec_mulVec_eq_conj h𝒲, ← mulVec_mulVec_eq_conj h𝒲,
      Entropy.restoringGlobal_mulVec_copy E p sBlank xBlank eBlank hx he Q T ψ]
  · have hvec : vecMulVec ψ.ofLp (star ψ.ofLp) =
        Uh * (vecMulVec Ω.ofLp (star Ω.ofLp)).submatrix rs.symm rs.symm * Uhᴴ := by
      have hsub : (vecMulVec Ω.ofLp (star Ω.ofLp)).submatrix rs.symm rs.symm =
          vecMulVec (fun i => Ω (rs.symm i)) (star fun i => Ω (rs.symm i)) := by
        ext i j
        simp [vecMulVec_apply]
      rw [hsub, hψdef, mul_vecMulVec, vecMulVec_mul, star_mulVec]
    have hg := hground
    rw [Entropy.restoringGroundComponent, Entropy.restoringGroundOuterProduct, hvec] at hg
    rw [← norm_toLp_mulVec_of_conjTranspose_mul_self h𝒲] at hg
    rw [← hphys, ← mulVec_mulVec_eq_conj h𝒲, ← mulVec_mulVec_eq_conj h𝒲]
    exact hg
  · intro L
    have h := hadj (Uh * L.submatrix rs.symm rs.symm * Uhᴴ)
    set LG := Uh * L.submatrix rs.symm rs.symm * Uhᴴ with hLG
    set RG := Entropy.restoringGlobal (Z := RegionalConfiguration q (X ∪ Y)ᶜ) E p sBlank xBlank Q T
    have key : ∀ {κ : Type} (M : Matrix (((RegionalConfiguration q X ×
        RegionalConfiguration q X) × (RegionalConfiguration q X × RegionalConfiguration q Y)) ×
          RegionalConfiguration q (X ∪ Y)ᶜ) κ ℂ), 𝒲ᴴ * (𝒲 * M) = M := by
      intro κ M
      rw [← Matrix.mul_assoc, h𝒲, Matrix.one_mul]
    have hconj : (L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) * R)ᴴ =
        𝒲 * (Entropy.restoringPhysicalLift LG * RG)ᴴ * 𝒲ᴴ := by
      rw [← hphys L]
      simp only [R, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, key]
      simp only [hLG, Matrix.mul_assoc]
      rfl
    have hleft : ((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) * R)ᴴ *ᵥ η) =
        𝒲 *ᵥ (RGᴴ *ᵥ ((Entropy.restoringPhysicalLift LG)ᴴ *ᵥ
          (Entropy.restoringRestored p ψ).ofLp)) := by
      rw [hconj, ← mulVec_mulVec_eq_conj h𝒲, conjTranspose_mul, ← mulVec_mulVec]
    have hnorm_left : ‖WithLp.toLp 2 ((L ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
        RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) *
          R)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ =
        ‖WithLp.toLp 2 (RGᴴ *ᵥ ((Entropy.restoringPhysicalLift LG)ᴴ *ᵥ
          (Entropy.restoringRestored p ψ).ofLp)) - Entropy.restoringCopy sBlank xBlank ψ‖ := by
      rw [hleft, ← WithLp.toLp_sub, ← mulVec_sub, norm_toLp_mulVec_of_conjTranspose_mul_self h𝒲,
        WithLp.toLp_sub]
    have hnorm_right : ‖WithLp.toLp 2 (LGᴴ *ᵥ ψ.ofLp) - ψ‖ =
        ‖WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp) - Ω‖ := by
      have hLGH : LGᴴ = Uh * (Lᴴ).submatrix rs.symm rs.symm * Uhᴴ := by
        rw [hLG, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
          conjTranspose_submatrix, Matrix.mul_assoc]
      have hdiff : WithLp.toLp 2 (LGᴴ *ᵥ ψ.ofLp) - ψ = WithLp.toLp 2 (Uh *ᵥ
          ((Lᴴ).submatrix rs.symm rs.symm *ᵥ (fun i => Ω (rs.symm i)) -
            fun i => Ω (rs.symm i))) := by
        rw [hLGH, hψdef, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec (M := Uhᴴ), hUh, one_mulVec,
          mulVec_sub]
        rfl
      rw [hdiff, norm_toLp_mulVec_of_conjTranspose_mul_self hUh, submatrix_mulVec_equiv]
      have hcomp : ((Lᴴ *ᵥ ((fun i => Ω (rs.symm i)) ∘ rs.symm.symm)) ∘ rs.symm -
          fun i => Ω (rs.symm i)) = (Lᴴ *ᵥ Ω.ofLp - Ω.ofLp) ∘ rs.symm := by
        ext i
        simp only [Pi.sub_apply, Function.comp_apply, Equiv.symm_symm]
        congr 2
        ext c
        simp
      rw [hcomp, EuclideanSpace.norm_toLp_comp_equiv, WithLp.toLp_sub]
    rw [hnorm_left, ← hnorm_right]
    exact h

end TNLean.PEPS.AreaLaw
