/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationBases
import TNLean.MPS.Preparation.MinimalCutRepresentationPadding
import TNLean.MPS.Preparation.IsometricChain

/-!
# Exact open-boundary representation with minimal bonds

The matrices of coordinate slicing between successive coefficient column
spaces form an open-boundary chain. Composition of prefix evaluation maps
proves exact coefficient reconstruction. The bond dimension at every cut
is the rank of that physical coefficient flattening.

The final existence theorem concerns nonzero tensors of positive length.
It uses the existing open-boundary chain and its coefficient convention.

Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- The matrix of one restricted physical-coordinate slicing map in the chosen cut bases.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutSiteMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (k : ℕ) (i : Fin d) : Matrix (Fin (cutCoefficientRank ψ k)) (Fin (cutCoefficientRank ψ
        (k + 1))) ℂ :=
  LinearMap.toMatrix (B (k + 1)) (B k) (cutSlice ψ k i)

/-- Evaluation of a cut-space vector at the prefix of a global configuration.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutEvaluationMap {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (σ : Fin N → Fin d) (k : ℕ) :
    cutColumnSpace ψ k →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (cutPrefixRestriction σ k)).comp (cutColumnSpace ψ k).subtype

/-- The coefficient row of prefix evaluation in the chosen cut basis.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutEvaluationMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (σ : Fin N → Fin d) (k : ℕ) : Matrix (Fin 1) (Fin (cutCoefficientRank ψ k)) ℂ :=
  LinearMap.toMatrix (B k) (Module.Basis.singleton (Fin 1) ℂ) (cutEvaluationMap ψ σ k)

/-- A prefix evaluation coefficient is the corresponding cut-basis vector evaluated
at that prefix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMatrix_apply {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (σ : Fin N → Fin d) (k : ℕ) (a : Fin 1) (b : Fin (cutCoefficientRank ψ k)) :
    cutEvaluationMatrix ψ B σ k a b = (B k b).val (cutPrefixRestriction σ k) := by
  rw [cutEvaluationMatrix, LinearMap.toMatrix_apply, Module.Basis.singleton_repr]
  rfl

/-- Consecutive prefix evaluations compose with physical-coordinate slicing.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMap_step {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (σ : Fin N → Fin d) (p : Fin N) :
    cutEvaluationMap ψ σ (p.val + 1) =
      (cutEvaluationMap ψ σ p.val).comp (cutSlice ψ p.val (σ p)) := by
  ext v
  exact (cutSlice_apply_restriction ψ σ p v).symm

/-- The matrix of prefix evaluation multiplies by the next site matrix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMatrix_step {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (σ : Fin N → Fin d) (p : Fin N) :
    cutEvaluationMatrix ψ B σ (p.val + 1) =
      cutEvaluationMatrix ψ B σ p.val * cutSiteMatrix ψ B p.val (σ p) := by
  change LinearMap.toMatrix (B (p.val + 1)) (Module.Basis.singleton (Fin 1) ℂ)
      (cutEvaluationMap ψ σ (p.val + 1)) = _
  rw [cutEvaluationMap_step]
  exact LinearMap.toMatrix_comp (B (p.val + 1)) (B p.val)
    (Module.Basis.singleton (Fin 1) ℂ) (cutEvaluationMap ψ σ p.val)
      (cutSlice ψ p.val (σ p))

/-- The square chain obtained by zero-padding the slicing matrices of a prefix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutPrefixChain {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (D k : ℕ) : MPSChainTensor d D k :=
  fun p i ↦ Matrix.zeroPad D (cutSiteMatrix ψ B p.val i)

/-- The padded prefix evaluation matrix is its initial matrix multiplied
by the ordered product of padded site matrices. This follows from composition
of linear maps, with no expansion over complete virtual paths.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMatrix_eq_initial_mul_eval {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hbound : ∀ k, k ≤ N → cutCoefficientRank ψ k ≤ D) (σ : Fin N → Fin d)
    (k : ℕ) (hk : k ≤ N) :
    Matrix.zeroPad D (cutEvaluationMatrix ψ B σ k) =
      Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) *
        MPSChainTensor.eval (cutPrefixChain ψ B D k) (fun p ↦ σ (Fin.castLE hk p)) := by
  induction k with
  | zero => simp [MPSChainTensor.eval]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    let p : Fin N := ⟨k, by omega⟩
    rw [MPSChainTensor.eval_succ']
    change Matrix.zeroPad D (cutEvaluationMatrix ψ B σ (k + 1)) =
      Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) *
        (MPSChainTensor.eval (cutPrefixChain ψ B D k) (fun q ↦ σ (Fin.castLE hk' q)) *
          Matrix.zeroPad D (cutSiteMatrix ψ B k (σ p)))
    have hstep := cutEvaluationMatrix_step ψ B σ p
    rw [hstep, Matrix.zeroPad_mul _ _ (hbound k hk'), ih hk', Matrix.mul_assoc]

/-- The initial evaluation row is the zero-coordinate basis vector when
the left endpoint cut basis is normalized to one.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initialCutEvaluation_row {d N D : ℕ} (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (σ : Fin N → Fin d) (hD : 0 < D) :
    (Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0)) ⟨0, hD⟩ = basisVecZero hD := by
  have hentries : ∀ a b, cutEvaluationMatrix ψ B σ 0 a b = 1 := by
    intro a b
    rw [cutEvaluationMatrix_apply, hB0 b]
    rfl
  ext β
  simp [Matrix.zeroPad, cutCoefficientRank_zero ψ hψ, hentries, basisVecZero,
    Pi.single_apply, Fin.ext_iff]

/-- The normalized initial evaluation matrix preserves the zero-coordinate
row of every matrix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initialCutEvaluation_mul_apply {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (σ : Fin N → Fin d) (hD : 0 < D)
    (M : Matrix (Fin D) (Fin D) ℂ) (β : Fin D) :
    (Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) * M) ⟨0, hD⟩ β = M ⟨0, hD⟩ β := by
  change (Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) ⟨0, hD⟩) ⬝ᵥ
    (fun γ ↦ M γ β) = M ⟨0, hD⟩ β
  rw [initialCutEvaluation_row ψ hψ B hB0 σ hD]
  exact basisVecZero_dotProduct hD _

/-- The zero-coordinate entry of the padded site product equals the physical
coefficient when the two endpoint cut bases are fixed to one and to the full tensor.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixChain_eval_entry {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hbound : ∀ k, k ≤ N → cutCoefficientRank ψ k ≤ D) (σ : Fin N → Fin d) (hD : 0 < D) :
    MPSChainTensor.eval (cutPrefixChain ψ B D N) σ ⟨0, hD⟩ ⟨0, hD⟩ = ψ σ := by
  have hlast : Matrix.zeroPad D (cutEvaluationMatrix ψ B σ N) ⟨0, hD⟩ ⟨0, hD⟩ =
      ψ σ := by
    rw [Matrix.zeroPad_apply_of_lt _ (by simp) (cutCoefficientRank_pos ψ hψ N)]
    rw [cutEvaluationMatrix_apply, hBN]
    exact fullCutVector_restriction ψ σ
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M ⟨0, hD⟩ ⟨0, hD⟩)
    (cutEvaluationMatrix_eq_initial_mul_eval ψ B hbound σ N (Nat.le_refl N))
  rw [hlast, initialCutEvaluation_mul_apply ψ hψ B hB0 σ hD] at h
  exact h.symm

/-- The open-boundary chain whose bond dimensions are the physical cut ranks
and whose sites are the restricted slicing maps in the chosen bases.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalCutChain {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hbound : ∀ k : Fin (N + 1), cutCoefficientRank ψ k.val ≤ D) : OBCChainTensor d D N where
  bondDim k := cutCoefficientRank ψ k.val
  bondDim_le := hbound
  left_dim := cutCoefficientRank_zero ψ hψ
  right_dim := cutCoefficientRank_last ψ hψ
  tensor p i := cutSiteMatrix ψ B p.val i

/-- The chain of slicing matrices represents the full coefficient tensor exactly
when its endpoint bases are fixed to one and to that tensor.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalCutChain_coeff {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hbound : ∀ k : Fin (N + 1), cutCoefficientRank ψ k.val ≤ D) (σ : Fin N → Fin d) :
    (minimalCutChain ψ hψ B hbound).coeff σ = ψ σ := by
  rw [OBCChainTensor.coeff_eq_eval_zeroPad]
  change MPSChainTensor.eval (cutPrefixChain ψ B D N) σ
    ⟨0, (minimalCutChain ψ hψ B hbound).bondBound_pos⟩
    ⟨0, (minimalCutChain ψ hψ B hbound).bondBound_pos⟩ = ψ σ
  apply cutPrefixChain_eval_entry ψ hψ B hB0 hBN
  intro k hk
  exact hbound ⟨k, by omega⟩

/-- Every nonzero physical coefficient tensor of positive length whose cut
ranks are bounded by D has an exact open-boundary representation with each
bond dimension equal to its cut rank. No normalization or phase restriction
is imposed on the coefficient tensor.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_obcChainTensor_coeff_eq_bondDim_eq_cutCoefficientRank {d N D : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (hbound : ∀ k : Fin (N + 1), cutCoefficientRank ψ k.val ≤ D) :
    ∃ A : OBCChainTensor d D N,
      (∀ k, A.bondDim k = cutCoefficientRank ψ k.val) ∧ ∀ σ, A.coeff σ = ψ σ := by
  obtain ⟨B, hB0, hBN⟩ := exists_cutBasisFamily_with_endpoints ψ hψ hN
  exact ⟨minimalCutChain ψ hψ B hbound, (fun _ ↦ rfl),
    minimalCutChain_coeff ψ hψ B hB0 hBN hbound⟩

end MPSPreparation
