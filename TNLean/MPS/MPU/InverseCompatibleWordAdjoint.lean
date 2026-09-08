/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleGates

/-!
# All-word adjunction of the inverse-compatible endpoints

For a tensor $U$ and a unitary gauge $T$ with $U^\dagger_{ij}=T^\dagger U_{ij}T$,
write $U[p,q]$ for its evaluation on two equal-length physical words.
Physical adjunction exchanges $p,q$ and conjugates entries, without word reversal.
Let $X,Y$ be the raw inverse-compatible first factors and $X_2,Y_2$ the second
source factors. We define the endpoint contractions
$A_N=Y_2\mathbin{-}U[p,q]\mathbin{-}Y$ and
$B_N=X\mathbin{-}U[p,q]\mathbin{-}X_2$ with the product indices specified below.
If $T\overline T=\sigma I$, then $A_N=\sigma B_N^\dagger$ for every $N$.

This is the all-word local substitution extending the contraction in
arXiv:2502.20257, `main.tex` lines 5444–5487, using the candidate factors at
lines 5390–5432 and `eq:defT`, `eq:intro_sigma` at lines 1552–1562.
It produces exactly one scalar $\sigma$, with no extra swap or reversal.
It is not the final chain-sewing argument or a proof of `eq:UUU`.
No canonicality, simplicity, comparison unitarity, or rank transport is required.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D) (T : Matrix.unitaryGroup (Fin D) ℂ)

/-- The local physical-adjoint gauge lifts to equal-length words by unitary cancellation.
Source: arXiv:2502.20257, `eq:defT` (lines 1552–1557), iterated along a finite word. -/
theorem evalWord_physicalAdjointTensor_eq_unitary_gauge
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (p q : List (Fin d)) (hlen : p.length = q.length) :
    evalWord (physicalAdjointTensor U) p q =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * evalWord U p q * T := by
  have hleft : (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * T = 1 := T.property.1
  have hright : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ = 1 := T.property.2
  induction p generalizing q with
  | nil =>
      have hq : q = [] := List.length_eq_zero_iff.mp hlen.symm
      subst q
      simpa only [evalWord_nil, Matrix.mul_one] using hleft.symm
  | cons i p ih =>
      cases q with
      | nil => simp at hlen
      | cons j q =>
          have hpq : p.length = q.length := Nat.succ.inj hlen
          rw [evalWord_cons, evalWord_cons, hT, ih q hpq]
          calc
            _ = (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j *
                ((T : Matrix (Fin D) (Fin D) ℂ) *
                  (T : Matrix (Fin D) (Fin D) ℂ)ᴴ) * evalWord U p q * T := by
              simp only [Matrix.mul_assoc]
            _ = _ := by rw [hright, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- The raw candidate $X=AY_2^\dagger$ recovers $Y_2=X^\dagger A$.
Source: arXiv:2502.20257, line 5432. No comparison matrix is used. -/
theorem sourceY₂_eq_inverseCompatibleX₁_adjoint_mul_leftGauge :
    sourceY₂ U = (inverseCompatibleX₁ U T)ᴴ * inverseCompatibleLeftGauge (d := d) T := by
  have hA : (inverseCompatibleLeftGauge (d := d) T)ᴴ *
      inverseCompatibleLeftGauge (d := d) T = 1 :=
    (Matrix.kronecker_mem_unitary (show (1 : Matrix (Fin d) (Fin d) ℂ) ∈
      unitary (Matrix (Fin d) (Fin d) ℂ) from one_mem _)
      (Matrix.map_star_mem_unitaryGroup_iff.mpr T.property)).1
  rw [inverseCompatibleX₁, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hA, Matrix.mul_one]

/-- The $Y_2$--word--$Y$ endpoint matrix: rows are $(l,(p,s))$ and
columns are $(a,(q,b))$, with $p,q$ length-$N$ configurations.
Source: the all-word extension of arXiv:2502.20257, lines 5444–5487. -/
noncomputable def inverseCompatibleWordA (N : ℕ) :
    Matrix (Fin ℓ[U] × ((Fin N → Fin d) × Fin ℓ[U]))
      (Fin d × ((Fin N → Fin d) × Fin d)) ℂ :=
  fun (l, p, s) (a, q, b) ↦ ∑ α : Fin D, ∑ β : Fin D,
    sourceY₂ U l (a, α) * evalWord U (List.ofFn p) (List.ofFn q) α β *
      inverseCompatibleY₁ U T s (β, b)

/-- The $X$--word--$X_2$ endpoint matrix, with the reverse row and column types
from `inverseCompatibleWordA`. Source: the all-word extension of
arXiv:2502.20257, lines 5444–5487. -/
noncomputable def inverseCompatibleWordB (N : ℕ) :
    Matrix (Fin d × ((Fin N → Fin d) × Fin d))
      (Fin ℓ[U] × ((Fin N → Fin d) × Fin ℓ[U])) ℂ :=
  fun (a, p, b) (l, q, s) ↦ ∑ α : Fin D, ∑ β : Fin D,
    inverseCompatibleX₁ U T (a, α) l * evalWord U (List.ofFn p) (List.ofFn q) α β *
      sourceX₂ U (β, b) s

/-- The all-word endpoint identity has exactly one phase and no spatial reflection.
This is the local substitution extending arXiv:2502.20257, lines 5444–5487,
not the subsequent finite-chain sewing or `eq:UUU`. -/
theorem inverseCompatibleWordA_eq_smul_wordB_adjoint
    (hT : ∀ i j, physicalAdjointTensor U i j =
      (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)
    (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) (N : ℕ) :
    inverseCompatibleWordA U T N = σ • (inverseCompatibleWordB U T N)ᴴ := by
  let Tc := (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)
  have hunit : (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * T = 1 := T.property.1
  have hTc : Tc = σ • (T : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
    have h := congrArg (fun M ↦ (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * M) hσ
    simpa only [← Matrix.mul_assoc, hunit, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one] using h
  ext ⟨l, p, s⟩ ⟨a, q, b⟩
  let C : Matrix (Fin ℓ[U]) (Fin D) ℂ :=
    fun t γ ↦ star (inverseCompatibleX₁ U T (a, γ) t)
  let E : Matrix (Fin D) (Fin ℓ[U]) ℂ := fun δ t ↦ star (sourceX₂ U (δ, b) t)
  let M := evalWord U (List.ofFn p) (List.ofFn q)
  let W := (evalWord U (List.ofFn q) (List.ofFn p)).map (starRingEnd ℂ)
  have hword : (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * M * T = W := by
    rw [← evalWord_physicalAdjointTensor_eq_unitary_gauge U T hT _ _ (by simp)]
    exact evalWord_physicalAdjointTensor U _ _ (by simp)
  have hleft (α : Fin D) : sourceY₂ U l (a, α) = (C * Tc) l α := by
    rw [sourceY₂_eq_inverseCompatibleX₁_adjoint_mul_leftGauge U T]
    simp only [inverseCompatibleLeftGauge, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Fintype.sum_ite_eq']
    rfl
  have hright (β : Fin D) : inverseCompatibleY₁ U T s (β, b) =
      ((T : Matrix (Fin D) (Fin D) ℂ) * E) β s := by
    simp only [inverseCompatibleY₁, inverseCompatibleRightGauge, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq']
    apply Finset.sum_congr rfl
    intro δ _
    exact mul_comm _ _
  have hcontract : C * Tc * M * ((T : Matrix (Fin D) (Fin D) ℂ) * E) =
      σ • (C * W * E) := by
    rw [hTc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    calc
      _ = C * ((T : Matrix (Fin D) (Fin D) ℂ)ᴴ * M *
          (T : Matrix (Fin D) (Fin D) ℂ)) * E := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hword]
  change (∑ α : Fin D, ∑ β : Fin D,
    sourceY₂ U l (a, α) * M α β * inverseCompatibleY₁ U T s (β, b)) = _
  simp_rw [hleft, hright]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Matrix.mul_apply]
  rw [hcontract]
  change σ * (C * W * E) l s = σ * star (∑ α : Fin D, ∑ β : Fin D,
    inverseCompatibleX₁ U T (a, α) l *
      evalWord U (List.ofFn q) (List.ofFn p) α β * sourceX₂ U (β, b) s)
  congr 1
  simp only [Matrix.mul_apply, Finset.sum_mul, star_sum, star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr₂
  intro α _ β _
  dsimp only [C, W, E, Matrix.map_apply]
  rw [starRingEnd_apply]
  ring

/-- The empty-word $A$ entries are precisely the literal new $u$ gate entries.
Source: the zero-interior-length case of the contraction in arXiv:2502.20257,
lines 5444–5487. -/
@[simp] theorem inverseCompatibleWordA_zero_apply
    (l s : Fin ℓ[U]) (a b : Fin d) (p q : Fin 0 → Fin d) :
    inverseCompatibleWordA U T 0 (l, p, s) (a, q, b) = inverseCompatibleU U T (l, s) (a, b) := by
  simp only [inverseCompatibleWordA, List.ofFn_zero, evalWord_nil, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_ite_eq, inverseCompatibleU]

/-- The empty-word $B$ entries are precisely the literal new $v$ gate entries.
Source: the zero-interior-length case of the contraction in arXiv:2502.20257,
lines 5444–5487. -/
@[simp] theorem inverseCompatibleWordB_zero_apply
    (a b : Fin d) (l s : Fin ℓ[U]) (p q : Fin 0 → Fin d) :
    inverseCompatibleWordB U T 0 (a, p, b) (l, q, s) = inverseCompatibleV U T (a, b) (l, s) := by
  simp only [inverseCompatibleWordB, List.ofFn_zero, evalWord_nil, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_ite_eq, inverseCompatibleV]

end MPOTensor
