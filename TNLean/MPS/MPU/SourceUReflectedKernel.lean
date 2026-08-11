/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MatchingContractions
import TNLean.MPS.MPU.SourceUContraction
import TNLean.MPS.MPU.SuppliedWitnessReblocking

/-!
# Reflected open-tail contraction for the source tensor u

This file exposes the doubled-bond reflection and an independent spatial
reindexing of blocked words, then transports the supplied transfer witnesses
to the output-layer insertion used by the sandwiched open-tail coefficient in
arXiv:1703.09188, Lemma III.5 and its proof in Section III.B
(lines 536--557).  The transfer proof uses the doubled-bond swap; the blocked-word
reversal records a separate spatial coordinate and is not used in that proof.
The final sandwiched finite-sum collapse is separate from these transport
identities.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Reverse the word encoded by a blocked physical index.

This is an independent spatial reindexing coordinate for the graphical
reflection in arXiv:1703.09188, Lemma III.5 and its proof in Section III.B,
lines 536--557.
It is distinct from the reversal of two blocked letters caused by conjugate
transposition in the supplied-contraction transport below. -/
noncomputable def blockWordReverseEquiv (d K : ℕ) :
    Fin (MPSTensor.blockPhysDim d K) ≃ Fin (MPSTensor.blockPhysDim d K) :=
  (MPSTensor.decodeBlockEquiv d K).trans
    ((Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin d))).trans
      (MPSTensor.decodeBlockEquiv d K).symm)

@[simp] theorem decodeBlock_blockWordReverseEquiv
    (i : Fin (MPSTensor.blockPhysDim d K)) (k : Fin K) :
    MPSTensor.decodeBlock d K (blockWordReverseEquiv d K i) k =
      MPSTensor.decodeBlock d K i (Fin.rev k) := by
  simp [blockWordReverseEquiv, MPSTensor.decodeBlockEquiv_apply]

@[simp] theorem wordOfBlock_blockWordReverseEquiv
    (i : Fin (MPSTensor.blockPhysDim d K)) :
    MPSTensor.wordOfBlock d K (blockWordReverseEquiv d K i) =
      (MPSTensor.wordOfBlock d K i).reverse := by
  simp only [MPSTensor.wordOfBlock]
  calc
    List.ofFn (MPSTensor.decodeBlock d K (blockWordReverseEquiv d K i)) =
        List.ofFn (MPSTensor.decodeBlock d K i ∘ Fin.rev) := by
      congr 1
      funext k
      simp
    _ = List.map (MPSTensor.decodeBlock d K i ∘ Fin.rev) (List.finRange K) := by
      simp [List.ofFn_eq_map]
    _ = List.map (MPSTensor.decodeBlock d K i) (List.finRange K).reverse := by
      simp [List.map_map, Function.comp_def, List.finRange_reverse]
    _ = (List.ofFn (MPSTensor.decodeBlock d K i)).reverse := by
      simp [List.ofFn_eq_map, List.map_reverse]

@[simp] theorem blockWordReverseEquiv_involutive
    (i : Fin (MPSTensor.blockPhysDim d K)) :
    blockWordReverseEquiv d K (blockWordReverseEquiv d K i) = i := by
  apply (MPSTensor.decodeBlockEquiv d K).injective
  funext k
  simp

/-- The normalized reflected double layer is the original normalized
double layer with the two doubled-bond components exchanged. -/
theorem normalizedDiagonal_doubleLayerTensor_physicalAdjointTensor
    (W : MPOTensor d D) :
    normalizedDiagonal (doubleLayerTensor (physicalAdjointTensor W)) =
      (normalizedDiagonal (doubleLayerTensor W)).submatrix
        (bondPairSwapEquiv D) (bondPairSwapEquiv D) := by
  classical
  ext x y
  obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨b, e⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [normalizedDiagonal, contractPhysical, Matrix.one_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.sum_apply, doubleLayerTensor_apply, kroneckerMap_apply,
    physicalAdjointTensor_apply, star_star]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

/-- The supplied normalized transfer power remains the same rank-one
projector after the additional positive $D^2$ blocking. -/
theorem normalizedDiagonal_blockTensor_mul_sq_eq_vecMulVec_of_transfer_power
    [NeZero d] [NeZero D] (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρtrace : Matrix.trace ρ = 1)
    (J : ℕ)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    normalizedDiagonal (doubleLayerTensor (blockTensor U (J * (D * D)))) =
      Matrix.vecMulVec
        (fun x : Fin (D * D) ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x : Fin (D * D) ↦
          (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)) := by
  let R := Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec
  have hpair : (1 : Matrix (Fin D) (Fin D) ℂ).vec ⬝ᵥ ρ.vec = 1 := by
    rw [Matrix.vec_one_dotProduct_vec_eq_trace, hρtrace]
  have hRidem : R * R = R := by
    simp only [R, Matrix.vecMulVec_mul_vecMulVec, hpair, one_smul]
  have hDsq : 0 < D * D := Nat.mul_pos (NeZero.pos D) (NeZero.pos D)
  have hpowpos : ∀ n : ℕ, 0 < n → R ^ n = R := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    clear hn
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, hRidem]
  have hRpow : R ^ (D * D) = R := hpowpos _ hDsq
  have hpowerR :
      transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J = R := hpower
  rw [normalizedDiagonal_doubleLayerTensor_blockTensor, pow_mul, hpowerR, hRpow]
  rfl

/-- After conjugate transposition, reflected normalized transfer witnesses
have the boundary orientation $|1)(\rho|$ used by the output-first tail.
The doubled-bond swap is essential for the column-stacking convention
`Matrix.vec ρ (a,b) = ρ b a`. -/
theorem conjTranspose_normalizedDiagonal_reflected_eq_vecMulVec
    [NeZero d] (U : MPOTensor d D) (K : ℕ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hE : normalizedDiagonal (doubleLayerTensor (blockTensor U K)) =
      Matrix.vecMulVec
        (fun x : Fin (D * D) ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x : Fin (D * D) ↦
          (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    (normalizedDiagonal
      (doubleLayerTensor (blockTensor (physicalAdjointTensor U) K)))ᴴ =
      Matrix.vecMulVec
        (fun x : Fin (D * D) ↦
          (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))
        (fun x : Fin (D * D) ↦ ρ.vec (finProdFinEquiv.symm x)) := by
  letI : NeZero (MPSTensor.blockPhysDim d K) := ⟨by
    rw [MPSTensor.blockPhysDim_eq_pow]
    exact pow_ne_zero K (NeZero.ne d)⟩
  rw [← physicalAdjointTensor_blockTensor]
  rw [normalizedDiagonal_doubleLayerTensor_physicalAdjointTensor, hE]
  ext x y
  obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨b, e⟩, rfl⟩ := finProdFinEquiv.surjective y
  simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.vecMulVec_apply,
    Matrix.vec,
    Equiv.symm_apply_apply, Matrix.one_apply, star_mul']
  rw [hρ.isHermitian.apply]
  simp [eq_comm]

/-- Reflection transports the supplied transfer power to the transpose of the
supplied matrix. This is the raw orientation whose conjugate transpose
has boundary order $|1)(\rho|$. -/
theorem reflected_transfer_power_eq_vecMulVec_transpose [NeZero d]
    (U : MPOTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (J : ℕ)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    transferMatrix
        (MPSTensor.transferMap (physicalAdjointTensor U).normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.transpose.vec
        (1 : Matrix (Fin D) (Fin D) ℂ).vec := by
  letI : NeZero (MPSTensor.blockPhysDim d J) := ⟨by
    simpa only [MPSTensor.blockPhysDim_eq_pow] using
      pow_ne_zero J (NeZero.ne d)⟩
  rw [← Equiv.apply_eq_iff_eq
    (Matrix.reindex finProdFinEquiv finProdFinEquiv)]
  change (transferMatrix
      (MPSTensor.transferMap (physicalAdjointTensor U).normalizedFlattening) ^ J).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm = _
  rw [← normalizedDiagonal_doubleLayerTensor_blockTensor,
    ← physicalAdjointTensor_blockTensor,
    normalizedDiagonal_doubleLayerTensor_physicalAdjointTensor,
    normalizedDiagonal_doubleLayerTensor_blockTensor, hpower]
  apply Matrix.ext fun x y ↦ ?_
  rcases finProdFinEquiv.surjective x with ⟨⟨a, c⟩, rfl⟩
  rcases finProdFinEquiv.surjective y with ⟨⟨b, e⟩, rfl⟩
  by_cases hbe : b = e
  · subst e
    simp [Matrix.submatrix_apply, Matrix.vecMulVec_apply, Matrix.vec,
      Matrix.transpose_apply]
  · simp [Matrix.submatrix_apply, Matrix.vecMulVec_apply, Matrix.vec,
      Matrix.transpose_apply, hbe, Ne.symm hbe]

private theorem star_dotProduct_mulVec {n : Type*} [Fintype n]
    (a b : n → ℂ) (M : Matrix n n ℂ) :
    star (a ⬝ᵥ (M *ᵥ b)) = star b ⬝ᵥ (Mᴴ *ᵥ star a) := by
  symm
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  exact Matrix.star_dotProduct_star (M *ᵥ b) a

/-- The supplied `simple1` and `simple2` contractions at the exact direct
block length, transported to the conjugate-transposed reflected output layer.
The insertion is $|1)(\rho|$, with the order of the two blocked letters
reversed by conjugate transposition. -/
theorem IsMPU.reflected_blockTensor_mul_sq_simple_contractions_of_transfer_power
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hρtrace : Matrix.trace ρ = 1) (J : ℕ) (hJ : 0 < J)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    let K := J * (D * D)
    let W := MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U) K
    let ρ' : Fin (D * D) → ℂ := fun x ↦ ρ.vec (finProdFinEquiv.symm x)
    let Φ' : Fin (D * D) → ℂ := fun x ↦
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
    (∀ I₁ J₁, ρ' ⬝ᵥ ((doubleLayerTensor W I₁ J₁)ᴴ *ᵥ Φ') =
      if I₁ = J₁ then 1 else 0) ∧
    (∀ I₁ J₁ L₁ M₁,
      (doubleLayerTensor W L₁ M₁)ᴴ * (doubleLayerTensor W I₁ J₁)ᴴ =
        (doubleLayerTensor W L₁ M₁)ᴴ * Matrix.vecMulVec Φ' ρ' *
          (doubleLayerTensor W I₁ J₁)ᴴ) := by
  classical
  let K := J * (D * D)
  let W := MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U) K
  let ρ' : Fin (D * D) → ℂ := fun x ↦ ρ.vec (finProdFinEquiv.symm x)
  let Φ' : Fin (D * D) → ℂ := fun x ↦
    (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
  have hpowerRef := reflected_transfer_power_eq_vecMulVec_transpose U ρ J hpower
  have htraceT : Matrix.trace ρ.transpose = 1 := by
    rw [Matrix.trace_transpose, hρtrace]
  have hs := hU.physicalAdjointTensor.blockTensor_mul_sq_simple_contractions_of_transfer_power
      ρ.transpose htraceT J hJ hpowerRef
  dsimp only at hs ⊢
  have hstarρ : star (fun x : Fin (D * D) ↦
      ρ.transpose.vec (finProdFinEquiv.symm x)) = ρ' := by
    funext x
    obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective x
    simp only [Pi.star_apply, Matrix.vec, Equiv.symm_apply_apply,
      Matrix.transpose_apply]
    dsimp only [ρ']
    simp only [Equiv.symm_apply_apply, Matrix.vec]
    exact hρ.isHermitian.apply c a
  have hstarΦ : star Φ' = Φ' := by
    funext x
    obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective x
    dsimp only [Φ']
    simp only [Pi.star_apply, Equiv.symm_apply_apply, Matrix.vec, Matrix.one_apply]
    simp
  constructor
  · intro I J'
    calc
      ρ' ⬝ᵥ ((doubleLayerTensor (MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U)
          (J * (D * D))) I J')ᴴ *ᵥ Φ') =
          star ((fun x : Fin (D * D) ↦
            (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)) ⬝ᵥ
              (doubleLayerTensor (MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U)
                (J * (D * D))) I J' *ᵥ
                fun x : Fin (D * D) ↦
                  ρ.transpose.vec (finProdFinEquiv.symm x))) := by
            rw [star_dotProduct_mulVec, hstarρ, hstarΦ]
      _ = if I = J' then 1 else 0 := by rw [hs.1 I J']; simp
  · intro I J' L M
    have hRank :
        (Matrix.vecMulVec
          (fun x : Fin (D * D) ↦ ρ.transpose.vec (finProdFinEquiv.symm x)) Φ')ᴴ =
          Matrix.vecMulVec Φ' ρ' := by
      rw [Matrix.conjTranspose_vecMulVec, hstarρ, hstarΦ]
    have h := congrArg Matrix.conjTranspose (hs.2 I J' L M)
    repeat' rw [Matrix.conjTranspose_mul] at h
    rw [hRank] at h
    simpa only [Matrix.mul_assoc] using h

/-- The raw transfer witnesses at the exact $J D^2$ block transport
through output reflection to the insertion $|1)(\rho|$. -/
theorem conjTranspose_normalizedDiagonal_reflected_blockTensor_eq_vecMulVec
    [NeZero d] [NeZero D] (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hρtrace : Matrix.trace ρ = 1) (J : ℕ)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    (normalizedDiagonal (doubleLayerTensor
      (blockTensor (physicalAdjointTensor U) (J * (D * D)))))ᴴ =
      Matrix.vecMulVec
        (fun x : Fin (D * D) ↦
          (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))
        (fun x : Fin (D * D) ↦ ρ.vec (finProdFinEquiv.symm x)) := by
  apply conjTranspose_normalizedDiagonal_reflected_eq_vecMulVec U (J * (D * D)) ρ hρ
  exact normalizedDiagonal_blockTensor_mul_sq_eq_vecMulVec_of_transfer_power
    U ρ hρtrace J hpower

/-- The output-first normalized-diagonal power has the transported
transpose-weight orientation before cyclic trace movement. -/
theorem outputLayer_normalizedDiagonal_pow_eq_vecMulVec
    [NeZero d] [NeZero D] (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hρtrace : Matrix.trace ρ = 1) (J : ℕ)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    normalizedDiagonal (doubleLayerTensor (physicalAdjointTensor U)) ^ (J * (D * D)) =
      Matrix.vecMulVec
        (fun x : Fin (D * D) ↦ ρ.transpose.vec (finProdFinEquiv.symm x))
        (fun x : Fin (D * D) ↦
          (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)) := by
  have h := conjTranspose_normalizedDiagonal_reflected_blockTensor_eq_vecMulVec
    U ρ hρ hρtrace J hpower
  rw [doubleLayerTensor_blockTensor, normalizedDiagonal_blockTensor] at h
  have h' := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_vecMulVec] at h'
  have hstarρ : star (fun x : Fin (D * D) ↦
      ρ.vec (finProdFinEquiv.symm x)) =
      fun x ↦ ρ.transpose.vec (finProdFinEquiv.symm x) := by
    funext x
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective x
    simp only [Pi.star_apply, Matrix.vec, Matrix.transpose_apply,
      Equiv.symm_apply_apply]
    exact hρ.isHermitian.apply a b
  have hstarΦ : star (fun x : Fin (D * D) ↦
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)) =
      fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x) := by
    funext x
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective x
    simp only [Pi.star_apply, Matrix.vec, Matrix.one_apply,
      Equiv.symm_apply_apply]
    simp
  simpa only [hstarρ, hstarΦ] using h'

/-- The exact reflected witnesses persist on the common `(J D² + 2)` block,
with the same `|1)(ρ|` insertion and conjugate-transposed product order. -/
theorem IsMPU.reflected_blockTensor_mul_sq_add_two_simple_contractions
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hρtrace : Matrix.trace ρ = 1) (J : ℕ) (hJ : 0 < J)
    (hpower : transferMatrix (MPSTensor.transferMap U.normalizedFlattening) ^ J =
      Matrix.vecMulVec ρ.vec (1 : Matrix (Fin D) (Fin D) ℂ).vec) :
    let K := J * (D * D)
    let W := MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U) (K + 2)
    let ρ' : Fin (D * D) → ℂ := fun x ↦ ρ.vec (finProdFinEquiv.symm x)
    let Φ' : Fin (D * D) → ℂ := fun x ↦
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
    (∀ I₁ J₁, ρ' ⬝ᵥ ((doubleLayerTensor W I₁ J₁)ᴴ *ᵥ Φ') =
      if I₁ = J₁ then 1 else 0) ∧
    (∀ I₁ J₁ L₁ M₁,
      (doubleLayerTensor W L₁ M₁)ᴴ * (doubleLayerTensor W I₁ J₁)ᴴ =
        (doubleLayerTensor W L₁ M₁)ᴴ * Matrix.vecMulVec Φ' ρ' *
          (doubleLayerTensor W I₁ J₁)ᴴ) := by
  classical
  let K := J * (D * D)
  let ρT : Fin (D * D) → ℂ := fun x ↦
    ρ.transpose.vec (finProdFinEquiv.symm x)
  let ρ' : Fin (D * D) → ℂ := fun x ↦ ρ.vec (finProdFinEquiv.symm x)
  let Φ' : Fin (D * D) → ℂ := fun x ↦
    (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
  have hpowerRef := reflected_transfer_power_eq_vecMulVec_transpose U ρ J hpower
  have htraceT : Matrix.trace ρ.transpose = 1 := by
    rw [Matrix.trace_transpose, hρtrace]
  have hs := hU.physicalAdjointTensor.blockTensor_mul_sq_simple_contractions_of_transfer_power
    ρ.transpose htraceT J hJ hpowerRef
  dsimp only at hs
  have hsadd := blockTensor_add_two_simple_contractions_of_supplied
    hU.physicalAdjointTensor Φ' ρT hs.2
  have hstarρ : star ρT = ρ' := by
    funext x
    obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective x
    simp only [Pi.star_apply, Matrix.vec, Matrix.transpose_apply,
      Equiv.symm_apply_apply, ρT, ρ']
    exact hρ.isHermitian.apply c a
  have hstarΦ : star Φ' = Φ' := by
    funext x
    obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective x
    simp only [Pi.star_apply, Equiv.symm_apply_apply, Matrix.vec,
      Matrix.one_apply, Φ']
    simp
  dsimp only [K] at hsadd ⊢
  constructor
  · intro I J'
    calc
      ρ' ⬝ᵥ ((doubleLayerTensor
          (MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U)
            (J * (D * D) + 2)) I J')ᴴ *ᵥ Φ') =
          star (Φ' ⬝ᵥ (doubleLayerTensor
            (MPOTensor.blockTensor (MPOTensor.physicalAdjointTensor U)
              (J * (D * D) + 2)) I J' *ᵥ ρT)) := by
              rw [star_dotProduct_mulVec, hstarρ, hstarΦ]
      _ = if I = J' then 1 else 0 := by rw [hsadd.1 I J']; simp
  · intro I J' L M
    have hRank : (Matrix.vecMulVec ρT Φ')ᴴ =
        Matrix.vecMulVec Φ' ρ' := by
      rw [Matrix.conjTranspose_vecMulVec, hstarρ, hstarΦ]
    have h := congrArg Matrix.conjTranspose (hsadd.2 I J' L M)
    repeat' rw [Matrix.conjTranspose_mul] at h
    rw [hRank] at h
    simpa only [Matrix.mul_assoc] using h

end MPOTensor
