/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking

/-!
# Reblocking supplied MPU-simple witnesses

This file preserves specified `simple1` and `simple2` witnesses when a direct
physical block is extended by one or two sites. The proof uses the suffix of the
first word and prefix of the second word, so no existentially chosen witnesses
replace the supplied pair.

Source: arXiv:1703.09188, corollary following Proposition III.3, lines
442--446.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPOTensor

/-- Supplied `simple2` witnesses persist when a direct block is extended by
one site; the suffix/prefix windows preserve the exact witnesses.

Source: arXiv:1703.09188, corollary following Proposition III.3, lines
442--446. -/
theorem blockTensor_succ_simple2_of_supplied
    {d D : ℕ} {U : MPOTensor d D} {k : ℕ}
    (a b : Fin (D * D) → ℂ)
    (h₂ : ∀ i j m l : Fin (MPSTensor.blockPhysDim d k),
      doubleLayerTensor (blockTensor U k) i j *
          doubleLayerTensor (blockTensor U k) m l =
        doubleLayerTensor (blockTensor U k) i j * Matrix.vecMulVec b a *
          doubleLayerTensor (blockTensor U k) m l) :
    ∀ I J K L : Fin (MPSTensor.blockPhysDim d (k + 1)),
      doubleLayerTensor (blockTensor U (k + 1)) I J *
          doubleLayerTensor (blockTensor U (k + 1)) K L =
        doubleLayerTensor (blockTensor U (k + 1)) I J * Matrix.vecMulVec b a *
          doubleLayerTensor (blockTensor U (k + 1)) K L := by
  classical
  let W := doubleLayerTensor U
  let suffixIndex (I : Fin (MPSTensor.blockPhysDim d (k + 1))) :
      Fin (MPSTensor.blockPhysDim d k) :=
    (MPSTensor.decodeBlockEquiv d k).symm
      (fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) I x.succ)
  let prefixIndex (I : Fin (MPSTensor.blockPhysDim d (k + 1))) :
      Fin (MPSTensor.blockPhysDim d k) :=
    (MPSTensor.decodeBlockEquiv d k).symm
      (fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) I x.castSucc)
  have hmiddle (I J K L : Fin (MPSTensor.blockPhysDim d (k + 1))) :
      evalWord W
          (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) I x.succ)
          (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) J x.succ) *
        evalWord W
          (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) K x.castSucc)
          (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) L x.castSucc) =
      evalWord W
          (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) I x.succ)
          (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) J x.succ) *
        Matrix.vecMulVec b a *
          evalWord W
            (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) K x.castSucc)
            (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) L x.castSucc) := by
    have h := h₂ (suffixIndex I) (suffixIndex J) (prefixIndex K) (prefixIndex L)
    simpa only [doubleLayerTensor_blockTensor, blockTensor_apply,
      MPSTensor.wordOfBlock, MPSTensor.decodeBlock_decodeBlockEquiv_symm,
      W, suffixIndex, prefixIndex] using h
  have hfirst (I J : Fin (MPSTensor.blockPhysDim d (k + 1))) :
      evalWord W (List.ofFn (MPSTensor.decodeBlock d (k + 1) I))
          (List.ofFn (MPSTensor.decodeBlock d (k + 1) J)) =
        W (MPSTensor.decodeBlock d (k + 1) I 0)
            (MPSTensor.decodeBlock d (k + 1) J 0) *
          evalWord W
            (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) I x.succ)
            (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) J x.succ) := by
    rw [List.ofFn_succ, List.ofFn_succ, evalWord_cons]
  have hlast (I J : Fin (MPSTensor.blockPhysDim d (k + 1))) :
      evalWord W (List.ofFn (MPSTensor.decodeBlock d (k + 1) I))
          (List.ofFn (MPSTensor.decodeBlock d (k + 1) J)) =
        evalWord W
            (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) I x.castSucc)
            (List.ofFn fun x : Fin k ↦ MPSTensor.decodeBlock d (k + 1) J x.castSucc) *
          W (MPSTensor.decodeBlock d (k + 1) I (Fin.last k))
            (MPSTensor.decodeBlock d (k + 1) J (Fin.last k)) := by
    rw [List.ofFn_succ', List.ofFn_succ', List.concat_eq_append,
      List.concat_eq_append, evalWord_append W _ _ _ _ (by simp)]
    simp
  intro I J K L
  simp only [doubleLayerTensor_blockTensor, blockTensor_apply,
    MPSTensor.wordOfBlock]
  rw [hfirst I J, hlast K L]
  have h := congrArg
    (fun X ↦ W (MPSTensor.decodeBlock d (k + 1) I 0)
        (MPSTensor.decodeBlock d (k + 1) J 0) * X *
      W (MPSTensor.decodeBlock d (k + 1) K (Fin.last k))
        (MPSTensor.decodeBlock d (k + 1) L (Fin.last k)))
    (hmiddle I J K L)
  simpa only [Matrix.mul_assoc] using h

/-- Supplied `simple2` witnesses persist at the common direct block two sites
longer, by two exact suffix/prefix window extensions. -/
private lemma blockTensor_add_two_simple2
    {d D : ℕ} {U : MPOTensor d D} {k : ℕ}
    (a b : Fin (D * D) → ℂ)
    (h₂ : ∀ i j m l : Fin (MPSTensor.blockPhysDim d k),
      doubleLayerTensor (blockTensor U k) i j *
          doubleLayerTensor (blockTensor U k) m l =
        doubleLayerTensor (blockTensor U k) i j * Matrix.vecMulVec b a *
          doubleLayerTensor (blockTensor U k) m l) :
    ∀ I J K L : Fin (MPSTensor.blockPhysDim d (k + 2)),
      doubleLayerTensor (blockTensor U (k + 2)) I J *
          doubleLayerTensor (blockTensor U (k + 2)) K L =
        doubleLayerTensor (blockTensor U (k + 2)) I J * Matrix.vecMulVec b a *
          doubleLayerTensor (blockTensor U (k + 2)) K L := by
  have h₂₁ := blockTensor_succ_simple2_of_supplied (a := a) (b := b) h₂
  have h₂₂ := blockTensor_succ_simple2_of_supplied (a := a) (b := b) h₂₁
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h₂₂

private lemma trace_mul_rankOne_mul_supplied {n : Type*} [Fintype n]
    (a b : n → ℂ) (A X : Matrix n n ℂ) :
    Matrix.trace (A * Matrix.vecMulVec b a * X) =
      a ⬝ᵥ ((X * A) *ᵥ b) := by
  rw [Matrix.trace_mul_comm (A * Matrix.vecMulVec b a) X, ← Matrix.mul_assoc,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, ← Matrix.mulVec_mulVec]
  simp [dotProduct, mul_comm]

/-- For specified witnesses, MPU unitarity and `simple2` recover `simple1`
without changing either witness.

Source: arXiv:1703.09188, Definition III.2 and the corollary following
Proposition III.3, lines 363--374 and 442--446. -/
theorem IsMPU.simple1_of_simple2_supplied
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPU U)
    (a b : Fin (D * D) → ℂ)
    (h₂ : ∀ i j k l : Fin d,
      doubleLayerTensor U i j * doubleLayerTensor U k l =
        doubleLayerTensor U i j * Matrix.vecMulVec b a *
          doubleLayerTensor U k l) :
    ∀ i j : Fin d,
      a ⬝ᵥ (doubleLayerTensor U i j *ᵥ b) = if i = j then 1 else 0 := by
  classical
  intro i j
  let A := doubleLayerTensor U i j
  let x := a ⬝ᵥ (A *ᵥ b)
  have hclosed (N : ℕ) (hN : 1 < N) :
      Matrix.trace (evalWord (doubleLayerTensor U)
        (List.ofFn (fun _ : Fin N ↦ i)) (List.ofFn (fun _ : Fin N ↦ j))) =
        if i = j then 1 else 0 := by
    let σ : Fin N → Fin d := fun _ ↦ i
    let τ : Fin N → Fin d := fun _ ↦ j
    have hentry := congrArg (fun M ↦ M σ τ)
      (show mpo (doubleLayerTensor U) N =
          (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) by
        rw [mpo_doubleLayerTensor, hU.conjTranspose_mpo_mul_mpo hN])
    rw [mpo_apply, mpoMatrixEntry] at hentry
    have hστ : σ = τ ↔ i = j := by
      constructor
      · intro h
        exact congrFun h ⟨0, by omega⟩
      · intro h
        subst j
        rfl
    simpa only [Matrix.one_apply, hστ, σ, τ] using hentry
  have hA2 : A * A = A * Matrix.vecMulVec b a * A := by
    exact h₂ i j i j
  have hx2 : x ^ 2 = if i = j then 1 else 0 := by
    have h := hclosed 2 (by omega)
    simp only [List.ofFn_succ, List.ofFn_zero, evalWord_cons, evalWord_nil,
      Matrix.mul_one] at h
    change Matrix.trace (A * A) = _ at h
    rw [hA2, trace_mul_rankOne_mul_supplied, hA2] at h
    change x ^ 2 = _
    simpa [x, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMulVec_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec,
      pow_two] using h
  have hx3 : x ^ 3 = if i = j then 1 else 0 := by
    have h := hclosed 3 (by omega)
    simp only [List.ofFn_succ, List.ofFn_zero, evalWord_cons, evalWord_nil,
      Matrix.mul_one] at h
    change Matrix.trace (A * (A * A)) = _ at h
    have hA3 : A * (A * A) =
        A * Matrix.vecMulVec b a * (A * Matrix.vecMulVec b a * A) := by
      calc
        A * (A * A) = A * (A * Matrix.vecMulVec b a * A) := by rw [hA2]
        _ = (A * A) * Matrix.vecMulVec b a * A := by
          simp only [Matrix.mul_assoc]
        _ = (A * Matrix.vecMulVec b a * A) *
            Matrix.vecMulVec b a * A := by rw [hA2]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [hA3, trace_mul_rankOne_mul_supplied] at h
    have hreassoc : A * Matrix.vecMulVec b a * A * A =
        A * Matrix.vecMulVec b a * (A * A) := by
      simp only [Matrix.mul_assoc]
    rw [hreassoc, hA2] at h
    change x ^ 3 = _
    simpa [x, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMulVec_mulVec, Matrix.vecMul_smul, Matrix.vecMul_vecMulVec,
      dotProduct_smul, Matrix.dotProduct_mulVec, smul_eq_mul,
      pow_succ, pow_two, mul_assoc] using h
  by_cases hij : i = j
  · rw [if_pos hij] at hx2 hx3 ⊢
    have hx3' : x ^ 2 * x = 1 := by simpa [pow_succ] using hx3
    rw [hx2, one_mul] at hx3'
    exact hx3'
  · rw [if_neg hij] at hx2 hx3 ⊢
    exact sq_eq_zero_iff.mp hx2

/-- Exact supplied witnesses extend from a direct block of length $k$ to the
common overlapping-window block of length $k+2$, without replacing them by
existentially chosen witnesses.

Source: arXiv:1703.09188, corollary following Proposition III.3, lines
442--446. -/
theorem IsMPU.blockTensor_add_two_simple_contractions_of_supplied
    {d D : ℕ} {U : MPOTensor d D} (hU : IsMPU U) {k : ℕ}
    (a b : Fin (D * D) → ℂ)
    (h₂ : ∀ i j m l : Fin (MPSTensor.blockPhysDim d k),
      doubleLayerTensor (MPOTensor.blockTensor U k) i j *
          doubleLayerTensor (MPOTensor.blockTensor U k) m l =
        doubleLayerTensor (MPOTensor.blockTensor U k) i j * Matrix.vecMulVec b a *
          doubleLayerTensor (MPOTensor.blockTensor U k) m l) :
    (∀ I J : Fin (MPSTensor.blockPhysDim d (k + 2)),
      a ⬝ᵥ (doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) I J *ᵥ b) =
        if I = J then 1 else 0) ∧
    (∀ I J K L : Fin (MPSTensor.blockPhysDim d (k + 2)),
      doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) I J *
          doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) K L =
        doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) I J * Matrix.vecMulVec b a *
          doubleLayerTensor (MPOTensor.blockTensor U (k + 2)) K L) := by
  have h₂add := blockTensor_add_two_simple2 (a := a) (b := b) h₂
  exact ⟨IsMPU.simple1_of_simple2_supplied (hU.blockTensor (k + 2) (by omega)) a b h₂add,
    h₂add⟩

end MPOTensor
