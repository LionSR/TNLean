import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.Conjugation
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.Core.BlockingInfrastructure

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.NoncommRing

/-!
# Cyclic-sector decompositions for blocked MPS tensors

This file develops the projection and compression tools used to split blocked
left-canonical tensors into cyclic sectors. The main results compress tensors
supported on orthogonal projections and assemble commuting projection data into
multi-block decompositions, following the peripheral-spectrum decomposition used
in canonical-form arguments.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex KadisonSchwarz

namespace MPSTensor

variable {d D : ℕ}

section BasicProjectionWordLemmas

/-- Left-multiply every letter by `P`. -/
noncomputable def leftSectorTensor (P : MatrixAlg D) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => P * A i

/-- If `P` commutes with every letter of `A`, then it commutes with every evaluated word. -/
lemma commutes_evalWord_of_commutes_letters
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d), P * evalWord A w = evalWord A w * P := by
  intro w
  induction w with
  | nil => simp only [evalWord, mul_one, one_mul]
  | cons i w ih =>
      simp only [evalWord]
      calc P * (A i * evalWord A w)
          = A i * (evalWord A w * P) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hComm i, Matrix.mul_assoc,
              Matrix.mul_assoc, ih]
        _ = A i * evalWord A w * P := by rw [← Matrix.mul_assoc]

lemma left_mul_evalWord_leftSectorTensor_of_commutes
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d),
      P * evalWord (leftSectorTensor P A) w = P * evalWord A w := by
  intro w
  induction w with
  | nil => simp only [evalWord, mul_one]
  | cons i w ih =>
      simp only [leftSectorTensor, evalWord]
      calc P * (P * A i * evalWord (leftSectorTensor P A) w)
          = P * P * A i * evalWord (leftSectorTensor P A) w := by
            simp only [Matrix.mul_assoc]
        _ = P * A i * evalWord (leftSectorTensor P A) w := by rw [hPidem]
        _ = A i * (P * evalWord (leftSectorTensor P A) w) := by
            rw [← Matrix.mul_assoc, hComm i, Matrix.mul_assoc]
        _ = A i * (P * evalWord A w) := by rw [ih]
        _ = P * (A i * evalWord A w) := by
            rw [← Matrix.mul_assoc, ← hComm i, Matrix.mul_assoc]

/-- A left-sector tensor is supported on the sector projection. -/
lemma leftSectorTensor_supported
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ i : Fin d, P * leftSectorTensor P A i * P = leftSectorTensor P A i := by
  intro i
  simp only [leftSectorTensor]
  calc P * (P * A i) * P = P * P * A i * P := by simp only [Matrix.mul_assoc]
    _ = P * A i * P := by rw [hPidem]
    _ = P * A i := by rw [hComm i, Matrix.mul_assoc, hPidem]

end BasicProjectionWordLemmas

section Compression

variable {P : MatrixAlg D}

/-- Word evaluation of the unitary-conjugated tensor. -/
private lemma evalWord_conj_unitary
    (A : MPSTensor d D) (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ w : List (Fin d),
      evalWord (fun i => (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) w =
        (↑U : MatrixAlg D)ᴴ * evalWord A w * (↑U : MatrixAlg D) := by
  intro w
  induction w with
  | nil =>
      have hUU : (↑U : MatrixAlg D)ᴴ * (↑U : MatrixAlg D) = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
      simp only [evalWord, mul_one, hUU]
  | cons i w ih =>
      have hUU : (↑U : MatrixAlg D) * (↑U : MatrixAlg D)ᴴ = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.prop
      simp only [evalWord]
      rw [ih]
      calc (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D) *
            ((↑U : MatrixAlg D)ᴴ * evalWord A w * (↑U : MatrixAlg D))
          = (↑U : MatrixAlg D)ᴴ * A i * ((↑U : MatrixAlg D) * (↑U : MatrixAlg D)ᴴ) *
              evalWord A w * (↑U : MatrixAlg D) := by noncomm_ring
        _ = (↑U : MatrixAlg D)ᴴ * (A i * evalWord A w) * (↑U : MatrixAlg D) := by
              simp only [hUU, mul_one, Matrix.mul_assoc]

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.
-/
theorem exists_compressedTensor_of_supported_projection
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) := by
  classical
  -- Spectral diagonalization of P
  let hHerm : P.IsHermitian := hP.1
  let U := hHerm.eigenvectorUnitary
  let Umat : MatrixAlg D := (U : MatrixAlg D)
  have hUU : Umat * Umatᴴ = 1 :=
    by simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.prop
  have hU'U : Umatᴴ * Umat = 1 :=
    by simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  -- Helper: trace invariance under unitary conjugation
  have trace_conj (M : MatrixAlg D) : Matrix.trace (Umatᴴ * M * Umat) = Matrix.trace M := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm Umatᴴ (M * Umat),
      Matrix.mul_assoc, hUU, Matrix.mul_one]
  let Pdiag : MatrixAlg D := Umatᴴ * P * Umat
  let f : Fin D → ℂ := fun j => (↑(hHerm.eigenvalues j) : ℂ)
  have hPdiag_eq : Pdiag = Matrix.diagonal f := by
    have h := hHerm.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Pdiag, f, Unitary.conjStarAlgAut_star_apply] using h
  have hPdiag_idem : Pdiag * Pdiag = Pdiag := by
    change Umatᴴ * P * Umat * (Umatᴴ * P * Umat) = Umatᴴ * P * Umat
    calc Umatᴴ * P * Umat * (Umatᴴ * P * Umat)
        = Umatᴴ * (P * (Umat * Umatᴴ) * P) * Umat := by simp only [Matrix.mul_assoc]
      _ = Umatᴴ * (P * P) * Umat := by rw [hUU, Matrix.mul_one]
      _ = Umatᴴ * P * Umat := by rw [hP.2]
  have hf01 : ∀ j : Fin D, f j = 0 ∨ f j = 1 := by
    intro j
    have hDiag_idem : Matrix.diagonal f * Matrix.diagonal f = Matrix.diagonal f := by
      simpa [hPdiag_eq] using hPdiag_idem
    have hfun : (fun k => f k * f k) = f := by
      apply Matrix.diagonal_injective; simpa [Matrix.diagonal_mul_diagonal] using hDiag_idem
    exact mul_self_eq_self_or_eq_one (f j) (congrFun hfun j)
  -- Index splitting
  let p : Fin D → Prop := fun j => f j = 1
  haveI : DecidablePred p := fun _ => inferInstance
  let S := { j : Fin D // p j }
  let T := { j : Fin D // ¬ p j }
  let n := Fintype.card S
  have hfT : ∀ t : T, f t.1 = 0 := fun t => (hf01 t.1).resolve_right t.2
  let eST : Fin D ≃ (S ⊕ T) := (Equiv.sumCompl p).symm
  let eS : S ≃ Fin n := Fintype.equivFin S
  -- Conjugated tensor
  let B : MPSTensor d D := fun i => Umatᴴ * A i * Umat
  -- Algebra isomorphism for reindexing
  let φ : MatrixAlg D ≃ₐ[ℂ] Matrix (S ⊕ T) (S ⊕ T) ℂ := Matrix.reindexAlgEquiv ℂ ℂ eST
  let P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ)
  -- Pdiag in S⊕T basis
  have hPdiag_std : φ Pdiag = P0 := by
    change Matrix.reindex eST eST Pdiag = P0
    rw [hPdiag_eq, show Matrix.reindex eST eST (Matrix.diagonal f) =
        Matrix.diagonal (f ∘ eST.symm) from by simp only [reindex_apply, submatrix_diagonal_equiv]]
    ext x y; cases x with
    | inl s => cases y with
      | inl s' => by_cases h : s = s'
                  · subst h; simpa [p, P0] using s.2
                  · simp only [ne_eq, Sum.inl.injEq, h, not_false_eq_true, diagonal_apply_ne, fromBlocks_apply₁₁, one_apply_ne, P0]
      | inr t => simp only [ne_eq, reduceCtorEq, not_false_eq_true, diagonal_apply_ne, fromBlocks_apply₁₂, zero_apply, P0]
    | inr t => cases y with
      | inl s => simp only [ne_eq, reduceCtorEq, not_false_eq_true, diagonal_apply_ne, fromBlocks_apply₂₁, zero_apply, P0]
      | inr t' => by_cases h : t = t'
                  · subst h; simpa [p, P0] using hfT t
                  · simp only [ne_eq, Sum.inr.injEq, h, not_false_eq_true, diagonal_apply_ne, fromBlocks_apply₂₂, zero_apply, P0]
  -- B_i is Pdiag-supported
  have hBsupp : ∀ i : Fin d, Pdiag * B i * Pdiag = B i := by
    intro i
    have hkey : Pdiag * B i * Pdiag = Umatᴴ * (P * A i * P) * Umat := by
      change Umatᴴ * P * Umat * (Umatᴴ * A i * Umat) * (Umatᴴ * P * Umat) =
          Umatᴴ * (P * A i * P) * Umat
      calc Umatᴴ * P * Umat * (Umatᴴ * A i * Umat) * (Umatᴴ * P * Umat)
          = Umatᴴ * (P * (Umat * Umatᴴ) * A i * (Umat * Umatᴴ) * P) * Umat := by
            simp only [Matrix.mul_assoc]
        _ = Umatᴴ * (P * A i * P) * Umat := by rw [hUU, Matrix.mul_one, Matrix.mul_one]
    rw [hkey, hSupp i]
  -- Block structure
  let X : Fin d → Matrix (S ⊕ T) (S ⊕ T) ℂ := fun i => φ (B i)
  let B11 : Fin d → Matrix S S ℂ := fun i => (X i).toBlocks₁₁
  have hX_block : ∀ i : Fin d,
      X i = Matrix.fromBlocks (B11 i) 0 0 (0 : Matrix T T ℂ) := by
    intro i
    have hsupp_block : P0 * X i * P0 = X i := by
      have := congrArg φ (hBsupp i); simp only [map_mul, hPdiag_std] at this; exact this
    rw [(Matrix.fromBlocks_toBlocks (X i)).symm]
    rw [(Matrix.fromBlocks_toBlocks (X i)).symm] at hsupp_block
    simp only [P0, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero] at hsupp_block
    -- `hsupp_block` forces all blocks outside the `S`-sector to vanish.
    have extract (x y : S ⊕ T) := congrFun (congrFun hsupp_block x) y
    have h12 : (X i).toBlocks₁₂ = 0 := by
      ext s t
      have h := extract (Sum.inl s) (Sum.inr t)
      simp only [fromBlocks, of_apply, Sum.elim_inl, Sum.elim_inr, zero_apply] at h
      exact h.symm
    have h21 : (X i).toBlocks₂₁ = 0 := by
      ext t s
      have h := extract (Sum.inr t) (Sum.inl s)
      simp only [fromBlocks, of_apply, Sum.elim_inr, Sum.elim_inl, zero_apply] at h
      exact h.symm
    have h22 : (X i).toBlocks₂₂ = 0 := by
      ext t t'
      have h := extract (Sum.inr t) (Sum.inr t')
      simp only [fromBlocks, of_apply, Sum.elim_inr, zero_apply] at h
      exact h.symm
    rw [h12, h21, h22]
  -- Compressed tensor
  let C : MPSTensor d n := fun i => Matrix.reindex eS eS (B11 i)
  refine ⟨n, C, ?_, ?_, ?_⟩
  -- (1) Trace identity: n = tr P
  · show (n : ℂ) = Matrix.trace P
    have : Matrix.trace P = Matrix.trace Pdiag := by
      change Matrix.trace P = Matrix.trace (Umatᴴ * P * Umat)
      rw [trace_conj]
    rw [this, hPdiag_eq, Matrix.trace_diagonal]
    have hfsum : ∑ j : Fin D, f j = ∑ j : Fin D, if p j then (1 : ℂ) else 0 := by
      congr 1; ext j; show f j = if p j then 1 else 0
      by_cases hp : p j
      · simp only [show f j = 1 from hp, hp, ↓reduceIte]
      · simp only [show f j = 0 from (hf01 j).resolve_right hp, hp, ↓reduceIte]
    rw [hfsum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    change n = (Finset.univ.filter p).card
    exact Fintype.card_subtype p
  -- (2) TP condition: ∑ C_i† C_i = 1
  · show ∑ i : Fin d, (C i)ᴴ * C i = 1
    -- First: ∑ B_i† B_i = Pdiag
    have hTPB : ∑ i : Fin d, (B i)ᴴ * B i = Pdiag := by
      have hterm : ∀ i, (B i)ᴴ * B i = Umatᴴ * ((A i)ᴴ * A i) * Umat := by
        intro i
        change
          (Umatᴴ * A i * Umat)ᴴ * (Umatᴴ * A i * Umat) = Umatᴴ * ((A i)ᴴ * A i) * Umat
        -- (U† A U)† = U† A† U†† = U† A† U (note U†† = U)
        have hconj : (Umatᴴ * A i * Umat)ᴴ = Umatᴴ * (A i)ᴴ * Umat := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
          rw [Matrix.mul_assoc]
        rw [hconj]
        -- U† A† U * U† A U = U† A† (UU†) A U = U† (A† A) U
        calc Umatᴴ * (A i)ᴴ * Umat * (Umatᴴ * A i * Umat)
            = Umatᴴ * ((A i)ᴴ * (Umat * Umatᴴ) * A i) * Umat := by
              simp only [Matrix.mul_assoc]
          _ = Umatᴴ * ((A i)ᴴ * A i) * Umat := by rw [hUU, Matrix.mul_one]
      simp_rw [hterm]
      -- ∑ i, U† ((A i)† A i) U = U† (∑ (A i)† A i) U = U† P U = Pdiag
      trans Umatᴴ * (∑ i : Fin d, (A i)ᴴ * A i) * Umat
      · rw [Finset.mul_sum, Finset.sum_mul]
      · rw [hTP]
    -- Transport to S⊕T: ∑ B11_i† B11_i = 1_S
    have hTPblock : ∑ i : Fin d, (B11 i)ᴴ * B11 i = (1 : Matrix S S ℂ) := by
      -- φ(∑ B_i† B_i) = ∑ φ(B_i† * B_i) = ∑ (X_i)† (X_i) = P0
      -- But we also need φ(B_i†) = (X_i)†
      have hφ_ct : ∀ i, φ ((B i)ᴴ) = (X i)ᴴ := by
        intro i; ext a b
        simp only [reindexAlgEquiv, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm, reindexLinearEquiv_symm,
          AlgEquiv.coe_mk, Equiv.coe_fn_mk, reindexLinearEquiv_apply, reindex_apply,
          submatrix_apply, conjTranspose_apply, RCLike.star_def, φ, X]
      -- h : ∑ (X_i)† * X_i = P0
      have h : ∑ i : Fin d, (X i)ᴴ * X i = P0 := by
        have h0 := congrArg φ hTPB
        rw [map_sum] at h0
        simp only [map_mul] at h0
        -- h0 : ∑ φ (B i)ᴴ * φ (B i) = φ Pdiag
        -- φ (B i)ᴴ is actually φ((B i)ᴴ) after map_mul, which equals (X i)ᴴ by hφ_ct
        -- Actually hφ_ct says φ (B i)ᴴ = (X i)ᴴ where φ (B i) = X i
        -- So φ (B i)ᴴ = (X i)ᴴ, and φ (B i) = X i
        simp only [show ∀ i, φ (B i) = X i from fun i => rfl] at h0
        -- Now need: φ (B i)ᴴ = (X i)ᴴ... but after map_mul, what does h0 look like?
        -- Let me just use the fact that φ preserves star/conjTranspose
        rw [hPdiag_std] at h0
        convert h0 using 1
      -- Substitute block form X_i = fromBlocks(B11_i, 0, 0, 0)
      have hblock : ∀ i, (X i)ᴴ * X i =
          Matrix.fromBlocks ((B11 i)ᴴ * B11 i) 0 0 (0 : Matrix T T ℂ) := by
        intro i; rw [hX_block i]
        simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.zero_mul, mul_zero]
      simp_rw [hblock] at h
      -- Extract (S,S) block from h
      ext s s'
      have h1 := congrFun (congrFun h (Sum.inl s)) (Sum.inl s')
      -- LHS of h1: (∑ fromBlocks(...))(inl s)(inl s') = ∑ (fromBlocks(...))(inl s)(inl s')
      -- = ∑ (B11 i)† * B11 i s s'
      -- RHS of h1: P0 (inl s) (inl s') = 1 s s'
      -- h1 : (∑ x, fromBlocks((B11 x)† * B11 x, 0, 0, 0))(inl s)(inl s') = 1 s s'
      -- goal : (∑ i, (B11 i)† * B11 i) s s' = 1 s s'
      exact congrFun (congrFun (show ∑ i : Fin d, (B11 i)ᴴ * B11 i = (1 : Matrix S S ℂ) from by
        ext s1 s2
        have h2 := congrFun (congrFun h (Sum.inl s1)) (Sum.inl s2)
        simp only [P0, Matrix.fromBlocks_apply₁₁, Matrix.sum_apply,
          Matrix.fromBlocks_apply₁₁] at h2
        rwa [Matrix.sum_apply]) s) s'
    -- Transport to Fin n
    have hterm : ∀ i, (C i)ᴴ * C i = Matrix.reindex eS eS ((B11 i)ᴴ * B11 i) := by
      intro i
      change
        (Matrix.reindex eS eS (B11 i))ᴴ * Matrix.reindex eS eS (B11 i) =
          Matrix.reindex eS eS ((B11 i)ᴴ * B11 i)
      rw [show (Matrix.reindex eS eS (B11 i))ᴴ = Matrix.reindex eS eS ((B11 i)ᴴ) from by
        ext a b; simp only [reindex_apply, conjTranspose_apply, submatrix_apply, RCLike.star_def]]
      simp only [reindex_apply, submatrix_mul_equiv]
    simp_rw [hterm]
    -- ∑ reindex eS eS (f i) = reindex eS eS (∑ f i)
    ext a b
    simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.one_apply]
    rw [show (∑ i : Fin d, ((B11 i)ᴴ * B11 i) (eS.symm a) (eS.symm b)) =
        (∑ i : Fin d, (B11 i)ᴴ * B11 i) (eS.symm a) (eS.symm b) from
      (Matrix.sum_apply (eS.symm a) (eS.symm b) _ _).symm]
    rw [hTPblock, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  -- (3) MPV identity
  · intro N σ
    set w := List.ofFn σ
    -- mpv C σ = tr(evalWord B11 w) (by reindexing)
    have hmpv_C : mpv C σ = Matrix.trace (_root_.evalWord B11 w) := by
      simp only [mpv, coeff]
      have : MPSTensor.evalWord C w = Matrix.reindex eS eS (_root_.evalWord B11 w) := by
        simpa [C] using MPSTensor.evalWord_reindex (e := eS) (A := B11) w
      rw [this]; exact Matrix.trace_reindex eS _
    -- tr(evalWord B11 w) = tr(Pdiag * evalWord B w)
    -- Proved entrywise using the block structure
    have htr_key : Matrix.trace (_root_.evalWord B11 w) =
        Matrix.trace (Pdiag * evalWord B w) := by
      -- Both sides = ∑_{s:S} (evalWord B11 w) s s
      -- Reindex RHS to S⊕T
      have htrace_reindex :
          Matrix.trace (Pdiag * evalWord B w) =
            Matrix.trace (φ (Pdiag * evalWord B w)) := by
        change Matrix.trace (Pdiag * evalWord B w) =
          Matrix.trace (Matrix.reindex eST eST (Pdiag * evalWord B w))
        rw [Matrix.trace_reindex]
      rw [htrace_reindex]
      rw [map_mul, hPdiag_std]
      -- φ(evalWord B w) = evalWord X w
      have hφ_eval : φ (evalWord B w) = _root_.evalWord X w := by
        change Matrix.reindex eST eST (evalWord B w) = _root_.evalWord X w
        have h := evalWord_reindex_fin (e := eST) (A := B) w
        rw [show (fun i => Matrix.reindex eST eST (B i)) = X from by
          ext i; simp only [reindex_apply, submatrix_apply, reindexAlgEquiv_apply, X, φ]] at h
        exact h.symm
      rw [hφ_eval]
      -- Now: tr(P0 * evalWord X w) = tr(evalWord B11 w)
      -- Entrywise argument
      change Matrix.trace (_root_.evalWord B11 w) =
        Matrix.trace (P0 * _root_.evalWord X w)
      symm
      -- tr(P0 * M) = ∑_{s:S} M (inl s) (inl s) for any M
      rw [show Matrix.trace (P0 * _root_.evalWord X w) =
          ∑ x : S ⊕ T, (P0 * _root_.evalWord X w) x x from rfl,
        Fintype.sum_sum_type]
      -- T part is zero since P0 has zero T-rows
      have hT_zero : ∑ t : T, (P0 * _root_.evalWord X w) (Sum.inr t) (Sum.inr t) = 0 := by
        apply Finset.sum_eq_zero; intro t _
        change (P0 * _root_.evalWord X w) (Sum.inr t) (Sum.inr t) = 0
        simp only [Matrix.mul_apply]
        apply Finset.sum_eq_zero; intro y _
        cases y with
        | inl s => simp only [fromBlocks_apply₂₁, zero_apply, zero_mul, P0]
        | inr t' => simp only [fromBlocks_apply₂₂, zero_apply, zero_mul, P0]
      rw [hT_zero, add_zero]
      -- S part: (P0 * M)(inl s)(inl s) = M(inl s)(inl s) since P0 is identity on S
      have hS_eq : ∀ s : S, (P0 * _root_.evalWord X w) (Sum.inl s) (Sum.inl s) =
          _root_.evalWord X w (Sum.inl s) (Sum.inl s) := by
        intro s; simp only [Matrix.mul_apply]
        rw [Fintype.sum_sum_type]
        have hT : ∑ t : T, P0 (Sum.inl s) (Sum.inr t) *
            _root_.evalWord X w (Sum.inr t) (Sum.inl s) = 0 := by
          apply Finset.sum_eq_zero; intro t _
          simp only [fromBlocks_apply₁₂, zero_apply, zero_mul, P0]
        rw [hT, add_zero]
        rw [Finset.sum_eq_single s]
        · simp only [fromBlocks_apply₁₁, one_apply_eq, one_mul, P0]
        · intro s' _ hs'
          have hsne : s ≠ s' := hs' ∘ Eq.symm
          have hzero : P0 (Sum.inl s) (Sum.inl s') = 0 := by
            simp only [fromBlocks_apply₁₁, ne_eq, hsne, not_false_eq_true, one_apply_ne, P0]
          simp only [hzero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ s) h
      simp_rw [hS_eq]
      -- Now: ∑_{s:S} evalWord X w (inl s) (inl s) = ∑_{s:S} evalWord B11 w s s
      -- This follows because (evalWord X w).toBlocks₁₁ = evalWord B11 w
      -- (by induction, since each X_i = fromBlocks(B11_i, 0, 0, 0))
      congr 1; ext s
      -- evalWord X w (inl s) (inl s) = evalWord B11 w s s
      suffices ∀ ww : List (Fin d), ∀ s1 s2 : S,
          _root_.evalWord X ww (Sum.inl s1) (Sum.inl s2) =
          _root_.evalWord B11 ww s1 s2 from this w s s
      intro ww; induction ww with
      | nil =>
          intro s1 s2; simp only [_root_.evalWord, one_apply, Sum.inl.injEq]
      | cons j ww ih =>
          intro s1 s2
          simp only [_root_.evalWord, Matrix.mul_apply, Fintype.sum_sum_type]
          -- T contribution is zero
          have : ∑ t : T, X j (Sum.inl s1) (Sum.inr t) *
              _root_.evalWord X ww (Sum.inr t) (Sum.inl s2) = 0 := by
            apply Finset.sum_eq_zero; intro t _
            rw [show X j (Sum.inl s1) (Sum.inr t) = 0 from by
              rw [hX_block j]; simp only [fromBlocks_apply₁₂, zero_apply]]
            simp only [zero_mul]
          rw [this, add_zero]
          congr 1; ext s'
          rw [show X j (Sum.inl s1) (Sum.inl s') = B11 j s1 s' from by
            rw [hX_block j]; simp only [fromBlocks_apply₁₁]]
          rw [ih s' s2]
    -- tr(Pdiag * evalWord B w) = tr(P * evalWord A w) by unitary conjugation
    have htr_conj : Matrix.trace (Pdiag * evalWord B w) =
        Matrix.trace (P * evalWord A (List.ofFn σ)) := by
      have hEvalB := evalWord_conj_unitary A U (List.ofFn σ)
      rw [show (fun i => (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) = B from rfl] at hEvalB
      rw [hEvalB]
      change
        Matrix.trace (Umatᴴ * P * Umat * (Umatᴴ * evalWord A (List.ofFn σ) * Umat)) =
          Matrix.trace (P * evalWord A (List.ofFn σ))
      set M := evalWord A (List.ofFn σ)
      -- U†PU * U†MU = U†P(UU†)MU = U†(PM)U, tr = tr(PM) by trace_conj
      have hprod : Umatᴴ * P * Umat * (Umatᴴ * M * Umat) = Umatᴴ * (P * M) * Umat := by
        calc Umatᴴ * P * Umat * (Umatᴴ * M * Umat)
            = Umatᴴ * (P * (Umat * Umatᴴ) * M) * Umat := by simp only [Matrix.mul_assoc]
          _ = Umatᴴ * (P * M) * Umat := by rw [hUU, Matrix.mul_one]
      rw [hprod, trace_conj]
    calc mpv C σ
        = Matrix.trace (_root_.evalWord B11 w) := hmpv_C
      _ = Matrix.trace (Pdiag * evalWord B w) := htr_key
      _ = Matrix.trace (P * evalWord A (List.ofFn σ)) := htr_conj

end Compression

section CompressionPositiveMPV

/-- A supported-projection compression preserves MPVs at all positive lengths.

This is the usable replacement for a heterogeneous `SameMPV₂` statement: compression changes the
`N = 0` coefficient from `trace 1 = D` to `trace P`, so exact all-length equality is false in
general, but every positive-length MPV is preserved. -/
theorem exists_compressedTensor_of_supported_projection_pos_mpv
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ {N : ℕ}, 0 < N → ∀ σ : Fin N → Fin d, mpv A σ = mpv C σ) := by
  obtain ⟨dim, C, hdim, hCtp, hCmpv⟩ :=
    exists_compressedTensor_of_supported_projection A P hP hSupp hTP
  refine ⟨dim, C, hdim, hCtp, ?_⟩
  have hleft : ∀ i : Fin d, P * A i = A i := by
    intro i
    calc
      P * A i = P * (P * A i * P) := by rw [hSupp i]
      _ = (P * P) * A i * P := by simp only [Matrix.mul_assoc]
      _ = P * A i * P := by rw [hP.2]
      _ = A i := by simpa [Matrix.mul_assoc] using hSupp i
  have hword :
      ∀ {w : List (Fin d)}, w ≠ [] → P * evalWord A w = evalWord A w := by
    intro w hw
    cases w with
    | nil =>
        cases hw rfl
    | cons i w =>
        calc
          P * evalWord A (i :: w) = P * (A i * evalWord A w) := by rfl
          _ = (P * A i) * evalWord A w := by rw [Matrix.mul_assoc]
          _ = A i * evalWord A w := by rw [hleft i]
          _ = evalWord A (i :: w) := by rfl
  intro N hN σ
  cases N with
  | zero =>
      cases Nat.not_lt_zero _ hN
  | succ n' =>
      have hPw :
          P * evalWord A (List.ofFn σ) = evalWord A (List.ofFn σ) := by
        apply hword
        simp only [List.ofFn_succ, ne_eq, reduceCtorEq, not_false_eq_true]
      calc
        mpv A σ = Matrix.trace (evalWord A (List.ofFn σ)) := by rfl
        _ = Matrix.trace (P * evalWord A (List.ofFn σ)) := by
              exact congrArg Matrix.trace hPw.symm
        _ = mpv C σ := (hCmpv (N := n'.succ) σ).symm

end CompressionPositiveMPV

section CommutingProjectionDecomposition

variable {m : ℕ}

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor. -/
theorem exists_blockDecomp_of_commuting_projections
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) := by
  -- For each k, sector tensor P_k * A_i is P_k-supported
  have hSectorSupp : ∀ k i, P k * (P k * A i) * P k = P k * A i := by
    intro k i
    rw [← Matrix.mul_assoc (P k) (P k) _, (hPproj k).2,
      hComm k i, Matrix.mul_assoc, (hPproj k).2]
  -- TP condition for each sector
  have hSectorTP : ∀ k, ∑ i : Fin d, (P k * A i)ᴴ * (P k * A i) = P k := by
    intro k
    have hterm : ∀ i, (P k * A i)ᴴ * (P k * A i) = (A i)ᴴ * A i * P k := by
      intro i
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P k)ᴴ (P k) (A i), (hPproj k).1.eq, (hPproj k).2]
      rw [hComm k i, ← Matrix.mul_assoc]
    simp_rw [hterm, ← Finset.sum_mul, hLeft, Matrix.one_mul]
  -- Apply compression to each sector
  choose dim blocks hDim hTPblocks hMPVblocks using fun k =>
    exists_compressedTensor_of_supported_projection
      (fun i => P k * A i) (P k) (hPproj k) (hSectorSupp k) (hSectorTP k)
  -- Per-sector trace relation: mpv(blocks k) σ = tr(P_k · evalWord A σ)
  have hSectorTrace : ∀ k (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace := by
    intro k N σ
    rw [hMPVblocks k N σ]
    congr 1
    exact left_mul_evalWord_leftSectorTensor_of_commutes (P k) A (hPproj k).2 (hComm k) _
  refine ⟨dim, blocks, hTPblocks, ?_, hSectorTrace⟩
  -- SameMPV₂ follows from summing per-sector traces over the projection partition
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum]; simp only [one_pow, one_smul]
  simp only [mpv, coeff]
  conv_lhs => rw [show evalWord A (List.ofFn σ) = 1 * evalWord A (List.ofFn σ) from by
    rw [Matrix.one_mul]]
  rw [show (1 : MatrixAlg D) = ∑ k : Fin m, P k from hPsum.symm]
  rw [Finset.sum_mul, Matrix.trace_sum]
  congr 1; ext k
  exact (hSectorTrace k N σ).symm

end CommutingProjectionDecomposition

section FixedAdjointProjection

/-- A fixed orthogonal projection for the adjoint blocked map commutes with every Kraus operator
of the blocked tensor. -/
theorem commutes_letters_of_adjoint_fixed_projection
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : MatrixAlg D} (hP : IsOrthogonalProjection P)
    (hFix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) P = P) :
    ∀ i : Fin d, P * A i = A i * P := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hTPK : IsTPKraus (d := d) (D := D) A := by simpa [IsTPKraus] using hLeft
  have hUnitalK : IsUnitalKraus (d := d) (D := D) K :=
    KadisonSchwarz.isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTPK
  have hKFix : krausMap K P = P := by
    simpa [K, KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hFix
  have hEq : krausMap K (Pᴴ * P) = (krausMap K P)ᴴ * krausMap K P := by
    calc
      krausMap K (Pᴴ * P) = krausMap K P := by simp only [(hP.1.eq), (hP.2)]
      _ = P := hKFix
      _ = Pᴴ * P := by simp only [(hP.1.eq), (hP.2)]
      _ = (krausMap K P)ᴴ * krausMap K P := by simp only [hKFix]
  intro i
  have hComm := KadisonSchwarz.kraus_commute_of_ks_equality (K := K) hUnitalK P hEq i
  simpa [K, hKFix] using hComm

theorem exists_blockDecomp_of_adjoint_fixed_projections
    {m : ℕ}
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hFix : ∀ k : Fin m, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) := by
  have hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k := by
    intro k i
    exact commutes_letters_of_adjoint_fixed_projection
        (A := A) hLeft (hP := hPproj k) (hFix := hFix k) i
  exact exists_blockDecomp_of_commuting_projections A P hPproj hPsum hLeft hComm

end FixedAdjointProjection

end MPSTensor
