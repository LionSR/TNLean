/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.Channel.KoashiImoto.InvariantConditionalBlockForm

/-!
# Bipartite block form from normalized conditional slices

This file reconstructs the bipartite marginal in the minimum joint-support
coordinates of its normalized conditional slices.  The reconstruction uses the
finite informationally complete effects on the first subsystem.

This is a scope-restricted step toward Hayden, Jozsa, Petz and Winter,
arXiv:quant-ph/0304007v2, Theorem 6, equation (14), lines 499--502; extending
the coordinates to the ambient middle subsystem remains open.

**Convention (factor order):** TNLean orders each middle-system summand as
the common density factor followed by the conditional-state-dependent factor,
opposite to HJPW.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

variable {dA dB dC n : ℕ}

/-- Conditional slicing commutes with compression of the retained factor.

This is the coordinate identity underlying HJPW,
arXiv:quant-ph/0304007v2, Theorem 6, equation (14), lines 499--502. -/
private theorem conditionalSlice_one_kronecker_compression
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (M : Matrix (Fin dA) (Fin dA) ℂ)
    (V : Matrix (Fin dB) (Fin n) ℂ) :
    conditionalSlice
        ((1 ⊗ₖ V)ᴴ * ρ * (1 ⊗ₖ V)) M =
      Vᴴ * conditionalSlice ρ M * V := by
  classical
  let T : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X ↦ Vᴴ * X * V
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hmap :
      idTensorMapLM (δ := Fin dA) T ρ =
        (1 ⊗ₖ V)ᴴ * ρ * (1 ⊗ₖ V) := by
    ext ⟨a, k⟩ ⟨b, l⟩
    simp only [idTensorMapLM_apply, idTensorMap_apply, T,
      Matrix.mul_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    simp_rw [Fintype.sum_prod_type]
    simp
    rfl
  rw [← hmap, ← map_conditionalSlice]
  rfl

/-- Conditional slicing commutes with extension of the retained factor.

This is the coordinate identity used to reconstruct the ambient bipartite
state in HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (14),
lines 499--502. -/
private theorem conditionalSlice_one_kronecker_extension
    (ρ : Matrix (Fin dA × Fin n) (Fin dA × Fin n) ℂ)
    (M : Matrix (Fin dA) (Fin dA) ℂ)
    (V : Matrix (Fin dB) (Fin n) ℂ) :
    conditionalSlice
        ((1 ⊗ₖ V) * ρ * (1 ⊗ₖ V)ᴴ) M =
      V * conditionalSlice ρ M * Vᴴ := by
  classical
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin dB) (Fin dB) ℂ :=
    { toFun := fun X ↦ V * X * Vᴴ
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hmap :
      idTensorMapLM (δ := Fin dA) T ρ =
        (1 ⊗ₖ V) * ρ * (1 ⊗ₖ V)ᴴ := by
    ext ⟨a, k⟩ ⟨b, l⟩
    simp only [idTensorMapLM_apply, idTensorMap_apply, T,
      Matrix.mul_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    simp_rw [Fintype.sum_prod_type]
    simp
    rfl
  rw [← hmap, ← map_conditionalSlice]
  rfl

/-- A positive conditional slice with zero real trace vanishes. -/
private theorem conditionalSlice_eq_zero_of_trace_re_eq_zero
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : ρ.PosSemidef) (s : ICEffectIndex dA)
    (htrace : (conditionalSlice ρ
      (informationallyCompleteEffect s)).trace.re = 0) :
    conditionalSlice ρ (informationallyCompleteEffect s) = 0 := by
  let ξ := conditionalSlice ρ (informationallyCompleteEffect s)
  have hξ : ξ.PosSemidef :=
    hρ.conditionalSlice (informationallyCompleteEffect_posSemidef s)
  apply (hξ.trace_eq_zero_iff).mp
  apply Complex.ext
  · exact htrace
  · simpa using (Complex.nonneg_iff.mp hξ.trace_nonneg).2.symm

/-- Rescaling an active normalized conditional state recovers its
unnormalized conditional slice. -/
private theorem trace_re_smul_normalizedConditionalSlice
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (s : ActiveConditionalEffectIndex ρ) :
    ((conditionalSlice ρ
        (informationallyCompleteEffect (s : ICEffectIndex dA))).trace.re : ℂ) •
      normalizedConditionalSlice ρ s =
    conditionalSlice ρ
      (informationallyCompleteEffect (s : ICEffectIndex dA)) := by
  rw [normalizedConditionalSlice, smul_smul]
  rw [show
    ((conditionalSlice ρ
        (informationallyCompleteEffect (s : ICEffectIndex dA))).trace.re : ℂ) *
      (((conditionalSlice ρ
        (informationallyCompleteEffect (s : ICEffectIndex dA))).trace.re)⁻¹ : ℝ) =
        1 by exact_mod_cast mul_inv_cancel₀ s.property]
  simp

/-- Reconstruction from normalized active conditional states and vanishing
inactive conditional slices. -/
private theorem one_kronecker_reconstructs_of_normalizedConditionalSlice
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) (V : Matrix (Fin dB) (Fin n) ℂ)
    (hrec : ∀ s : ActiveConditionalEffectIndex ρ,
      V * (Vᴴ * normalizedConditionalSlice ρ s * V) * Vᴴ =
        normalizedConditionalSlice ρ s) :
    ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V) *
          (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V)ᴴ * ρ *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V)) *
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V)ᴴ = ρ := by
  apply eq_of_conditionalSlice_informationallyCompleteEffect_eq
  intro s
  rw [conditionalSlice_one_kronecker_extension,
    conditionalSlice_one_kronecker_compression]
  by_cases hs :
      (conditionalSlice ρ (informationallyCompleteEffect s)).trace.re = 0
  · rw [conditionalSlice_eq_zero_of_trace_re_eq_zero hρ s hs]
    simp
  · let x : ActiveConditionalEffectIndex ρ := ⟨s, hs⟩
    let p : ℂ :=
      (conditionalSlice ρ (informationallyCompleteEffect s)).trace.re
    have hscale :
        p • normalizedConditionalSlice ρ x =
          conditionalSlice ρ (informationallyCompleteEffect s) :=
      trace_re_smul_normalizedConditionalSlice ρ x
    calc
      V * (Vᴴ * conditionalSlice ρ (informationallyCompleteEffect s) * V) * Vᴴ =
          p • (V * (Vᴴ * normalizedConditionalSlice ρ x * V) * Vᴴ) := by
            rw [← hscale]
            simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = p • normalizedConditionalSlice ρ x := by rw [hrec x]
      _ = conditionalSlice ρ (informationallyCompleteEffect s) := hscale

/-- Reassociate subsystem A with the joint-support direct-sum coordinates.

The target order is the one used by TNLean in HJPW Theorem 6, equation (14):
the common factor precedes the joint A--conditional factor. -/
def markovBipartiteBlockEquiv
    {ι : Type*} {d m : ι → ℕ}
    (e : ((j : ι) × (Fin (m j) × Fin (d j))) ≃ Fin n) :
    ((j : ι) × (Fin (m j) × (Fin dA × Fin (d j)))) ≃
      Fin dA × Fin n :=
  (Equiv.sigmaCongrRight fun j ↦
      (Equiv.refl (Fin (m j))).prodCongr
        (Equiv.prodComm (Fin dA) (Fin (d j)))
      |>.trans (Equiv.prodAssoc (Fin (m j)) (Fin (d j)) (Fin dA)).symm)
    |>.trans (Equiv.sigmaProdDistrib
      (fun j : ι ↦ Fin (m j) × Fin (d j)) (Fin dA)).symm
    |>.trans (e.prodCongr (Equiv.refl (Fin dA)))
    |>.trans (Equiv.prodComm (Fin n) (Fin dA))

@[simp]
theorem markovBipartiteBlockEquiv_apply
    {ι : Type*} {d m : ι → ℕ}
    (e : ((j : ι) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (a : Fin dA)
    (z : (j : ι) × (Fin (m j) × Fin (d j))) :
    markovBipartiteBlockEquiv (dA := dA) e
        ⟨z.1, (z.2.1, (a, z.2.2))⟩ =
      (a, e z) := by
  simp [markovBipartiteBlockEquiv]

@[simp]
theorem markovBipartiteBlockEquiv_symm_apply
    {ι : Type*} {d m : ι → ℕ}
    (e : ((j : ι) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (a : Fin dA)
    (z : (j : ι) × (Fin (m j) × Fin (d j))) :
    (markovBipartiteBlockEquiv (dA := dA) e).symm (a, e z) =
      ⟨z.1, (z.2.1, (a, z.2.2))⟩ := by
  simp [markovBipartiteBlockEquiv]
  rfl

/-- Conditional-slice block equations reconstruct a positive bipartite
direct-sum tensor form. -/
private theorem exists_bipartiteBlockForm_of_conditionalSlice_blockForm
    {K : ℕ} {d m : Fin K → ℕ}
    (R : Matrix (Fin dA × Fin n) (Fin dA × Fin n) ℂ)
    (hR : R.PosSemidef)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (hσtrace : ∀ j, (σ j).trace = 1)
    (hslice : ∀ s : ICEffectIndex dA,
      ∃ X : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ,
        conditionalSlice R (informationallyCompleteEffect s) =
          Matrix.reindex e e
            (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j)) :
    ∃ ω : ∀ j,
        Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ,
      (∀ j, (ω j).PosSemidef) ∧
      R = Matrix.reindex (markovBipartiteBlockEquiv e)
        (markovBipartiteBlockEquiv e)
        (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ ω j) ∧
      ∑ j, (ω j).trace = R.trace := by
  classical
  let g := markovBipartiteBlockEquiv (dA := dA) e
  let S := Matrix.reindex g.symm g.symm R
  let ω : ∀ j,
      Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ :=
    fun j ↦ Matrix.partialTraceLeft
      (S.submatrix (fun z ↦ ⟨j, z⟩) (fun z ↦ ⟨j, z⟩))
  have hS : S.PosSemidef := by
    exact hR.submatrix g
  have hωpos : ∀ j, (ω j).PosSemidef := by
    intro j
    exact (hS.submatrix (fun z ↦ ⟨j, z⟩)).partialTraceLeft
  have hform : R = Matrix.reindex (markovBipartiteBlockEquiv e)
      (markovBipartiteBlockEquiv e)
      (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ ω j) := by
    apply eq_of_conditionalSlice_informationallyCompleteEffect_eq
    intro s
    obtain ⟨X, hX⟩ := hslice s
    ext k l
    let zk := e.symm k
    let zl := e.symm l
    have hk : k = e zk := by simp [zk]
    have hl : l = e zl := by simp [zl]
    conv_lhs =>
      rw [hk, hl]
    conv_rhs =>
      rw [hk, hl]
    obtain ⟨j, zk⟩ := zk
    obtain ⟨j', zl⟩ := zl
    by_cases hj : j = j'
    · subst j'
      have hωslice :
          conditionalSlice (ω j) (informationallyCompleteEffect s) =
            X j := by
        ext c d'
        change
          (∑ a, ∑ b, (∑ x,
            R (a, e ⟨j, (x, c)⟩)
              (b, e ⟨j, (x, d')⟩)) *
            informationallyCompleteEffect s b a) =
          X j c d'
        simp_rw [Finset.sum_mul]
        calc
          (∑ a, ∑ b, ∑ x,
              R (a, e ⟨j, (x, c)⟩)
                  (b, e ⟨j, (x, d')⟩) *
                informationallyCompleteEffect s b a) =
              ∑ a, ∑ x, ∑ b,
                R (a, e ⟨j, (x, c)⟩)
                    (b, e ⟨j, (x, d')⟩) *
                  informationallyCompleteEffect s b a := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.sum_comm]
          _ =
              ∑ x, ∑ a, ∑ b,
                R (a, e ⟨j, (x, c)⟩)
                    (b, e ⟨j, (x, d')⟩) *
                  informationallyCompleteEffect s b a := by
                    rw [Finset.sum_comm]
          _ = ∑ x, σ j x x * X j c d' := by
            apply Finset.sum_congr rfl
            intro x _
            have hentry := congrFun (congrFun hX
              (e ⟨j, (x, c)⟩))
              (e ⟨j, (x, d')⟩)
            simpa only [conditionalSlice, Matrix.reindex_apply,
              Matrix.submatrix_apply, Equiv.symm_apply_apply,
              Matrix.blockDiagonal'_apply_eq,
              Matrix.kroneckerMap_apply] using hentry
          _ = (σ j).trace * X j c d' := by
            rw [← Finset.sum_mul]
            rfl
          _ = X j c d' := by rw [hσtrace, one_mul]
      calc
        conditionalSlice R (informationallyCompleteEffect s)
            (e ⟨j, zk⟩) (e ⟨j, zl⟩) =
            σ j zk.1 zl.1 * X j zk.2 zl.2 := by
              have hentry := congrFun (congrFun hX
                (e ⟨j, zk⟩)) (e ⟨j, zl⟩)
              simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
                Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq,
                Matrix.kroneckerMap_apply] using hentry
        _ = σ j zk.1 zl.1 *
            conditionalSlice (ω j) (informationallyCompleteEffect s)
              zk.2 zl.2 := by rw [hωslice]
        _ = conditionalSlice
            (Matrix.reindex (markovBipartiteBlockEquiv e)
              (markovBipartiteBlockEquiv e)
              (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ ω j))
            (informationallyCompleteEffect s)
            (e ⟨j, zk⟩) (e ⟨j, zl⟩) := by
              simp only [conditionalSlice, Matrix.reindex_apply,
                Matrix.submatrix_apply, Matrix.blockDiagonal'_apply_eq,
                Matrix.kroneckerMap_apply,
                markovBipartiteBlockEquiv_symm_apply]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              simpa only [mul_comm, mul_left_comm, mul_assoc] using
                (Fintype.sum_mul_mul_eq_mul_sum_mul
                  (σ j zk.1 zl.1) (fun x => informationallyCompleteEffect s x a)
                  (fun x => ω j (a, zk.2) (x, zl.2))).symm
    · calc
        conditionalSlice R (informationallyCompleteEffect s)
            (e ⟨j, zk⟩) (e ⟨j', zl⟩) = 0 := by
          have hentry := congrFun (congrFun hX (e ⟨j, zk⟩)) (e ⟨j', zl⟩)
          simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
            Equiv.symm_apply_apply,
            Matrix.blockDiagonal'_apply_ne _ _ _ hj] using hentry
        _ = conditionalSlice
            (Matrix.reindex (markovBipartiteBlockEquiv e)
              (markovBipartiteBlockEquiv e)
              (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ ω j))
            (informationallyCompleteEffect s)
            (e ⟨j, zk⟩) (e ⟨j', zl⟩) := by
              simp only [conditionalSlice, Matrix.reindex_apply,
                Matrix.submatrix_apply,
                Matrix.blockDiagonal'_apply_ne _ _ _ hj,
                zero_mul, Finset.sum_const_zero,
                markovBipartiteBlockEquiv_symm_apply]
  refine ⟨ω, hωpos, hform, ?_⟩
  have htrace := congrArg Matrix.trace hform
  rw [Matrix.trace_reindex, Matrix.trace_blockDiagonal'] at htrace
  simpa only [Matrix.trace_kronecker, hσtrace, one_mul] using htrace.symm

/-- The invariant conditional-family witnesses together with the bipartite
block form on their minimum joint support.

This structure retains the preserving family, density operators, support
isometry, and block-action identities used to obtain the coordinates.  Its
final fields add the joint-support bipartite reconstruction toward HJPW
Theorem 6, equation (14), lines 499--502.

**Scope restriction (HJPW Theorem 6, equation (14)):** the direct-sum
coordinates cover only the minimum joint support, not the ambient middle
subsystem.  This is documented in
`docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`.
Elimination: extend the coordinates to the ambient middle subsystem before
proving the recovery-dilation action of equation (15). -/
structure MarkovBipartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))] where
  F : Kraus.PreservingKrausFamily
    (normalizedConditionalSlice (traceC_ABC ρ_ABC))
  n : ℕ
  V : Matrix (Fin dB) (Fin n) ℂ
  petzMiddleChannel_eq : ∀ X, Kraus.map F.Kfam X =
    petzMiddleChannel ρ_ABC hρ_dm.1 X
  V_isometry : Vᴴ * V = 1
  V_range : V * Vᴴ = (Kraus.commonAverage_posSemidef
      (normalizedConditionalSlice (traceC_ABC ρ_ABC))
        (normalizedConditionalSlice_posSemidef
          (SSAPosDef.traceC_ABC_posSemidef hρ_dm.1))).supportProj
  support_reconstruction : ∀ x,
    V * Kraus.supportCompressedFamily V
      (normalizedConditionalSlice (traceC_ABC ρ_ABC)) x * Vᴴ =
      normalizedConditionalSlice (traceC_ABC ρ_ABC) x
  K : ℕ
  d : Fin K → ℕ
  m : Fin K → ℕ
  e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n
  U : Matrix (Fin n) (Fin n) ℂ
  σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ
  q : ActiveConditionalEffectIndex (traceC_ABC ρ_ABC) → Fin K → ℝ
  τ : ActiveConditionalEffectIndex (traceC_ABC ρ_ABC) → ∀ j,
    Matrix (Fin (d j)) (Fin (d j)) ℂ
  U_unitary : U ∈ Matrix.unitaryGroup (Fin n) ℂ
  d_pos : ∀ j, 0 < d j
  m_pos : ∀ j, 0 < m j
  σ_pos : ∀ j, (σ j).PosSemidef
  σ_trace : ∀ j, (σ j).trace = 1
  q_nonneg : ∀ x j, 0 ≤ q x j
  q_sum : ∀ x, ∑ j, q x j = 1
  τ_pos : ∀ x j, (τ x j).PosSemidef
  τ_trace : ∀ x j, (τ x j).trace = 1
  normalizedConditionalSlice_eq : ∀ x,
    star U * Kraus.supportCompressedFamily V
        (normalizedConditionalSlice (traceC_ABC ρ_ABC)) x * U =
      Matrix.reindex e e
        (Matrix.blockDiagonal' fun j ↦
          (q x j : ℂ) • (σ j ⊗ₖ τ x j))
  preserving_support_action :
    ∀ G : Kraus.PreservingKrausFamily
        (normalizedConditionalSlice (traceC_ABC ρ_ABC)),
      Kraus.IsPreserving
          (Kraus.supportCompressedFamily V
            (normalizedConditionalSlice (traceC_ABC ρ_ABC)))
          (Kraus.supportCompressedKraus V G.Kfam) ∧
        ∀ X, Kraus.map G.Kfam (V * X * Vᴴ) =
          V * Kraus.map (Kraus.supportCompressedKraus V G.Kfam) X * Vᴴ
  preserving_block_action :
    ∀ G : Kraus.PreservingKrausFamily
        (Kraus.supportCompressedFamily V
          (normalizedConditionalSlice (traceC_ABC ρ_ABC))),
      ∃ C : (i : Fin G.numKraus) → ∀ j,
          Matrix (Fin (m j)) (Fin (m j)) ℂ,
        (∀ i,
          Matrix.reindex e.symm e.symm (star U * G.Kfam i * U) =
            Matrix.blockDiagonal' fun j ↦
              C i j ⊗ₖ (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) ∧
        (∀ j, Kraus.IsTP (fun i ↦ C i j)) ∧
        (∀ j, Kraus.map (fun i ↦ C i j) (σ j) = σ j) ∧
        ∀ j (A : Matrix (Fin (m j)) (Fin (m j)) ℂ)
            (B : Matrix (Fin (d j)) (Fin (d j)) ℂ),
          Matrix.reindex e.symm e.symm
              (star U * Kraus.map G.Kfam
                (U * Matrix.reindex e e
                  (Matrix.directSumBlockEmbedding (m := m) (d := d) j
                    (A ⊗ₖ B)) * star U) * U) =
            Matrix.directSumBlockEmbedding (m := m) (d := d) j
              (Kraus.map (fun i ↦ C i j) A ⊗ₖ B)
  ambient_reconstruction :
    let W := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V
    W * (Wᴴ * traceC_ABC ρ_ABC * W) * Wᴴ = traceC_ABC ρ_ABC
  ω : ∀ j, Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ
  ω_pos : ∀ j, (ω j).PosSemidef
  bipartite_block_form :
    let W := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V
    let R := ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U)ᴴ *
      (Wᴴ * traceC_ABC ρ_ABC * W) *
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U)
    R = Matrix.reindex (markovBipartiteBlockEquiv e)
      (markovBipartiteBlockEquiv e)
      (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ ω j)
  ω_trace_sum : ∑ j, (ω j).trace = 1

/-- **Markov bipartite block form on the minimum joint support.**

At equality in strong subadditivity, the exact joint-support witnesses of
`exists_normalizedConditionalSliceBlockForm_preservingBlockAction_jointSupport`
also reconstruct the bipartite marginal.  The result retains the complete
preserving family, density operators, support isometry, and block-action
identities.  With `W = 1_A ⊗ V`, the ambient state is reconstructed from its
support compression.  After the same unitary `U`, that compression is
`\bigoplus_j σ_j ⊗ ω_j`, where each unnormalized `ω j` is positive and their
traces sum to one.

TNLean uses the reverse tensor-factor order from HJPW.  The tensor equation is
only on the minimum joint-support coordinates; no ambient equivalence on
subsystem B or rectangular recovery action is claimed.

**Scope restriction (HJPW Theorem 6, equation (14)):** the source states an
ambient direct-sum equivalence on subsystem B, whereas this theorem supplies
the block equation only after compression to the minimum joint support.  This
is documented in
`docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex`.
Elimination: extend the support coordinates to ambient B before proving the
recovery-dilation action of equation (15). -/
theorem exists_markovBipartiteBlockForm_jointSupport
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    letI : Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC)) :=
      activeConditionalEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
        rw [← trace_eq_trace_traceC_ABC]
        exact hρ_dm.2)
    Nonempty (MarkovBipartiteBlockForm ρ_ABC hρ_dm) := by
  classical
  letI : Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC)) :=
    activeConditionalEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
      rw [← trace_eq_trace_traceC_ABC]
      exact hρ_dm.2)
  obtain ⟨F, n, V, hFmap, hV, hVrange, hrec, K, d, m, e, U, σ, q, τ,
      hU, hd, hm, hσpos, hσtrace, hqnonneg, hqsum, hτpos, hτtrace,
      hfamily, hpres, haction⟩ :=
    exists_normalizedConditionalSliceBlockForm_preservingBlockAction_jointSupport
      ρ_ABC hρ_dm hSSA
  let ρ_AB := traceC_ABC ρ_ABC
  let μ := normalizedConditionalSlice ρ_AB
  let W := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ V
  have hABpos : ρ_AB.PosSemidef :=
    SSAPosDef.traceC_ABC_posSemidef hρ_dm.1
  have hambient : W * (Wᴴ * ρ_AB * W) * Wᴴ = ρ_AB :=
    one_kronecker_reconstructs_of_normalizedConditionalSlice
      ρ_AB hABpos V (by
        intro x
        simpa only [Kraus.supportCompressedFamily] using hrec x)
  let R := ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U)ᴴ *
    (Wᴴ * ρ_AB * W) *
    ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U)
  have hR : R.PosSemidef := by
    have hcompressed : (Wᴴ * ρ_AB * W).PosSemidef :=
      by simpa only [Matrix.conjTranspose_conjTranspose] using
        hABpos.mul_mul_conjTranspose_same Wᴴ
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hcompressed.mul_mul_conjTranspose_same
        (((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U)ᴴ)
  have hslice : ∀ s : ICEffectIndex dA,
      ∃ X : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ,
        conditionalSlice R (informationallyCompleteEffect s) =
          Matrix.reindex e e
            (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j) := by
    intro s
    by_cases hs :
        (conditionalSlice ρ_AB (informationallyCompleteEffect s)).trace.re = 0
    · refine ⟨fun _ ↦ 0, ?_⟩
      dsimp only [R, W]
      rw [conditionalSlice_one_kronecker_compression,
        conditionalSlice_one_kronecker_compression,
        conditionalSlice_eq_zero_of_trace_re_eq_zero hABpos s hs]
      ext z w
      simp [Matrix.blockDiagonal'_apply]
    · let x : ActiveConditionalEffectIndex ρ_AB := ⟨s, hs⟩
      let p : ℂ :=
        (conditionalSlice ρ_AB (informationallyCompleteEffect s)).trace.re
      refine ⟨fun j ↦ (p * q x j) • τ x j, ?_⟩
      dsimp only [R, W]
      rw [conditionalSlice_one_kronecker_compression,
        conditionalSlice_one_kronecker_compression]
      have hscale :
          p • normalizedConditionalSlice ρ_AB x =
            conditionalSlice ρ_AB (informationallyCompleteEffect s) :=
        trace_re_smul_normalizedConditionalSlice ρ_AB x
      rw [← hscale]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      rw [show Vᴴ * normalizedConditionalSlice ρ_AB x * V =
        Kraus.supportCompressedFamily V μ x by rfl]
      change p • (star U * Kraus.supportCompressedFamily V μ x * U) = _
      rw [hfamily x]
      ext z w
      simp only [Matrix.smul_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply]
      let z' := e.symm z
      let w' := e.symm w
      have hz : e.symm z = z' := rfl
      have hw : e.symm w = w' := rfl
      rw [hz, hw]
      by_cases hzw : z'.1 = w'.1
      · obtain ⟨j, z'⟩ := z'
        obtain ⟨j', w'⟩ := w'
        dsimp only at hzw
        subst j'
        change p •
              Matrix.blockDiagonal'
                (fun j ↦ (q x j : ℂ) • (σ j ⊗ₖ τ x j))
                ⟨j, z'⟩ ⟨j, w'⟩ =
            Matrix.blockDiagonal'
              (fun j ↦ σ j ⊗ₖ ((p * q x j) • τ x j))
              ⟨j, z'⟩ ⟨j, w'⟩
        rw [Matrix.blockDiagonal'_apply_eq,
          Matrix.blockDiagonal'_apply_eq]
        simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply]
        ring
      · change p •
            Matrix.blockDiagonal'
              (fun j ↦ (q x j : ℂ) • (σ j ⊗ₖ τ x j)) z' w' =
          Matrix.blockDiagonal'
            (fun j ↦ σ j ⊗ₖ ((p * q x j) • τ x j)) z' w'
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hzw,
          Matrix.blockDiagonal'_apply_ne _ _ _ hzw]
        simp
  obtain ⟨ω, hωpos, hRform, hωtraceR⟩ :=
    exists_bipartiteBlockForm_of_conditionalSlice_blockForm
      R hR e σ hσtrace hslice
  have hRtrace : R.trace = 1 := by
    have hW : Wᴴ * W = 1 := by
      dsimp only [W]
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, hV, Matrix.one_mul]
      exact Matrix.one_kronecker_one
    have hUright : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hT :
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U) *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ U)ᴴ = 1 := by
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, hUright, Matrix.one_mul]
      exact Matrix.one_kronecker_one
    have hcompressedTrace : (Wᴴ * ρ_AB * W).trace = 1 := by
      have ht := congrArg Matrix.trace hambient
      rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul] at ht
      rw [ht]
      rw [← trace_eq_trace_traceC_ABC]
      exact hρ_dm.2
    dsimp only [R]
    rw [Matrix.trace_mul_cycle, hT, Matrix.one_mul]
    exact hcompressedTrace
  exact ⟨{
    F := F
    n := n
    V := V
    petzMiddleChannel_eq := hFmap
    V_isometry := hV
    V_range := hVrange
    support_reconstruction := hrec
    K := K
    d := d
    m := m
    e := e
    U := U
    σ := σ
    q := q
    τ := τ
    U_unitary := hU
    d_pos := hd
    m_pos := hm
    σ_pos := hσpos
    σ_trace := hσtrace
    q_nonneg := hqnonneg
    q_sum := hqsum
    τ_pos := hτpos
    τ_trace := hτtrace
    normalizedConditionalSlice_eq := hfamily
    preserving_support_action := hpres
    preserving_block_action := haction
    ambient_reconstruction := hambient
    ω := ω
    ω_pos := hωpos
    bipartite_block_form := hRform
    ω_trace_sum := hωtraceR.trans hRtrace }⟩

end Matrix
