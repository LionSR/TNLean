/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.MarkovDilation.AmbientBlockAction
import TNLean.Channel.KoashiImoto.MarkovDilation.SectorAction

/-!
# Markov dilation block form

This file provides the source-facing ambient block-coordinate dilation at
equality in strong subadditivity.  It records one chosen pure-ancilla physical
unitary, its supported agreement with the Petz channel, and the exact recovery
identity in HJPW equation (11).  No equality of the two channels is asserted
on the ambient complementary sector.

Source: Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 6, equation (15), lines 547--560;
Appendix A, Theorem 10, Property 2, lines 791--800; the equivalence
2 iff 2', lines 808--823; and the operation-level proof of 2',
lines 853--882.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

open MarkovDilation

variable {dA dB dC : ℕ}

/-- Ambient block-coordinate and physical-unitary data for the HJPW recovery
dilation.

`U_BCE_blocks` is the literal direct-sum unitary in the ambient tensor
coordinates.  `U_BCE_physical` is its conjugate in the original middle-system
coordinates.  The chosen pure-ancilla recovery agrees with the Petz channel
on inputs supported by `jointSupport.V * jointSupport.U` and satisfies the
exact recovery identity, but no equality is asserted on the complementary
ambient sector.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560; Appendix A, Theorem 10, Property 2, lines 791--800;
the equivalence 2 iff 2', lines 808--823; and the operation-level proof
of 2', lines 853--882.  This structure records one chosen pure-ancilla
unitary, not every unitary associated with the operation. -/
structure MarkovDilationBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    (F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm) where
  r : ℕ
  c₀ : Fin dC
  k₀ : Fin r
  R : Fin r → Matrix (Fin dB × Fin dC) (Fin dB) ℂ
  L : Fin r → ∀ j : Fin F.jointSupport.K,
    Matrix (Fin (F.jointSupport.m j) × Fin dC)
      (Fin (F.jointSupport.m j)) ℂ
  Ulocal : ∀ s : AmbientMarkovBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K,
    Matrix
      (Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r))
      (Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r)) ℂ
  U_BCE_blocks : Matrix (Fin dB × (Fin dC × Fin r))
    (Fin dB × (Fin dC × Fin r)) ℂ
  U_BCE_physical : Matrix (Fin dB × (Fin dC × Fin r))
    (Fin dB × (Fin dC × Fin r)) ℂ
  petz_kraus :
    ∀ X, partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
        (traceLeftA_posSemidef hρ_dm.1) X =
      rectangularKrausMap R X
  sector_tp :
    ∀ j, ∑ i, (L i j)ᴴ * L i j =
      (1 : Matrix (Fin (F.jointSupport.m j))
        (Fin (F.jointSupport.m j)) ℂ)
  sector_state_fixed :
    ∀ j,
      partialTraceRight
          (rectangularKrausMap (fun i ↦ L i j) (F.jointSupport.σ j)) =
        F.jointSupport.σ j
  complement_local_identity :
    ∀ z : Fin (dB - F.jointSupport.n), Ulocal (Sum.inl z) = 1
  sector_pure_ancilla_extension :
    ∀ j,
      Matrix.reindex
          (Equiv.prodAssoc (Fin (F.jointSupport.m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (F.jointSupport.m j)))
          (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientMarkovCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding
            (S := Fin (F.jointSupport.m j)) (c₀, k₀)
  local_unitary :
    ∀ s, Ulocal s ∈ Matrix.unitaryGroup
      (Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r)) ℂ
  block_coordinate_unitary_eq :
    U_BCE_blocks =
      Matrix.reindex
        (dilationBlockEquiv
          (ambientMarkovMiddleBlockEquiv F.e₀ F.jointSupport.e))
        (dilationBlockEquiv
          (ambientMarkovMiddleBlockEquiv F.e₀ F.jointSupport.e))
        (Matrix.blockDiagonal' fun s ↦
          Ulocal s ⊗ₖ
            (1 : Matrix
              (Fin (ambientMarkovConditionalDim F.jointSupport.d s))
              (Fin (ambientMarkovConditionalDim F.jointSupport.d s)) ℂ))
  block_coordinate_unitary :
    U_BCE_blocks ∈ Matrix.unitaryGroup (Fin dB × (Fin dC × Fin r)) ℂ
  physical_unitary_eq :
    U_BCE_physical =
      (F.U_B ⊗ₖ (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)) *
        U_BCE_blocks *
        star (F.U_B ⊗ₖ
          (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ))
  physical_unitary :
    U_BCE_physical ∈ Matrix.unitaryGroup (Fin dB × (Fin dC × Fin r)) ℂ
  inverse_coordinate_eq :
    star (F.U_B ⊗ₖ
        (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)) *
        U_BCE_physical *
        (F.U_B ⊗ₖ
          (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)) =
      U_BCE_blocks
  dilation_isometry_support :
    pureAncillaDilationIsometry c₀ k₀ U_BCE_physical *
        (F.jointSupport.V * F.jointSupport.U) =
      stinespringV R * (F.jointSupport.V * F.jointSupport.U)
  chosen_recovery_cptp :
    IsKrausCPTP (pureAncillaRecovery c₀ k₀ U_BCE_physical)
  recovery_agrees_on_support :
    ∀ X : Matrix (Fin F.jointSupport.n) (Fin F.jointSupport.n) ℂ,
      pureAncillaRecovery c₀ k₀ U_BCE_physical
          ((F.jointSupport.V * F.jointSupport.U) * X *
            (F.jointSupport.V * F.jointSupport.U)ᴴ) =
        partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
          (traceLeftA_posSemidef hρ_dm.1)
          ((F.jointSupport.V * F.jointSupport.U) * X *
            (F.jointSupport.V * F.jointSupport.U)ᴴ)
  recovery_eq11 :
    idTensorMapLM (δ := Fin dA)
        (pureAncillaRecovery c₀ k₀ U_BCE_physical)
        (traceC_ABC ρ_ABC) =
      ρ_ABC

/-- The sector output state on one supported common-factor sector together with
the output subsystem.

Its common-factor, or first-factor, marginal is the original common-factor
state; no state is assigned to an ambient complementary sector.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
noncomputable def MarkovDilationBlockForm.sectorOutputState
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    Matrix (Fin (F.jointSupport.m j) × Fin dC)
      (Fin (F.jointSupport.m j) × Fin dC) ℂ :=
  rectangularKrausMap (fun i ↦ D.L i j) (F.jointSupport.σ j)

/-- Applying one supported-sector recovery to an unnormalized left factor
and the common sector output state gives the tripartite tensor product of that
left factor with the sector output state.

This is the local block-action substitution used in the final lines of HJPW
Theorem 6. The left factor is deliberately not normalized: its trace may be
zero, and normalization is performed only in the final Markov decomposition.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (14)--(15),
lines 547--570. -/
theorem MarkovDilationBlockForm.idTensorMap_sectorOutput
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K)
    (ω : Matrix
      (Fin dA × Fin (F.jointSupport.d j))
      (Fin dA × Fin (F.jointSupport.d j)) ℂ) :
    idTensorMapLM (δ := Fin dA × Fin (F.jointSupport.d j))
        (rectangularKrausMap (fun i ↦ D.L i j))
        (ω ⊗ₖ F.jointSupport.σ j) =
      ω ⊗ₖ D.sectorOutputState j := by
  rw [idTensorMapLM_apply, idTensorMap_kronecker]
  rfl

/-- A supported sector output state is positive semidefinite.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
theorem MarkovDilationBlockForm.sectorOutputState_posSemidef
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    (D.sectorOutputState j).PosSemidef := by
  exact (rectangularKrausMap_isKrausCPTP
    (fun i ↦ D.L i j) (D.sector_tp j)).map_posSemidef
      (F.jointSupport.σ_pos j)

/-- A supported sector output state has trace one.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
theorem MarkovDilationBlockForm.sectorOutputState_trace
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    (D.sectorOutputState j).trace = 1 := by
  rw [MarkovDilationBlockForm.sectorOutputState,
    (rectangularKrausMap_isKrausCPTP
      (fun i ↦ D.L i j) (D.sector_tp j)).trace_map,
    F.jointSupport.σ_trace]

/-- The common-factor, or first-factor, marginal of a supported sector output
state is the original common-factor state.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560. -/
theorem
    MarkovDilationBlockForm.partialTraceRight_sectorOutputState
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F)
    (j : Fin F.jointSupport.K) :
    partialTraceRight (D.sectorOutputState j) =
      F.jointSupport.σ j :=
  D.sector_state_fixed j

/-- In the ambient HJPW coordinates, the Markov tripartite state has zero
complementary blocks and supported blocks in conditional--common-output order.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (11), (14), and
(15), lines 470--570. -/
theorem MarkovDilationBlockForm.ambient_tripartite_block_form
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    {F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm}
    (D : MarkovDilationBlockForm ρ_ABC hρ_dm F) :
    let eB := ambientMarkovMiddleBlockEquiv F.e₀ F.jointSupport.e
    star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))) *
        ρ_ABC *
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))) =
      ambientTripartiteBlockMatrix eB F.jointSupport.ω
        D.sectorOutputState := by
  classical
  dsimp only
  let eB := ambientMarkovMiddleBlockEquiv F.e₀ F.jointSupport.e
  let liftC := F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ)
  let TOut : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ →ₗ[ℂ]
      Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ :=
    { toFun := fun X => star liftC * X * (star liftC)ᴴ
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp }
  let TIn : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dB) (Fin dB) ℂ :=
    { toFun := fun X => star F.U_B * X * (star F.U_B)ᴴ
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp }
  let Rphysical := pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_physical
  let Rblocks := pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
  have hcov (X : Matrix (Fin dB) (Fin dB) ℂ) :
      TOut (Rphysical X) = Rblocks (TIn X) := by
    change star liftC *
        pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_physical X *
          (star liftC)ᴴ =
      pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
        (star F.U_B * X * (star F.U_B)ᴴ)
    rw [D.physical_unitary_eq]
    simpa only [liftC, ← Matrix.star_eq_conjTranspose, star_star] using
      pureAncillaRecovery_physical_conjugation
        D.c₀ D.k₀ F.U_B F.U_B_unitary D.U_BCE_blocks X
  have hmap : TOut.comp Rphysical = Rblocks.comp TIn := by
    apply LinearMap.ext
    intro X
    exact hcov X
  have hstarTensorC :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC) =
        (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ star liftC := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.star_eq_conjTranspose]
  have hstarTensorB :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) =
        (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ star F.U_B := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.star_eq_conjTranspose]
  have hconjTensorC :
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ star liftC)ᴴ =
        (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.star_eq_conjTranspose, star_star]
  have hconjTensorB :
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ star F.U_B)ᴴ =
        (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.star_eq_conjTranspose, star_star]
  have htransport (X : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC) *
          idTensorMapLM (δ := Fin dA) Rphysical X *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC) =
        idTensorMapLM (δ := Fin dA) Rblocks
          (star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) * X *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B)) := by
    rw [hstarTensorC, hstarTensorB]
    have hout := idTensorMap_conjugation (δ := Fin dA)
      (star liftC) (idTensorMapLM (δ := Fin dA) Rphysical X)
    have hin := idTensorMap_conjugation (δ := Fin dA)
      (star F.U_B) X
    rw [hconjTensorC] at hout
    rw [hconjTensorB] at hin
    calc
      _ = idTensorMapLM (δ := Fin dA) TOut
          (idTensorMapLM (δ := Fin dA) Rphysical X) := by
            simpa only [TOut] using hout.symm
      _ = idTensorMapLM (δ := Fin dA) (TOut.comp Rphysical) X := by
            rw [idTensorMapLM_comp]
            rfl
      _ = idTensorMapLM (δ := Fin dA) (Rblocks.comp TIn) X := by rw [hmap]
      _ = idTensorMapLM (δ := Fin dA) Rblocks
          (idTensorMapLM (δ := Fin dA) TIn X) := by
            rw [idTensorMapLM_comp]
            rfl
      _ = _ := by
        congr 1
  have hinput :
      star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) *
          traceC_ABC ρ_ABC *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) =
        ambientBipartiteBlockMatrix eB F.jointSupport.σ F.jointSupport.ω := by
    rw [F.ambient_bipartite_block_form]
    unfold ambientBipartiteBlockMatrix
    apply Matrix.ext
    intro x y
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    generalize (markovBipartiteBlockEquiv eB).symm x = p
    generalize (markovBipartiteBlockEquiv eB).symm y = q
    rcases p with ⟨s, u, av⟩
    rcases q with ⟨t, u', av'⟩
    rcases s with z | j <;> rcases t with z' | j' <;>
      simp [Matrix.blockDiagonal'_apply, ambientMarkovCommonState,
        ambientConditionalFactor, Matrix.kroneckerMap_apply]
  have hgeneric := blockDilation_fixedEnv_idTensorMap_blockDiagonal
    eB D.c₀ D.k₀ D.L D.Ulocal D.sector_pure_ancilla_extension
      F.jointSupport.σ F.jointSupport.ω
  have hUB : D.U_BCE_blocks = blockDilationUnitary eB D.Ulocal := by
    simpa only [eB, blockDilationUnitary] using D.block_coordinate_unitary_eq
  have hblockAction :
      idTensorMapLM (δ := Fin dA) Rblocks
          (ambientBipartiteBlockMatrix eB F.jointSupport.σ
            F.jointSupport.ω) =
        ambientTripartiteBlockMatrix eB F.jointSupport.ω
          D.sectorOutputState := by
    change idTensorMapLM (δ := Fin dA)
        (pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks)
          (ambientBipartiteBlockMatrix eB F.jointSupport.σ
            F.jointSupport.ω) = _
    rw [hUB]
    have hSlice : D.sectorOutputState =
        (fun j => rectangularKrausMap (fun i => D.L i j)
          (F.jointSupport.σ j)) := by
      rfl
    rw [hSlice]
    exact hgeneric
  calc
    _ = star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC) *
          idTensorMapLM (δ := Fin dA) Rphysical (traceC_ABC ρ_ABC) *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC) := by
          exact congrArg
            (fun X => star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC) *
              X * ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ liftC))
            D.recovery_eq11.symm
    _ = idTensorMapLM (δ := Fin dA) Rblocks
          (star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) *
            traceC_ABC ρ_ABC *
              ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B)) :=
        htransport (traceC_ABC ρ_ABC)
    _ = idTensorMapLM (δ := Fin dA) Rblocks
          (ambientBipartiteBlockMatrix eB F.jointSupport.σ
            F.jointSupport.ω) := by rw [hinput]
    _ = _ := hblockAction

/-- Relative to a chosen ambient Markov bipartite block form, the HJPW
recovery has a block-coordinate dilation of equation (15), with a corresponding
physical unitary and an exact realization of equation (11).

The literal block-coordinate unitary and its physical conjugate are recorded
separately.  Agreement with the Petz channel is asserted exactly on supported
inputs, with no complementary-sector equality claim.

This is the relative constructor used after the ambient block form has been
chosen; `exists_markovDilationBlockForm` is the source-facing theorem
that constructs that form from equality in strong subadditivity.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560; Appendix A, Theorem 10, Property 2, lines 791--800;
the equivalence 2 iff 2', lines 808--823; and the operation-level proof
of 2', lines 853--882.  The theorem constructs one chosen pure-ancilla
unitary, not every associated unitary. -/
theorem exists_markovDilationBlockForm_of_ambientBipartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian)
    [Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC))]
    (F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm) :
    Nonempty (MarkovDilationBlockForm ρ_ABC hρ_dm F) := by
  classical
  obtain ⟨r, R, S, C, L, hRmap, hRtp, hS, hSmap, hSsupport, hCblock,
      hSblock, hCtp, hL, hLtp, hLfix⟩ :=
    exists_normalizedSliceSectorBlocks ρ_ABC hρ_dm hSSA F
  have hBne : NeZero dB := by
    refine ⟨fun h ↦ ?_⟩
    subst dB
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρ_dm
    exact zero_ne_one hρ_dm.2
  have hCne : NeZero dC := by
    refine ⟨fun h ↦ ?_⟩
    subst dC
    rw [Matrix.trace_eq_zero_of_isEmpty] at hρ_dm
    exact zero_ne_one hρ_dm.2
  have hrne : NeZero r := by
    refine ⟨fun hr ↦ ?_⟩
    subst r
    have b : Fin dB := ⟨0, Nat.pos_of_ne_zero (NeZero.ne dB)⟩
    have hentry := congrFun (congrFun hRtp b) b
    simp at hentry
  let c₀ : Fin dC := ⟨0, Nat.pos_of_ne_zero (NeZero.ne dC)⟩
  let k₀ : Fin r := ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
  have hUsector : ∀ j : Fin F.jointSupport.K,
      ∃ U : Matrix.unitaryGroup
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ,
        Matrix.reindex
            (Equiv.prodAssoc (Fin (F.jointSupport.m j)) (Fin dC) (Fin r))
            (Equiv.refl (Fin (F.jointSupport.m j)))
            (stinespringV (fun i ↦ L i j)) =
          (U : Matrix
            (Fin (F.jointSupport.m j) × (Fin dC × Fin r))
            (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ) *
            fixedEnvEmbedding
              (S := Fin (F.jointSupport.m j)) (c₀, k₀) := by
    intro j
    exact exists_unitary_stinespringV_mul_fixedEnvEmbedding_eq
      c₀ k₀ (fun i ↦ L i j) (hLtp j)
  choose Us hUs using hUsector
  let Ulocal : ∀ s : AmbientMarkovBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K,
      Matrix
        (Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
          (Fin dC × Fin r))
        (Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
          (Fin dC × Fin r)) ℂ
    | Sum.inl _ => 1
    | Sum.inr j => by
        change Matrix
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r))
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ
        exact (Us j : Matrix
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r))
          (Fin (F.jointSupport.m j) × (Fin dC × Fin r)) ℂ)
  have hUlocal : ∀ s, Ulocal s ∈ Matrix.unitaryGroup
      (Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
        (Fin dC × Fin r)) ℂ := by
    intro s
    rcases s with z | j
    · exact Submonoid.one_mem _
    · convert (Us j).property using 1 <;> rfl
  let eD := dilationBlockEquiv
    (E := Fin dC × Fin r)
    (ambientMarkovMiddleBlockEquiv F.e₀ F.jointSupport.e)
  let U_BCE : Matrix (Fin dB × (Fin dC × Fin r))
      (Fin dB × (Fin dC × Fin r)) ℂ :=
    Matrix.reindex eD eD
      (Matrix.blockDiagonal' fun s ↦
        Ulocal s ⊗ₖ
          (1 : Matrix
            (Fin (ambientMarkovConditionalDim F.jointSupport.d s))
            (Fin (ambientMarkovConditionalDim F.jointSupport.d s)) ℂ))
  have hUblocks : ∀ s,
      Ulocal s ⊗ₖ
          (1 : Matrix
            (Fin (ambientMarkovConditionalDim F.jointSupport.d s))
            (Fin (ambientMarkovConditionalDim F.jointSupport.d s)) ℂ) ∈
        Matrix.unitaryGroup
          ((Fin (ambientMarkovCommonDim F.jointSupport.m s) ×
              (Fin dC × Fin r)) ×
            Fin (ambientMarkovConditionalDim F.jointSupport.d s)) ℂ := by
    intro s
    exact Matrix.kronecker_mem_unitary (hUlocal s) (Submonoid.one_mem _)
  have hUBCE : U_BCE ∈
      Matrix.unitaryGroup (Fin dB × (Fin dC × Fin r)) ℂ :=
    reindex_blockDiagonal'_mem_unitary eD _ hUblocks
  let lift := F.U_B ⊗ₖ
    (1 : Matrix (Fin dC × Fin r) (Fin dC × Fin r) ℂ)
  let U_BCE_physical : Matrix (Fin dB × (Fin dC × Fin r))
      (Fin dB × (Fin dC × Fin r)) ℂ :=
    lift * U_BCE * star lift
  obtain ⟨hUBCEphysical, hUBCEinverse⟩ :=
    physicalDilationUnitary_spec F.U_B F.U_B_unitary U_BCE hUBCE
  have hUlocalStinespring : ∀ j,
      Matrix.reindex
          (Equiv.prodAssoc (Fin (F.jointSupport.m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (F.jointSupport.m j)))
          (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientMarkovCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding
            (S := Fin (F.jointSupport.m j)) (c₀, k₀) := by
    intro j
    simpa [Ulocal, ambientMarkovCommonDim] using hUs j
  let J := ambientSupportEmbedding F.e₀
  let Z := F.jointSupport.V * F.jointSupport.U
  have hblockSlices := blockDilation_slice_support F.e₀ F.jointSupport.e
    c₀ k₀ C L hL Ulocal hUlocalStinespring
  have hcoordinate :
      lift * (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J) =
        Matrix.reindex
          (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
          (Equiv.refl (Fin F.jointSupport.n))
          (stinespringV R * Z) := by
    apply Matrix.ext
    rintro ⟨b, ⟨c, i⟩⟩ x
    let Bk := Matrix.reindex F.jointSupport.e F.jointSupport.e
      (Matrix.blockDiagonal' fun j ↦
        C (finProdFinEquiv (c, i)) j ⊗ₖ
          (1 : Matrix (Fin (F.jointSupport.d j))
            (Fin (F.jointSupport.d j)) ℂ))
    have hslices :
        rightOutputSlice
            (lift *
              (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J))
            (c, i) =
          rightOutputSlice
            (Matrix.reindex
              (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
              (Equiv.refl (Fin F.jointSupport.n))
              (stinespringV R * Z)) (c, i) := by
      calc
        rightOutputSlice
            (lift *
              (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J))
            (c, i) =
          F.U_B * rightOutputSlice
            (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J)
            (c, i) := by
              exact rightOutputSlice_kronecker_one_mul F.U_B _ (c, i)
        _ = F.U_B * (J * Bk) := by
          apply congrArg (fun X ↦ F.U_B * X)
          simpa [U_BCE, eD, J, Bk] using hblockSlices c i
        _ = (F.U_B * J) * Bk := by simp only [Matrix.mul_assoc]
        _ = Z * Bk := by
          rw [show Z = F.U_B * J by
            simpa [Z, J] using
              F.ambient_support_isometry]
        _ = S (finProdFinEquiv (c, i)) * Z :=
          (hSblock (finProdFinEquiv (c, i))).symm
        _ = rightOutputSlice (R i) c * Z := by
          rw [hS (finProdFinEquiv (c, i))]
          simp only [Equiv.symm_apply_apply]
        _ = rightOutputSlice
            (Matrix.reindex
              (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
              (Equiv.refl (Fin F.jointSupport.n))
              (stinespringV R * Z)) (c, i) :=
          (rightOutputSlice_reindex_stinespringV_mul R Z c i).symm
    exact congrFun (congrFun hslices b) x
  have hphysicalCoordinate :
      U_BCE_physical * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * Z =
        Matrix.reindex
          (Equiv.prodAssoc (Fin dB) (Fin dC) (Fin r))
          (Equiv.refl (Fin F.jointSupport.n))
          (stinespringV R * Z) := by
    calc
      U_BCE_physical * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * Z =
          lift * (U_BCE * fixedEnvEmbedding (S := Fin dB) (c₀, k₀) * J) := by
        rw [show Z = F.U_B * J by
          simpa [Z, J] using
            F.ambient_support_isometry]
        exact physicalDilation_mul_fixedEnvEmbedding_mul_support
          (c₀, k₀) F.U_B F.U_B_unitary U_BCE J
      _ = _ := hcoordinate
  have hIsometry :
      pureAncillaDilationIsometry c₀ k₀ U_BCE_physical * Z =
        stinespringV R * Z := by
    ext ⟨⟨b, c⟩, i⟩ x
    have hentry := congrFun (congrFun hphysicalCoordinate (b, (c, i))) x
    simpa [pureAncillaDilationIsometry, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.prodAssoc, Matrix.mul_apply] using hentry
  have hAgree :
      ∀ X : Matrix (Fin F.jointSupport.n) (Fin F.jointSupport.n) ℂ,
        pureAncillaRecovery c₀ k₀ U_BCE_physical (Z * X * Zᴴ) =
          partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1) (Z * X * Zᴴ) := by
    intro X
    exact (pureAncillaRecovery_eq_rectangularKrausMap_on_support
      c₀ k₀ U_BCE_physical R Z hIsometry X).trans
        (hRmap (Z * X * Zᴴ)).symm
  have hReconstruct :
      let W := (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ Z
      W * (Wᴴ * traceC_ABC ρ_ABC * W) * Wᴴ =
        traceC_ABC ρ_ABC := by
    simpa only [Z] using supportReconstruction_mul_unitary
      (traceC_ABC ρ_ABC) F.jointSupport.V F.jointSupport.U
        F.jointSupport.U_unitary F.jointSupport.ambient_reconstruction
  have hChosenEqPetz :
      idTensorMapLM (δ := Fin dA)
          (pureAncillaRecovery c₀ k₀ U_BCE_physical)
          (traceC_ABC ρ_ABC) =
        idTensorMapLM (δ := Fin dA)
          (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1))
          (traceC_ABC ρ_ABC) :=
    idTensorMap_eq_of_isometry_reconstruction
      (pureAncillaRecovery c₀ k₀ U_BCE_physical)
      (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
        (traceLeftA_posSemidef hρ_dm.1))
      (traceC_ABC ρ_ABC) Z hReconstruct hAgree
  have hEq11 :
      idTensorMapLM (δ := Fin dA)
          (pureAncillaRecovery c₀ k₀ U_BCE_physical)
          (traceC_ABC ρ_ABC) =
        ρ_ABC := by
    calc
      _ = idTensorMapLM (δ := Fin dA)
          (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
            (traceLeftA_posSemidef hρ_dm.1))
          (traceC_ABC ρ_ABC) := hChosenEqPetz
      _ = ρ_ABC :=
        idTensor_partialTraceRightPetzChannel_traceC_ABC_eq_of_isSSAEquality
          ρ_ABC hρ_dm hSSA
  refine ⟨{
    r := r
    c₀ := c₀
    k₀ := k₀
    R := R
    L := L
    Ulocal := Ulocal
    U_BCE_blocks := U_BCE
    U_BCE_physical := U_BCE_physical
    petz_kraus := hRmap
    sector_tp := hLtp
    sector_state_fixed := hLfix
    complement_local_identity := ?_
    sector_pure_ancilla_extension := hUlocalStinespring
    local_unitary := hUlocal
    block_coordinate_unitary_eq := rfl
    block_coordinate_unitary := hUBCE
    physical_unitary_eq := rfl
    physical_unitary := hUBCEphysical
    inverse_coordinate_eq := hUBCEinverse
    dilation_isometry_support := hIsometry
    chosen_recovery_cptp :=
      pureAncillaRecovery_isKrausCPTP
        c₀ k₀ U_BCE_physical hUBCEphysical
    recovery_agrees_on_support := ?_
    recovery_eq11 := hEq11 }⟩
  · intro z
    rfl
  · simpa only [Z] using hAgree

/-- At equality in strong subadditivity, the HJPW recovery admits an ambient
block-coordinate dilation of equation (15), with a corresponding physical
unitary and an exact realization of equation (11).

This source-facing theorem constructs the active conditional-effect index and ambient
bipartite block form internally.  Its conclusion combines the chosen ambient
form with its dilation witness, so no hypothesis beyond the
tripartite density-matrix and strong-subadditivity equality assumptions is
added to HJPW Theorem 6.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equation (15),
lines 547--560; Appendix A, Theorem 10, Property 2, lines 791--800;
the equivalence 2 iff 2', lines 808--823; and the operation-level proof
of 2', lines 853--882. -/
theorem exists_markovDilationBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    letI : Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC)) :=
      activeConditionalEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
        rw [← trace_eq_trace_traceC_ABC]
        exact hρ_dm.2)
    Nonempty
      (Σ F : AmbientMarkovBipartiteBlockForm ρ_ABC hρ_dm,
        MarkovDilationBlockForm ρ_ABC hρ_dm F) := by
  classical
  letI : Nonempty (ActiveConditionalEffectIndex (traceC_ABC ρ_ABC)) :=
    activeConditionalEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
      rw [← trace_eq_trace_traceC_ABC]
      exact hρ_dm.2)
  obtain ⟨F⟩ :=
    exists_ambientMarkovBipartiteBlockForm ρ_ABC hρ_dm hSSA
  obtain ⟨D⟩ :=
    exists_markovDilationBlockForm_of_ambientBipartiteBlockForm
      ρ_ABC hρ_dm hSSA F
  exact ⟨⟨F, D⟩⟩

end Matrix
