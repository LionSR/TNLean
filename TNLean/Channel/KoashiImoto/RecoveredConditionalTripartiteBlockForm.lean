/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.HayashiMarkovStructure
import TNLean.Channel.KrausBlockTransport
import TNLean.Channel.KoashiImoto.RecoveredConditionalDilation.Covariance
import TNLean.Channel.KoashiImoto.RecoveredConditionalDilationBlockForm

/-!
# Recovered conditional tripartite block form

This file transports the recovered bipartite factors and the sector recovery
states into the tripartite direct sum at equality in strong subadditivity.
The middle-system fibres are written in HJPW order, with the conditional
factor before the common factor. Complementary sectors remain zero.

Source: Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570;
arXiv:1606.00608, Appendix C.2, Lemma `Lsigma3`, equation `eq:sigma3`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker
namespace Matrix
open RecoveredConditionalDilationInternal
variable {dA dB dC : ℕ}
/-- Canonical finite enumeration of the ambient recovered sectors. -/
def recoveredAmbientHayashiSector
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) :
    AmbientRecoveredBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K :=
  finSumFinEquiv.symm j
/-- The HJPW left-factor dimension in the canonical ambient enumeration. -/
def recoveredAmbientHayashiLeftDim
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) : ℕ :=
  ambientRecoveredConditionalDim F.jointSupport.d
    (recoveredAmbientHayashiSector F j)
/-- The HJPW right-factor dimension in the canonical ambient enumeration. -/
def recoveredAmbientHayashiRightDim
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) : ℕ :=
  ambientRecoveredCommonDim F.jointSupport.m
    (recoveredAmbientHayashiSector F j)
/-- The ambient middle-system decomposition in HJPW order before enumerating
its sectors by a single finite type. -/
def recoveredAmbientHJPWMiddleEquiv
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) :
    Fin dB ≃
      ((s : AmbientRecoveredBlockIndex
        (dB - F.jointSupport.n) F.jointSupport.K) ×
        (Fin (ambientRecoveredConditionalDim F.jointSupport.d s) ×
          Fin (ambientRecoveredCommonDim F.jointSupport.m s))) :=
  let eSwap :=
    Equiv.sigmaCongrRight fun s :
        AmbientRecoveredBlockIndex
          (dB - F.jointSupport.n) F.jointSupport.K ↦
      Equiv.prodComm
        (Fin (ambientRecoveredCommonDim F.jointSupport.m s))
        (Fin (ambientRecoveredConditionalDim F.jointSupport.d s))
  (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e).symm
    |>.trans eSwap
/-- The recovered `b_j^R ⊗ b_j^L` coordinates become
`b_j^L ⊗ b_j^R` coordinates by swapping the two fibre entries. -/
@[simp]
theorem recoveredAmbientHJPWMiddleEquiv_apply_coordinate
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (s : AmbientRecoveredBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K)
    (r : Fin (ambientRecoveredCommonDim F.jointSupport.m s))
    (l : Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) :
    recoveredAmbientHJPWMiddleEquiv F
        (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
          ⟨s, (r, l)⟩) =
      ⟨s, (l, r)⟩ := by
  simp [recoveredAmbientHJPWMiddleEquiv]
/-- The ambient middle-system decomposition in HJPW order
`b_j^L ⊗ b_j^R`, with the sectors canonically enumerated by `Fin`.
The recovered bipartite witness stores each fibre in the reverse order
`b_j^R ⊗ b_j^L`; `recoveredAmbientHJPWMiddleEquiv` performs the explicit
factor swap before this equivalence enumerates the sectors.
Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (13)--(15),
lines 493--502 and 547--570. -/
def recoveredAmbientHayashiMiddleEquiv
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) :
    Fin dB ≃
      ((j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) ×
        (Fin (recoveredAmbientHayashiLeftDim F j) ×
          Fin (recoveredAmbientHayashiRightDim F j))) :=
  (recoveredAmbientHJPWMiddleEquiv F).trans
    (Equiv.sigmaCongrLeft' finSumFinEquiv)
/-- The enumerated HJPW equivalence sends a recovered coordinate to its swapped fibre. -/
@[simp]
theorem recoveredAmbientHayashiMiddleEquiv_apply_coordinate
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (q : Fin ((dB - F.jointSupport.n) + F.jointSupport.K))
    (r : Fin (recoveredAmbientHayashiRightDim F q))
    (l : Fin (recoveredAmbientHayashiLeftDim F q)) :
    recoveredAmbientHayashiMiddleEquiv F
      (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
        ⟨recoveredAmbientHayashiSector F q, (r, l)⟩) =
      ⟨q, (l, r)⟩ := by
  rw [recoveredAmbientHayashiMiddleEquiv, Equiv.trans_apply]
  rw [recoveredAmbientHJPWMiddleEquiv_apply_coordinate]
  let eSector :
      ((s : AmbientRecoveredBlockIndex
          (dB - F.jointSupport.n) F.jointSupport.K) ×
        (Fin (ambientRecoveredConditionalDim F.jointSupport.d s) ×
          Fin (ambientRecoveredCommonDim F.jointSupport.m s))) ≃
      ((j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) ×
        (Fin (recoveredAmbientHayashiLeftDim F j) ×
          Fin (recoveredAmbientHayashiRightDim F j))) :=
    Equiv.sigmaCongrLeft' finSumFinEquiv
  exact eSector.apply_symm_apply ⟨q, (l, r)⟩
/-- The middle-system unitary with the orientation used by the Hayashi
coordinate equation.
The ambient recovered witness records the coordinate-to-physical unitary
`U_B`. Therefore the physical-to-coordinate unitary in
`U ρ Uᴴ` is `U_Bᴴ`.
Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, equations (13)--(15),
lines 493--502 and 547--570. -/
def recoveredAmbientHayashiUnitary
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm) :
    Matrix.unitaryGroup (Fin dB) ℂ :=
  ⟨star F.U_B, by
    rw [Matrix.mem_unitaryGroup_iff]
    simpa only [star_star] using
      Matrix.mem_unitaryGroup_iff'.mp F.U_B_unitary⟩
private def
    RecoveredConditionalDilationBlockForm.ambientRecoveredKraus
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (i : Fin D.r)
    (s : AmbientRecoveredBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K) :
    Matrix
      (Fin (ambientRecoveredCommonDim F.jointSupport.m s) × Fin dC)
      (Fin (ambientRecoveredCommonDim F.jointSupport.m s)) ℂ :=
  match s with
  | Sum.inl _ => 0
  | Sum.inr j => D.L i j
private noncomputable def
    RecoveredConditionalDilationBlockForm.ambientRecoveredBlockKraus
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (i : Fin D.r) :
    Matrix (Fin dB × Fin dC) (Fin dB) ℂ :=
  let eB := recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
  Matrix.reindex (dilationBlockEquiv (E := Fin dC) eB) eB
    (Matrix.blockDiagonal' fun s ↦
      D.ambientRecoveredKraus i s ⊗ₖ
        (1 : Matrix
          (Fin (ambientRecoveredConditionalDim F.jointSupport.d s))
          (Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) ℂ))
private theorem
    RecoveredConditionalDilationBlockForm.blockCoordinateDilation_isometry
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F) :
    pureAncillaDilationIsometry D.c₀ D.k₀ D.U_BCE_blocks *
        ambientSupportEmbedding F.e₀ =
      stinespringV D.ambientRecoveredBlockKraus *
        ambientSupportEmbedding F.e₀ := by
  classical
  let C : Fin (dC * D.r) → ∀ j : Fin F.jointSupport.K,
      Matrix (Fin (F.jointSupport.m j))
        (Fin (F.jointSupport.m j)) ℂ :=
    fun k j ↦ rightOutputSlice
      (D.L (finProdFinEquiv.symm k).2 j)
      (finProdFinEquiv.symm k).1
  have hL : ∀ i j u c u', D.L i j (u, c) u' =
      C (finProdFinEquiv (c, i)) j u u' := by
    intro i j u c u'
    change D.L i j (u, c) u' =
      rightOutputSlice
        (D.L (finProdFinEquiv.symm (finProdFinEquiv (c, i))).2 j)
        (finProdFinEquiv.symm (finProdFinEquiv (c, i))).1 u u'
    rw [Equiv.symm_apply_apply]
    rfl
  have hslices :=
    blockDilation_slice_support F.e₀ F.jointSupport.e
      D.c₀ D.k₀ C D.L hL D.Ulocal D.sector_pure_ancilla_extension
  have hK : ∀ c i,
      rightOutputSlice (D.ambientRecoveredBlockKraus i) c *
          ambientSupportEmbedding F.e₀ =
        ambientSupportEmbedding F.e₀ *
          Matrix.reindex F.jointSupport.e F.jointSupport.e
            (Matrix.blockDiagonal' fun j ↦
              C (finProdFinEquiv (c, i)) j ⊗ₖ
                (1 : Matrix (Fin (F.jointSupport.d j))
                  (Fin (F.jointSupport.d j)) ℂ)) := by
    intro c i
    ext b x
    rw [← (recoveredAmbientMiddleBlockEquiv
      F.e₀ F.jointSupport.e).apply_symm_apply b,
      ← F.jointSupport.e.apply_symm_apply x]
    generalize (recoveredAmbientMiddleBlockEquiv
      F.e₀ F.jointSupport.e).symm b = sb
    generalize F.jointSupport.e.symm x = sx
    rcases sb with ⟨s, u, v⟩
    rcases sx with ⟨j, u', v'⟩
    rcases s with z | j'
    · change Fin 1 at u v
      have hu : u = (0 : Fin 1) := Subsingleton.elim _ _
      have hv : v = (0 : Fin 1) := Subsingleton.elim _ _
      subst u
      subst v
      have hrow :
          recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
              ⟨Sum.inl z, ((0 : Fin 1), (0 : Fin 1))⟩ =
            F.e₀ (Sum.inl z) := by rfl
      rw [hrow]
      rw [mul_ambientSupportEmbedding_apply,
        ambientSupportEmbedding_mul_apply_complement]
      have hcol :
          (recoveredAmbientMiddleBlockEquiv
            F.e₀ F.jointSupport.e).symm
              (F.e₀ (Sum.inr
                (F.jointSupport.e ⟨j, (u', v')⟩))) =
            ⟨Sum.inr j, (u', v')⟩ := by
        rw [← show recoveredAmbientMiddleBlockEquiv
          F.e₀ F.jointSupport.e ⟨Sum.inr j, (u', v')⟩ =
            F.e₀ (Sum.inr
              (F.jointSupport.e ⟨j, (u', v')⟩)) by rfl]
        exact Equiv.symm_apply_apply _ _
      have hout :
          (dilationBlockEquiv
            (recoveredAmbientMiddleBlockEquiv
              F.e₀ F.jointSupport.e)).symm
              (F.e₀ (Sum.inl z), c) =
            ⟨Sum.inl z, (((0 : Fin 1), c), (0 : Fin 1))⟩ := by
        rw [← show dilationBlockEquiv
          (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e)
            ⟨Sum.inl z, (((0 : Fin 1), c), (0 : Fin 1))⟩ =
              (F.e₀ (Sum.inl z), c) by rfl]
        exact Equiv.symm_apply_apply _ _
      simp [ambientRecoveredBlockKraus, ambientRecoveredKraus,
        rightOutputSlice,
        Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.blockDiagonal'_apply, hcol, hout]
    · by_cases hj : j' = j
      · subst j'
        have hrow :
            recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
                ⟨Sum.inr j, (u, v)⟩ =
              F.e₀ (Sum.inr (F.jointSupport.e ⟨j, (u, v)⟩)) := by
          rfl
        rw [hrow]
        rw [mul_ambientSupportEmbedding_apply,
          ambientSupportEmbedding_mul_apply_support]
        have hcol :
            (recoveredAmbientMiddleBlockEquiv
              F.e₀ F.jointSupport.e).symm
                (F.e₀ (Sum.inr
                  (F.jointSupport.e ⟨j, (u', v')⟩))) =
              ⟨Sum.inr j, (u', v')⟩ := by
          rw [← show recoveredAmbientMiddleBlockEquiv
            F.e₀ F.jointSupport.e ⟨Sum.inr j, (u', v')⟩ =
              F.e₀ (Sum.inr
                (F.jointSupport.e ⟨j, (u', v')⟩)) by rfl]
          exact Equiv.symm_apply_apply _ _
        have hout :
            (dilationBlockEquiv
              (recoveredAmbientMiddleBlockEquiv
                F.e₀ F.jointSupport.e)).symm
                (F.e₀ (Sum.inr
                  (F.jointSupport.e ⟨j, (u, v)⟩)), c) =
              ⟨Sum.inr j, ((u, c), v)⟩ := by
          rw [← show dilationBlockEquiv
            (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e)
              ⟨Sum.inr j, ((u, c), v)⟩ =
                (F.e₀ (Sum.inr
                  (F.jointSupport.e ⟨j, (u, v)⟩)), c) by rfl]
          exact Equiv.symm_apply_apply _ _
        simp [ambientRecoveredBlockKraus, ambientRecoveredKraus,
          rightOutputSlice, Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply, C, hcol, hout]
        have hp :
            finProdFinEquiv.symm (finProdFinEquiv (c, i)) = (c, i) :=
          Equiv.symm_apply_apply _ _
        have hc :
            (finProdFinEquiv (c, i)).divNat = c :=
          congrArg Prod.fst hp
        have hi :
            (finProdFinEquiv (c, i)).modNat = i :=
          congrArg Prod.snd hp
        rw [hc, hi]
        rfl
      · have hrow :
            recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
                ⟨Sum.inr j', (u, v)⟩ =
              F.e₀ (Sum.inr (F.jointSupport.e ⟨j', (u, v)⟩)) := by
          rfl
        rw [hrow]
        rw [mul_ambientSupportEmbedding_apply,
          ambientSupportEmbedding_mul_apply_support]
        have hcol :
            (recoveredAmbientMiddleBlockEquiv
              F.e₀ F.jointSupport.e).symm
                (F.e₀ (Sum.inr
                  (F.jointSupport.e ⟨j, (u', v')⟩))) =
              ⟨Sum.inr j, (u', v')⟩ := by
          rw [← show recoveredAmbientMiddleBlockEquiv
            F.e₀ F.jointSupport.e ⟨Sum.inr j, (u', v')⟩ =
              F.e₀ (Sum.inr
                (F.jointSupport.e ⟨j, (u', v')⟩)) by rfl]
          exact Equiv.symm_apply_apply _ _
        have hout :
            (dilationBlockEquiv
              (recoveredAmbientMiddleBlockEquiv
                F.e₀ F.jointSupport.e)).symm
                (F.e₀ (Sum.inr
                  (F.jointSupport.e ⟨j', (u, v)⟩)), c) =
              ⟨Sum.inr j', ((u, c), v)⟩ := by
          rw [← show dilationBlockEquiv
            (recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e)
              ⟨Sum.inr j', ((u, c), v)⟩ =
                (F.e₀ (Sum.inr
                  (F.jointSupport.e ⟨j', (u, v)⟩)), c) by rfl]
          exact Equiv.symm_apply_apply _ _
        simp [ambientRecoveredBlockKraus, ambientRecoveredKraus,
          rightOutputSlice,
          Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.blockDiagonal'_apply, hj, hcol, hout]
  rw [D.block_coordinate_unitary_eq]
  ext ⟨⟨b, c⟩, i⟩ x
  change
    rightOutputSlice
        ((Matrix.reindex
              (dilationBlockEquiv
                (recoveredAmbientMiddleBlockEquiv
                  F.e₀ F.jointSupport.e))
              (dilationBlockEquiv
                (recoveredAmbientMiddleBlockEquiv
                  F.e₀ F.jointSupport.e))
              (Matrix.blockDiagonal' fun s ↦
                D.Ulocal s ⊗ₖ
                  (1 : Matrix
                    (Fin (ambientRecoveredConditionalDim
                      F.jointSupport.d s))
                    (Fin (ambientRecoveredConditionalDim
                      F.jointSupport.d s)) ℂ)) *
            fixedEnvEmbedding (S := Fin dB) (D.c₀, D.k₀)) *
          ambientSupportEmbedding F.e₀)
        (c, i) b x =
      (rightOutputSlice (D.ambientRecoveredBlockKraus i) c *
        ambientSupportEmbedding F.e₀) b x
  have hentry := congrFun (congrFun (hslices c i) b) x
  have hKentry := congrFun (congrFun (hK c i) b) x
  exact hentry.trans hKentry.symm
private def ambientRecoveredConditionalBlock
    {n K : ℕ} (d : Fin K → ℕ)
    (B : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (s : AmbientRecoveredBlockIndex n K) :
    Matrix (Fin (ambientRecoveredConditionalDim d s))
      (Fin (ambientRecoveredConditionalDim d s)) ℂ :=
  match s with
  | Sum.inl _ => 0
  | Sum.inr j => B j
private theorem ambientRecoveredConditionalBlock_bipartiteBlock_apply
    {n K dA : ℕ} {d : Fin K → ℕ}
    (ω : ∀ j, Matrix (Fin dA × Fin (d j))
      (Fin dA × Fin (d j)) ℂ)
    (a a' : Fin dA)
    (s : AmbientRecoveredBlockIndex n K)
    (l l' : Fin (ambientRecoveredConditionalDim d s)) :
    ambientRecoveredConditionalBlock d
        (fun j ↦ bipartiteBlock (ω j) a a') s l l' =
      ambientRecoveredConditionalState ω s (a, l) (a', l') := by
  cases s <;> rfl
private theorem ambientRecoveredBlockState_eq_supportSandwich
    {n K : ℕ} {m d : Fin K → ℕ}
    (e₀ : (Fin (dB - n) ⊕ Fin n) ≃ Fin dB)
    (e : ((j : Fin K) × (Fin (m j) × Fin (d j))) ≃ Fin n)
    (σ : ∀ j, Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (B : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    let eB := recoveredAmbientMiddleBlockEquiv e₀ e
    Matrix.reindex eB eB
        (Matrix.blockDiagonal' fun s ↦
          ambientRecoveredCommonState σ s ⊗ₖ
            ambientRecoveredConditionalBlock d B s) =
      ambientSupportEmbedding e₀ *
        Matrix.reindex e e
          (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ B j) *
        (ambientSupportEmbedding e₀)ᴴ := by
  classical
  dsimp only
  let eB := recoveredAmbientMiddleBlockEquiv e₀ e
  let X := Matrix.reindex e e
    (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ B j)
  have hJ :
      ambientSupportEmbedding e₀ * X * (ambientSupportEmbedding e₀)ᴴ =
        Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 X) := by
    ext b b'
    rw [← e₀.apply_symm_apply b, ← e₀.apply_symm_apply b']
    generalize e₀.symm b = sb
    generalize e₀.symm b' = tb
    rcases sb with z | s <;> rcases tb with z' | t <;>
      simp [X, ambientSupportEmbedding, Matrix.mul_apply,
        Matrix.one_apply]
  have heBcomp (z : Fin (dB - n)) :
      eB.symm (e₀ (Sum.inl z)) =
        ⟨Sum.inl z, ((0 : Fin 1), (0 : Fin 1))⟩ := by
    rw [← show eB ⟨Sum.inl z, ((0 : Fin 1), (0 : Fin 1))⟩ =
      e₀ (Sum.inl z) by rfl]
    exact Equiv.symm_apply_apply _ _
  have heBsupp (j : Fin K) (u : Fin (m j)) (v : Fin (d j)) :
      eB.symm (e₀ (Sum.inr (e ⟨j, (u, v)⟩))) =
        ⟨Sum.inr j, (u, v)⟩ := by
    rw [← show eB ⟨Sum.inr j, (u, v)⟩ =
      e₀ (Sum.inr (e ⟨j, (u, v)⟩)) by rfl]
    exact Equiv.symm_apply_apply _ _
  have hambient :
      Matrix.reindex eB eB
          (Matrix.blockDiagonal' fun s ↦
            ambientRecoveredCommonState σ s ⊗ₖ
              ambientRecoveredConditionalBlock d B s) =
        Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 X) := by
    ext x y
    rw [← eB.apply_symm_apply x, ← eB.apply_symm_apply y]
    generalize eB.symm x = sx
    generalize eB.symm y = sy
    rcases sx with ⟨s, u, v⟩
    rcases sy with ⟨t, u', v'⟩
    rcases s with z | j <;> rcases t with z' | j'
    · change Fin 1 at u v u' v'
      fin_cases u
      fin_cases v
      fin_cases u'
      fin_cases v'
      simp [eB, X, ambientRecoveredCommonState,
        ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
        heBcomp]
    · change Fin 1 at u v
      fin_cases u
      fin_cases v
      simp [eB, X, ambientRecoveredCommonState,
        ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
        heBcomp, heBsupp]
    · change Fin 1 at u' v'
      fin_cases u'
      fin_cases v'
      simp [eB, X, ambientRecoveredCommonState,
        ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
        heBcomp, heBsupp]
    · by_cases hj : j = j'
      · subst j'
        simp [eB, X, ambientRecoveredCommonState,
          ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
          heBsupp]
      · simp [eB, X, ambientRecoveredCommonState,
          ambientRecoveredConditionalBlock,
          Matrix.blockDiagonal'_apply, hj, heBsupp]
  exact hambient.trans hJ.symm
/-- The recovered output factor on an ambient sector.

Supported sectors carry the recovered `b_j^R C` state. Complementary sectors
carry the zero operator; no normalized filler is chosen here.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570. -/
noncomputable def
    RecoveredConditionalDilationBlockForm.ambientRecoveredOutputFactor
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F) :
    (s : AmbientRecoveredBlockIndex
      (dB - F.jointSupport.n) F.jointSupport.K) →
      Matrix
        (Fin (ambientRecoveredCommonDim F.jointSupport.m s) × Fin dC)
        (Fin (ambientRecoveredCommonDim F.jointSupport.m s) × Fin dC) ℂ
  | Sum.inl _ => 0
  | Sum.inr j => D.recoveredSectorState j

private theorem
    RecoveredConditionalDilationBlockForm.blockCoordinateRecovery
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F)
    (B : ∀ j, Matrix (Fin (F.jointSupport.d j))
      (Fin (F.jointSupport.d j)) ℂ) :
    let eB := recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
    let eOut := dilationBlockEquiv (E := Fin dC) eB
    pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
        (Matrix.reindex eB eB
          (Matrix.blockDiagonal' fun s ↦
            ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
              ambientRecoveredConditionalBlock F.jointSupport.d B s)) =
      Matrix.reindex eOut eOut
        (Matrix.blockDiagonal' fun s ↦
          D.ambientRecoveredOutputFactor s ⊗ₖ
            ambientRecoveredConditionalBlock F.jointSupport.d B s) := by
  classical
  dsimp only
  let eB := recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
  let eOut := dilationBlockEquiv (E := Fin dC) eB
  let J := ambientSupportEmbedding F.e₀
  let X := Matrix.reindex F.jointSupport.e F.jointSupport.e
    (Matrix.blockDiagonal' fun j ↦ F.jointSupport.σ j ⊗ₖ B j)
  let K₀ := fun i : Fin D.r ↦ Matrix.blockDiagonal' fun s ↦
    D.ambientRecoveredKraus i s ⊗ₖ
      (1 : Matrix
        (Fin (ambientRecoveredConditionalDim F.jointSupport.d s))
        (Fin (ambientRecoveredConditionalDim F.jointSupport.d s)) ℂ)
  have hsupport :=
    ambientRecoveredBlockState_eq_supportSandwich
      F.e₀ F.jointSupport.e F.jointSupport.σ B
  have hmap :=
    pureAncillaRecovery_eq_rectangularKrausMap_on_support
      D.c₀ D.k₀ D.U_BCE_blocks D.ambientRecoveredBlockKraus J
      D.blockCoordinateDilation_isometry X
  change
    pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
        (Matrix.reindex eB eB
          (Matrix.blockDiagonal' fun s ↦
            ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
              ambientRecoveredConditionalBlock F.jointSupport.d B s)) =
      Matrix.reindex eOut eOut
        (Matrix.blockDiagonal' fun s ↦
          D.ambientRecoveredOutputFactor s ⊗ₖ
            ambientRecoveredConditionalBlock F.jointSupport.d B s)
  have hrec :
      pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
          (Matrix.reindex eB eB
            (Matrix.blockDiagonal' fun s ↦
              ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
                ambientRecoveredConditionalBlock F.jointSupport.d B s)) =
        rectangularKrausMap D.ambientRecoveredBlockKraus
          (Matrix.reindex eB eB
            (Matrix.blockDiagonal' fun s ↦
              ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
                ambientRecoveredConditionalBlock F.jointSupport.d B s)) := by
    simpa only [eB, J, X, hsupport] using hmap
  rw [hrec]
  change
    rectangularKrausMap
        (fun i ↦ Matrix.reindex eOut eB (K₀ i))
        (Matrix.reindex eB eB
          (Matrix.blockDiagonal' fun s ↦
            ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
              ambientRecoveredConditionalBlock F.jointSupport.d B s)) =
      _
  rw [rectangularKrausMap_reindex]
  rw [rectangularKrausMap_blockDiagonal_kronecker_one]
  congr 2
  funext s
  rcases s with z | j
  · simp [ambientRecoveredKraus, ambientRecoveredOutputFactor,
      ambientRecoveredConditionalBlock, ambientRecoveredCommonState,
      rectangularKrausMap]
  · simp [ambientRecoveredKraus, ambientRecoveredOutputFactor,
      ambientRecoveredConditionalBlock, ambientRecoveredCommonState,
      RecoveredConditionalDilationBlockForm.recoveredSectorState]
    rfl
/-- The unnormalized tripartite direct sum in HJPW factor order.

On a supported sector the block is
`ω_j ⊗ D.recoveredSectorState j`, where `ω_j` is the unnormalized
`A b_j^L` factor. Complementary blocks are zero.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570;
arXiv:1606.00608, Appendix C.2, Lemma `Lsigma3`, equation `eq:sigma3`. -/
noncomputable def
    RecoveredConditionalDilationBlockForm.ambientTripartiteBlockState
    {ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ}
    {hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1}
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    {F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm}
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F) :
    Matrix
      (Fin dA ×
        (((j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) ×
            (Fin (recoveredAmbientHayashiLeftDim F j) ×
              Fin (recoveredAmbientHayashiRightDim F j))) ×
          Fin dC))
      (Fin dA ×
        (((j : Fin ((dB - F.jointSupport.n) + F.jointSupport.K)) ×
            (Fin (recoveredAmbientHayashiLeftDim F j) ×
              Fin (recoveredAmbientHayashiRightDim F j))) ×
          Fin dC)) ℂ :=
  Matrix.reindex
    (HayashiMarkov.sigmaAssoc
      (dA := dA) (dC := dC)
      (recoveredAmbientHayashiLeftDim F)
      (recoveredAmbientHayashiRightDim F))
    (HayashiMarkov.sigmaAssoc
      (dA := dA) (dC := dC)
      (recoveredAmbientHayashiLeftDim F)
      (recoveredAmbientHayashiRightDim F))
    (Matrix.blockDiagonal' fun j ↦
      ambientRecoveredConditionalState F.jointSupport.ω
          (recoveredAmbientHayashiSector F j) ⊗ₖ
        D.ambientRecoveredOutputFactor
          (recoveredAmbientHayashiSector F j))

/-- The final HJPW substitution for fixed ambient and dilation witnesses.

After conjugating by `U_Bᴴ` and explicitly swapping each middle-system fibre
from the recovered `b_j^R ⊗ b_j^L` order to HJPW's
`b_j^L ⊗ b_j^R` order, the tripartite state is the direct sum
`⊕_j ω_j ⊗ η_j`. Complementary blocks are zero.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570;
arXiv:1606.00608, Appendix C.2, Lemma `Lsigma3`, equation `eq:sigma3`. -/
structure RecoveredConditionalTripartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F) : Type where
  /-- The transformed state equals the raw HJPW direct sum in ambient coordinates. -/
  tripartite_block_form :
    Matrix.reindex
        (HayashiMarkov.abcEquiv
          (dA := dA) (dB := dB) (dC := dC)
          (recoveredAmbientHayashiMiddleEquiv F))
        (HayashiMarkov.abcEquiv
          (dA := dA) (dB := dB) (dC := dC)
          (recoveredAmbientHayashiMiddleEquiv F))
        (HayashiMarkov.liftB
            (dA := dA) (dB := dB) (dC := dC)
            (recoveredAmbientHayashiUnitary F : Matrix (Fin dB) (Fin dB) ℂ) *
          ρ_ABC *
          (HayashiMarkov.liftB
            (dA := dA) (dB := dB) (dC := dC)
            (recoveredAmbientHayashiUnitary F :
              Matrix (Fin dB) (Fin dB) ℂ))ᴴ) =
      D.ambientTripartiteBlockState
/-- Fixed ambient and dilation witnesses determine the exact tripartite
direct-sum transport in HJPW coordinates.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570. -/
theorem exists_recoveredConditionalTripartiteBlockForm_of_dilationBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    [Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC))]
    (F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm)
    (D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F) :
    Nonempty (RecoveredConditionalTripartiteBlockForm ρ_ABC hρ_dm F D) := by
  classical
  let T_B : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ]
      Matrix (Fin dB) (Fin dB) ℂ :=
    { toFun := fun X ↦ star F.U_B * X * F.U_B
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp }
  let T_BC : Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ →ₗ[ℂ]
      Matrix (Fin dB × Fin dC) (Fin dB × Fin dC) ℂ :=
    { toFun := fun X ↦
        star (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ)) * X *
          (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp }
  let Rblocks :=
    pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
  let Rphysical :=
    pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_physical
  have hcov : Rblocks.comp T_B = T_BC.comp Rphysical := by
    apply LinearMap.ext
    intro X
    change
      pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_blocks
          (star F.U_B * X * F.U_B) =
        star (F.U_B ⊗ₖ
            (1 : Matrix (Fin dC) (Fin dC) ℂ)) *
          pureAncillaRecovery D.c₀ D.k₀ D.U_BCE_physical X *
          (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))
    exact
      pureAncillaRecovery_inverse_coordinate D.c₀ D.k₀
        F.U_B F.U_B_unitary D.U_BCE_physical D.U_BCE_blocks
        D.inverse_coordinate_eq X
  let ρ_AB := traceC_ABC ρ_ABC
  let eB := recoveredAmbientMiddleBlockEquiv F.e₀ F.jointSupport.e
  let ρ_AB_blocks :=
    Matrix.reindex (recoveredBipartiteBlockEquiv eB)
      (recoveredBipartiteBlockEquiv eB)
      (Matrix.blockDiagonal' fun s ↦
        ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
          ambientRecoveredConditionalState F.jointSupport.ω s)
  have hAB :
      idTensorMapLM (δ := Fin dA) T_B ρ_AB = ρ_AB_blocks := by
    have hconj := idTensorMap_conjugation (star F.U_B) ρ_AB
    have hUB :
        (star F.U_B)ᴴ = F.U_B := by
      simp only [star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    rw [hUB] at hconj
    calc
      idTensorMapLM (δ := Fin dA) T_B ρ_AB =
          star ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) *
            ρ_AB *
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ F.U_B) := by
              simpa only [T_B, Matrix.conjTranspose_kronecker,
                Matrix.conjTranspose_one, star_eq_conjTranspose,
                Matrix.conjTranspose_conjTranspose] using hconj
      _ = ρ_AB_blocks := by
        simpa only [ρ_AB, ρ_AB_blocks, eB,
          Matrix.star_eq_conjTranspose] using F.ambient_bipartite_block_form
  have hcoordinate :
      HayashiMarkov.liftB
            (dA := dA) (dB := dB) (dC := dC) (star F.U_B) *
          ρ_ABC *
          (HayashiMarkov.liftB
            (dA := dA) (dB := dB) (dC := dC) (star F.U_B))ᴴ =
        idTensorMapLM (δ := Fin dA) Rblocks ρ_AB_blocks := by
    have hconj := idTensorMap_conjugation
      (star (F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ))) ρ_ABC
    have hUBC :
        (star (F.U_B ⊗ₖ
          (1 : Matrix (Fin dC) (Fin dC) ℂ)))ᴴ =
            F.U_B ⊗ₖ (1 : Matrix (Fin dC) (Fin dC) ℂ) := by
      simp only [star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    rw [hUBC] at hconj
    calc
      HayashiMarkov.liftB (star F.U_B) * ρ_ABC *
          (HayashiMarkov.liftB (star F.U_B))ᴴ =
        idTensorMapLM (δ := Fin dA) T_BC ρ_ABC := by
          simpa only [T_BC, HayashiMarkov.liftB,
            Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
            star_eq_conjTranspose] using hconj.symm
      _ = idTensorMapLM (δ := Fin dA) T_BC
          (idTensorMapLM (δ := Fin dA) Rphysical ρ_AB) := by
            rw [D.recovery_eq11]
      _ = idTensorMapLM (δ := Fin dA) (T_BC.comp Rphysical) ρ_AB := by
            rw [idTensorMapLM_comp, LinearMap.comp_apply]
      _ = idTensorMapLM (δ := Fin dA) (Rblocks.comp T_B) ρ_AB := by
            rw [hcov]
      _ = idTensorMapLM (δ := Fin dA) Rblocks
          (idTensorMapLM (δ := Fin dA) T_B ρ_AB) := by
            rw [idTensorMapLM_comp, LinearMap.comp_apply]
      _ = idTensorMapLM (δ := Fin dA) Rblocks ρ_AB_blocks := by
            rw [hAB]
  refine ⟨{ tripartite_block_form := ?_ }⟩
  rw [show recoveredAmbientHayashiUnitary F =
      (⟨star F.U_B, by
        rw [Matrix.mem_unitaryGroup_iff]
        simpa only [star_star] using
          Matrix.mem_unitaryGroup_iff'.mp F.U_B_unitary⟩ :
        Matrix.unitaryGroup (Fin dB) ℂ) by rfl]
  change Matrix.reindex _ _
      (HayashiMarkov.liftB (star F.U_B) * ρ_ABC *
        (HayashiMarkov.liftB (star F.U_B))ᴴ) =
    D.ambientTripartiteBlockState
  rw [hcoordinate]
  let Bblock (a a' : Fin dA) (j : Fin F.jointSupport.K) :=
    bipartiteBlock (F.jointSupport.ω j) a a'
  have heBcomp (z : Fin (dB - F.jointSupport.n)) :
      eB.symm (F.e₀ (Sum.inl z)) =
        ⟨Sum.inl z, ((0 : Fin 1), (0 : Fin 1))⟩ := by
    rw [← show eB ⟨Sum.inl z, ((0 : Fin 1), (0 : Fin 1))⟩ =
      F.e₀ (Sum.inl z) by rfl]
    exact Equiv.symm_apply_apply _ _
  have heBsupp (j : Fin F.jointSupport.K)
      (u : Fin (F.jointSupport.m j))
      (v : Fin (F.jointSupport.d j)) :
      eB.symm (F.e₀ (Sum.inr
        (F.jointSupport.e ⟨j, (u, v)⟩))) =
        ⟨Sum.inr j, (u, v)⟩ := by
    rw [← show eB ⟨Sum.inr j, (u, v)⟩ =
      F.e₀ (Sum.inr
        (F.jointSupport.e ⟨j, (u, v)⟩)) by rfl]
    exact Equiv.symm_apply_apply _ _
  have hbipartite (a a' : Fin dA) :
      bipartiteBlock ρ_AB_blocks a a' =
        Matrix.reindex eB eB
          (Matrix.blockDiagonal' fun s ↦
            ambientRecoveredCommonState F.jointSupport.σ s ⊗ₖ
              ambientRecoveredConditionalBlock F.jointSupport.d
                (Bblock a a') s) := by
    ext b b'
    rw [← eB.apply_symm_apply b, ← eB.apply_symm_apply b']
    generalize eB.symm b = sb
    generalize eB.symm b' = tb
    rcases sb with ⟨s, u, v⟩
    rcases tb with ⟨t, u', v'⟩
    rcases s with z | j <;> rcases t with z' | j'
    · change Fin 1 at u v u' v'
      fin_cases u
      fin_cases v
      fin_cases u'
      fin_cases v'
      simp [ρ_AB_blocks, eB, Bblock, bipartiteBlock_apply,
        ambientRecoveredCommonState, ambientRecoveredConditionalState,
        ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
        heBcomp]
    · change Fin 1 at u v
      fin_cases u
      fin_cases v
      simp [ρ_AB_blocks, eB, Bblock, bipartiteBlock_apply,
        ambientRecoveredCommonState, ambientRecoveredConditionalState,
        ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
        heBcomp, heBsupp]
    · change Fin 1 at u' v'
      fin_cases u'
      fin_cases v'
      simp [ρ_AB_blocks, eB, Bblock, bipartiteBlock_apply,
        ambientRecoveredCommonState, ambientRecoveredConditionalState,
        ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
        heBcomp, heBsupp]
    · by_cases hj : j = j'
      · subst j'
        simp [ρ_AB_blocks, eB, Bblock, bipartiteBlock_apply,
          ambientRecoveredCommonState, ambientRecoveredConditionalState,
          ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
          heBsupp]
        exact Or.inl rfl
      · simp [ρ_AB_blocks, eB, Bblock, bipartiteBlock_apply,
          ambientRecoveredCommonState, ambientRecoveredConditionalState,
          ambientRecoveredConditionalBlock, Matrix.blockDiagonal'_apply,
          hj, heBsupp]
  ext ⟨a, ⟨⟨q, ⟨l, r⟩⟩, c⟩⟩
      ⟨a', ⟨⟨q', ⟨l', r'⟩⟩, c'⟩⟩
  let s := recoveredAmbientHayashiSector F q
  let s' := recoveredAmbientHayashiSector F q'
  have hmid :
      recoveredAmbientHayashiMiddleEquiv F (eB ⟨s, (r, l)⟩) =
        ⟨q, (l, r)⟩ := by
    dsimp only [s, eB]
    exact recoveredAmbientHayashiMiddleEquiv_apply_coordinate F q r l
  have hmid' :
      recoveredAmbientHayashiMiddleEquiv F (eB ⟨s', (r', l')⟩) =
        ⟨q', (l', r')⟩ := by
    dsimp only [s', eB]
    exact recoveredAmbientHayashiMiddleEquiv_apply_coordinate F q' r' l'
  have habc :
      (HayashiMarkov.abcEquiv
        (recoveredAmbientHayashiMiddleEquiv F)).symm
          (a, ⟨q, (l, r)⟩, c) =
        (a, eB ⟨s, (r, l)⟩, c) := by
    rw [← show HayashiMarkov.abcEquiv
      (recoveredAmbientHayashiMiddleEquiv F)
        (a, eB ⟨s, (r, l)⟩, c) =
          (a, ⟨q, (l, r)⟩, c) by
            simp [HayashiMarkov.abcEquiv, hmid]]
    exact Equiv.symm_apply_apply _ _
  have habc' :
      (HayashiMarkov.abcEquiv
        (recoveredAmbientHayashiMiddleEquiv F)).symm
          (a', ⟨q', (l', r')⟩, c') =
        (a', eB ⟨s', (r', l')⟩, c') := by
    rw [← show HayashiMarkov.abcEquiv
      (recoveredAmbientHayashiMiddleEquiv F)
        (a', eB ⟨s', (r', l')⟩, c') =
          (a', ⟨q', (l', r')⟩, c') by
            simp [HayashiMarkov.abcEquiv, hmid']]
    exact Equiv.symm_apply_apply _ _
  have hsigma :
      (HayashiMarkov.sigmaAssoc
        (dA := dA) (dC := dC)
        (recoveredAmbientHayashiLeftDim F)
        (recoveredAmbientHayashiRightDim F)).symm
          (a, ⟨q, (l, r)⟩, c) =
        ⟨q, ((a, l), (r, c))⟩ := by
    rw [← show HayashiMarkov.sigmaAssoc
      (dA := dA) (dC := dC)
      (recoveredAmbientHayashiLeftDim F)
      (recoveredAmbientHayashiRightDim F)
        ⟨q, ((a, l), (r, c))⟩ =
          (a, ⟨q, (l, r)⟩, c) by rfl]
    exact Equiv.symm_apply_apply _ _
  have hsigma' :
      (HayashiMarkov.sigmaAssoc
        (dA := dA) (dC := dC)
        (recoveredAmbientHayashiLeftDim F)
        (recoveredAmbientHayashiRightDim F)).symm
          (a', ⟨q', (l', r')⟩, c') =
        ⟨q', ((a', l'), (r', c'))⟩ := by
    rw [← show HayashiMarkov.sigmaAssoc
      (dA := dA) (dC := dC)
      (recoveredAmbientHayashiLeftDim F)
      (recoveredAmbientHayashiRightDim F)
        ⟨q', ((a', l'), (r', c'))⟩ =
          (a', ⟨q', (l', r')⟩, c') by rfl]
    exact Equiv.symm_apply_apply _ _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    idTensorMapLM_apply, idTensorMap_apply, habc, habc',
    RecoveredConditionalDilationBlockForm.ambientTripartiteBlockState,
    hsigma, hsigma']
  change
    Rblocks (bipartiteBlock ρ_AB_blocks a a')
        (eB ⟨s, (r, l)⟩, c)
        (eB ⟨s', (r', l')⟩, c') =
      Matrix.blockDiagonal' (fun q ↦
        ambientRecoveredConditionalState F.jointSupport.ω
            (recoveredAmbientHayashiSector F q) ⊗ₖ
          D.ambientRecoveredOutputFactor
            (recoveredAmbientHayashiSector F q))
        ⟨q, ((a, l), (r, c))⟩
        ⟨q', ((a', l'), (r', c'))⟩
  rw [hbipartite]
  have hrec := D.blockCoordinateRecovery (Bblock a a')
  have hentry := congrFun (congrFun hrec
    (dilationBlockEquiv eB ⟨s, ((r, c), l)⟩))
    (dilationBlockEquiv eB ⟨s', ((r', c'), l')⟩)
  dsimp only [eB, Rblocks] at hentry ⊢
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at hentry
  simp only [Equiv.symm_apply_apply] at hentry
  by_cases hq : q = q'
  · subst q'
    dsimp only [s, s'] at hentry ⊢
    convert hentry using 1 <;>
      simp [Matrix.reindex_apply, recoveredAmbientHayashiSector,
        Matrix.blockDiagonal'_apply, Matrix.kroneckerMap_apply]
    rw [ambientRecoveredConditionalBlock_bipartiteBlock_apply]
    exact mul_comm _ _
  · have hs : s ≠ s' := by
      intro hss
      apply hq
      exact finSumFinEquiv.symm.injective hss
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply,
      recoveredAmbientHayashiSector, s, s',
      Matrix.blockDiagonal'_apply, Matrix.kroneckerMap_apply,
      Bblock, bipartiteBlock_apply, hq, hs] using hentry

/-- At equality in strong subadditivity, the tripartite state has the raw
HJPW direct-sum form `⊕_j ω_j ⊗ η_j` in ambient middle-system coordinates.

This theorem introduces no probability normalization or density fillers.

Source: HJPW, arXiv:quant-ph/0304007v2, Theorem 6, lines 562--570;
arXiv:1606.00608, Appendix C.2, Lemma `Lsigma3`, equation `eq:sigma3`. -/
theorem exists_recoveredConditionalTripartiteBlockForm
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    letI : Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC)) :=
      recoveredEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
        rw [← trace_eq_trace_traceC_ABC]
        exact hρ_dm.2)
    Nonempty
      (Σ F : RecoveredConditionalAmbientBipartiteBlockForm ρ_ABC hρ_dm,
        Σ D : RecoveredConditionalDilationBlockForm ρ_ABC hρ_dm F,
          RecoveredConditionalTripartiteBlockForm ρ_ABC hρ_dm F D) := by
  classical
  letI : Nonempty (RecoveredEffectIndex (traceC_ABC ρ_ABC)) :=
    recoveredEffectIndex_nonempty (traceC_ABC ρ_ABC) (by
      rw [← trace_eq_trace_traceC_ABC]
      exact hρ_dm.2)
  obtain ⟨⟨F, D⟩⟩ :=
    exists_recoveredDilationBlockUnitary ρ_ABC hρ_dm hSSA
  obtain ⟨T⟩ :=
    exists_recoveredConditionalTripartiteBlockForm_of_dilationBlockForm
      ρ_ABC hρ_dm F D
  exact ⟨⟨F, D, T⟩⟩

end Matrix
