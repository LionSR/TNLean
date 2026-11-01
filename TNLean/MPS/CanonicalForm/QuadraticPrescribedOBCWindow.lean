/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.QuadraticPerronNormalization
import TNLean.MPS.Preparation.OBCMinimalPrefixBasis

/-!
# A quadratic solution over the prescribed OBC representation

The prescribed OBC tensor represents the actual periodic state and has
bonds bounded by the source's squared virtual dimension. Condition C1
forces equality at every cut of the reconstruction window. Its original
physical prefix columns are consequently actual physical cut bases, and
physical slicing gives its original site matrices. The basis-independent
window construction therefore supplies a quadratic solution over this
prescribed window, without selecting a different representation.

Canonicality or uniqueness of the OBC tensor is unnecessary: the result
holds for every actual bounded OBC representation of that state. The
hypotheses retain a C1 TI tensor with a nonzero letter and the full source
size regime. No window gauge, solution or bond equality is an input.

Source: PGVWC07, arXiv:quant-ph/0608197, the prescribed squared-bond
canonical OBC window and first clause of Theorem 8, MPSarchive.tex
lines 1139--1169.
-/

open Matrix MPSPreparation OBCChainTensor
open scoped BigOperators

namespace MPSTensor

variable {d D N L : ℕ} {A : MPSTensor d D}

private theorem toMatrix_reindex_reindex_apply {ι κ ι' κ' M₁ M₂ : Type*}
    [Fintype ι] [Finite κ] [Fintype ι'] [Finite κ'] [DecidableEq ι] [DecidableEq ι']
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (b₁ : Module.Basis ι ℂ M₁) (b₂ : Module.Basis κ ℂ M₂) (e₁ : ι ≃ ι') (e₂ : κ ≃ κ')
    (f : M₁ →ₗ[ℂ] M₂) (a : κ') (b : ι') :
    LinearMap.toMatrix (b₁.reindex e₁) (b₂.reindex e₂) f a b =
      LinearMap.toMatrix b₁ b₂ f (e₂.symm a) (e₁.symm b) := by
  simp [LinearMap.toMatrix_apply]

private theorem prescribedOBCBondNeZero (B : OBCChainTensor d (D * D) N) : NeZero D :=
  ⟨fun hD ↦ by have h := B.bondBound_pos; simp [hD] at h⟩

private def reconstructionCut (hN : 2 * L + D ^ 4 < N)
    (j : Fin (D ^ 4 + 1)) : Fin (N + 1) :=
  ⟨L + j.val, by have := j.isLt; omega⟩

/-- The prescribed OBC bonds at every endpoint-inclusive window cut
are forced to have squared virtual dimension. The lower bound is the
actual physical cut rank and the upper bound belongs to the supplied OBC
representation's type. Source: PGVWC07, lines 1139--1169. -/
theorem prescribedOBC_window_bondDim_eq (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) : B.bondDim (reconstructionCut hN j) = D * D := by
  have : NeZero D := prescribedOBCBondNeZero B
  have hrank : cutRank B.coeff (L + j.val) = D * D := by
    rw [hcoeff, ← cutCoefficientRank_eq_cutRank _
      (show L + j.val ≤ N by have := j.isLt; omega)]
    exact quadraticWindow_cutCoefficientRank_eq_of_isNBlkInjective A hC1 hletter hN j
  apply le_antisymm (B.bondDim_le _)
  exact hrank.symm.le.trans (B.cutRank_coeff_le (reconstructionCut hN j))

private theorem prescribedOBC_window_minimal (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) :
    B.bondDim (reconstructionCut hN j) = cutCoefficientRank B.coeff (L + j.val) := by
  have : NeZero D := prescribedOBCBondNeZero B
  rw [prescribedOBC_window_bondDim_eq hletter hC1 hN B hcoeff, hcoeff,
    quadraticWindow_cutCoefficientRank_eq_of_isNBlkInjective A hC1 hletter hN j]

/-- The original window bonds, identified with the doubled virtual
coordinates by their derived dimension equality.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
noncomputable def prescribedOBCWindowBondEquiv (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) :
    Fin (B.bondDim (reconstructionCut hN j)) ≃ (Fin D × Fin D) :=
  (finCongr (prescribedOBC_window_bondDim_eq hletter hC1 hN B hcoeff j)).trans
    finProdFinEquiv.symm

/-- The prescribed original OBC site matrices in their proved doubled
bond coordinates. This definition does not replace the supplied OBC
representation by a newly selected one.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
noncomputable def quadraticPrescribedOBCWindow (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A) :
    Fin (D ^ 4) → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun j i ↦ Matrix.reindex (prescribedOBCWindowBondEquiv hletter hC1 hN B hcoeff j.castSucc)
    (prescribedOBCWindowBondEquiv hletter hC1 hN B hcoeff j.succ)
    (B.tensor ⟨L + j.val, by have := j.isLt; omega⟩ i)

/-- The physical cut bases are derived from the original prescribed
OBC prefix columns, with only the forced doubled-coordinate reindexing.
Source: PGVWC07, MPSarchive.tex lines 1139--1169. -/
noncomputable def prescribedOBCWindowCutBases (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) :
    Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace B.coeff (L + j.val)) :=
  (physicalPrefixBasis B (reconstructionCut hN j)
    (prescribedOBC_window_minimal hletter hC1 hN B hcoeff j)).reindex
      (prescribedOBCWindowBondEquiv hletter hC1 hN B hcoeff j)

/-- The actual original supplied window is exactly physical slicing
in its derived prefix bases. No comparison identity is assumed.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
theorem quadraticPrescribedOBCWindow_eq_physicalCutWindow
    (hletter : ∃ i, A i ≠ 0) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) (B : OBCChainTensor d (D * D) N)
    (hcoeff : B.coeff = mpv A) :
    quadraticPrescribedOBCWindow hletter hC1 hN B hcoeff =
      quadraticPhysicalCutWindow B.coeff (prescribedOBCWindowCutBases hletter hC1 hN B hcoeff) := by
  classical
  funext j i
  let p : Fin N := ⟨L + j.val, by have := j.isLt; omega⟩
  have hprev : B.bondDim p.castSucc = cutCoefficientRank B.coeff p.val :=
    prescribedOBC_window_minimal hletter hC1 hN B hcoeff j.castSucc
  have hnext : B.bondDim p.succ = cutCoefficientRank B.coeff (p.val + 1) :=
    prescribedOBC_window_minimal hletter hC1 hN B hcoeff j.succ
  have hsite := toMatrix_cutSlice_physicalPrefixBasis B p hprev hnext i
  ext a b
  let e₁ := prescribedOBCWindowBondEquiv hletter hC1 hN B hcoeff j.castSucc
  let e₂ := prescribedOBCWindowBondEquiv hletter hC1 hN B hcoeff j.succ
  have key : quadraticPhysicalCutWindow B.coeff
      (prescribedOBCWindowCutBases hletter hC1 hN B hcoeff) j i a b =
        LinearMap.toMatrix (physicalPrefixBasis B p.succ hnext)
          (physicalPrefixBasis B p.castSucc hprev) (cutSlice B.coeff p.val i)
          (e₁.symm a) (e₂.symm b) := by
    exact toMatrix_reindex_reindex_apply
      (physicalPrefixBasis B (reconstructionCut hN j.succ)
        (prescribedOBC_window_minimal hletter hC1 hN B hcoeff j.succ))
      (physicalPrefixBasis B (reconstructionCut hN j.castSucc)
        (prescribedOBC_window_minimal hletter hC1 hN B hcoeff j.castSucc))
      e₂ e₁ (cutSlice B.coeff (L + j.val) i) a b
  rw [key, hsite]
  rfl

/-- The prescribed actual bounded OBC window admits a quadratic
solution, constructed from the C1 TI representation of its actual state.
The OBC tensor may be the unique canonical one from the source, but no
uniqueness or gauge comparison is needed to identify its original sites.
Source: PGVWC07, first clause of Theorem 8, lines 1139--1169. -/
theorem exists_quadraticSolution_prescribedOBCWindow
    (hletter : ∃ i, A i ≠ 0) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) (B : OBCChainTensor d (D * D) N)
    (hcoeff : B.coeff = mpv A) :
    Nonempty (QuadraticReconstructionSolution
      (quadraticPrescribedOBCWindow hletter hC1 hN B hcoeff)) := by
  have : NeZero D := prescribedOBCBondNeZero B
  rw [quadraticPrescribedOBCWindow_eq_physicalCutWindow]
  have hsource : ∀ (ψ : (Fin N → Fin d) → ℂ), ψ = mpv A →
      ∀ C : (j : Fin (D ^ 4 + 1)) →
        Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace ψ (L + j.val)),
      Nonempty (QuadraticReconstructionSolution (quadraticPhysicalCutWindow ψ C)) := by
    intro ψ hψ
    subst ψ
    exact fun C ↦ exists_quadraticSolution_physicalCutWindow_of_isNBlkInjective
      A hC1 hletter hN.le C
  exact hsource B.coeff hcoeff _

/-- A nonzero physical state with a C1 TI representation supplies a
quadratic solution over its prescribed squared-bond OBC window. The
nonzero-letter condition and Perron normalization are both derived;
no canonical TI hypothesis or positive C1 length is imposed.
Source: PGVWC07, first clause of Theorem 8, MPSarchive.tex lines 1139--1169. -/
theorem exists_quadraticSolution_prescribedOBCWindow_of_mpv_ne_zero
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    ∃ hletter : ∃ i, A i ≠ 0, Nonempty (QuadraticReconstructionSolution
      (quadraticPrescribedOBCWindow hletter hC1 hN B hcoeff)) := by
  have hletter := exists_apply_ne_zero_of_mpv_ne_zero A (by omega : 0 < N) hnonzero
  exact ⟨hletter, exists_quadraticSolution_prescribedOBCWindow hletter hC1 hN B hcoeff⟩

end MPSTensor
