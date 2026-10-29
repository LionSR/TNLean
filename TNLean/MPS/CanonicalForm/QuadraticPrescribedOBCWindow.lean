/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.QuadraticPhysicalCutWindow
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
hypotheses retain the canonical C1 TI tensor and the full source size
regime. No window gauge, solution or bond equality is an input.

**Scope restriction (canonical TI input):** the TI tensor is explicitly
canonical and C1. The printed first clause starts from existence of a C1
TI representation. Composing its canonical normalization with this result
remains necessary for that exact input statement; see
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, the prescribed squared-bond
canonical OBC window and first clause of Theorem 8, MPSarchive.tex
lines 1139--1169.
-/

open Matrix MPSPreparation OBCChainTensor
open scoped BigOperators

namespace MPSTensor

variable {d D N L : ℕ} {A : MPSTensor d D}

private def prescribedOBCBondNeZero (B : OBCChainTensor d (D * D) N) : NeZero D :=
  ⟨fun hD ↦ by have h := B.bondBound_pos; simpa [hD] using h⟩

private def reconstructionCut (hN : 2 * L + D ^ 4 < N)
    (j : Fin (D ^ 4 + 1)) : Fin (N + 1) :=
  ⟨L + j.val, by have := j.isLt; omega⟩

/-- The prescribed OBC bonds at every endpoint-inclusive window cut
are forced to have squared virtual dimension. The lower bound is the
actual physical cut rank and the upper bound belongs to the supplied OBC
representation's type. Source: PGVWC07, lines 1139--1169. -/
theorem prescribedOBC_window_bondDim_eq (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) : B.bondDim (reconstructionCut hN j) = D * D := by
  let : NeZero D := prescribedOBCBondNeZero B
  have hrank : cutRank B.coeff (L + j.val) = D * D := by
    rw [hcoeff]
    have hj := j.isLt
    exact cutRank_mpv_eq_of_canonical hA hC1 (by omega) (by omega) (by omega)
  apply le_antisymm (B.bondDim_le _)
  rw [← hrank]
  exact B.cutRank_coeff_le (reconstructionCut hN j)

private theorem prescribedOBC_window_minimal (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) :
    B.bondDim (reconstructionCut hN j) = cutCoefficientRank B.coeff (L + j.val) := by
  let : NeZero D := prescribedOBCBondNeZero B
  rw [prescribedOBC_window_bondDim_eq hA hC1 hN B hcoeff, hcoeff,
    quadraticWindow_cutCoefficientRank_eq hA hC1 hN j]

/-- The original window bonds, identified with the doubled virtual
coordinates by their derived dimension equality.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
noncomputable def prescribedOBCWindowBondEquiv (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) :
    Fin (B.bondDim (reconstructionCut hN j)) ≃ (Fin D × Fin D) :=
  (finCongr (prescribedOBC_window_bondDim_eq hA hC1 hN B hcoeff j)).trans
    finProdFinEquiv.symm

/-- The prescribed original OBC site matrices in their proved doubled
bond coordinates. This definition does not replace the supplied OBC
representation by a newly selected one.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
noncomputable def quadraticPrescribedOBCWindow (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A) :
    Fin (D ^ 4) → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun j i ↦ Matrix.reindex (prescribedOBCWindowBondEquiv hA hC1 hN B hcoeff j.castSucc)
    (prescribedOBCWindowBondEquiv hA hC1 hN B hcoeff j.succ)
    (B.tensor ⟨L + j.val, by have := j.isLt; omega⟩ i)

/-- The physical cut bases are derived from the original prescribed
OBC prefix columns, with only the forced doubled-coordinate reindexing.
Source: PGVWC07, MPSarchive.tex lines 1139--1169. -/
noncomputable def prescribedOBCWindowCutBases (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d (D * D) N) (hcoeff : B.coeff = mpv A)
    (j : Fin (D ^ 4 + 1)) :
    Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace B.coeff (L + j.val)) :=
  (physicalPrefixBasis B (reconstructionCut hN j)
    (prescribedOBC_window_minimal hA hC1 hN B hcoeff j)).reindex
      (prescribedOBCWindowBondEquiv hA hC1 hN B hcoeff j)

/-- The actual original supplied window is exactly physical slicing
in its derived prefix bases. No comparison identity is assumed.
Source: PGVWC07, MPSarchive.tex lines 1139--1152. -/
theorem quadraticPrescribedOBCWindow_eq_physicalCutWindow
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) (B : OBCChainTensor d (D * D) N)
    (hcoeff : B.coeff = mpv A) :
    quadraticPrescribedOBCWindow hA hC1 hN B hcoeff =
      quadraticPhysicalCutWindow B.coeff (prescribedOBCWindowCutBases hA hC1 hN B hcoeff) := by
  classical
  funext j i
  let p : Fin N := ⟨L + j.val, by have := j.isLt; omega⟩
  have hprev : B.bondDim p.castSucc = cutCoefficientRank B.coeff p.val :=
    prescribedOBC_window_minimal hA hC1 hN B hcoeff j.castSucc
  have hnext : B.bondDim p.succ = cutCoefficientRank B.coeff (p.val + 1) :=
    prescribedOBC_window_minimal hA hC1 hN B hcoeff j.succ
  have hsite := toMatrix_cutSlice_physicalPrefixBasis B p hprev hnext i
  ext a b
  have hentry := congrFun (congrFun hsite
    ((prescribedOBCWindowBondEquiv hA hC1 hN B hcoeff j.castSucc).symm a))
      ((prescribedOBCWindowBondEquiv hA hC1 hN B hcoeff j.succ).symm b)
  simpa only [quadraticPrescribedOBCWindow, quadraticPhysicalCutWindow,
    prescribedOBCWindowCutBases, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply] using hentry.symm

/-- The prescribed actual bounded OBC window admits a quadratic
solution, constructed from the C1 TI representation of its actual state.
The OBC tensor may be the unique canonical one from the source, but no
uniqueness or gauge comparison is needed to identify its original sites.
Source: PGVWC07, first clause of Theorem 8, lines 1139--1169. -/
theorem exists_quadraticSolution_prescribedOBCWindow
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) (B : OBCChainTensor d (D * D) N)
    (hcoeff : B.coeff = mpv A) :
    Nonempty (QuadraticReconstructionSolution
      (quadraticPrescribedOBCWindow hA hC1 hN B hcoeff)) := by
  let : NeZero D := prescribedOBCBondNeZero B
  rw [quadraticPrescribedOBCWindow_eq_physicalCutWindow]
  have hsource : ∀ (ψ : (Fin N → Fin d) → ℂ), ψ = mpv A →
      ∀ C : (j : Fin (D ^ 4 + 1)) →
        Module.Basis (Fin D × Fin D) ℂ (cutColumnSpace ψ (L + j.val)),
      Nonempty (QuadraticReconstructionSolution (quadraticPhysicalCutWindow ψ C)) := by
    intro ψ hψ
    subst ψ
    exact fun C ↦ exists_quadraticSolution_physicalCutWindow hA hC1 hN.le C
  exact hsource B.coeff hcoeff _

end MPSTensor
