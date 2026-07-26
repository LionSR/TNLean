/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Trace
import TNLean.Algebra.ListProduct
import TNLean.MPS.MPDO.FirstSite
import TNLean.MPS.MPDO.VerticalCF
import TNLean.MPS.MPDO.ZCL

/-!
# The sector trace identity for matrix product density operators

This file formalizes the trace identification
$\tr(P_{\alpha,k}H^{(N)}P_{\alpha,k}) = \mu_{\alpha,k}\,d_\alpha$ from the
proof of Proposition 4.13 of arXiv:1606.00608, lines 1895--1902, together
with the positivity chain it supports: since w.l.o.g. $\mu_{\alpha,1}>0$,
the identity forces $d_\alpha>0$ and hence $\mu_{\alpha,k}>0$ for every
sector.

Closing the vertical (physical) indices of a single site of an MPO tensor
$M$ produces the matrix $E = \sum_i M^{ii}$ on the horizontal bond
space; the trace of the density operator $H^{(N)}$ is the horizontal trace of
$N$ such loops.  Inserting a matrix $P$ into one loop produces
the inserted loop $E_P$.  The displayed diagram defining $d_\alpha$ in the
proof of Proposition 4.13 of arXiv:1606.00608, lines 1899--1901, is one loop
of the vertical basis tensor $M_\alpha$ followed by loops of $M$, closed by
the horizontal trace; the compression $P_{\alpha,k}H^{(N)}P_{\alpha,k}$ is by
the sector projector acting on one site, as in the diagrams of that proof.

## Main definitions

* `verticalLoop` / `verticalLoopWith`:
  the closed single-site vertical loop $E = \sum_i M^{ii}$, and the loop with a
  matrix $P$ inserted, $E_P = \sum_{i,j} P_{ji}\,M^{ij}$.
* `representativeLoop`:
  the closed loop of a vertical representative, defined entrywise by
  $(E_\alpha)_{ab}=\operatorname{tr}(M_\alpha^{(a,b)})$.
* `sectorCompression`:
  the compression $P_1H^{(N+1)}P_1$ of the density operator by a matrix
  acting on the first site.
* `blockChainTrace`:
  the scalar $d_\alpha^{(N+1)} = \tr(E_\alpha E^N)$, one marked loop
  followed by `N` loops of `M`, closed by the horizontal trace.  This is the
  length-resolved form of the scalar $d_\alpha$ displayed in the proof of
  Proposition 4.13 of arXiv:1606.00608, lines 1899--1901.
* `SectorProjectorData`:
  the hypotheses carried by a sector projector $P_{\alpha,k}$ of the vertical
  decomposition $\bigoplus_{\alpha,k}\mu_{\alpha,k}X_{\alpha,k}M_\alpha
  X_{\alpha,k}^{-1}$ (arXiv:1606.00608, line 1898): orthogonality, and the
  loop identity $E_P = \mu\,E_\alpha$.

## Main results

* `trace_mpo_eq_trace_verticalLoop_pow`:
  $\tr H^{(N)} = \tr(E^N)$ with `E = verticalLoop M`.
* `trace_mpo_ne_zero_of_isSourceZCL`:
  source zero correlation length forces the trace of every positive-length
  density operator to be nonzero.
* `trace_mpo_pos_of_isMPDO_isSourceZCL`:
  if the tensor also generates an MPDO, these traces are strictly positive.
* `trace_firstSiteMatrix_mul_mpo` / `trace_sectorCompression_of_idempotent`:
  the general trace computation
  $\tr(P_1H^{(N+1)}P_1) = \tr(E_P\,E^N)$ for idempotent `P`.
* `SectorProjectorData.trace_sectorCompression`:
  the sector trace identity
  $\tr(P_{\alpha,k}H^{(N+1)}P_{\alpha,k}) = \mu_{\alpha,k}\,d_\alpha^{(N+1)}$
  (arXiv:1606.00608, line 1898).
* `SectorProjectorData.weight_mul_blockChainTrace_pos`,
  `blockChainTrace_pos`, `sector_weight_pos`:
  the positivity chain of arXiv:1606.00608, lines 1898--1902: a nonzero
  sector compression gives $\mu_{\alpha,k}d_\alpha^{(N+1)}>0$; with the
  normalization $\mu_{\alpha,1}>0$ this forces $d_\alpha^{(N+1)}>0$ and
  $\mu_{\alpha,k}>0$.

## Application to the vertical decomposition

The grouped decomposition in `TNLean.MPS.MPDO.VerticalBNT` constructs, for
each sector $(\alpha,k)$, the orthogonal projector $P_{\alpha,k}$ and its
`SectorProjectorData`.  The representative loop is defined entrywise by
$(E_\alpha)_{ab}=\operatorname{tr}(M_\alpha^{(a,b)})$.  It is independent of
$k$ because cyclicity of trace removes the internal similarity
$X_{\alpha,k}M_\alpha^{(a,b)}X_{\alpha,k}^{-1}$.  The formal decomposition uses
normalized BNT-refined horizontal form to find a nonzero sector compression,
and hence deduces the positivity of every grouped coefficient.  The remaining
argument of Proposition 4.13 begins with the reflected marked-chain comparison at line
1909.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  proof of Proposition 4.13, lines 1895--1902
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-! ### Single-site vertical loops -/

/-- The closed vertical loop of a single site: contracting the ket index of
an MPO tensor with its bra index gives the matrix $\sum_i M^{ii}$ on the
horizontal bond space.  Each unmarked site of the diagram defining
$d_\alpha$ in the proof of Proposition 4.13 of arXiv:1606.00608, lines
1899--1901, contributes one such loop.  As a matrix this is the physical-trace
transfer object `physTraceTransfer` of the zero-correlation-length layer; the
definition delegates to it, and this name records the loop role the matrix
plays in the sector-trace diagrams. -/
noncomputable def verticalLoop (M : MPOTensor d D) : Matrix (Fin D) (Fin D) ℂ :=
  physTraceTransfer M

/-- The vertical loop is the physical-trace transfer matrix. -/
theorem verticalLoop_eq_physTraceTransfer (M : MPOTensor d D) :
    verticalLoop M = physTraceTransfer M :=
  rfl

/-- The single-site vertical loop with a matrix $P$ inserted,
$E_P = \sum_{i,j}P_{ji}\,M^{ij}$.  This is the closed vertical loop of the
vertically viewed product $PM$, the contraction produced at the marked site
when the density operator is compressed by $P$ there, as in the diagrams of
the proof of Proposition 4.13 of arXiv:1606.00608, lines 1895--1902. -/
noncomputable def verticalLoopWith (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ a : Fin d, ∑ i : Fin d, P a i • M i a

/-- The closed loop of a vertical representative tensor, written entrywise as

\[
  (E_A)_{ab}=\operatorname{tr}(A^{(a,b)}).
\]

This is the matrix $E_\alpha$ in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1898--1901. -/
noncomputable def representativeLoop (A : MPSTensor (D * D) n) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun a b => Matrix.trace (A (finProdFinEquiv (a, b)))

/-- Identifying equal representative bond dimensions does not change the
closed representative loop. -/
@[simp] theorem representativeLoop_cast {n m : ℕ} (hdim : n = m)
    (A : MPSTensor (D * D) n) :
    representativeLoop (cast (congr_arg (MPSTensor (D * D)) hdim) A) =
      representativeLoop A := by
  subst m
  rfl

/-- Entrywise, the loop with a physical insertion is the trace of the
corresponding vertically viewed letter after multiplication by the insertion.
This is the marked single-site contraction in arXiv:1606.00608, line 1898. -/
theorem verticalLoopWith_apply_eq_trace_mul_verticalTensor
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ) (a b : Fin D) :
    verticalLoopWith M P a b =
      Matrix.trace (P * verticalTensor M (finProdFinEquiv (a, b))) := by
  simp only [verticalLoopWith, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, verticalTensor_finProdFinEquiv,
    smul_eq_mul]

/-- Inserting the identity recovers the plain vertical loop. -/
@[simp] theorem verticalLoopWith_one (M : MPOTensor d D) :
    verticalLoopWith M 1 = verticalLoop M := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro i _ hia
    rw [Matrix.one_apply_ne' hia, zero_smul]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- The inserted loop is the closed vertical loop of the vertically viewed
product $PM$. -/
theorem verticalLoop_ketLeftMul (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    verticalLoop (M.ketLeftMul P) = verticalLoopWith M P := by
  simp only [verticalLoop, physTraceTransfer, ketLeftMul, verticalLoopWith]

/-- The inserted loop is also the closed vertical loop of $MP$: the insertion
point inside the loop is immaterial, by cyclicity of the single-site trace. -/
theorem verticalLoop_braRightMul (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    verticalLoop (M.braRightMul P) = verticalLoopWith M P := by
  simp only [verticalLoop, physTraceTransfer, braRightMul, verticalLoopWith]
  exact Finset.sum_comm

/-- **Summing the diagonal word evaluations closes the vertical loops.** The
sum $\sum_\sigma M^{\sigma_0\sigma_0}\cdots M^{\sigma_{N-1}\sigma_{N-1}}$ over
all length-$N$ configurations $\sigma$ is the $N$-th
power of the single-site vertical loop.  This is the contraction pattern of
the closed diagrams in the proof of Proposition 4.13 of arXiv:1606.00608,
lines 1895--1902: each site contributes one loop, and the loops multiply
along the horizontal bond. -/
theorem sum_evalWord_diag_eq_verticalLoop_pow (M : MPOTensor d D) (N : ℕ) :
    ∑ σ : Fin N → Fin d, evalWord M (List.ofFn σ) (List.ofFn σ) =
      verticalLoop M ^ N := by
  rw [verticalLoop, physTraceTransfer, ← List.prod_replicate,
    ← List.ofFn_const, List.prod_ofFn_sum]
  exact Finset.sum_congr rfl fun σ _ => evalWord_ofFn M σ σ

/-- **The trace of the density operator is a chain of vertical loops:**
$\tr H^{(N)} = \tr(E^N)$ with `E` the single-site vertical loop.  This is the
fully closed diagram of the proof of Proposition 4.13 of arXiv:1606.00608,
lines 1895--1902, with no site marked. -/
theorem trace_mpo_eq_trace_verticalLoop_pow (M : MPOTensor d D) (N : ℕ) :
    Matrix.trace (mpo M N) = Matrix.trace (verticalLoop M ^ N) := by
  rw [← sum_evalWord_diag_eq_verticalLoop_pow M N, Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, mpo_apply, mpoMatrixEntry]

/-- Source zero correlation length forces the trace of every nonempty-chain
density operator to be nonzero.  Indeed, after dividing the physical-trace
transfer by its positive eigenvalue, one obtains a nonzero idempotent.  Its
trace is nonzero, and all its positive powers are equal to itself.

This supplies the strict normalization needed in the sector entropy identity;
it does not use the empty-chain convention.

Source: arXiv:1606.00608, Definition 4.2, lines 735--739, and Appendix C.2,
lines 1760--1780. -/
theorem trace_mpo_ne_zero_of_isSourceZCL (M : MPOTensor d D)
    (hZCL : IsSourceZCL M) {N : ℕ} (hN : 0 < N) :
    Matrix.trace (mpo M N) ≠ 0 := by
  obtain ⟨lam, hlam, hidem⟩ := hZCL.normalized_idempotent
  let E := ((lam : ℂ)⁻¹) • physTraceTransfer M
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlam
  have hEne : E ≠ 0 := by
    dsimp only [E]
    exact smul_ne_zero (inv_ne_zero hlamC) hZCL.1
  have hEtrace : Matrix.trace E ≠ 0 := by
    intro htrace
    have hLinIdem : IsIdempotentElem (Matrix.toLinAlgEquiv' E) :=
      hidem.map
        (Matrix.toLinAlgEquiv' : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ]
          Module.End ℂ (Fin D → ℂ)).toMonoidHom
    have hLinZero : E.toLin' = 0 :=
      LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hLinIdem
        (by simpa using htrace)
    exact hEne (Matrix.toLinAlgEquiv'.injective (by simpa using hLinZero))
  have hscale : physTraceTransfer M = (lam : ℂ) • E := by
    dsimp only [E]
    rw [smul_smul, mul_inv_cancel₀ hlamC, one_smul]
  rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer,
    hscale, smul_pow, hidem.pow_eq hN.ne', Matrix.trace_smul, smul_eq_mul]
  exact mul_ne_zero (pow_ne_zero N hlamC) hEtrace

/-- An MPDO tensor with source zero correlation length has strictly positive
normalization on every nonempty chain.

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1780.  This is the strict
form of the displayed inequality \(p_j\geq0\)
needed to divide each sector by its trace. -/
theorem trace_mpo_pos_of_isMPDO_isSourceZCL (M : MPOTensor d D)
    (hM : IsMPDO M) (hZCL : IsSourceZCL M) {N : ℕ} (hN : 0 < N) :
    0 < Matrix.trace (mpo M N) := by
  apply Matrix.PosSemidef.trace_pos_of_ne_zero (hM N hN)
  intro hzero
  exact trace_mpo_ne_zero_of_isSourceZCL M hZCL hN (by rw [hzero, Matrix.trace_zero])

/-! ### The first-site compression and its trace -/

/-- The compression of the $(N+1)$-site density operator by a matrix `P`
acting on the first site, $P_1H^{(N+1)}P_1$ with
$P_1 = P\otimes\Id^{\otimes N}$.  For the sector projectors of the vertical
decomposition this is the compression
$P_{\alpha,k}H^{(N)}P_{\alpha,k}$ of the proof of Proposition 4.13 of
arXiv:1606.00608, line 1898, whose diagrams mark a single site. -/
noncomputable def sectorCompression (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ :=
  firstSiteMatrix P N * mpo M (N + 1) * firstSiteMatrix P N

theorem sectorCompression_def (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    sectorCompression M P N =
      firstSiteMatrix P N * mpo M (N + 1) * firstSiteMatrix P N :=
  rfl

/-- First-site compressions of an MPDO by a Hermitian matrix are positive
semidefinite: the inequality $P_{\alpha,k}H^{(N)}P_{\alpha,k}\ge 0$ of the
proof of Proposition 4.13 of arXiv:1606.00608, lines 1898--1899, with the
projector acting on one site. -/
theorem sectorCompression_posSemidef (M : MPOTensor d D) (hM : IsMPDO M)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) (N : ℕ) :
    (sectorCompression M P N).PosSemidef :=
  mpo_compress_posSemidef M hM (N + 1) (by omega) (firstSiteMatrix P N)
    (firstSiteMatrix_isHermitian hP N)

/-- A nonzero first-site compression of an MPDO by a Hermitian matrix has
positive trace: the strict positivity in
$0 \ne P_{\alpha,k}H^{(N)}P_{\alpha,k}\ge 0$ of the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1898--1899. -/
theorem sectorCompression_trace_pos (M : MPOTensor d D) (hM : IsMPDO M)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) (N : ℕ)
    (hne : sectorCompression M P N ≠ 0) :
    0 < Matrix.trace (sectorCompression M P N) :=
  mpo_compress_trace_pos M hM (N + 1) (by omega) (firstSiteMatrix P N)
    (firstSiteMatrix_isHermitian hP N) hne

/-- Move a doubly indexed scalar-weighted sum inside a trace pairing. -/
private theorem sum_sum_mul_trace (c : Fin d → Fin d → ℂ)
    (B : Fin d → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (W : Matrix (Fin D) (Fin D) ℂ) :
    ∑ a : Fin d, ∑ i : Fin d, c a i * Matrix.trace (B a i * W) =
      Matrix.trace ((∑ a : Fin d, ∑ i : Fin d, c a i • B a i) * W) := by
  calc
    ∑ a : Fin d, ∑ i : Fin d, c a i * Matrix.trace (B a i * W)
        = ∑ a : Fin d, Matrix.trace ((∑ i : Fin d, c a i • B a i) * W) :=
          Finset.sum_congr rfl fun a _ => sum_mul_trace_eq_trace_sum_smul _ _ _
    _ = Matrix.trace ((∑ a : Fin d, ∑ i : Fin d, c a i • B a i) * W) := by
          rw [Finset.sum_mul, Matrix.trace_sum]

/-- **The general first-site trace computation.** For any matrix `P`, the
trace of $P_1H^{(N+1)}$ closes the marked loop with `P` inserted and the `N`
remaining loops without insertion:
$\tr(P_1H^{(N+1)}) = \tr(E_P\,E^N)$.  This is the contraction underlying the
diagram defining $d_\alpha$ in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1899--1901. -/
theorem trace_firstSiteMatrix_mul_mpo (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix.trace (firstSiteMatrix P N * mpo M (N + 1)) =
      Matrix.trace (verticalLoopWith M P * verticalLoop M ^ N) := by
  have hdiag : ∀ (a : Fin d) (ρ : Fin N → Fin d),
      (firstSiteMatrix P N * mpo M (N + 1)) (Fin.cons a ρ) (Fin.cons a ρ) =
        ∑ i : Fin d,
          P a i * Matrix.trace (M i a * evalWord M (List.ofFn ρ) (List.ofFn ρ)) := by
    intro a ρ
    rw [firstSiteMatrix_mul_apply]
    have hcomp : (Fin.cons a ρ : Fin (N + 1) → Fin d) ∘ Fin.succ = ρ := by
      funext n
      simp [Fin.cons_succ]
    simp only [Fin.cons_zero, hcomp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mpo_cons_cons]
  calc
    Matrix.trace (firstSiteMatrix P N * mpo M (N + 1))
        = ∑ σ : Fin (N + 1) → Fin d,
            (firstSiteMatrix P N * mpo M (N + 1)) σ σ := by
          simp only [Matrix.trace, Matrix.diag]
    _ = ∑ a : Fin d, ∑ ρ : Fin N → Fin d,
          (firstSiteMatrix P N * mpo M (N + 1)) (Fin.cons a ρ) (Fin.cons a ρ) :=
        sum_fin_succ_eq_sum_cons _
    _ = ∑ a : Fin d, ∑ ρ : Fin N → Fin d, ∑ i : Fin d,
          P a i * Matrix.trace (M i a * evalWord M (List.ofFn ρ) (List.ofFn ρ)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ρ _ => hdiag a ρ
    _ = ∑ ρ : Fin N → Fin d, ∑ a : Fin d, ∑ i : Fin d,
          P a i * Matrix.trace (M i a * evalWord M (List.ofFn ρ) (List.ofFn ρ)) :=
        Finset.sum_comm
    _ = ∑ ρ : Fin N → Fin d,
          Matrix.trace (verticalLoopWith M P * evalWord M (List.ofFn ρ) (List.ofFn ρ)) :=
        Finset.sum_congr rfl fun ρ _ => sum_sum_mul_trace _ _ _
    _ = Matrix.trace (verticalLoopWith M P *
          ∑ ρ : Fin N → Fin d, evalWord M (List.ofFn ρ) (List.ofFn ρ)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = Matrix.trace (verticalLoopWith M P * verticalLoop M ^ N) := by
        rw [sum_evalWord_diag_eq_verticalLoop_pow]

/-- For an idempotent `P`, the trace of the first-site compression equals the
trace of the inserted-loop chain:
$\tr(P_1H^{(N+1)}P_1) = \tr(E_P\,E^N)$. -/
theorem trace_sectorCompression_of_idempotent (M : MPOTensor d D)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P * P = P) (N : ℕ) :
    Matrix.trace (sectorCompression M P N) =
      Matrix.trace (verticalLoopWith M P * verticalLoop M ^ N) := by
  rw [sectorCompression_def, Matrix.trace_mul_cycle,
    firstSiteMatrix_mul_firstSiteMatrix, hP, trace_firstSiteMatrix_mul_mpo]

/-! ### Sector projectors and the trace identity -/

/-- The scalar $d_\alpha$ of the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1899--1901, resolved by chain length: one marked
loop `Eα` followed by `N` vertical loops of `M`, closed by the horizontal
trace, $d_\alpha^{(N+1)} = \tr(E_\alpha\,E^N)$.  The displayed diagram in the
source suppresses the length dependence. -/
noncomputable def blockChainTrace (M : MPOTensor d D)
    (Eα : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) : ℂ :=
  Matrix.trace (Eα * verticalLoop M ^ N)

/-- **Sector projector hypotheses.** The hypotheses carried by the projector
$P_{\alpha,k}$ selecting the sector $(\alpha,k)$ in the vertical
decomposition
$\bigoplus_{\alpha,k}\mu_{\alpha,k}X_{\alpha,k}M_\alpha X_{\alpha,k}^{-1}$ of
the proof of Proposition 4.13 of arXiv:1606.00608, line 1898:

* $P$ is an orthogonal projector (idempotent and Hermitian);
* inserting $P$ into the single-site vertical loop selects the sector
  contribution, $E_P = \mu\,E_\alpha$.

In the source decomposition the loop identity holds with
$\mu = \mu_{\alpha,k}$ and
$(E_\alpha)_{ab}=\operatorname{tr}(M_\alpha^{(a,b)})$, independently of $k$:
cyclicity of trace removes the internal similarity
$X_{\alpha,k}M_\alpha^{(a,b)}X_{\alpha,k}^{-1}$.  The grouped decomposition in
`TNLean.MPS.MPDO.VerticalBNT` supplies this data. -/
structure SectorProjectorData (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ)
    (Eα : Matrix (Fin D) (Fin D) ℂ) : Prop where
  /-- The sector projector is idempotent. -/
  idempotent : P * P = P
  /-- The sector projector is Hermitian. -/
  hermitian : P.IsHermitian
  /-- Inserting the projector into the single-site vertical loop selects the
  sector: the inserted loop is the sector weight times the closed loop of the
  sector's basis tensor. -/
  loop_eq : verticalLoopWith M P = μ • Eα

/-- An isometric vertical corner related to a representative by an invertible
gauge determines the corresponding sector projector and loop identity.

For $P=VV^\dagger$, cyclicity of trace gives

\[
  \operatorname{tr}(P\widetilde M_{ab})
  =\operatorname{tr}(V^\dagger\widetilde M_{ab}V)
  =\omega\operatorname{tr}(A^{(a,b)}),
\]

where the internal similarity cancels.  This is the sector-loop computation
in the proof of Proposition 4.13 of arXiv:1606.00608, line 1898. -/
theorem sectorProjectorData_of_gauge_corner
    (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (V : Matrix (Fin d) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (X : GL (Fin n) ℂ) (ω : ℂ)
    (hcorner : ∀ v,
      ω • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
        (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ)) =
          Vᴴ * verticalTensor M v * V) :
    SectorProjectorData M (V * Vᴴ) ω (representativeLoop A) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  · change (V * Vᴴ)ᴴ = V * Vᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  · ext a b
    rw [verticalLoopWith_apply_eq_trace_mul_verticalTensor]
    calc
      Matrix.trace ((V * Vᴴ) * verticalTensor M (finProdFinEquiv (a, b))) =
          Matrix.trace
            ((Vᴴ * verticalTensor M (finProdFinEquiv (a, b))) * V) := by
        rw [Matrix.mul_assoc]
        exact Matrix.trace_mul_comm V
          (Vᴴ * verticalTensor M (finProdFinEquiv (a, b)))
      _ = Matrix.trace
          (ω • ((X : Matrix (Fin n) (Fin n) ℂ) *
            A (finProdFinEquiv (a, b)) *
              (↑(X⁻¹) : Matrix (Fin n) (Fin n) ℂ))) :=
        congrArg Matrix.trace (hcorner _).symm
      _ = (ω • representativeLoop A) a b := by
        rw [Matrix.trace_smul, MPSTensor.trace_conj_eq]
        rfl

/-- **The sector trace identity**
(arXiv:1606.00608, proof of Proposition 4.13, line 1898): the trace of the
sector compression is the sector weight times the marked-loop chain trace,
$$\tr\bigl(P_{\alpha,k}H^{(N+1)}P_{\alpha,k}\bigr)
  = \mu_{\alpha,k}\,d_\alpha^{(N+1)}.$$
The source states the identity at the particular length where the
compression does not vanish; this is the identity at every length. -/
theorem SectorProjectorData.trace_sectorCompression {M : MPOTensor d D}
    {P : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ} {Eα : Matrix (Fin D) (Fin D) ℂ}
    (h : SectorProjectorData M P μ Eα) (N : ℕ) :
    Matrix.trace (sectorCompression M P N) = μ * blockChainTrace M Eα N := by
  rw [trace_sectorCompression_of_idempotent M h.idempotent N, h.loop_eq,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, blockChainTrace]

/-- A nonzero sector compression makes the weighted chain trace a positive
real: $\mu_{\alpha,k}\,d_\alpha^{(N+1)} > 0$ (arXiv:1606.00608, proof of
Proposition 4.13, lines 1898--1899). -/
theorem SectorProjectorData.weight_mul_blockChainTrace_pos {M : MPOTensor d D}
    {P : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ} {Eα : Matrix (Fin D) (Fin D) ℂ}
    (h : SectorProjectorData M P μ Eα) (hM : IsMPDO M) (N : ℕ)
    (hne : sectorCompression M P N ≠ 0) :
    0 < μ * blockChainTrace M Eα N := by
  have hpos := sectorCompression_trace_pos M hM h.hermitian N hne
  rwa [h.trace_sectorCompression N] at hpos

/-- **Positivity of the chain trace $d_\alpha$** (arXiv:1606.00608, proof of
Proposition 4.13, lines 1898--1902).  Let the sector $(\alpha,1)$ carry the
normalization $\mu_{\alpha,1} > 0$ and let the compression of some sector
$(\alpha,k)$ be nonzero at length $N+1$.  Then $d_\alpha^{(N+1)} > 0$.

The source concludes $d_\alpha>0$ from the sector $(\alpha,1)$ alone; at a
fixed length this needs the $(\alpha,1)$ compression to be nonzero there,
which follows from the nonvanishing of the $(\alpha,k)$ compression: the
$(\alpha,k)$ trace identity forces $d_\alpha^{(N+1)} \ne 0$, so the
$(\alpha,1)$ compression has nonzero trace $\mu_{\alpha,1}d_\alpha^{(N+1)}$
and is itself nonzero. -/
theorem blockChainTrace_pos {M : MPOTensor d D}
    {P₁ P : Matrix (Fin d) (Fin d) ℂ} {μ₁ μ : ℂ}
    {Eα : Matrix (Fin D) (Fin D) ℂ} (hM : IsMPDO M)
    (h₁ : SectorProjectorData M P₁ μ₁ Eα) (hμ₁ : 0 < μ₁)
    (h : SectorProjectorData M P μ Eα) (N : ℕ)
    (hne : sectorCompression M P N ≠ 0) :
    0 < blockChainTrace M Eα N := by
  have hd_ne : blockChainTrace M Eα N ≠ 0 :=
    right_ne_zero_of_mul (h.weight_mul_blockChainTrace_pos hM N hne).ne'
  have hne₁ : sectorCompression M P₁ N ≠ 0 := by
    intro h0
    have htr := h₁.trace_sectorCompression N
    rw [h0, Matrix.trace_zero] at htr
    exact mul_ne_zero hμ₁.ne' hd_ne htr.symm
  have hpos₁ := h₁.weight_mul_blockChainTrace_pos hM N hne₁
  have h0 : μ₁ * 0 < μ₁ * blockChainTrace M Eα N := by rwa [mul_zero]
  exact lt_of_mul_lt_mul_left h0 hμ₁.le

/-- **Positivity of the sector weights**
(arXiv:1606.00608, proof of Proposition 4.13, lines 1898--1902): with the
normalization $\mu_{\alpha,1} > 0$, every sector $(\alpha,k)$ whose
compression is nonzero at some length has $\mu_{\alpha,k} > 0$. -/
theorem sector_weight_pos {M : MPOTensor d D}
    {P₁ P : Matrix (Fin d) (Fin d) ℂ} {μ₁ μ : ℂ}
    {Eα : Matrix (Fin D) (Fin D) ℂ} (hM : IsMPDO M)
    (h₁ : SectorProjectorData M P₁ μ₁ Eα) (hμ₁ : 0 < μ₁)
    (h : SectorProjectorData M P μ Eα) (N : ℕ)
    (hne : sectorCompression M P N ≠ 0) :
    0 < μ := by
  have hd := blockChainTrace_pos hM h₁ hμ₁ h N hne
  have hpos := h.weight_mul_blockChainTrace_pos hM N hne
  rw [mul_comm] at hpos
  have h0 : blockChainTrace M Eα N * 0 < blockChainTrace M Eα N * μ := by
    rwa [mul_zero]
  exact lt_of_mul_lt_mul_left h0 hd.le

end MPOTensor
