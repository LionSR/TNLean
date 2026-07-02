/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.LocalSupport
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.RFP.StructuralFull
import Mathlib.Data.Fin.Basic

/-!
# Basic-vector form and translated two-site parent terms

This file isolates the source ingredients used for the forward direction
\(\mathrm{RFP}\Rightarrow\mathrm{NNCPH}\) in arXiv:1606.00608, Theorem 3.10.
The proof passage at source line 1307 says that the implication follows from
the structural characterization theorem. That theorem, stated at source lines
543--555, writes a canonical-form RFP tensor as
\[
  A^i =
    \bigoplus_{j=1}^{g}\bigoplus_{q=1}^{r_j}
      \mu_{j,q}X_{j,q}\Lambda_jU^i_jX_{j,q}^{-1}.
\]
The source then writes the corresponding basic vectors as
\[
  |V^{(N)}(A_j)\rangle=U^{\otimes N}|\varphi_j\rangle^{\otimes N},
  \qquad
  |\varphi_j\rangle=\sum_m\lambda_m|m,m\rangle,
\]
where \(\varphi_j\) is shared by \(b_n\) and \(a_{n+1}\), and \(U\) acts on
\((a_n,b_n)\). The remaining parent-Hamiltonian step is to pass from this
basic-vector form to commutativity of the translated two-site terms
\(h_i=\tau_i(P_2^\perp)\).

The declarations below separate four mathematical statements:

* the coefficient expression for \(U^{\otimes L}\varphi_j^{\otimes L}\);
* the disjoint adjacent-pair coefficient condition used later in this file;
* the two local coefficient-space representatives used before the \(AX\) and
  \(XB\) lifts;
* the already formalized Appendix B structural form.

**Scope restriction (overlapping two-site terms):** The source \(AX\) and
\(XB\) support maps are treated in their basic-vector form. Definition D.2 of
arXiv:1606.00608 supplies the parent-commuting condition for the \(Q_{AX}\) and
\(Q_{XB}\) projectors. The coefficient representatives \(\widehat Q_{AX}\) and
\(\widehat Q_{XB}\) below are only the common two-site coefficient-space
representative \(q_2(\Lambda U)\), identified with \(q_2(A)\) after the
Appendix B core-tensor comparison, before it is placed on the \(AX\) and \(XB\)
faces. They do not by themselves construct the source projectors on
\(\mathcal H_A\otimes\mathcal H_X\) and
\(\mathcal H_X\otimes\mathcal H_B\), nor do they prove the lifted commutator.
For this reason commutativity of the translated idempotents is kept as an
explicit hypothesis. Eliminating this hypothesis is the source
projector-construction and commutator step recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Extract the `p`-th adjacent two-site block from a configuration on `2N`
sites. -/
def productPairWindow (N : ℕ) (σ : Cfg d (2 * N)) (p : Fin N) : Cfg d 2 :=
  fun j => σ ⟨2 * p.val + j.val, by
    have hp : p.val < N := p.isLt
    have hj : j.val < 2 := j.isLt
    omega⟩

@[simp] lemma productPairWindow_apply (N : ℕ) (σ : Cfg d (2 * N)) (p : Fin N)
    (j : Fin 2) :
    productPairWindow N σ p j = σ ⟨2 * p.val + j.val, by
      have hp : p.val < N := p.isLt
      have hj : j.val < 2 := j.isLt
      omega⟩ := rfl

/-- On one adjacent pair, the extracted window is the whole two-site configuration. -/
@[simp] theorem productPairWindow_one (σ : Cfg d (2 * 1)) :
    productPairWindow 1 σ 0 = σ := by
  funext j
  simp [productPairWindow]

/-- The even-chain state obtained by repeating a fixed two-site amplitude on
disjoint adjacent pairs.

This is the disjoint adjacent-pair expression used by the conditional
nearest-neighbor parent-term theorem below. It is not the basic-vector formula
of arXiv:1606.00608, lines 570--578, by itself: the source formula first puts
\(\varphi_j\) between \(b_n\) and \(a_{n+1}\) and then applies \(U\) to
\((a_n,b_n)\) at every site. Any use of this disjoint adjacent-pair expression
therefore has to be justified separately from the source formula. -/
def productPairState (ψ₂ : NSiteSpace d 2) (N : ℕ) : NSiteSpace d (2 * N) :=
  fun σ => ∏ p : Fin N, ψ₂ (productPairWindow N σ p)

@[simp] lemma productPairState_zero (ψ₂ : NSiteSpace d 2) :
    productPairState ψ₂ 0 = fun _ => (1 : ℂ) := by
  funext σ
  simp [productPairState]

/-- On a single adjacent pair, the product state is the original two-site amplitude. -/
@[simp] theorem productPairState_one (ψ₂ : NSiteSpace d 2) (σ : Cfg d (2 * 1)) :
    productPairState ψ₂ 1 σ = ψ₂ σ := by
  simp [productPairState]

/-- An MPS tensor has disjoint adjacent-pair MPVs when every positive
even-length coefficient factors as a repeated copy of one fixed two-site
amplitude on the pairs \((0,1),(2,3),\ldots\).

This is a generic factorization predicate: it does not assert that the two-site
amplitude is entangled. The zero-pair case is omitted because the empty-chain
MPV coefficient is the bond dimension, whereas the empty disjoint-pair amplitude
is \(1\). Odd chain lengths are omitted because this predicate is used only to
identify the translated two-site parent terms in the RFP-to-NNCPH direction of
arXiv:1606.00608, Theorem 3.10.

**Scope restriction:** Appendix B first produces the basic-vector expression
\(U^{\otimes N}\varphi_j^{\otimes N}\). This predicate is the later disjoint
adjacent-pair condition used by the present formal statement; it is not, by
itself, the full Appendix B factorization theorem. -/
def HasProductPairMPV (A : MPSTensor d D) : Prop :=
  ∃ ψ₂ : NSiteSpace d 2, ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
    mpv A σ = productPairState ψ₂ N σ

theorem HasProductPairMPV.exists_twoSiteAmplitude {A : MPSTensor d D}
    (hA : HasProductPairMPV A) :
    ∃ ψ₂ : NSiteSpace d 2, ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
      mpv A σ = productPairState ψ₂ N σ :=
  hA

/-- Witness that the nearest-neighbor local terms of \(A\) are idempotents
\(p_i\) associated to the adjacent two-site factors on an \(N\)-site chain, with
\(p_i p_j=p_j p_i\).

**Scope restriction (local projectors):** The three-site \(AX/XB\) support maps
for adjacent windows give the local support maps. This structure does not
construct the source projectors \(Q_{AX}\) and \(Q_{XB}\), nor does it identify
them with the translated length-two parent terms. The projectors are therefore
stated directly as endomorphisms of the full \(N\)-site space. -/
structure HasProductPairLocalProjectors (A : MPSTensor d D) (N : ℕ) where
  proj : Fin N → NSiteSpace d N →ₗ[ℂ] NSiteSpace d N
  hidem : ∀ i, proj i * proj i = proj i
  hlocal : ∀ i, localTerm A 2 N i = proj i
  hcomm : ∀ i j, proj i * proj j = proj j * proj i

theorem HasProductPairLocalProjectors.localTerm_idempotent
    {A : MPSTensor d D} {N : ℕ}
    (hPair : HasProductPairLocalProjectors A N) (i : Fin N) :
    localTerm A 2 N i * localTerm A 2 N i = localTerm A 2 N i := by
  rw [hPair.hlocal i, hPair.hidem i]

/-- The stated local projector hypotheses imply commutativity of the
nearest-neighbor parent-Hamiltonian local terms.

This is exactly the body of `IsCommutingParentHam A 2 N` after unfolding the
definition in `ParentHamiltonian/Commuting.lean`. -/
theorem HasProductPairLocalProjectors.commuting_twoSite_localTerms
    {A : MPSTensor d D} {N : ℕ}
    (hPair : HasProductPairLocalProjectors A N) :
    ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i := by
  intro i j
  rw [hPair.hlocal i, hPair.hlocal j]
  exact hPair.hcomm i j

/-- A commuting family of translated length-two parent terms gives the local
projector witness, since each translated parent term is already idempotent. -/
noncomputable def HasProductPairLocalProjectors.of_commuting_localTerms
    {A : MPSTensor d D} {N : ℕ}
    (hcomm : ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i) :
    HasProductPairLocalProjectors A N where
  proj := fun i => localTerm A 2 N i
  hidem := fun i => _root_.MPSTensor.localTerm_idempotent A 2 N i
  hlocal := fun _ => rfl
  hcomm := hcomm

/-- Conditional hypotheses for a tensor whose positive even-chain coefficients
factor through one disjoint adjacent two-site amplitude and whose
nearest-neighbor parent terms are commuting idempotents on every finite chain. -/
structure ProductPairBridge (A : MPSTensor d D) where
  pairAmplitude : NSiteSpace d 2
  hmpv : ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
    mpv A σ = productPairState pairAmplitude N σ
  localProjectors : ∀ N, HasProductPairLocalProjectors A N

theorem ProductPairBridge.mpv_eq_productPairState {A : MPSTensor d D}
    (hBridge : ProductPairBridge A) :
    ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
      mpv A σ = productPairState hBridge.pairAmplitude N σ :=
  hBridge.hmpv

theorem ProductPairBridge.hasProductPairMPV {A : MPSTensor d D}
    (hBridge : ProductPairBridge A) :
    HasProductPairMPV A :=
  ⟨hBridge.pairAmplitude, hBridge.hmpv⟩

/-- The conditional adjacent-pair hypotheses yield the unfolded `IsNNCPH`
conclusion: all two-site local terms commute on every finite chain.

The statement is written as the commutation equation for the translated
two-site parent terms, which is the nearest-neighbor commutation condition in
arXiv:1606.00608, Definition 3.9. -/
theorem ProductPairBridge.commuting_twoSite_localTerms
    {A : MPSTensor d D} (hBridge : ProductPairBridge A) (N : ℕ) :
    ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i :=
  (hBridge.localProjectors N).commuting_twoSite_localTerms

theorem ProductPairBridge.localTerm_idempotent
    {A : MPSTensor d D} (hBridge : ProductPairBridge A) (N : ℕ) (i : Fin N) :
    localTerm A 2 N i * localTerm A 2 N i = localTerm A 2 N i :=
  (hBridge.localProjectors N).localTerm_idempotent i

/-! ### Appendix B structural form used below -/

/-- Structure recording the Appendix B normal-tensor decomposition
\(A^i=X\Lambda U^iX^{-1}\) in the source unit pair-index convention.

The theorem `rfp_nt_structural_full_unit_pair` proves existence of this
structural form from the RFP, normality, and left-canonical hypotheses. The
remaining coefficient condition and parent-term identities must use the same
\(X,\Lambda,U\). -/
structure AppendixBStructuralData (A : MPSTensor d D) where
  /-- The virtual-bond change of basis. -/
  X : Matrix (Fin D) (Fin D) ℂ
  /-- Positive diagonal weights. -/
  Λ : Fin D → ℝ
  /-- The residual tensor family satisfying the source pair-index isometry. -/
  U : MPSTensor d D
  /-- The change-of-basis matrix is invertible. -/
  hX_det : X.det ≠ 0
  /-- The diagonal weights are strictly positive. -/
  hΛ_pos : ∀ k, 0 < Λ k
  /-- The residual tensor satisfies the source unit pair-index orthonormality
  condition from arXiv:1606.00608, lines 550--554, restricted to one block. -/
  hU_pair : ∀ p q : Fin D × Fin D,
    ∑ i : Fin d, star (U i p.1 p.2) * U i q.1 q.2 =
      if p = q then 1 else 0
  /-- The original tensor has the Appendix B structural form. -/
  hA_eq : ∀ i, A i = X * Matrix.diagonal (fun k => (Λ k : ℂ)) * U i * X⁻¹

/-- The proved structural form gives a nonempty bundled Appendix B form. -/
theorem AppendixBStructuralData.exists_ofRFP (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Nonempty (AppendixBStructuralData A) := by
  classical
  obtain ⟨X, Λ, U, hX_det, hΛ_pos, hU_pair, hA_eq⟩ :=
    rfp_nt_structural_full_unit_pair A hNT hRFP hLeft
  exact ⟨
    { X := X
      Λ := Λ
      U := U
      hX_det := hX_det
      hΛ_pos := hΛ_pos
      hU_pair := hU_pair
      hA_eq := hA_eq }⟩

/-- Extract the Appendix B structural form from the proved structural theorem.

This is a noncomputable definition only because it chooses a witness from the
nonempty type produced by `AppendixBStructuralData.exists_ofRFP`; it introduces
no new assumptions or trusted constants. -/
noncomputable def AppendixBStructuralData.ofRFP (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    AppendixBStructuralData A :=
  Classical.choice (AppendixBStructuralData.exists_ofRFP A hNT hRFP hLeft)

/-- The two-site amplitude read from a chosen Appendix B structural
form.

The key point is that this amplitude depends on the chosen decomposition
\(X,\Lambda,U\); the even-chain factorization must use this particular
structural amplitude, not an unrelated two-site vector. -/
noncomputable def AppendixBStructuralData.twoSiteAmplitude {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) : NSiteSpace d 2 :=
  let L : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.diagonal fun k => (hStruct.Λ k : ℂ)
  fun σ =>
    Matrix.trace
      ((hStruct.X * L * hStruct.U (σ 0) * hStruct.X⁻¹) *
        (hStruct.X * L * hStruct.U (σ 1) * hStruct.X⁻¹))

/-- The tensor \(\Lambda U^i\) associated to a chosen Appendix B structural form.

The structural equality says that `A` is a similarity transform of this tensor.
Separating it out makes the equality of periodic coefficients a consequence of
trace cyclicity applied to the basis-change matrices \(X\) and \(X^{-1}\). -/
noncomputable def AppendixBStructuralData.coreTensor {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) : MPSTensor d D :=
  fun i => Matrix.diagonal (fun k => (hStruct.Λ k : ℂ)) * hStruct.U i

@[simp] theorem AppendixBStructuralData.coreTensor_apply {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (i : Fin d) :
    hStruct.coreTensor i = Matrix.diagonal (fun k => (hStruct.Λ k : ℂ)) * hStruct.U i :=
  rfl

/-- The Appendix B pair-index orthogonality for the core tensor \(\Lambda U^i\).

Source: arXiv:1606.00608, lines 543--555, especially the source unit
pair-index isometry equation.  Multiplication by \(\Lambda\) on the left
weights the two virtual left indices. -/
theorem AppendixBStructuralData.coreTensor_pair_orthogonality
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (p q : Fin D × Fin D) :
    ∑ i : Fin d, star (hStruct.coreTensor i p.1 p.2) *
        hStruct.coreTensor i q.1 q.2 =
      (hStruct.Λ p.1 : ℂ) * (hStruct.Λ q.1 : ℂ) *
        (if p = q then 1 else 0) := by
  classical
  calc
    ∑ i : Fin d, star (hStruct.coreTensor i p.1 p.2) *
        hStruct.coreTensor i q.1 q.2 =
      (hStruct.Λ p.1 : ℂ) * (hStruct.Λ q.1 : ℂ) *
        (∑ i : Fin d, star (hStruct.U i p.1 p.2) *
          hStruct.U i q.1 q.2) := by
        simp [AppendixBStructuralData.coreTensor, Matrix.diagonal_mul,
          Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = (hStruct.Λ p.1 : ℂ) * (hStruct.Λ q.1 : ℂ) *
        (if p = q then 1 else 0) := by
        rw [hStruct.hU_pair p q]

/-! ### Coefficients of the source basic-vector expression -/

/-- The next virtual bond in the cyclic chain of length \(L\). -/
def cyclicVirtualSucc {L : ℕ} (hL : 0 < L) (t : Fin L) : Fin L :=
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  t + 1

/-- The coefficient expression obtained from the source basic-vector formula.

For a chain of length \(L\), choose a virtual index \(\alpha_t\) at each site.
The factor at site \(t\) is
\[
  \Lambda_{\alpha_t}\,
  (U^{\sigma_t})_{\alpha_t,\alpha_{t+1}},
\]
where the successor is cyclic. This is the coefficient form of the source
description
\[
  |V^{(N)}(A_j)\rangle=U^{\otimes N}|\varphi_j\rangle^{\otimes N},
  \qquad
  |\varphi_j\rangle=\sum_m \lambda_m |m,m\rangle,
\]
with \(\varphi_j\) shared between \(b_n\) and \(a_{n+1}\). -/
noncomputable def AppendixBStructuralData.cyclicVirtualPairState
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    {L : ℕ} (hL : 0 < L) : NSiteSpace d L :=
  fun σ =>
    ∑ α : Fin L → Fin D, ∏ t : Fin L,
      (hStruct.Λ (α t) : ℂ) *
        hStruct.U (σ t) (α t) (α (cyclicVirtualSucc hL t))

/-- The coefficient of the Appendix B core tensor is the coefficient form of
the source basic-vector expression.

This is the coefficient form of
\[
  |V^{(L)}(A_j)\rangle=U^{\otimes L}|\varphi_j\rangle^{\otimes L},
  \qquad
  |\varphi_j\rangle=\sum_m\lambda_m|m,m\rangle,
\]
with \(\varphi_j\) shared between \(b_t\) and \(a_{t+1}\). It is not the
disjoint adjacent physical-pair condition used later for nearest-neighbor
parent-term commutation. -/
theorem AppendixBStructuralData.mpv_coreTensor_eq_cyclicVirtualPairState
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    {L : ℕ} (hL : 0 < L) (σ : Cfg d L) :
    mpv hStruct.coreTensor σ = hStruct.cyclicVirtualPairState hL σ := by
  classical
  haveI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rw [mpv, coeff, trace_evalWord_eq_sum_cyclic]
  simp [AppendixBStructuralData.cyclicVirtualPairState,
    AppendixBStructuralData.coreTensor, cyclicVirtualSucc, Matrix.diagonal_mul]

/-- The original tensor is gauge equivalent to its Appendix B core tensor. -/
theorem AppendixBStructuralData.gaugeEquiv_coreTensor {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) :
    GaugeEquiv hStruct.coreTensor A := by
  let Xg : GL (Fin D) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero hStruct.X hStruct.hX_det
  refine ⟨Xg, ?_⟩
  intro i
  simp [Xg, AppendixBStructuralData.coreTensor, hStruct.hA_eq i, Matrix.mul_assoc]

/-- The Appendix B basis change leaves every local ground space unchanged. -/
theorem AppendixBStructuralData.groundSpace_eq_coreTensor {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (L : ℕ) :
    groundSpace A L = groundSpace hStruct.coreTensor L :=
  (hStruct.gaugeEquiv_coreTensor.groundSpace_eq L).symm

/-- The Appendix B basis change leaves the canonical parent interaction unchanged.

Source: arXiv:1606.00608, lines 543--555. -/
theorem AppendixBStructuralData.parentInteraction_eq_coreTensor {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (L : ℕ) :
    parentInteraction A L = parentInteraction hStruct.coreTensor L := by
  simp [parentInteraction, groundSpaceES, hStruct.groundSpace_eq_coreTensor L]

/-- The two-site Appendix B basic-vector support for the core tensor.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
noncomputable def AppendixBStructuralData.twoSiteBasicSpace {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) : Submodule ℂ (NSiteSpace d 2) :=
  groundSpace hStruct.coreTensor 2

/-- The \(AX\) two-site coefficient-space representative associated with the
Appendix B core tensor.

This is the common two-site coefficient representative \(q_2(\Lambda U)\)
before it is placed on the \(AX\) face. It is not, by itself, a construction of
the source projector \(Q_{AX}\) as an operator on
\(\mathcal H_A\otimes\mathcal H_X\).

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
noncomputable def AppendixBStructuralData.appendixBQAX {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2 :=
  parentInteraction hStruct.coreTensor 2

/-- The \(XB\) two-site coefficient-space representative associated with the
Appendix B core tensor.

This is the same common two-site coefficient representative
\(\widehat Q_{AX}\), now reserved for the later \(XB\)-lift. It is not, by
itself, a construction of the source projector \(Q_{XB}\) as an operator on
\(\mathcal H_X\otimes\mathcal H_B\).

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
noncomputable def AppendixBStructuralData.appendixBQXB {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2 :=
  hStruct.appendixBQAX

/-- The Appendix B \(AX\) coefficient representative is the canonical two-site
parent interaction of the original tensor.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.appendixBQAX_eq_parentInteraction {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) :
    hStruct.appendixBQAX = parentInteraction A 2 := by
  rw [AppendixBStructuralData.appendixBQAX]
  exact (hStruct.parentInteraction_eq_coreTensor 2).symm

/-- The Appendix B \(XB\) coefficient representative is the canonical two-site
parent interaction of the original tensor.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.appendixBQXB_eq_parentInteraction {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) :
    hStruct.appendixBQXB = parentInteraction A 2 := by
  rw [AppendixBStructuralData.appendixBQXB]
  exact hStruct.appendixBQAX_eq_parentInteraction

/-- The Appendix B \(AX\) two-site coefficient representative is idempotent.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.appendixBQAX_idempotent {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) :
    hStruct.appendixBQAX * hStruct.appendixBQAX = hStruct.appendixBQAX := by
  rw [hStruct.appendixBQAX_eq_parentInteraction]
  exact parentInteraction_idempotent A 2

/-- The Appendix B \(XB\) two-site coefficient representative is idempotent.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.appendixBQXB_idempotent {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) :
    hStruct.appendixBQXB * hStruct.appendixBQXB = hStruct.appendixBQXB := by
  rw [hStruct.appendixBQXB_eq_parentInteraction]
  exact parentInteraction_idempotent A 2

/-- The Appendix B two-site coefficient representatives satisfy the algebraic
part of Definition D.2 once their \(AX\) and \(XB\) lifts commute.

The idempotency of the two representatives follows from their identification
with the canonical two-site parent interaction; the sole hypothesis is the
commutation of their lifted operators.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.hasOverlappingTwoSiteCommutation_of_commute_lifts
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hcomm :
      leftPairLift hStruct.appendixBQAX * rightPairLift hStruct.appendixBQXB =
        rightPairLift hStruct.appendixBQXB * leftPairLift hStruct.appendixBQAX) :
    HasOverlappingTwoSiteCommutation (d := d) hStruct.appendixBQAX
      hStruct.appendixBQXB where
  left_idempotent := hStruct.appendixBQAX_idempotent
  right_idempotent := hStruct.appendixBQXB_idempotent
  commute_lifts := hcomm

/-- On a three-site window, the first translated length-two parent term is the
\(AX\) lift of the Appendix B \(AX\) coefficient representative.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.localTerm_two_three_zero_eq_leftPairLift_appendixBQAX
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    localTerm A 2 3 (0 : Fin 3) = leftPairLift hStruct.appendixBQAX := by
  rw [localTerm_two_three_zero_eq_leftPairLift_parentInteraction,
    hStruct.appendixBQAX_eq_parentInteraction]

/-- On a three-site window, the second translated length-two parent term is the
\(XB\) lift of the Appendix B \(XB\) coefficient representative.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.localTerm_two_three_one_eq_rightPairLift_appendixBQXB
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) :
    localTerm A 2 3 (1 : Fin 3) = rightPairLift hStruct.appendixBQXB := by
  rw [localTerm_two_three_one_eq_rightPairLift_parentInteraction,
    hStruct.appendixBQXB_eq_parentInteraction]

/-- The algebraic overlapping condition for the Appendix B two-site coefficient
representatives transports to commutation of the first two three-site parent
terms.

This is only the local transport from the Definition D.2 \(AX/XB\) equation to
the translated parent interactions.  It does not construct the source
projectors or prove their lifted commutator from the Appendix B basic-vector
form.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.localTerm_two_three_zero_one_commute_of_overlapping
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (h : HasOverlappingTwoSiteCommutation (d := d) hStruct.appendixBQAX
      hStruct.appendixBQXB) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) := by
  rw [hStruct.localTerm_two_three_zero_eq_leftPairLift_appendixBQAX,
    hStruct.localTerm_two_three_one_eq_rightPairLift_appendixBQXB]
  exact h.commute_lifts

/-- If the lifted Appendix B \(AX\) and \(XB\) coefficient representatives
commute, then the first two translated length-two parent terms commute on the
three-site window.

This is the composed local consequence of the already isolated idempotency
statements and the supplied Definition D.2 lifted commutator.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.localTerm_two_three_zero_one_commute_of_commute_lifts
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    (hcomm :
      leftPairLift hStruct.appendixBQAX * rightPairLift hStruct.appendixBQXB =
        rightPairLift hStruct.appendixBQXB * leftPairLift hStruct.appendixBQAX) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) :=
  hStruct.localTerm_two_three_zero_one_commute_of_overlapping
    (hStruct.hasOverlappingTwoSiteCommutation_of_commute_lifts hcomm)

/-- Definition D.2 data for the Appendix B \(AX\) and \(XB\) coefficient
representatives gives commutation of the first two translated length-two parent
terms on the three-site window.

This theorem only transports already-supplied Definition D.2 data to the
canonical parent interactions identified above.  The construction of that data
remains to be derived from the Appendix B basic-vector form.

Source: arXiv:1606.00608, lines 543--578 and Definition D.2, lines
2205--2218. -/
theorem AppendixBStructuralData.localTerm_two_three_zero_one_commute_of_appendixD2
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A)
    {KAXB : Submodule ℂ (NSiteSpace d 3)}
    (hD2 : HasAppendixD2ParentCommutingHamiltonian
      (d := d) KAXB hStruct.appendixBQAX hStruct.appendixBQXB) :
    localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) :=
  hStruct.localTerm_two_three_zero_one_commute_of_overlapping hD2.to_overlapping

/-- The Appendix B basis change does not change any MPV coefficient. -/
theorem AppendixBStructuralData.mpv_eq_coreTensor {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) {N : ℕ} (σ : Cfg d N) :
    mpv A σ = mpv hStruct.coreTensor σ :=
  (GaugeEquiv.sameMPV hStruct.gaugeEquiv_coreTensor N σ).symm

/-- The original tensor has the Appendix B cyclic basic-vector coefficient.

Source: arXiv:1606.00608, lines 543--555.

This combines the gauge-invariance of MPV coefficients with the coefficient
formula for the core tensor \(\Lambda U^i\).  The conclusion is the source
cyclic virtual-pair expression, not the disjoint adjacent physical-pair
condition used later in the conditional parent-Hamiltonian theorem. -/
theorem AppendixBStructuralData.mpv_eq_cyclicVirtualPairState {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) {L : ℕ} (hL : 0 < L) (σ : Cfg d L) :
    mpv A σ = hStruct.cyclicVirtualPairState hL σ := by
  rw [hStruct.mpv_eq_coreTensor σ, hStruct.mpv_coreTensor_eq_cyclicVirtualPairState hL σ]

/-- The structural two-site amplitude is exactly the two-site MPV coefficient. -/
theorem AppendixBStructuralData.twoSiteAmplitude_eq_mpv {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (σ : Cfg d 2) :
    hStruct.twoSiteAmplitude σ = mpv A σ := by
  simp [mpv, coeff, AppendixBStructuralData.twoSiteAmplitude, hStruct.hA_eq,
    evalWord, List.ofFn_succ, List.ofFn_zero]

/-- Equivalently, the structural two-site amplitude is the two-site coefficient of
\(\Lambda U^i\). -/
theorem AppendixBStructuralData.twoSiteAmplitude_eq_coreTensor_mpv {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (σ : Cfg d 2) :
    hStruct.twoSiteAmplitude σ = mpv hStruct.coreTensor σ := by
  rw [hStruct.twoSiteAmplitude_eq_mpv σ, hStruct.mpv_eq_coreTensor σ]

/-- On two sites, the Appendix B cyclic basic-vector coefficient is the
structural two-site amplitude. -/
theorem AppendixBStructuralData.cyclicVirtualPairState_two_eq_twoSiteAmplitude
    {A : MPSTensor d D} (hStruct : AppendixBStructuralData A) (σ : Cfg d 2) :
    hStruct.cyclicVirtualPairState (by decide : 0 < 2) σ =
      hStruct.twoSiteAmplitude σ := by
  rw [← hStruct.mpv_coreTensor_eq_cyclicVirtualPairState (by decide : 0 < 2) σ,
    hStruct.twoSiteAmplitude_eq_coreTensor_mpv]

/-- The length-two case of the disjoint adjacent-pair coefficient condition. -/
theorem AppendixBStructuralData.mpv_coreTensor_eq_productPairState_one {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (σ : Cfg d (2 * 1)) :
    mpv hStruct.coreTensor σ = productPairState hStruct.twoSiteAmplitude 1 σ := by
  rw [productPairState_one]
  exact (hStruct.twoSiteAmplitude_eq_coreTensor_mpv σ).symm

/-- The length-two case of the requested even-chain factorization is automatic
from the definition of the structural two-site amplitude. -/
theorem AppendixBStructuralData.mpv_eq_productPairState_one {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) (σ : Cfg d (2 * 1)) :
    mpv A σ = productPairState hStruct.twoSiteAmplitude 1 σ := by
  rw [productPairState_one, hStruct.twoSiteAmplitude_eq_mpv]

/-- The remaining disjoint adjacent-pair condition needed after the source
basic-vector expression.

For a fixed structural form, this captures the two facts that are still not
produced by the Appendix B structural datum: the coefficient formula for
\(U^{\otimes N}\varphi_j^{\otimes N}\) must be related to the repeated
disjoint adjacent two-site amplitude stated here, and the nearest-neighbor
parent projectors on each finite chain must be identified with a commuting
family attached to the source projectors \(Q_{AX}\) and \(Q_{XB}\). -/
structure AppendixBProductPairExtraction {A : MPSTensor d D}
    (hStruct : AppendixBStructuralData A) where
  /-- Positive even-chain adjacent-pair factorization through the structural
  two-site amplitude. -/
  hmpv : ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
    mpv A σ = productPairState hStruct.twoSiteAmplitude N σ
  /-- Local projectors realizing the nearest-neighbor parent terms. -/
  localProjectors : ∀ N, HasProductPairLocalProjectors A N

/-- Construct the coefficient part of the conditional structure from the
Appendix B core tensor.

This reduces the coefficient computation to the core tensor \(\Lambda U^i\);
the local projector identities remain a separate hypothesis. -/
noncomputable def AppendixBProductPairExtraction.ofCoreTensorFactorization
    {A : MPSTensor d D} {hStruct : AppendixBStructuralData A}
    (hCore : ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
      mpv hStruct.coreTensor σ = productPairState hStruct.twoSiteAmplitude N σ)
    (hProj : ∀ N, HasProductPairLocalProjectors A N) :
    AppendixBProductPairExtraction hStruct where
  hmpv := by
    intro N hN σ
    rw [hStruct.mpv_eq_coreTensor σ]
    exact hCore N hN σ
  localProjectors := hProj

/-- Construct the conditional Appendix B extraction from the coefficient
factorization and the all-chain commutation equations for the translated
length-two parent terms.

The idempotency of the local terms is supplied by `localTerm_idempotent`; the
source-dependent obligation in this constructor is only the commutation family. -/
noncomputable def AppendixBProductPairExtraction.ofCoreTensorFactorizationAndCommutation
    {A : MPSTensor d D} {hStruct : AppendixBStructuralData A}
    (hCore : ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
      mpv hStruct.coreTensor σ = productPairState hStruct.twoSiteAmplitude N σ)
    (hComm : ∀ N, ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i) :
    AppendixBProductPairExtraction hStruct :=
  AppendixBProductPairExtraction.ofCoreTensorFactorization hCore
    (fun N => HasProductPairLocalProjectors.of_commuting_localTerms (hComm N))

/-- The conditional Appendix B hypotheses yield the `ProductPairBridge`
structure used by the parent-Hamiltonian statements. -/
noncomputable def AppendixBProductPairExtraction.toProductPairBridge
    {A : MPSTensor d D} {hStruct : AppendixBStructuralData A}
    (hExtract : AppendixBProductPairExtraction hStruct) :
    ProductPairBridge A where
  pairAmplitude := hStruct.twoSiteAmplitude
  hmpv := hExtract.hmpv
  localProjectors := hExtract.localProjectors

/-- The conditional Appendix B hypotheses give the unfolded nearest-neighbor
commutation statement on every finite chain. -/
theorem AppendixBProductPairExtraction.commuting_twoSite_localTerms
    {A : MPSTensor d D} {hStruct : AppendixBStructuralData A}
    (hExtract : AppendixBProductPairExtraction hStruct) (N : ℕ) :
    ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i :=
  hExtract.toProductPairBridge.commuting_twoSite_localTerms N

/-- Conditional form of the forward implication in arXiv:1606.00608,
Theorem 3.10:
RFP plus the proved Appendix B structural theorem implies the nearest-neighbor
commutation equation as soon as the disjoint adjacent-pair coefficient condition
and the two-site projector identities are supplied for the resulting structural
form.

This theorem deliberately stops short of claiming the full Beigi-independent
`rfp_implies_nncph`: the missing hypothesis is exactly
`AppendixBProductPairExtraction` for the structural form produced by
`AppendixBStructuralData.ofRFP`. -/
theorem commuting_twoSite_localTerms_of_rfp_of_appendixBExtraction
    (A : MPSTensor d D) [NeZero D]
    (hNT : IsNormal A) (hRFP : IsRFP A)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hExtract : AppendixBProductPairExtraction
      (AppendixBStructuralData.ofRFP A hNT hRFP hLeft))
    (N : ℕ) :
    ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i :=
  hExtract.commuting_twoSite_localTerms N

end MPSTensor
