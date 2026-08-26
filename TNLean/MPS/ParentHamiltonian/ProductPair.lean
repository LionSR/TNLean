/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Basic

/-!
# Product-pair states and local projectors

This file defines even-chain product-pair states and the generic local-projector
conditions used to prove commutativity of translated two-site parent terms.
-/

open scoped BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Extract the \(p\)-th two-site physical pair from a configuration on \(2N\)
sites, using the pairs \((0,1),(2,3),\ldots\). -/
def productPairWindow (N : ℕ) (σ : Cfg d (2 * N)) (p : Fin N) : Cfg d 2 :=
  fun j => σ ⟨2 * p.val + j.val, by
    have hp : p.val < N := p.isLt
    have hj : j.val < 2 := j.isLt
    omega⟩

/-- Evaluating a physical pair window selects sites \(2p\) and \(2p+1\). -/
@[simp] lemma productPairWindow_apply (N : ℕ) (σ : Cfg d (2 * N)) (p : Fin N)
    (j : Fin 2) :
    productPairWindow N σ p j = σ ⟨2 * p.val + j.val, by
      have hp : p.val < N := p.isLt
      have hj : j.val < 2 := j.isLt
      omega⟩ := rfl

/-- For one physical pair, the extracted window is the whole two-site configuration. -/
@[simp] theorem productPairWindow_one (σ : Cfg d (2 * 1)) :
    productPairWindow 1 σ 0 = σ := by
  funext j
  simp [productPairWindow]

/-- The even-chain state obtained by repeating a fixed two-site amplitude on the
physical pairs \((0,1),(2,3),\ldots\).

This is the physical-pair factorization used by the conditional
nearest-neighbor parent-term theorem below. It is not the basic-vector formula
of arXiv:1606.00608, lines 570--578, by itself: the source formula first puts
\(\varphi_j\) between \(b_n\) and \(a_{n+1}\) and then applies \(U\) to
\((a_n,b_n)\) at every site. Any use of this physical-pair factorization
therefore has to be justified separately from the source formula. -/
def productPairState (ψ₂ : NSiteSpace d 2) (N : ℕ) : NSiteSpace d (2 * N) :=
  fun σ => ∏ p : Fin N, ψ₂ (productPairWindow N σ p)

/-- The zero-fold physical pair product is the constant-one state. -/
@[simp] lemma productPairState_zero (ψ₂ : NSiteSpace d 2) :
    productPairState ψ₂ 0 = fun _ => (1 : ℂ) := by
  funext σ
  simp [productPairState]

/-- For one physical pair, the product state is the original two-site amplitude. -/
@[simp] theorem productPairState_one (ψ₂ : NSiteSpace d 2) (σ : Cfg d (2 * 1)) :
    productPairState ψ₂ 1 σ = ψ₂ σ := by
  simp [productPairState]

/-- An MPS tensor has even-chain physical-pair factorization when every positive
even-length coefficient factors as a repeated copy of one fixed two-site
amplitude on the pairs \((0,1),(2,3),\ldots\).

This is a generic factorization predicate: it does not assert that the two-site
amplitude is entangled. The zero-pair case is omitted because the empty-chain
MPV coefficient is the bond dimension, whereas the empty physical-pair product is
\(1\). Odd chain lengths are omitted because this predicate is used only to
identify the translated two-site parent terms in the RFP-to-NNCPH direction of
arXiv:1606.00608, Theorem 3.10.

**Scope restriction:** Appendix B first produces the basic-vector expression
\(U^{\otimes N}\varphi_j^{\otimes N}\). The condition above instead asks for an
even-chain physical-pair factorization; by itself, it is not the full Appendix B
factorization theorem. -/
def HasProductPairMPV (A : MPSTensor d D) : Prop :=
  ∃ ψ₂ : NSiteSpace d 2, ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
    mpv A σ = productPairState ψ₂ N σ

/-- Hypotheses asserting that the nearest-neighbor local terms of \(A\) are
commuting idempotents \(p_i\) on an \(N\)-site chain, with
\(p_i p_j = p_j p_i\).

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

/-- A commuting family of translated length-two parent terms satisfies the
local-projector hypotheses, since each translated parent term is already
idempotent. -/
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
factor through one repeated two-site amplitude and whose nearest-neighbor parent
terms are commuting idempotents on every finite chain of length greater than two. -/
structure ProductPairBridge (A : MPSTensor d D) where
  pairAmplitude : NSiteSpace d 2
  hmpv : ∀ N, 0 < N → ∀ σ : Cfg d (2 * N),
    mpv A σ = productPairState pairAmplitude N σ
  localProjectors : ∀ N, 2 < N → HasProductPairLocalProjectors A N

/-- The conditional physical-pair hypotheses yield the unfolded `IsNNCPH`
conclusion: all two-site local terms commute on every finite chain of length at
least three.

The statement is written as the commutation equation for the translated
two-site parent terms, which is the nearest-neighbor commutation condition in
arXiv:1606.00608, Definition 3.9. -/
theorem ProductPairBridge.commuting_twoSite_localTerms
    {A : MPSTensor d D} (hBridge : ProductPairBridge A) (N : ℕ) (hN : 2 < N) :
    ∀ i j : Fin N,
      localTerm A 2 N i * localTerm A 2 N j =
        localTerm A 2 N j * localTerm A 2 N i :=
  (hBridge.localProjectors N hN).commuting_twoSite_localTerms

end MPSTensor
