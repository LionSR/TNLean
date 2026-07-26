/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InvariantProjection
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral

/-!
# Exclusion of periodic vectors for matrix product density operators

This file formalizes the periodic-sector step in the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1888--1893.  If the vertically
viewed tensor of a tensor generating matrix product density operators had a
nontrivial $p$-periodic vector, the source asserts that there would be an
orthogonal projector $Q$ satisfying, for every $N$,
$$
  QH^{(N)}\ne H^{(N)}Q,
  \qquad
  Q\bigl[H^{(N)}\bigr]^p=\bigl[H^{(N)}\bigr]^pQ
$$
(eq2:proof.IV.12).  Since every $H^{(N)}$ is positive semidefinite, the second
family of identities forces $QH^{(N)}=H^{(N)}Q$, contradicting the first.

The commutation identities imposed on $Q$ are recorded by `PeriodicSectorProjector`, with
$Q$ acting on the first site as does the projector $P$ of the
invariant-projection step (eq1:proof.IV.12, lines 1874--1887).  The
contradiction is proved unconditionally: `isEmpty_periodicSectorProjector`
shows that a matrix product density operator admits no such projector.  The
implication from a nontrivial $p$-periodic vector to such a projector — which
the source asserts from the general theory of the peripheral spectrum of
completely positive maps at lines 1889--1891 — is stated as the hypothesis
`PeriodicVectorYieldsProjector`.  The cyclic decomposition of the peripheral
spectrum (Wolf 2012, Theorem 6.6) applied to the vertical transfer map
supplies the projector with its word invariance and single-letter
displacement (`TNLean/MPS/MPDO/CyclicProjector.lean`).  The all-length
non-commutation family is retained as a stronger conditional formulation.  For
a tensor in normalized BNT-refined horizontal form, the
theorem `hasNoPeriodicVectors_verticalTensor_of_horizontalCF` instead uses the
one noncommuting length supplied by the contrapositive of Lemma L.  No literal
canonical-form conclusion is asserted.

## Main definitions

* `PeriodicSectorProjector`: an orthogonal projector on the physical space
  with the commutation identities eq2:proof.IV.12 of arXiv:1606.00608.
* `PeriodicVectorYieldsProjector`: the hypothesis that every nontrivial
  $p$-periodic vector of the vertically viewed tensor supplies a
  periodic-sector projector.

## Main results

* `isEmpty_periodicSectorProjector`: a matrix product density operator admits
  no periodic-sector projector.
* `hasNoPeriodicVectors_verticalTensor`: granted the hypothesis, the
  vertically viewed tensor of a matrix product density operator has no
  nontrivial $p$-periodic vectors.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1888--1893
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The orthogonal projector postulated by the periodic-sector step in the
proof of Proposition 4.13 of arXiv:1606.00608, lines 1888--1891.  A
nontrivial $p$-periodic vector of the vertically viewed tensor would supply
an orthogonal projector $Q$ on the physical space — the virtual space of the
vertically viewed tensor — that fails to commute with the density operator
$H^{(N)}$ at every length while commuting with its $p$-th power
$[H^{(N)}]^p$ at every length (eq2:proof.IV.12).  As with the projector $P$
of the invariant-projection step (eq1:proof.IV.12, lines 1874--1887), $Q$
acts on an $(N+1)$-site chain through the first-site operator
$Q_1=Q\otimes\Id^{\otimes N}$. -/
structure PeriodicSectorProjector (M : MPOTensor d D) (p : ℕ) where
  /-- The orthogonal projector $Q$ of arXiv:1606.00608, line 1889, on the
  physical space. -/
  Q : Matrix (Fin d) (Fin d) ℂ
  /-- $Q$ is self-adjoint (arXiv:1606.00608, line 1889: $Q$ is an orthogonal
  projector). -/
  isHermitian : Q.IsHermitian
  /-- $Q$ is idempotent (arXiv:1606.00608, line 1889: $Q$ is an orthogonal
  projector). -/
  isIdempotentElem : IsIdempotentElem Q
  /-- The exponent is positive: the source's $p$ is the period of a
  nontrivial $p$-periodic vector (arXiv:1606.00608, lines 227 and 1889). -/
  p_ne_zero : p ≠ 0
  /-- $QH^{(N)}\ne H^{(N)}Q$ at every length (arXiv:1606.00608, line 1889). -/
  not_commute : ∀ N : ℕ, ¬ Commute (firstSiteMatrix Q N) (mpo M (N + 1))
  /-- $Q[H^{(N)}]^p=[H^{(N)}]^pQ$ at every length (eq2:proof.IV.12,
  arXiv:1606.00608, lines 1890--1891). -/
  commute_pow : ∀ N : ℕ, Commute (firstSiteMatrix Q N) (mpo M (N + 1) ^ p)

/-- A matrix product density operator admits no periodic-sector projector:
since $H^{(N)}$ is positive semidefinite, commutation of $Q_1$ with
$[H^{(N)}]^p$ forces commutation with $H^{(N)}$ itself, contradicting
$QH^{(N)}\ne H^{(N)}Q$.  This is the contradiction concluding the
periodic-sector step in the proof of Proposition 4.13 of arXiv:1606.00608,
lines 1892--1893. -/
theorem isEmpty_periodicSectorProjector (M : MPOTensor d D) (hM : IsMPDO M)
    {p : ℕ} : IsEmpty (PeriodicSectorProjector M p) :=
  ⟨fun QP => QP.not_commute 0
    (mpo_commute_of_commute_pow M hM 1 (by omega) QP.p_ne_zero
      (QP.commute_pow 0))⟩

/-- **Hypothesis** (arXiv:1606.00608, lines 1889--1891): every nontrivial
$p$-periodic vector of the vertically viewed tensor supplies a
periodic-sector projector.  A nontrivial $p$-periodic vector is presented as
in `MPSTensor.HasNoPeriodicVectors`: an irreducible restriction $B$
of the vertically viewed tensor to a minimal invariant subspace, carrying a
positive-definite transfer eigenvector with positive eigenvalue $r$ —
necessarily the spectral radius — together with a transfer eigenvalue of
modulus $r$ different from $r$.

The source asserts this implication from the general theory of the
peripheral spectrum of completely positive maps, with the exponent of the
projector equal to the period $p$ of the vector; only the existence of a
projector with some positive exponent enters the exclusion argument, so the
exponent is not tied to the period here.  The intended derivation
applies the cyclic decomposition of the peripheral spectrum (Wolf 2012,
Theorem 6.6) to the vertical transfer map: the cyclic projections of a
period-$p$ sector are permuted by one vertical layer, hence fail to commute
with $H^{(N)}$, while remaining invariant for $p$ stacked layers, whose
density operator is $[H^{(N)}]^p$; invariance then gives commutation with
$[H^{(N)}]^p$ by the argument of eq1:proof.IV.12 (lines 1874--1887) applied
to the stacked tensor.  The stacking and invariance parts of this
derivation are formalized in `TNLean/MPS/MPDO/StackedLayers.lean`, which
reduces this hypothesis to `PeriodicVectorYieldsCyclicProjector`; the
cyclic projections themselves, with their word invariance and single-letter
displacement, are constructed in `TNLean/MPS/MPDO/CyclicProjector.lean`,
which proves the conclusion from normalized BNT-refined horizontal form by
using one noncommuting length.  The definition below retains the stronger
all-length formulation. -/
def PeriodicVectorYieldsProjector (M : MPOTensor d D) : Prop :=
  ∀ ⦃n : ℕ⦄ (V : Matrix (Fin d) (Fin n) ℂ) (B : MPSTensor (D * D) n)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (r : ℝ),
    Vᴴ * V = 1 → (∀ v : Fin (D * D), verticalTensor M v * V = V * B v) →
    MPSTensor.IsIrreducibleTensor B → ρ.PosDef → 0 < r →
    MPSTensor.transferMap (d := D * D) (D := n) B ρ = (r : ℂ) • ρ →
    ∀ μ : ℂ,
      Module.End.HasEigenvalue (MPSTensor.transferMap (d := D * D) (D := n) B) μ →
      ‖μ‖ = r → μ ≠ (r : ℂ) →
      ∃ p : ℕ, Nonempty (PeriodicSectorProjector M p)

/-- The vertically viewed tensor of a matrix product density operator has no
nontrivial $p$-periodic vectors, granted that periodic vectors supply
periodic-sector projectors.  This is the periodic-sector step in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1888--1893: a nontrivial
$p$-periodic vector would supply an orthogonal projector with the
commutation identities eq2:proof.IV.12, and positive semidefiniteness of the
density operators rules such a projector out.

**Scope restriction (conditional on the supplied projector):** the source
draws the projector from the general theory of the peripheral spectrum; here
that implication is the explicit all-length hypothesis.  The theorem in
`TNLean/MPS/MPDO/CyclicProjector.lean` uses one noncommuting length but assumes
normalized BNT-refined horizontal form, not the literal CPSV canonical form. -/
theorem hasNoPeriodicVectors_verticalTensor (M : MPOTensor d D)
    (hM : IsMPDO M) (hYield : PeriodicVectorYieldsProjector M) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) := by
  intro n V B ρ r hV hint hirr hρ hr hfix μ hμ hnorm
  by_contra hne
  obtain ⟨p, ⟨QP⟩⟩ := hYield V B ρ r hV hint hirr hρ hr hfix μ hμ hnorm hne
  exact (isEmpty_periodicSectorProjector M hM).false QP

end MPOTensor
