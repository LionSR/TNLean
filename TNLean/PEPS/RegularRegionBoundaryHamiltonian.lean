/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundarySupportedGram
import TNLean.PEPS.RegularRegionInjectivity

/-!
# Supported boundary Hamiltonians of actual regular PEPS regions

For a connected finite region of regular G-injective site tensors, the
actual open-region contraction is G-injective. Tracing its physical indices
gives a virtual Gram operator with strictly positive restriction to the
invariant boundary. Its logarithm supplies a finite Hermitian boundary
Hamiltonian, and the full Gram operator is the corresponding exponential
compressed to that support.

**Scope restriction (regular virtual spaces):** The virtual bonds have a
finite group's regular basis, the induced region is connected, and the
boundary has at least one edge. No connectedness of the complement is
needed. See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: SCP10, arXiv:1001.3807, Definition 5.1, Lemma 5.2, and the regular
boundary coordinates of Theorem 6.9, lines 1278–1358 and 2043–2076.
The finite logarithm is relevant to arXiv:1903.09439,
Conjecture `gap2Dboundary1dlocal`, lines 980–1024, but no short-range
decomposition or uniform bulk gap is asserted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The Hermitian boundary logarithm on normalized invariant coordinates
of an actual open region. Source: finite-dimensional consequence of SCP10,
Definition 5.1, Lemma 5.2, and Theorem 6.9, lines 1278–1358 and 2043–2076. -/
noncomputable def regularRegionBoundaryHamiltonian
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    Matrix (Fin n → G) (Fin n → G) ℂ :=
  regularBoundaryGramHamiltonian n (Matrix.mulVecLin (regularOpenRegionMatrix a R e))

/-- The actual region's supported boundary Hamiltonian is Hermitian.
Source: finite-dimensional boundary logarithm following SCP10,
Definition 5.1 and Theorem 6.9, lines 1278–1296 and 2043–2076. -/
theorem regularRegionBoundaryHamiltonian_isHermitian
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (regularRegionBoundaryHamiltonian a R e).IsHermitian :=
  regularBoundaryGramHamiltonian_isHermitian n _

/-- The actual regular PEPS boundary Gram operator has a supported finite
Gibbs representation whenever its region is connected. Source: consequence
of SCP10, Lemma 5.2 and Theorem 6.9, lines 1318–1358 and 2043–2076;
compare arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`. -/
theorem regularOpenRegionMatrix_gram_eq_compressed_exp_of_connected
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    {n : ℕ} (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1)) :
    (regularOpenRegionMatrix a R e).conjTranspose * regularOpenRegionMatrix a R e =
      LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n) *
        NormedSpace.exp (-regularRegionBoundaryHamiltonian a R e) *
          (LinearMap.toMatrix' (regularBoundarySupportEmbedding (G := G) n)).conjTranspose := by
  have hT := isGInjective_regularOpenRegionMatrix_of_connected a ha R hR e
  simpa only [regularRegionBoundaryHamiltonian, ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin'] using hT.regularBoundaryGram_eq_compressed_exp n

end TNLean.PEPS
