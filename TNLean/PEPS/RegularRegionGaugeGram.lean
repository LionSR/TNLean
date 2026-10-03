/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionGaugeContraction
import TNLean.PEPS.RegularRegionGaugeBoundary
import TNLean.PEPS.RegularRegionEntropy

/-!
# The actual Gram matrix of a region with removable regular bond operators

The actual vertex-gauge contraction identity is a permutation of the boundary
columns. When its internal residual operators are identities, local regular
isometry and connectedness therefore give a positive multiple of the transported
orthogonal boundary projector as the Gram matrix. The block Gram identity is
derived from the original contraction, rather than supplied as a hypothesis.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, the boundary
coordinate changes and isometry argument, local source lines 1765–1820 and
1935–1990.

**Scope restriction (removable internal operators):** The positive Gram and rank theorems
assume a vertex gauge with identity internal residuals. It is an auxiliary
flat-region calculation, not the unrestricted disk statement of Theorem 6.9;
the remaining source scope is recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix ComplexOrder

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G]

/-- The actual ordered twisted matrix is the reduced matrix with its columns
transported by the boundary gauge. Source: SCP10, lines 1765–1820 and 1935–1990. -/
theorem regularTwistedOpenRegionMatrix_regularRegionGauge
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) (k : {v : V // v ∈ R} → G) (u : Edge Γ → G) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularTwistedOpenRegionMatrix a u R e =
      (regularTwistedOpenRegionMatrix a (regularRegionGaugeEdgeOperators R k u) R e).submatrix
        (Equiv.refl _) (regularRegionBoundaryGaugeEquiv R k u e) := by
  funext σ x
  change openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
      (fun f => Fintype.equivFin G (x (e f))) σ =
    openRegionWeight (groupBondTensor
      (regularTwistedSite a (regularRegionGaugeEdgeOperators R k u))) R
      (fun f => Fintype.equivFin G (regularRegionBoundaryGaugeEquiv R k u e x (e f))) σ
  simp only [regularRegionBoundaryGaugeEquiv_apply]
  exact openRegionWeight_regularRegionGauge a ha R k u _ σ

/-- Identity internal residuals turn the actual twisted block into the original
untwisted block with transported columns. Source: SCP10, lines 1935–1990. -/
theorem regularTwistedOpenRegionMatrix_eq_submatrix_of_regularRegionGaugeResidual_eq_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ g v η s, a v (fun f => g * η f) s = a v η s)
    (R : Finset V) (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (hflat : ∀ f, regularRegionGaugeResidual R k u f = 1) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    regularTwistedOpenRegionMatrix a u R e =
      (regularOpenRegionMatrix a R e).submatrix
        (Equiv.refl _) (regularRegionBoundaryGaugeEquiv R k u e) := by
  funext σ x
  change openRegionWeight (groupBondTensor (regularTwistedSite a u)) R
      (fun f => Fintype.equivFin G (x (e f))) σ =
    openRegionWeight (groupBondTensor a) R
      (fun f => Fintype.equivFin G (regularRegionBoundaryGaugeEquiv R k u e x (e f))) σ
  simp only [regularRegionBoundaryGaugeEquiv_apply]
  exact openRegionWeight_eq_untwisted_of_regularRegionGaugeResidual_eq_one a ha R k u hflat _ σ

variable [DecidableEq G]

/-- Local regular isometry and connectedness give the actual positive Gram matrix
of a region whose internal bond operators are removable by a vertex gauge.
Source: SCP10, the flat-region boundary-isometry calculation, lines 1935–1990. -/
theorem exists_positive_gram_regularTwistedOpenRegionMatrix_of_regularRegionGaugeResidual_eq_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (hflat : ∀ f, regularRegionGaugeResidual R k u f = 1) {b : ℕ}
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    ∃ c : ℝ, 0 < c ∧
      (regularTwistedOpenRegionMatrix a u R e).conjTranspose *
        regularTwistedOpenRegionMatrix a u R e =
          (c : ℂ) • regularRegionGaugeBoundaryProjector R k u e := by
  obtain ⟨c, hc, hgram⟩ := exists_positive_gram_regularOpenRegionMatrix_of_connected a ha R hR e
  refine ⟨c, hc, ?_⟩
  rw [regularTwistedOpenRegionMatrix_eq_submatrix_of_regularRegionGaugeResidual_eq_one a
    (fun g v η s => (ha v).toIsGInjective.regularSiteMap_translation g η s) R k u hflat e]
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hgram,
    Matrix.submatrix_smul]
  rfl

omit [DecidableEq G] in
/-- A nonempty boundary of an actual connected region with removable internal
operators has the regular invariant rank. Source: SCP10, the boundary dimension
count in Theorem 6.9, lines 2027–2037. -/
theorem rank_regularTwistedOpenRegionMatrix_of_regularRegionGaugeResidual_eq_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (k : {v : V // v ∈ R} → G) (u : Edge Γ → G)
    (hflat : ∀ f, regularRegionGaugeResidual R k u f = 1) {b : ℕ} (hb : 0 < b)
    (e : {f : Edge Γ // IsRegionBoundaryEdge R f} ≃ Fin b) :
    (regularTwistedOpenRegionMatrix a u R e).rank = Fintype.card G ^ (b - 1) := by
  classical
  obtain ⟨c, hc, hgram⟩ :=
    exists_positive_gram_regularTwistedOpenRegionMatrix_of_regularRegionGaugeResidual_eq_one
      a ha R hR k u hflat e
  rw [← Matrix.rank_conjTranspose_mul_self, hgram,
    Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'))]
  exact rank_regularRegionGaugeBoundaryProjector R k u hb e

end TNLean.PEPS
