/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.FinitePureStateDecomposition
import TNLean.MPS.ParentHamiltonian.LocalParentExpectation
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces

/-!
# Zero-energy states for positive parent interactions

Consider all normalized positive norm-one state functionals whose expectation
vanishes on every translate of a fixed local interaction. This set is convex;
when the interaction is positive, it is a face of the full state space.
The constructed MPS state belongs to this set whenever the interaction
annihilates its local MPS space. In particular, a parent interaction of a
weighted block tensor annihilates the support of every normalized sector.
No translation invariance is assumed in defining the face or its constituents.

Source: Nachtergaele, arXiv:cond-mat/9410110, lines 854--887 and Theorem 1.1;
CPGSV21, arXiv:2011.12127, lines 1996--1999. These are face and membership
properties, not a classification of all states in the face.
-/

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open SpinChain

namespace MPSTensor
variable {d R : ℕ} [NeZero d]

/-- The normalized positive states of zero expectation on every translate of
one local interaction. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 854--887, the zero-energy state face. -/
def parentGroundStateFace (h : Matrix (Cfg d R) (Cfg d R) ℂ) :
    Set (QuasiLocalAlgebra d →L[ℂ] ℂ) :=
  {φ | φ ∈ quasiLocalStateSpace d ∧
    ∀ a : ℤ, φ (quasiLocalIntervalObservable d a R h) = 0}

/-- The zero-energy state set is convex over the real numbers.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 854--887. -/
theorem convex_parentGroundStateFace (h : Matrix (Cfg d R) (Cfg d R) ℂ) :
    Convex ℝ (parentGroundStateFace h) := by
  intro φ hφ ψ hψ a b ha hb hab
  refine ⟨convex_quasiLocalStateSpace hφ.1 hψ.1 ha hb hab, fun x => ?_⟩
  simp only [add_apply, smul_apply, hφ.2 x, hψ.2 x, smul_zero, zero_add]

/-- For a positive local interaction, its zero-energy state set is a face
of the full state space. No translation invariance is imposed on the states.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 860--887. -/
theorem isExtreme_parentGroundStateFace
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hpos : h.PosSemidef) :
    IsExtreme ℝ (quasiLocalStateSpace d) (parentGroundStateFace h) := by
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.nonneg
  refine ⟨fun φ hφ => hφ.1, ?_⟩
  intro φ hφ ψ hψ ω hω hseg
  rw [openSegment_eq_image] at hseg
  obtain ⟨t, ht, hdecomp⟩ := hseg
  refine ⟨hφ, fun a => ?_⟩
  have hzero : ω (star (quasiLocalIntervalObservable d a R Y) *
      quasiLocalIntervalObservable d a R Y) = 0 := by
    simpa only [map_mul, map_star] using hω.2 a
  simpa only [map_mul, map_star] using
    quasiLocalState_left_apply_eq_zero_of_convex_decomposition φ ψ ω hφ hψ
      ht.1 ht.2 hdecomp (quasiLocalIntervalObservable d a R Y) hzero
/-- The constructed state has zero energy when the local interaction
annihilates its finite-interval MPS space. Primitivity is unnecessary.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1 and
local support equations (3.1)--(3.2b). -/
theorem quasiLocalExpectation_mem_parentGroundStateFace_of_groundSpaceES_le_ker
    {D : ℕ} (A : MPSTensor d D) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (hX : groundSpaceES A R ≤ LinearMap.ker (Matrix.toEuclideanLin h)) :
    quasiLocalExpectation A hTP hρ hfix htr ∈ parentGroundStateFace h := by
  refine ⟨quasiLocalExpectation_isState A hTP hρ hfix htr, ?_⟩
  exact fun a => quasiLocalExpectation_interval_eq_zero_of_groundSpaceES_le_ker
    A hTP hρ hfix htr a h hX

/-- Each normalized sector state belongs to the zero-energy face of every
parent interaction of the weighted block tensor with nonzero coefficients.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1;
CPGSV21, arXiv:2011.12127, lines 1996--1999. -/
theorem quasiLocalExpectation_mem_parentGroundStateFace_toTensorFromBlocks
    {b : ℕ} {dim : Fin b → ℕ} (μ : Fin b → ℂ)
    (A : (j : Fin b) → MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0) (α : Fin b)
    (hTP : ∑ i, (A α i)ᴴ * A α i = 1)
    {ρ : Matrix (Fin (dim α)) (Fin (dim α)) ℂ} (hρ : ρ.PosSemidef)
    (hfix : Kraus.transferMap (A α) ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    {h : Matrix (Cfg d R) (Cfg d R) ℂ}
    (hParent : IsParentInteraction (toTensorFromBlocks (μ := μ) A) R
      (Matrix.toEuclideanLin h)) :
    quasiLocalExpectation (A α) hTP hρ hfix htr ∈ parentGroundStateFace h := by
  apply quasiLocalExpectation_mem_parentGroundStateFace_of_groundSpaceES_le_ker
    (A α) hTP hρ hfix htr h
  rw [hParent.ker_eq]
  exact groundSpaceES_block_le_toTensorFromBlocks μ A hμ α R

end MPSTensor
