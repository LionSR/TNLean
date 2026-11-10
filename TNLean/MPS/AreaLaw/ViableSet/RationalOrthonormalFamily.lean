/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Span
import TNLean.MPS.AreaLaw.ViableSet.OrthonormalRounding
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalTensorApproximation
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.ViabilityStability

/-!
# Rational approximation of a finite retained subspace

An orthonormal basis of the span of a finite family of matrix product states
has the finite-span bond bound. Rounding this basis gives a rational family
whose viability loss depends on the dimension of the retained subspace.
The family and its precision are chosen before the target vector.

This is an auxiliary approximation result for the finite-precision analysis
of Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
equation `eq:conv` and Claim `c:trim`, lines 472–478 and 549–559.
-/

open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- Every finite family of left-open MPS admits a rational replacement of no
larger cardinality, with an explicit common parameter height and a prescribed
viability loss. The finite-span bond bound accounts for orthonormalizing its
span; no condition on the original vectors' norms or linear dependence is needed.
The replacement is chosen before every normalized target and viability error. -/
theorem exists_rational_leftFamily_approximation_of_orthonormalization
    {L q b n : ℕ} (V : Finset (LeftBlockVector L q (n + 1))) (hk : n + 1 ≤ L)
    (hMPS : ∀ v ∈ V, IsLeftOpenMPS b v) {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) :
    let b' := V.card * max 1 b
    let θ : ℝ := ε / (2 * (V.card + 1))
    let K : ℝ := (q ^ (n + 1) : ℝ) * (max 1 (max 1 b') : ℝ) ^ (n + 2) *
      (n + 2) * 2 ^ (n + 1)
    let t := Nat.clog 2 ⌈K / θ⌉₊
    ∃ T : Finset (LeftBlockVector L q (n + 1)),
      T.card ≤ V.card ∧
      (∀ w ∈ T, Nonempty
        (RationalLeftOpenMPSRepresentationOfHeight (2 ^ (2 * t + 5)) b' w)) ∧
      ∀ (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (δ : ℝ),
        ‖Γ‖ = 1 → IsViable Γ δ (V : Set (LeftBlockVector L q (n + 1))) →
          IsViable Γ (δ + ε) (T : Set (LeftBlockVector L q (n + 1))) := by
  classical
  intro b' θ K t
  obtain ⟨r, u, hr, hu, hspan, humps⟩ :=
    exists_orthonormalBasis_isLeftOpenMPS_span V hMPS
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  choose w hrep hclose using fun j : Fin r ↦
    (humps j).exists_dyadic_rational_approximation_at_error hk (hu.norm_eq_one j) hθ
  let T := Finset.univ.image w
  have hbudget : 2 * (r : ℝ) * θ ≤ ε := by
    have hrreal : (r : ℝ) ≤ V.card := by exact_mod_cast hr
    have hrε := mul_le_mul_of_nonneg_right hrreal hε.le
    dsimp only [θ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((V.card : ℝ) + 1))).mpr
    nlinarith
  have hsmall : (r : ℝ) * θ < 1 := by nlinarith
  refine ⟨T, Finset.card_image_le.trans (by simpa using hr), ?_, ?_⟩
  · intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact hrep j
  · intro Γ δ hΓ hviable
    have huviable : IsViable Γ δ (Set.range u) := by
      obtain ⟨φ, hφ, hoverlap, hsupport⟩ := hviable
      refine ⟨φ, hφ, hoverlap, ?_⟩
      intro z
      rw [hspan]
      exact hsupport z
    have hwviable := huviable.round_orthonormal hu hΓ hθ.le hsmall hclose
    have hT : (T : Set (LeftBlockVector L q (n + 1))) = Set.range w := by
      simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hT]
    exact hwviable.mono_error (by linarith)

end TNLean.MPS.AreaLaw
