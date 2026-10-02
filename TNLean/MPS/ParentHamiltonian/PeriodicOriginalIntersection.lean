/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicPrimitiveSectorDecomposition
import TNLean.MPS.ParentHamiltonian.CyclicBlockedWordSpan
import TNLean.MPS.ParentHamiltonian.CyclicBoundaryIntersection
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockWordSpan
import TNLean.MPS.ParentHamiltonian.GaugePhaseSeparationTransport
import TNLean.MPS.ParentHamiltonian.BlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction
import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix
/-!
# Original-chain intersections of a periodic tensor

The cyclic primitive sector resolution supplies a simultaneous blocked word
span. Its embedded corner algebra is one cyclic matrix degree of the original
tensor. Left-canonical normalization propagates that span to every later
original length. Restricted boundary injectivity gives the one-step
intersection, and contiguous iteration identifies the canonical open kernels.
No divisibility condition on the original interval length is imposed.

**Scope restriction (periodic tensor presentation):** The statements concern
an explicitly supplied normalized periodic tensor. The passage from arbitrary
GVBS states to this tensor presentation is separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11),
Lemma existenceinteraction, and Section 6, lines 2649--2675;
arXiv:1708.00029, Lemma bdcf, for the cyclic sector resolution.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}
/-- Periodicity gives a cyclic projection resolution whose every sufficiently
large matrix degree is spanned by words of that original length.
Source: arXiv:1708.00029, Lemma bdcf; Nachtergaele,
arXiv:cond-mat/9410110, Section 6 and equations (3.10)--(3.11). -/
theorem IsPeriodic.exists_eventually_cyclic_wordSpan
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ P : ZMod m → Matrix (Fin D) (Fin D) ℂ,
      (∀ u, (P u).IsHermitian) ∧
      (∀ u v, P u * P v = if u = v then P u else 0) ∧
      (∑ u, P u) = 1 ∧
      (∀ u i, P u * A i = A i * P (u + 1)) ∧
      ∃ n₀, ∀ n ≥ n₀, Kraus.wordSpan A n = cyclicMatrixSubspace P n := by
  classical
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨dim, hdim, B, Q, V, ρ, hP, hρ, hDistinct, hproj, hsum, hshift,
    hiso, hV, hInt, hCoInt⟩ := hA.exists_cyclic_primitive_sector_resolution
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  let e : ZMod m ≃ Fin m := (ZMod.finEquiv m).symm.toEquiv
  let P : ZMod m → Matrix (Fin D) (Fin D) ℂ := fun u => Q (e (-u))
  have hHerm : ∀ u, (P u).IsHermitian := fun u => (hproj (e (-u))).1
  have hOrth : ∀ u v, P u * P v = if u = v then P u else 0 := by
    intro u v
    simpa only [P, Equiv.apply_eq_iff_eq, neg_inj] using
      orthogonalProjection_mul_eq_ite_of_sum_eq_one Q hproj hsum (e (-u)) (e (-v))
  have hSum : ∑ u, P u = 1 := by
    exact ((Equiv.neg (ZMod m)).trans e).sum_comp Q |>.trans hsum
  have heAdd (u : ZMod m) : e (u + 1) = e u + 1 := by
    change (ZMod.finEquiv m).symm (u + 1) = (ZMod.finEquiv m).symm u + 1
    rw [map_add, map_one]
  have hCycle : ∀ u i, P u * A i = A i * P (u + 1) := by
    intro u i
    have h := hshift (e (-(u + 1))) i
    rw [← heAdd] at h
    simpa only [P, neg_add, neg_neg, neg_add_cancel_right] using h
  have hVP : ∀ j, ∃ u : ZMod m, V j * (V j)ᴴ = P u := by
    intro j
    refine ⟨-(ZMod.finEquiv m j), ?_⟩
    change V j * (V j)ᴴ = Q ((ZMod.finEquiv m).symm (- -(ZMod.finEquiv m j)))
    rw [neg_neg, RingEquiv.symm_apply_apply, hV]
  obtain ⟨q, hq⟩ := exists_eventually_wordTupleSpanTop_of_isPrimitiveMPS B ρ hP hρ
    hDistinct.forall_ne_transport
  have hSumV : ∑ j, V j * (V j)ᴴ = 1 := by simpa only [hV] using hsum
  have hSpan := wordSpan_eq_cyclicMatrixSubspace_of_blocked_sector_span
    A P B V hiso hSumV hInt hVP hCycle (hq q le_rfl)
  exact ⟨P, hHerm, hOrth, hSum, hCycle, q * m, fun n hn =>
    wordSpan_eq_cyclicMatrixSubspace_of_ge A P hHerm hCycle hA.leftCanonical hSpan hn⟩
/-- The original boundary spaces of a periodic tensor satisfy the one-step
intersection at all sufficiently large lengths, without a residue restriction.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.11). -/
theorem IsPeriodic.exists_eventually_groundSpace_restriction_intersection
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ n₀, ∀ n ≥ n₀,
      ((⨅ b : Fin d, (groundSpace A (n + 1)).comap (restrictLastₗ b)) ⊓
        ⨅ a : Fin d, (groundSpace A (n + 1)).comap (restrictFirstₗ a)) =
        groundSpace A (n + 2) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, hP, hOrth, hSum, hCycle, n₀, hSpan⟩ := hA.exists_eventually_cyclic_wordSpan
  exact ⟨n₀, fun n hn => groundSpace_eq_restriction_intersection_of_cyclic_wordSpan
    A P hP hOrth hSum hCycle hA.leftCanonical (hSpan n hn)⟩
/-- Beyond a derived interaction range, every canonical open parent kernel is
exactly the original boundary-condition space, including the single-window
volume. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma existenceinteraction and equations (3.10)--(3.16). -/
theorem IsPeriodic.exists_ker_openParentHamiltonianES_eq_groundSpaceES
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R₀, 0 < R₀ ∧ ∀ R N, R₀ ≤ R → R ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let : NeZero d := ⟨hA.physDim_ne_zero⟩
  obtain ⟨n₀, hstep⟩ := hA.exists_eventually_groundSpace_restriction_intersection
  refine ⟨n₀ + 1, by omega, fun R N hR hRN => ?_⟩
  apply le_antisymm ?_ (groundSpaceES_le_ker_openParentHamiltonianES A R N)
  intro v hv
  apply (mem_groundSpaceES_iff A N v).mpr
  have hstep' : ∀ M, R ≤ M →
      ((⨅ b, (groundSpace A M).comap (restrictLastₗ b)) ⊓
        ⨅ a, (groundSpace A M).comap (restrictFirstₗ a)) = groundSpace A (M + 1) := by
    rintro (_ | n) hn
    · omega
    · simpa only [Nat.add_assoc] using hstep n (by omega)
  apply contiguous_mem_of_restriction_intersection_submodules
    (fun M => groundSpace A M) (by omega : 0 < R) hRN hstep'
  intro s hs τ
  let i : NonwrappingStart R N := ⟨⟨s, by omega⟩, hs⟩
  have hrestrictES := cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero
    A hRN i.1 (localTermES_eq_zero_of_openParentHamiltonianES_eq_zero A R N
      (LinearMap.mem_ker.mp hv) i) τ
  simpa [cyclicRestrictES,
    cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i.1) hRN i.2] using
    (mem_groundSpaceES_iff A R _).mp hrestrictES
/-- A periodic tensor admits a positive canonical parent interaction whose
open kernels equal its boundary spaces at every volume at least its range.
Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma existenceinteraction
and Theorem 1.1, in the explicit periodic tensor setting. -/
theorem IsPeriodic.exists_positive_parent_interaction
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES A N := by
  obtain ⟨R, hR, hKernel⟩ := hA.exists_ker_openParentHamiltonianES_eq_groundSpaceES
  refine ⟨R, hR, canonicalParentInteractionMatrix A R,
    canonicalParentInteractionMatrix_posSemidef A R, fun N hN => ?_⟩
  rw [toEuclideanLin_canonicalParentInteractionMatrix,
    openInteractionHamiltonianES_parentInteractionES A hR]
  exact hKernel R N le_rfl hN

end MPSTensor
