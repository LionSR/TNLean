/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.TwoProjectionCompression
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.ExtendRight

/-!
# Open-chain ground-projector geometry

This file defines the two open-chain ground spaces in Nachtergaele's
martingale condition C3 and proves that the corresponding projector defect
implies the generic Friedrichs-angle anticommutator estimate.

**Scope restriction (Nachtergaele C3):** This file formalizes only the open-chain
projector geometry and the implication from its defect to the Friedrichs and
anticommutator bounds. The FNW numerical transfer bound controlling the defect
remains unformalized; see
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

For the increasing intervals \(\Lambda_n = [1, n]\) in arXiv:cond-mat/9410110,
eq. (2.4), the two spaces are the ground conditions on \(\Lambda_n\) and on the tail
\(\Lambda_{n+1} \setminus \Lambda_{n-l}\) inside the common ambient chain
\(\Lambda_{n+1}\). Their
intersection is the ground space on \(\Lambda_{n+1}\).

## Main results

* `MPSTensor.openChainLeftGroundSpaceES` — the left-window ground space.
* `MPSTensor.openChainTailGroundSpaceES` — the tail-window ground space.
* `MPSTensor.openChainLeft_inf_tailGroundSpaceES` — their intersection is the
  longer open-chain ground space at the block-injectivity length.
* `MPSTensor.re_inner_openChain_anticommutator_ge_neg_of_groundProjection_defect` —
  the source-facing anticommutator consequence of the C3 projector defect.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, eqs. (2.4)--(2.5), Theorem 3,
  and Section 6.
-/

open scoped InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-- The open-chain left-window ground subspace on \(L + 1\) sites.

Membership says that every restriction obtained by fixing the final site lies
in \(G_L(A)\). This is the Hilbert-space range of the projector
\(G_{\Lambda_n}\) acting in the ambient space for \(\Lambda_{n+1}\) in Nachtergaele,
arXiv:cond-mat/9410110, eq. (2.4). -/
noncomputable def openChainLeftGroundSpaceES (A : MPSTensor d D) (L : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg d (L + 1))) :=
  (⨅ j : Fin d, (groundSpace A L).comap (restrictLastₗ j)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1))).symm.toLinearMap

/-- The open-chain tail-window ground subspace on \(K + L\) sites.

Membership says that every restriction obtained by fixing the \(K\)-site prefix
lies in \(G_L(A)\). For \(L = l + 1\), this is the Hilbert-space range of
\(G_{\Lambda_{n+1} \setminus \Lambda_{n-l}}\) in Nachtergaele,
arXiv:cond-mat/9410110, eq. (2.4). -/
noncomputable def openChainTailGroundSpaceES (A : MPSTensor d D) (K L : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cfg d (K + L))) :=
  (⨅ u : Fin K → Fin d, (groundSpace A L).comap (tailRestrictₗ u)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L))).symm.toLinearMap

/-- The orthogonal projector onto the open-chain left-window ground subspace. -/
noncomputable def openChainLeftGroundProjectionES (A : MPSTensor d D) (L : ℕ) :
    EuclideanSpace ℂ (Cfg d (L + 1)) →L[ℂ] EuclideanSpace ℂ (Cfg d (L + 1)) :=
  (openChainLeftGroundSpaceES A L).starProjection

/-- The orthogonal projector onto the open-chain tail-window ground subspace. -/
noncomputable def openChainTailGroundProjectionES (A : MPSTensor d D) (K L : ℕ) :
    EuclideanSpace ℂ (Cfg d (K + L)) →L[ℂ] EuclideanSpace ℂ (Cfg d (K + L)) :=
  (openChainTailGroundSpaceES A K L).starProjection

/-- Membership in the left-window Hilbert subspace is exactly
`InLeftGround` after transport by the canonical `WithLp` equivalence. -/
@[simp] theorem mem_openChainLeftGroundSpaceES_iff (A : MPSTensor d D) (L : ℕ)
    (v : EuclideanSpace ℂ (Cfg d (L + 1))) :
    v ∈ openChainLeftGroundSpaceES A L ↔
      InLeftGround A L (WithLp.linearEquiv 2 ℂ (NSiteSpace d (L + 1)) v) := by
  rw [openChainLeftGroundSpaceES, Submodule.mem_map_equiv]
  simp [InLeftGround, restrictLast]

/-- Membership in the tail-window Hilbert subspace is exactly `InTailGround`
after transport by the canonical `WithLp` equivalence. -/
@[simp] theorem mem_openChainTailGroundSpaceES_iff (A : MPSTensor d D) (K L : ℕ)
    (v : EuclideanSpace ℂ (Cfg d (K + L))) :
    v ∈ openChainTailGroundSpaceES A K L ↔
      InTailGround A K L (WithLp.linearEquiv 2 ℂ (NSiteSpace d (K + L)) v) := by
  rw [openChainTailGroundSpaceES, Submodule.mem_map_equiv]
  simp [InTailGround]

/-- The left-window and tail-window ground spaces intersect in the longer
open-chain ground space.

With \(n = K + L₀\) and \(l = L₀\), this identifies the common range of
\(G_{\Lambda_n}\) and \(G_{\Lambda_{n+1} \setminus \Lambda_{n-l}}\) with
\(G_{\Lambda_{n+1}}\), as used in
Nachtergaele, arXiv:cond-mat/9410110, eq. (2.4). The proof is the existing
open-chain grow-back theorem at the block-injectivity length. -/
theorem openChainLeft_inf_tailGroundSpaceES [NeZero D]
    {A : MPSTensor d D} {K L₀ : ℕ} (hInj : IsNBlkInjective A L₀)
    (hL₀ : 0 < L₀) :
    openChainLeftGroundSpaceES A (K + L₀) ⊓
      openChainTailGroundSpaceES A K (L₀ + 1) =
        groundSpaceES A (K + L₀ + 1) := by
  ext v
  rw [Submodule.mem_inf, mem_openChainLeftGroundSpaceES_iff,
    mem_openChainTailGroundSpaceES_iff, mem_groundSpaceES_iff]
  constructor
  · rintro ⟨hLeft, hTail⟩
    exact groundSpace_extend_right_of_isNBlkInjective hInj hL₀ hLeft hTail
  · intro hv
    exact ⟨groundSpace_inLeftGround A (K + L₀) hv,
      groundSpace_inTailGround A K (L₀ + 1) hv⟩

set_option maxHeartbeats 800000 in
-- The expanded finite-dimensional projector statement requires extra elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
-- Finite-dimensional orthogonal-projection instances require additional synthesis budget.
/-- Nachtergaele's open-chain ground-projector defect implies the
anticommutator lower bound for the complementary excitation projections.

Here the tail projector is \(G_{\Lambda_{n+1} \setminus \Lambda_{n-l}}\), the left
projector is \(G_{\Lambda_n}\), and the subtracted projector is
\(G_{\Lambda_{n+1}}\). Thus the hypothesis is the defect appearing in condition C3,
arXiv:cond-mat/9410110, eq. (2.4),
after identifying its common ground-space range. The later FNW transfer-mixing
estimate supplies the numerical bound on this defect; it is not asserted here. -/
theorem re_inner_openChain_anticommutator_ge_neg_of_groundProjection_defect
    [NeZero D] {A : MPSTensor d D} {K L₀ : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀) {η : ℝ}
    (hDefect :
      ‖openChainTailGroundProjectionES A K (L₀ + 1) ∘L
          openChainLeftGroundProjectionES A (K + L₀) -
        (groundSpaceES A (K + L₀ + 1)).starProjection‖ ≤ η)
    (v : EuclideanSpace ℂ (Cfg d (K + L₀ + 1))) :
    -η *
        (RCLike.re
            (⟪(openChainTailGroundSpaceES A K (L₀ + 1))ᗮ.starProjection v, v⟫_ℂ) +
          RCLike.re
            (⟪(openChainLeftGroundSpaceES A (K + L₀))ᗮ.starProjection v, v⟫_ℂ)) ≤
      RCLike.re
          (⟪(openChainTailGroundSpaceES A K (L₀ + 1))ᗮ.starProjection v,
            (openChainLeftGroundSpaceES A (K + L₀))ᗮ.starProjection v⟫_ℂ) +
        RCLike.re
          (⟪(openChainLeftGroundSpaceES A (K + L₀))ᗮ.starProjection v,
            (openChainTailGroundSpaceES A K (L₀ + 1))ᗮ.starProjection v⟫_ℂ) := by
  let U := openChainTailGroundSpaceES A K (L₀ + 1)
  let V := openChainLeftGroundSpaceES A (K + L₀)
  have hInter : U ⊓ V = groundSpaceES A (K + L₀ + 1) := by
    rw [inf_comm]
    exact openChainLeft_inf_tailGroundSpaceES hInj hL₀
  have hη : 0 ≤ η := (norm_nonneg _).trans hDefect
  have hDefect' :
      ‖U.starProjection ∘L V.starProjection -
        (groundSpaceES A (K + L₀ + 1)).starProjection‖ ≤ η := by
    simpa [U, V, openChainTailGroundProjectionES,
      openChainLeftGroundProjectionES] using hDefect
  have hAngle : Submodule.IsFriedrichsBound U V η := by
    apply Submodule.isFriedrichsBound_of_norm_starProjection_comp_sub_inf_starProjection_le
    simpa only [hInter] using hDefect'
  exact
    Submodule.re_inner_anticommutator_starProjection_orthogonal_ge_neg_of_friedrichs_bound
      U V hη hAngle v

end MPSTensor
