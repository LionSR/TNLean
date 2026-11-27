/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.Joint.JointMixedEndpointCoreEdges
import QICLean.Spectral.Gap.IsometricConjugationGap
import QICLean.Spectral.Gap.EuclideanSigmaFiberwiseMap
import TNLean.MPS.Tensor.Overlap

/-!
# The common ordered-pair core of the normalized joint constraint sum

The chain coordinates are Λ_L(E) × Cfg(d₀,n+1) × Λ_R(F). Regrouping them
by every ordered pair (x,y) exposes the core
Fin(D₀ x) × Cfg(d₀,n+1) × Fin(D₀ y), with exterior spectators
Fin(E x) × Fin(F y). The first and last terms are placements of the
previously constructed Φ_L and Φ_R support projectors. The middle term
is the original joint canonical open parent Hamiltonian on the middle
sites, including all shared physical directions. Entrywise identities
prove that their sum is the dependent extension of the explicit core sum.

There is at least one middle site, so the first and last edges are distinct.
The two-site chain is deliberately outside these definitions. No operator
identification with the actual physical Hamiltonian is asserted here: that
requires the separate reducing-frame and compressed-kernel results.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.

It also contains the following results.

* `MPSTensor.MPOSymmetry.jointMixedEndpoint_spectatorGap_iff`: dependent spectators for the joint
  mixed endpoint boundary coordinates.
-/

open MPTensor

namespace MPSTensor.MPOSymmetry

section JointMixedEndpointSpectatorGap

/-!
## Dependent spectators for the joint mixed endpoint boundary coordinates

For every ordered pair \((x,y)\) of block labels, the active coordinates are
\(\mathrm{Fin}(D_x^0)\times\operatorname{Cfg}(d_0,N)\times\mathrm{Fin}(D_y^0)\).
Replacing the exterior multiplicities \(D_x^0D_y^0\) by
\((D_x^0+D_x^1)(D_y^0+D_y^1)\) preserves each common nonnegative norm gap.
The first endpoint dimensions are positive; the second endpoint dimensions
are arbitrary. All ordered pairs, including distinct labels, are retained,
and the label type may be empty.

This is an operator-theoretic specialization for the boundary coordinates
used in GLM23, arXiv:2203.12563, Section 5, lines 1695–1777. Identifying the
actual endpoint Hamiltonians with extensions of one common active family is
a separate step, and is not asserted here.
-/

variable {r d₀ N : ℕ}

/-- For a fixed family of operators on the full ordered-pair active spaces,
enlarging both nonempty exterior spectator coordinates preserves exactly the
same common nonnegative norm gap. Neither positivity of the operators nor
equality of the two block labels is assumed. The label type may be empty.

Source context: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
The identification with actual endpoint Hamiltonians remains separate. -/
theorem jointMixedEndpoint_spectatorGap_iff
    (D₀ D₁ : Fin r → ℕ) (hD₀ : ∀ x, 0 < D₀ x)
    (G : ∀ q : Fin r × Fin r,
      EuclideanSpace ℂ (Fin (D₀ q.1) × Cfg d₀ N × Fin (D₀ q.2)) →L[ℂ]
        EuclideanSpace ℂ (Fin (D₀ q.1) × Cfg d₀ N × Fin (D₀ q.2)))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ v ∈ (LinearMap.ker (ContinuousLinearMap.dependentRightFiberwiseMap
        (S := fun q : Fin r × Fin r ↦ Fin (D₀ q.1) × Fin (D₀ q.2)) G).toLinearMap)ᗮ,
      δ * ‖v‖ ≤ ‖ContinuousLinearMap.dependentRightFiberwiseMap
        (S := fun q : Fin r × Fin r ↦ Fin (D₀ q.1) × Fin (D₀ q.2)) G v‖) ↔
      ∀ v ∈ (LinearMap.ker (ContinuousLinearMap.dependentRightFiberwiseMap
          (S := fun q : Fin r × Fin r ↦
            Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) G).toLinearMap)ᗮ,
        δ * ‖v‖ ≤ ‖ContinuousLinearMap.dependentRightFiberwiseMap
          (S := fun q : Fin r × Fin r ↦
            Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) G v‖ := by
  let : ∀ q : Fin r × Fin r, Nonempty (Fin (D₀ q.1) × Fin (D₀ q.2)) :=
    fun q ↦ ⟨⟨⟨0, hD₀ q.1⟩, ⟨0, hD₀ q.2⟩⟩⟩
  let : ∀ q : Fin r × Fin r,
      Nonempty (Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) :=
    fun q ↦ ⟨⟨⟨0, by have h := hD₀ q.1; omega⟩,
      ⟨0, by have h := hD₀ q.2; omega⟩⟩⟩
  exact ContinuousLinearMap.norm_gap_dependentRightFiberwiseMap_iff_dependentRightFiberwiseMap
    G hδ

end JointMixedEndpointSpectatorGap

section JointMixedEndpointCoreHamiltonian

open ContinuousLinearMap

noncomputable section

variable {r d n : ℕ} {D₀ E F : Fin r → ℕ}

/-- First normalized boundary coordinates, retaining the dependent label. -/
abbrev JointEndpointLeftIndex (D₀ E : Fin r → ℕ) :=
  (x : Fin r) × (Fin (E x) × Fin (D₀ x))

/-- Last normalized boundary coordinates, retaining the dependent label. -/
abbrev JointEndpointRightIndex (D₀ F : Fin r → ℕ) :=
  (y : Fin r) × (Fin (D₀ y) × Fin (F y))

/-- The normalized chain coordinates with arbitrary exterior dimensions. -/
abbrev JointEndpointChainCfg (d n : ℕ) (D₀ E F : Fin r → ℕ) :=
  JointEndpointLeftIndex D₀ E × Cfg d n × JointEndpointRightIndex D₀ F

/-- The common core retains every ordered pair, including distinct labels. -/
abbrev JointEndpointCoreCfg (d n : ℕ) (D₀ : Fin r → ℕ) (q : Fin r × Fin r) :=
  Fin (D₀ q.1) × Cfg d n × Fin (D₀ q.2)

/-- The full coordinate equivalence, with no restriction to diagonal pairs. -/
def jointEndpointChainSpectatorEquiv (d n : ℕ) (D₀ E F : Fin r → ℕ) :
    JointEndpointChainCfg d n D₀ E F ≃
      ((q : Fin r × Fin r) × (JointEndpointCoreCfg d n D₀ q ×
        (Fin (E q.1) × Fin (F q.2)))) where
  toFun := fun (⟨x, a, b⟩, σ, ⟨y, c, e⟩) ↦ ⟨(x, y), (b, σ, c), (a, e)⟩
  invFun := fun ⟨(x, y), (b, σ, c), (a, e)⟩ ↦ (⟨x, a, b⟩, σ, ⟨y, c, e⟩)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The ordered-pair coordinate regrouping preserves the Euclidean norm. -/
def jointEndpointChainSpectatorIsometry (d n : ℕ) (D₀ E F : Fin r → ℕ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (jointEndpointChainSpectatorEquiv d n D₀ E F)

/-- Fixing both labels and exterior registers selects the corresponding core. -/
def jointEndpointExteriorFiber
    (v : EuclideanSpace ℂ (JointEndpointChainCfg d n D₀ E F))
    (q : Fin r × Fin r) (s : Fin (E q.1) × Fin (F q.2)) :
    EuclideanSpace ℂ (JointEndpointCoreCfg d n D₀ q) :=
  WithLp.toLp 2 fun κ ↦ v (⟨q.1, s.1, κ.1⟩, κ.2.1, ⟨q.2, κ.2.2, s.2⟩)

/-- The first edge and the remaining chain coordinates, with one or more
middle sites. -/
def jointEndpointChainFirstEquiv (d n : ℕ) (D₀ E F : Fin r → ℕ) :
    JointEndpointChainCfg d (n + 1) D₀ E F ≃
      (JointEndpointLeftIndex D₀ E × Fin d) × (Cfg d n × JointEndpointRightIndex D₀ F) where
  toFun := fun (l, σ, t) ↦ ((l, σ 0), (Fin.tail σ, t))
  invFun := fun ((l, i), σ, t) ↦ (l, Fin.cons i σ, t)
  left_inv := by rintro ⟨l, σ, t⟩; simp only [Fin.cons_self_tail]
  right_inv := by rintro ⟨⟨l, i⟩, σ, t⟩; simp only [Fin.cons_zero, Fin.tail_cons]

/-- The last edge and the remaining chain coordinates. -/
def jointEndpointChainLastEquiv (d n : ℕ) (D₀ E F : Fin r → ℕ) :
    JointEndpointChainCfg d (n + 1) D₀ E F ≃
      (Fin d × JointEndpointRightIndex D₀ F) × (JointEndpointLeftIndex D₀ E × Cfg d n) where
  toFun := fun (l, σ, t) ↦ ((σ (Fin.last n), t), (l, Fin.init σ))
  invFun := fun ((i, t), l, σ) ↦ (l, Fin.snoc σ i, t)
  left_inv := by rintro ⟨l, σ, t⟩; simp only [Fin.snoc_init_self]
  right_inv := by rintro ⟨⟨i, t⟩, l, σ⟩; simp only [Fin.snoc_last, Fin.init_snoc]

/-- The original physical middle chain, with both full boundaries as spectators. -/
def jointEndpointChainBulkEquiv (d n : ℕ) (D₀ E F : Fin r → ℕ) :
    JointEndpointChainCfg d n D₀ E F ≃
      Cfg d n × (JointEndpointLeftIndex D₀ E × JointEndpointRightIndex D₀ F) where
  toFun := fun (l, σ, t) ↦ (σ, l, t)
  invFun := fun (σ, l, t) ↦ (l, σ, t)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The first core edge, retaining the opposite inner bond as a spectator. -/
def jointEndpointCoreFirstEquiv (d n : ℕ) (D₀ : Fin r → ℕ) (q : Fin r × Fin r) :
    JointEndpointCoreCfg d (n + 1) D₀ q ≃
      (Fin (D₀ q.1) × Fin d) × (Cfg d n × Fin (D₀ q.2)) where
  toFun := fun (b, σ, c) ↦ ((b, σ 0), (Fin.tail σ, c))
  invFun := fun ((b, i), σ, c) ↦ (b, Fin.cons i σ, c)
  left_inv := by rintro ⟨b, σ, c⟩; simp only [Fin.cons_self_tail]
  right_inv := by rintro ⟨⟨b, i⟩, σ, c⟩; simp only [Fin.cons_zero, Fin.tail_cons]

/-- The last core edge, retaining the opposite inner bond as a spectator. -/
def jointEndpointCoreLastEquiv (d n : ℕ) (D₀ : Fin r → ℕ) (q : Fin r × Fin r) :
    JointEndpointCoreCfg d (n + 1) D₀ q ≃
      (Fin d × Fin (D₀ q.2)) × (Fin (D₀ q.1) × Cfg d n) where
  toFun := fun (b, σ, c) ↦ ((σ (Fin.last n), c), (b, Fin.init σ))
  invFun := fun ((i, c), b, σ) ↦ (b, Fin.snoc σ i, c)
  left_inv := by rintro ⟨b, σ, c⟩; simp only [Fin.snoc_init_self]
  right_inv := by rintro ⟨⟨i, c⟩, b, σ⟩; simp only [Fin.snoc_last, Fin.init_snoc]

/-- The middle chain in a fixed ordered-pair core. -/
def jointEndpointCoreBulkEquiv (d n : ℕ) (D₀ : Fin r → ℕ) (q : Fin r × Fin r) :
    JointEndpointCoreCfg d n D₀ q ≃ Cfg d n × (Fin (D₀ q.1) × Fin (D₀ q.2)) where
  toFun := fun (b, σ, c) ↦ (σ, b, c)
  invFun := fun (σ, b, c) ↦ (b, σ, c)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

private def place {J I S : Type*} [Fintype J] [Fintype I] [Fintype S]
    (e : J ≃ I × S) (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ J →ₗ[ℂ] EuclideanSpace ℂ J :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.toLinearEquiv.conj
    (rightFiberwiseMap (S := S) T.toContinuousLinearMap).toLinearMap

private theorem place_apply {J I S : Type*} [Fintype J] [Fintype I] [Fintype S]
    (e : J ≃ I × S) (T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I)
    (v : EuclideanSpace ℂ J) (j : J) :
    place e T v j = T (WithLp.toLp 2 fun i ↦ v (e.symm (i, (e j).2))) (e j).1 := by
  have hRF (x : EuclideanSpace ℂ (I × S)) (z : I × S) :
      rightFiberwiseMap (S := S) T.toContinuousLinearMap x z =
        T (rightFiber x z.2) z.1 := by
    rcases z with ⟨i, s⟩
    exact rightFiberwiseMap_apply_apply _ x i s
  simp [place, LinearEquiv.conj_apply, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply, hRF, rightFiber]

/-- The placed first normalized constraint is the actual Φ_L range-complement
projector, with all other chain coordinates as spectators. -/
def jointEndpointNormalizedFirstTerm
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ) :
    EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F) :=
  place (jointEndpointChainFirstEquiv d n D₀ E F)
    (jointEndpointFirstEdgeCoreSupportES A E)ᗮ.starProjection.toLinearMap

/-- The placed last normalized constraint uses the actual Φ_R support. -/
def jointEndpointNormalizedLastTerm
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ) :
    EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F) :=
  place (jointEndpointChainLastEquiv d n D₀ E F)
    (jointEndpointLastEdgeCoreSupportES A F)ᗮ.starProjection.toLinearMap

/-- The whole original joint canonical middle-chain interaction sum. In
particular it uses the shared physical tensor formed from all blocks. -/
def jointEndpointNormalizedBulkTerm
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ) :
    EuclideanSpace ℂ (JointEndpointChainCfg d n D₀ E F) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointChainCfg d n D₀ E F) :=
  place (jointEndpointChainBulkEquiv d n D₀ E F)
    (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (fun _ ↦ 1) A) 2 n).hamiltonian)

/-- With exactly one middle site there is no bulk edge. Thus the shortest
chain described by the normalized sum has its two distinct boundary edges. -/
theorem jointEndpointNormalizedBulkTerm_one_eq_zero
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) :
    jointEndpointNormalizedBulkTerm A E F 1 = 0 := by
  have h0 : (parentChainInteraction (toTensorFromBlocks (fun _ ↦ 1) A) 2 1).hamiltonian = 0 :=
    Finset.sum_of_isEmpty (ι := Fin 0) _
  ext v κ
  rw [jointEndpointNormalizedBulkTerm, place_apply, h0]
  simp

/-- The first operator on an ordered-pair core uses the original left block. -/
def jointEndpointCoreFirstTerm
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (n : ℕ) (q : Fin r × Fin r) :
    EuclideanSpace ℂ (JointEndpointCoreCfg d (n + 1) D₀ q) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointCoreCfg d (n + 1) D₀ q) :=
  place (jointEndpointCoreFirstEquiv d n D₀ q) (endpointLeftCoreConstraintES (A q.1))

/-- The last operator on an ordered-pair core uses the original right block. -/
def jointEndpointCoreLastTerm
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (n : ℕ) (q : Fin r × Fin r) :
    EuclideanSpace ℂ (JointEndpointCoreCfg d (n + 1) D₀ q) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointCoreCfg d (n + 1) D₀ q) :=
  place (jointEndpointCoreLastEquiv d n D₀ q) (endpointRightCoreConstraintES (A q.2))

/-- Every core has the same original joint bulk interaction, retaining all
physical directions and all original block overlaps. -/
def jointEndpointCoreBulkTerm
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (n : ℕ) (q : Fin r × Fin r) :
    EuclideanSpace ℂ (JointEndpointCoreCfg d n D₀ q) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointCoreCfg d n D₀ q) :=
  place (jointEndpointCoreBulkEquiv d n D₀ q)
    (Matrix.toEuclideanLin
        (parentChainInteraction (toTensorFromBlocks (fun _ ↦ 1) A) 2 n).hamiltonian)

/-- The explicit common operator G_(x,y,n+1), independent of exterior
multiplicities. Its two boundary edges are distinct even when n = 0. -/
def jointEndpointCoreHamiltonian
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (n : ℕ) (q : Fin r × Fin r) :
    EuclideanSpace ℂ (JointEndpointCoreCfg d (n + 1) D₀ q) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointCoreCfg d (n + 1) D₀ q) :=
  jointEndpointCoreFirstTerm A n q + jointEndpointCoreBulkTerm A (n + 1) q +
    jointEndpointCoreLastTerm A n q

/-- The normalized constraint sum formed from the existing Φ_L and Φ_R
projectors and the unchanged joint bulk. Its physical identification is a
separate reducing-frame theorem; no such identification is assumed here. -/
def jointEndpointNormalizedSum
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ) :
    EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F) →ₗ[ℂ]
      EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F) :=
  jointEndpointNormalizedFirstTerm A E F n + jointEndpointNormalizedBulkTerm A E F (n + 1) +
    jointEndpointNormalizedLastTerm A E F n

/-- The placed Φ_L constraint acts on the left original-tensor core,
independently of the two exterior registers and the other label. -/
theorem jointEndpointNormalizedFirstTerm_apply_fiber
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ)
    (v : EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F))
    (q : Fin r × Fin r) (s : Fin (E q.1) × Fin (F q.2))
    (κ : JointEndpointCoreCfg d (n + 1) D₀ q) :
    jointEndpointNormalizedFirstTerm A E F n v
        (⟨q.1, s.1, κ.1⟩, κ.2.1, ⟨q.2, κ.2.2, s.2⟩) =
      jointEndpointCoreFirstTerm A n q (jointEndpointExteriorFiber v q s) κ := by
  rcases κ with ⟨b, σ, c⟩
  rw [jointEndpointNormalizedFirstTerm, jointEndpointCoreFirstTerm, place_apply, place_apply]
  change (jointEndpointFirstEdgeCoreSupportES A E)ᗮ.starProjection
      (WithLp.toLp 2 fun η ↦ v (η.1, Fin.cons η.2 (Fin.tail σ), ⟨q.2, c, s.2⟩))
      (⟨q.1, s.1, b⟩, σ 0) = _
  rw [jointEndpointFirstEdgeCoreConstraint_apply_fiber]
  rfl

/-- The reflected placed constraint acts on the right core block,
including for distinct left and right labels. -/
theorem jointEndpointNormalizedLastTerm_apply_fiber
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ)
    (v : EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F))
    (q : Fin r × Fin r) (s : Fin (E q.1) × Fin (F q.2))
    (κ : JointEndpointCoreCfg d (n + 1) D₀ q) :
    jointEndpointNormalizedLastTerm A E F n v
        (⟨q.1, s.1, κ.1⟩, κ.2.1, ⟨q.2, κ.2.2, s.2⟩) =
      jointEndpointCoreLastTerm A n q (jointEndpointExteriorFiber v q s) κ := by
  rcases κ with ⟨b, σ, c⟩
  rw [jointEndpointNormalizedLastTerm, jointEndpointCoreLastTerm, place_apply, place_apply]
  change (jointEndpointLastEdgeCoreSupportES A F)ᗮ.starProjection
      (WithLp.toLp 2 fun η ↦ v (⟨q.1, s.1, b⟩, Fin.snoc (Fin.init σ) η.1, η.2))
      (σ (Fin.last n), ⟨q.2, c, s.2⟩) = _
  rw [jointEndpointLastEdgeCoreConstraint_apply_fiber]
  rfl

/-- The unchanged joint bulk acts on each ordered-pair fiber in exactly
its original physical coordinates. No tensor is normalized in the bulk. -/
theorem jointEndpointNormalizedBulkTerm_apply_fiber
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ)
    (v : EuclideanSpace ℂ (JointEndpointChainCfg d n D₀ E F))
    (q : Fin r × Fin r) (s : Fin (E q.1) × Fin (F q.2))
    (κ : JointEndpointCoreCfg d n D₀ q) :
    jointEndpointNormalizedBulkTerm A E F n v
        (⟨q.1, s.1, κ.1⟩, κ.2.1, ⟨q.2, κ.2.2, s.2⟩) =
      jointEndpointCoreBulkTerm A n q (jointEndpointExteriorFiber v q s) κ := by
  rw [jointEndpointNormalizedBulkTerm, jointEndpointCoreBulkTerm, place_apply, place_apply]
  rfl

/-- The full normalized sum acts as the explicitly constructed G on every
ordered pair and exterior fiber. This follows from the three term identities. -/
theorem jointEndpointNormalizedSum_apply_fiber
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ)
    (v : EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F))
    (q : Fin r × Fin r) (s : Fin (E q.1) × Fin (F q.2))
    (κ : JointEndpointCoreCfg d (n + 1) D₀ q) :
    jointEndpointNormalizedSum A E F n v
        (⟨q.1, s.1, κ.1⟩, κ.2.1, ⟨q.2, κ.2.2, s.2⟩) =
      jointEndpointCoreHamiltonian A n q (jointEndpointExteriorFiber v q s) κ := by
  simp only [jointEndpointNormalizedSum, jointEndpointCoreHamiltonian,
    LinearMap.add_apply, PiLp.add_apply]
  rw [jointEndpointNormalizedFirstTerm_apply_fiber,
    jointEndpointNormalizedBulkTerm_apply_fiber, jointEndpointNormalizedLastTerm_apply_fiber]

/-- Isometric regrouping intertwines the normalized sum and its exact
dependent spectator extension, retaining every ordered pair. -/
theorem jointEndpointNormalizedSum_intertwines_coreSpectators
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ)
    (v : EuclideanSpace ℂ (JointEndpointChainCfg d (n + 1) D₀ E F)) :
    jointEndpointChainSpectatorIsometry d (n + 1) D₀ E F
        (jointEndpointNormalizedSum A E F n v) =
      dependentRightFiberwiseMap (S := fun q : Fin r × Fin r ↦ Fin (E q.1) × Fin (F q.2))
        (fun q ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap)
        (jointEndpointChainSpectatorIsometry d (n + 1) D₀ E F v) := by
  apply PiLp.ext
  rintro ⟨q, κ, s⟩
  change jointEndpointNormalizedSum A E F n v
      (⟨q.1, s.1, κ.1⟩, κ.2.1, ⟨q.2, κ.2.2, s.2⟩) =
    jointEndpointCoreHamiltonian A n q
      (dependentRightFiber (jointEndpointChainSpectatorIsometry d (n + 1) D₀ E F v) q s) κ
  rw [jointEndpointNormalizedSum_apply_fiber]
  rfl

/-- The normalized sum built from Φ_L, Φ_R and the original joint bulk is
unitarily equal to the dependent spectator extension of the common concrete
ordered-pair core family. Exterior and core dimensions may vanish. -/
theorem jointEndpointNormalizedSum_conj_coreSpectators
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E F : Fin r → ℕ) (n : ℕ) :
    (jointEndpointChainSpectatorIsometry d (n + 1) D₀ E F).toLinearEquiv.conj
        (jointEndpointNormalizedSum A E F n) =
      (dependentRightFiberwiseMap (S := fun q : Fin r × Fin r ↦ Fin (E q.1) × Fin (F q.2))
        (fun q ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap)).toLinearMap := by
  let U := jointEndpointChainSpectatorIsometry d (n + 1) D₀ E F
  apply LinearMap.ext
  intro v
  have h := jointEndpointNormalizedSum_intertwines_coreSpectators A E F n (U.symm v)
  change U (jointEndpointNormalizedSum A E F n (U.symm v)) =
    dependentRightFiberwiseMap (S := fun q : Fin r × Fin r ↦ Fin (E q.1) × Fin (F q.2))
      (fun q ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap) v
  change U (jointEndpointNormalizedSum A E F n (U.symm v)) =
    dependentRightFiberwiseMap (S := fun q : Fin r × Fin r ↦ Fin (E q.1) × Fin (F q.2))
      (fun q ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap) (U (U.symm v)) at h
  simpa only [U.apply_symm_apply] using h

/-- Canonical and enlarged exterior multiplicities give exactly the same
nonnegative norm gap for the explicitly constructed normalized constraint
sums. The core family is derived above; no operator identity or individual
block gap is assumed. The physical Hamiltonian bridge remains separate.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointEndpointNormalizedSum_norm_gap_iff_enlarged
    (D₀ D₁ : Fin r → ℕ) (hD₀ : ∀ x, 0 < D₀ x)
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ v ∈ (LinearMap.ker (jointEndpointNormalizedSum A D₀ D₀ n))ᗮ,
      δ * ‖v‖ ≤ ‖jointEndpointNormalizedSum A D₀ D₀ n v‖) ↔
      ∀ v ∈ (LinearMap.ker (jointEndpointNormalizedSum A
          (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x) n))ᗮ,
        δ * ‖v‖ ≤ ‖jointEndpointNormalizedSum A
          (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x) n v‖ := by
  let G := fun q : Fin r × Fin r ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap
  have hcanonical := LinearIsometryEquiv.norm_gap_iff_of_conj
    (jointEndpointChainSpectatorIsometry d (n + 1) D₀ D₀ D₀)
    (jointEndpointNormalizedSum A D₀ D₀ n)
    (dependentRightFiberwiseMap
      (S := fun q : Fin r × Fin r ↦ Fin (D₀ q.1) × Fin (D₀ q.2)) G).toLinearMap
    (jointEndpointNormalizedSum_conj_coreSpectators A D₀ D₀ n) δ
  have henlarged := LinearIsometryEquiv.norm_gap_iff_of_conj
    (jointEndpointChainSpectatorIsometry d (n + 1) D₀
      (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x))
    (jointEndpointNormalizedSum A (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x) n)
    (dependentRightFiberwiseMap (S := fun q : Fin r × Fin r ↦
      Fin (D₀ q.1 + D₁ q.1) × Fin (D₀ q.2 + D₁ q.2)) G).toLinearMap
    (jointEndpointNormalizedSum_conj_coreSpectators A
      (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x) n) δ
  exact hcanonical.trans ((jointMixedEndpoint_spectatorGap_iff D₀ D₁ hD₀ G hδ).trans
    henlarged.symm)

end

end JointMixedEndpointCoreHamiltonian

end MPSTensor.MPOSymmetry
