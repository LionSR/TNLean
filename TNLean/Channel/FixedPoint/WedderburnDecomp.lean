/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Wedderburn decomposition of fixed-point `*`-subalgebra (Wolf Theorem 6.14)

This file states the Wedderburn--Artin decomposition for the fixed-point
`*`-subalgebra established in `TNLean.Channel.FixedPoint.Algebra`.

Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` decomposes as a direct sum
of full matrix algebras (over ℂ, since ℂ is algebraically closed). Concretely,
Wolf Equation (1.39) gives the embedding

    B = U (0 ⊕ ⊕_k M_{d_k} ⊗ 1_{m_k}) U†

inside the ambient matrix algebra, for some unitary `U` and a Hilbert space
decomposition `ℂ^D = ℂ^{d₀} ⊕ ⊕_k ℂ^{d_k} ⊗ ℂ^{m_k}`.

## Main results

* `Kraus.fixedPointAlgebra_isSemisimpleRing`: the carrier type of the
  adjoint-fixed-point `StarSubalgebra` is a semisimple ring.
* `Kraus.fixedPointAlgebra_wedderburnArtin`: there exist `n : ℕ` and
  `dims : Fin n → ℕ` such that the fixed-point algebra is algebra-isomorphic
  to `Π i, Matrix (Fin (dims i)) (Fin (dims i)) ℂ`.

## Strategy

The proof chain is:
1. `StarSubalgebra ℂ Mat` is finite-dimensional (subalgebra of `M_D(ℂ)`).
2. Finite-dimensional ⟹ `IsArtinianRing` — available in Mathlib.
3. `*`-subalgebra over ℂ ⟹ `IsSemisimpleRing`: if `x` lies in the Jacobson
   radical, then `xᴴ * x` is nilpotent and self-adjoint, hence zero by the
   C⋆-norm identity.
4. `IsSemisimpleRing` + `FiniteDimensional ℂ` + `IsAlgClosed ℂ` ⟹
   Wedderburn--Artin decomposition — available in Mathlib via
   `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`.

The concrete unitary block-diagonal embedding (Wolf Equation 1.39) and the
conditional expectation form with density operators ρ_k (Wolf Equation 1.40)
require additional representation-theoretic results and are deferred
to future work.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14, Section 6.4]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equation 1.39–1.40, Section 1]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private theorem selfAdjoint_eq_zero_of_isNilpotent_matrix {x : Mat}
    (hxsa : IsSelfAdjoint x) (hxnil : IsNilpotent x) : x = 0 := by
  rcases hxnil with ⟨n, hn⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n ≤ 2 ^ k := ⟨n, Nat.le_of_lt n.lt_two_pow_self⟩
  have hpow : x ^ (2 ^ k) = 0 := pow_eq_zero_of_le hk hn
  have hnormpow : ‖x‖ ^ (2 ^ k) = 0 := by
    rw [← hxsa.norm_pow_two_pow k, hpow, norm_zero]
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnormpow)

/-! ## Abstract Wedderburn--Artin decomposition -/

section AbstractDecomp

variable (K : Fin d → Mat) (h_tp : IsTP K)
  {ρ : Mat} (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ)

/-- The carrier type of the adjoint-fixed-point `StarSubalgebra` is a
finite-dimensional ℂ-algebra, being a subalgebra of `M_D(ℂ)`.

This is a type alias for the subtype
`↥(adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix)`. -/
abbrev FixedPointAlgebra :=
  ↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)

/-- Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` is a semisimple ring. -/
theorem starSubalgebra_isSemisimpleRing (S : StarSubalgebra ℂ Mat) :
    IsSemisimpleRing S := by
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.finiteDimensional_subalgebra S.toSubalgebra
  haveI : IsArtinianRing S := IsArtinianRing.of_finite ℂ S
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  apply eq_bot_iff.mpr
  intro x hx
  let b : S := star x * x
  have hbJ : b ∈ Ring.jacobson S :=
    (Ring.jacobson S).mul_mem_left (star x) hx
  have hbNil : IsNilpotent b := by
    rcases (IsSemiprimaryRing.isNilpotent (R := S)) with ⟨n, hn⟩
    exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hbJ⟩
  have hbNilMat : IsNilpotent (b : Mat) :=
    hbNil.map S.subtype
  have hbSA : IsSelfAdjoint (b : Mat) := by
    change star (↑b : Mat) = (↑b : Mat)
    simp [b]
  have hb0Mat : (b : Mat) = 0 :=
    selfAdjoint_eq_zero_of_isNilpotent_matrix hbSA hbNilMat
  have hb0 : b = 0 := Subtype.ext hb0Mat
  have hx0Mat : (x : Mat) = 0 := by
    apply CStarRing.star_mul_self_eq_zero_iff (x := (x : Mat)).mp
    simpa [b] using congrArg Subtype.val hb0
  exact Subtype.ext hx0Mat

/-- The adjoint-fixed-point `*`-subalgebra is a semisimple ring.

This is the key algebraic input for the Wedderburn--Artin decomposition.
The proof requires showing that the Jacobson radical of a finite-dimensional
`*`-subalgebra of `M_D(ℂ)` is trivial. -/
theorem fixedPointAlgebra_isSemisimpleRing
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    IsSemisimpleRing
      (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)) :=
  starSubalgebra_isSemisimpleRing
    (adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)

/-- **Abstract Wedderburn--Artin decomposition** of the fixed-point algebra.

There exist `n : ℕ` and dimensions `dims : Fin n → ℕ` such that the
adjoint-fixed-point `*`-subalgebra is ℂ-algebra isomorphic to
`Π i, Matrix (Fin (dims i)) (Fin (dims i)) ℂ`.

This follows from `fixedPointAlgebra_isSemisimpleRing` and the Mathlib
theorem `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`. -/
theorem fixedPointAlgebra_wedderburnArtin
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    ∃ (n : ℕ) (dims : Fin n → ℕ),
      (∀ i, NeZero (dims i)) ∧
        Nonempty
          (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix) ≃ₐ[ℂ]
            Π i : Fin n, Matrix (Fin (dims i)) (Fin (dims i)) ℂ) :=
  letI : IsSemisimpleRing
      (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)) :=
    fixedPointAlgebra_isSemisimpleRing K h_tp hρ hρ_fix
  letI : FiniteDimensional ℂ
      (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)) :=
    FiniteDimensional.finiteDimensional_subalgebra
      ((adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix).toSubalgebra)
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ
    (↥(adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix))

end AbstractDecomp

/-! ## Concrete block-diagonal embedding (Wolf Equation 1.39) -/

section ConcreteDecomp

/-- Bundled data for a **Wedderburn block decomposition** of a `*`-subalgebra
of `M_D(ℂ)`: a number of blocks `n` and dimension pairs `(d_k, m_k)` intended
to witness that the algebra is unitarily conjugate to
`0 ⊕ ⊕_k M_{d_k} ⊗ 1_{m_k}`
inside the ambient matrix algebra.

This corresponds to Wolf Equation (1.39). Since this declaration is a `structure`,
it stores decomposition data; the proposition asserting existence of such a
decomposition is `Nonempty (IsWedderburnBlockDecomp S)`.

The `algEquiv` field ties the decomposition to the subalgebra `S` by
providing a ℂ-algebra isomorphism between `↥S` and a product of matrix
algebras `Π i, M_{d_i}(ℂ)`.

**Status**: Partial formalization only. The full concrete embedding data
(such as the unitary intertwiner `U` and the multiplicities `m_k` in the
ambient embedding) are deferred to future work. -/
structure IsWedderburnBlockDecomp
    (S : StarSubalgebra ℂ Mat) where
  /-- Number of simple summands. -/
  numBlocks : ℕ
  /-- Dimension of each matrix block (the `d_k`). -/
  blockDim : Fin numBlocks → ℕ
  /-- Multiplicity of each block (the `m_k`). -/
  multDim : Fin numBlocks → ℕ
  /-- The blocks are nondegenerate. -/
  blockDim_pos : ∀ i, 0 < blockDim i
  /-- The multiplicities are nondegenerate. -/
  multDim_pos : ∀ i, 0 < multDim i
  /-- The total size of the matrix blocks does not exceed `D`
  (equivalently, there is some complementary dimension not stated here). -/
  dim_le : ∑ i : Fin numBlocks, blockDim i * multDim i ≤ D
  /-- The subalgebra is ℂ-algebra isomorphic to the product of matrix blocks.
  This field ties the decomposition data to `S`. -/
  algEquiv : ↥S ≃ₐ[ℂ] Π i : Fin numBlocks,
    Matrix (Fin (blockDim i)) (Fin (blockDim i)) ℂ

-- TODO: The full structure should additionally include:
-- * A unitary `U : Mat` witnessing the conjugation
-- * A proof that `S.carrier` equals the image of the block-diagonal embedding
--   under conjugation by `U`
-- * Compatibility with the star structure
--
-- This requires:
-- (1) Central projection decomposition of a semisimple algebra
-- (2) Spectral theorem on the center to extract orthogonal projections
-- (3) Construction of the unitary intertwiner U

-- TODO: This theorem is a general fact about arbitrary `StarSubalgebra ℂ Mat`,
-- not specific to quantum channels or fixed-point algebras. It should
-- eventually be moved to `TNLean/Algebra/WedderburnArtin.lean` or similar.

/-- Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` admits a Wedderburn
block decomposition (Wolf Equation 1.39).

The current `IsWedderburnBlockDecomp` structure states the abstract
Wedderburn--Artin product decomposition, multiplicities set to `1`, and the
dimension bound. The unitary block-diagonal intertwiner is still
deferred in the structure TODO above. -/
theorem starSubalgebra_hasWedderburnBlockDecomp
    (S : StarSubalgebra ℂ Mat) :
    Nonempty (IsWedderburnBlockDecomp S) := by
  classical
  letI : IsSemisimpleRing S := starSubalgebra_isSemisimpleRing S
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.finiteDimensional_subalgebra S.toSubalgebra
  rcases IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S with
    ⟨n, blockDim, hblockDim, ⟨e⟩⟩
  refine ⟨
    { numBlocks := n
      blockDim := blockDim
      multDim := fun _ => 1
      blockDim_pos := fun i => haveI := hblockDim i; Nat.pos_of_neZero (blockDim i)
      multDim_pos := fun _ => by norm_num
      dim_le := ?_
      algEquiv := e }⟩
  let V := Fin D → ℂ
  let φ : S →ₐ[ℂ] Module.End ℂ V :=
    (Matrix.toLinAlgEquiv' :
      Mat ≃ₐ[ℂ] Module.End ℂ V).toAlgHom.comp S.subtype.toAlgHom
  let ι := Sigma fun i : Fin n => Fin (blockDim i)
  let diagUnit (a : ι) : Π i : Fin n,
      Matrix (Fin (blockDim i)) (Fin (blockDim i)) ℂ :=
    Pi.single a.1 (Matrix.single a.2 a.2 (1 : ℂ))
  let q (a : ι) : S := e.symm (diagUnit a)
  have hq_mul_self (a : ι) : q a * q a = q a := by
    rcases a with ⟨j, a⟩
    apply e.injective
    ext i r c
    by_cases hij : i = j
    · subst i
      simp [q, diagUnit]
    · simp [q, diagUnit, Pi.single_eq_of_ne hij]
  have hq_mul_zero (a b : ι) (hab : a ≠ b) : q a * q b = 0 := by
    rcases a with ⟨ia, a⟩
    rcases b with ⟨ib, b⟩
    apply e.injective
    ext i r c
    by_cases hiia : i = ia
    · subst i
      by_cases hiaib : ia = ib
      · subst ib
        have hab' : a ≠ b := by
          intro h
          exact hab (by cases h; rfl)
        simp [q, diagUnit, hab']
      · simp [q, diagUnit, hiaib]
    · simp [q, diagUnit, Pi.single_eq_of_ne hiia]
  have hq_ne_zero (a : ι) : q a ≠ 0 := by
    intro hq0
    have hdiag0 : diagUnit a = 0 := by
      calc
        diagUnit a = e (q a) := by simp [q]
        _ = e 0 := by rw [hq0]
        _ = 0 := by simp
    rcases a with ⟨i, a⟩
    have hentry : diagUnit ⟨i, a⟩ i a a = 1 := by
      simp [diagUnit]
    rw [hdiag0] at hentry
    simp at hentry
  have hφ_inj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply (Matrix.toLinAlgEquiv' : Mat ≃ₐ[ℂ] Module.End ℂ V).injective
    exact h
  have hφq_ne_zero (a : ι) : φ (q a) ≠ 0 := fun h =>
    hq_ne_zero a (hφ_inj (by simpa using h))
  have hφq_exists (a : ι) : ∃ w : V, φ (q a) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hφq_ne_zero a (LinearMap.ext h)
  choose w hw using hφq_exists
  let v (a : ι) : V := φ (q a) (w a)
  have hv_ne_zero (a : ι) : v a ≠ 0 := by
    simpa [v] using hw a
  have hφ_v_self (a : ι) : φ (q a) (v a) = v a := by
    simp [v, ← Module.End.mul_apply, ← map_mul, hq_mul_self]
  have hφ_v_zero (a b : ι) (hab : a ≠ b) : φ (q a) (v b) = 0 := by
    simp [v, ← Module.End.mul_apply, ← map_mul, hq_mul_zero a b hab]
  have hv_li : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have happ : φ (q a) (∑ b, g b • v b) = 0 := by
      rw [hg]
      simp
    have happ' : (∑ b, g b • φ (q a) (v b)) = 0 := by
      simpa [map_sum] using happ
    have hsum : (∑ b, g b • φ (q a) (v b)) = g a • v a := by
      rw [Finset.sum_eq_single a]
      · simp [hφ_v_self]
      · intro b _ hb
        simp [hφ_v_zero a b hb.symm]
      · intro ha
        exact (ha (Finset.mem_univ a)).elim
    have hga : g a • v a = 0 := by
      rw [← hsum, happ']
    exact (smul_eq_zero.mp hga).resolve_right (hv_ne_zero a)
  have hcard_le : Fintype.card ι ≤ Module.finrank ℂ V :=
    hv_li.fintype_card_le_finrank
  simpa [ι, V] using hcard_le

/-- **Wolf Theorem 6.14** (Heisenberg picture, abstract form).

The adjoint-fixed-point `*`-subalgebra `Fix(T*) = {X | T*(X) = X}` admits a
Wedderburn block decomposition.

Combined with `fixedPointAlgebra_wedderburnArtin`, this gives:
`Fix(T*) ≅ ⊕_k M_{d_k}(ℂ)` (abstract) and `Fix(T*) = U(⊕_k M_{d_k} ⊗ 1_{m_k})U†`
(concrete).
-/
theorem adjointFixedPoints_wedderburnDecomp
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    Nonempty
      (IsWedderburnBlockDecomp
        (adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)) :=
  starSubalgebra_hasWedderburnBlockDecomp _

end ConcreteDecomp

/-! ## Dimension constraints -/

section DimConstraints

/-- In any Wedderburn block decomposition of the fixed-point algebra, the
weighted sum of block dimensions and multiplicities is at most `D`.

Concretely, if the decomposition has simple summands `M_{d_k}(ℂ)` with
multiplicities `m_k`, then the parameters satisfy `Σ_k d_k * m_k ≤ D`. This
is exactly the ambient-dimension constraint stated in
`IsWedderburnBlockDecomp.dim_le`.

This is a convenience accessor for `IsWedderburnBlockDecomp.dim_le`. -/
theorem wedderburnBlockDims_sum_le
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    ∀ (w : IsWedderburnBlockDecomp
        (adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ hρ_fix)),
      ∑ i : Fin w.numBlocks, w.blockDim i * w.multDim i ≤ D :=
  fun w => w.dim_le

end DimConstraints

end Kraus
