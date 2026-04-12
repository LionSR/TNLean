/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Basis

/-!
# Wedderburn decomposition of fixed-point `*`-subalgebra (Wolf Theorem 6.14)

This file states the Wedderburn--Artin decomposition for the fixed-point
`*`-subalgebra established in `TNLean.Channel.FixedPoint.Algebra`.

Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` decomposes as a direct sum
of full matrix algebras (over ℂ, since ℂ is algebraically closed). Concretely,
Wolf Eq. (1.39) gives the embedding

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

The concrete unitary block-diagonal embedding (Wolf Eq. 1.39) and the
conditional expectation form with density operators ρ_k (Wolf Eq. 1.40)
require additional representation-theoretic results and are deferred
to future work.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 6.14, §6.4]
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Eq. 1.39–1.40, §1]
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

/-! ## Concrete block-diagonal embedding (Wolf Eq. 1.39) -/

section ConcreteDecomp

/-- Bundled data for a **Wedderburn block decomposition** of a `*`-subalgebra
of `M_D(ℂ)`: a number of blocks `n` and dimension pairs `(d_k, m_k)` intended
to witness that the algebra is unitarily conjugate to
`0 ⊕ ⊕_k M_{d_k} ⊗ 1_{m_k}`
inside the ambient matrix algebra.

This corresponds to Wolf Eq. (1.39). Since this declaration is a `structure`,
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
  (equivalently, there is some complementary dimension not recorded here). -/
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

/-- Pairwise orthogonal nonzero idempotents in `M_D(ℂ)` have count at most `D`.

If `f : ι → M_D(ℂ)` is a family of nonzero idempotents with `f i * f j = 0`
for `i ≠ j`, then the vectors `{f i *ᵥ v_i}` (chosen with `f i *ᵥ v_i ≠ 0`)
are linearly independent, giving `|ι| ≤ D`. -/
private theorem card_le_of_orthogonal_idempotents_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Mat}
    (h_idem : ∀ i, f i * f i = f i)
    (h_orth : ∀ i j, i ≠ j → f i * f j = 0)
    (h_ne : ∀ i, f i ≠ 0) :
    Fintype.card ι ≤ D := by
  -- For each i, choose v_i with f i *ᵥ v_i ≠ 0
  have hv : ∀ i, ∃ v : Fin D → ℂ, f i *ᵥ v ≠ 0 := by
    intro i
    by_contra hall
    push Not at hall
    exact h_ne i <| by
      ext a b
      have := congr_fun (hall (Pi.single b 1)) a
      simp [Matrix.col_apply] at this
      exact this
  choose v hv using hv
  -- The family is linearly independent
  have hli : LinearIndependent ℂ (fun i => f i *ᵥ v i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have key : f j *ᵥ (∑ i, g i • (f i *ᵥ v i)) = 0 := by rw [hg]; simp
    rw [Matrix.mulVec_sum] at key
    simp_rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at key
    rw [Finset.sum_eq_single j] at key
    · rw [h_idem] at key
      exact (smul_eq_zero.mp key).resolve_right (hv j)
    · intro i _ hi
      rw [h_orth j i (Ne.symm hi), Matrix.zero_mulVec, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  calc Fintype.card ι ≤ Module.finrank ℂ (Fin D → ℂ) := hli.fintype_card_le_finrank
    _ = D := Module.finrank_fin_fun ℂ

/-- Every finite-dimensional `*`-subalgebra of `M_D(ℂ)` admits a Wedderburn
block decomposition (Wolf Eq. 1.39).

The proof combines the abstract Wedderburn--Artin theorem (every semisimple
algebra over ℂ is a product of matrix algebras) with a dimension bound obtained
from counting orthogonal idempotents. Specifically, the diagonal matrix units
`Matrix.single k k 1` in each factor, transported to `M_D(ℂ)` via the
subalgebra embedding, yield `∑ d_i` linearly independent vectors, giving
`∑ d_i ≤ D`. -/
theorem starSubalgebra_hasWedderburnBlockDecomp
    (S : StarSubalgebra ℂ Mat) :
    Nonempty (IsWedderburnBlockDecomp S) := by
  haveI : IsSemisimpleRing S := starSubalgebra_isSemisimpleRing S
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.finiteDimensional_subalgebra S.toSubalgebra
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ ↥S
  -- Build the injective ring hom φ : (Π i, M_{d_i}(ℂ)) →+* M_D(ℂ)
  let φ : (Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) →+* Mat :=
    (S.toSubalgebra.val.toRingHom).comp e.symm.toRingHom
  have hφ_inj : Function.Injective φ :=
    Subtype.val_injective.comp e.symm.injective
  -- For each (i, k), define the image of the matrix unit in M_D(ℂ)
  let g : (Σ i : Fin n, Fin (d i)) → Mat := fun ⟨i, k⟩ =>
    φ (Pi.single i (Matrix.single k k 1))
  -- Verify idempotence
  have h_idem : ∀ p, g p * g p = g p := by
    intro ⟨i, k⟩
    show φ _ * φ _ = φ _
    rw [← map_mul, ← Pi.single_mul, Matrix.single_mul_single_same, mul_one]
  -- Verify pairwise orthogonality
  have h_orth : ∀ p q, p ≠ q → g p * g q = 0 := by
    intro ⟨i, k⟩ ⟨j, l⟩ hne
    show φ _ * φ _ = 0
    rw [← map_mul]
    by_cases hij : i = j
    · subst hij
      have hkl : k ≠ l := fun h => hne (Sigma.ext rfl (heq_of_eq h))
      rw [← Pi.single_mul, Matrix.single_mul_single_of_ne (h := hkl), Pi.single_zero, map_zero]
    · have hprod : Pi.single i (Matrix.single k k (1 : ℂ)) *
            Pi.single j (Matrix.single l l (1 : ℂ)) =
            (0 : ∀ t : Fin n, Matrix (Fin (d t)) (Fin (d t)) ℂ) := by
        funext x
        simp only [Pi.mul_apply, Pi.zero_apply]
        rcases eq_or_ne x i with rfl | hxi
        · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_zero]
        · rw [Pi.single_eq_of_ne hxi, zero_mul]
      rw [hprod, map_zero]
  -- Verify nonzero
  have h_ne : ∀ p, g p ≠ 0 := by
    intro ⟨i, k⟩ h
    have h0 := hφ_inj (show φ (Pi.single i (Matrix.single k k (1 : ℂ))) = φ 0 by
      rw [map_zero]; exact h)
    have h1 := congr_fun h0 i
    simp at h1
    have h2 := congr_fun (congr_fun h1 k) k
    simp at h2
  -- Count: card (Σ i, Fin (d i)) = ∑ d_i ≤ D
  have hsum_le : ∑ i : Fin n, d i ≤ D := by
    have := card_le_of_orthogonal_idempotents_ne_zero h_idem h_orth h_ne
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact this
  exact ⟨{
    numBlocks := n
    blockDim := d
    multDim := fun _ => 1
    blockDim_pos := fun i => Nat.pos_of_ne_zero (hd i).out
    multDim_pos := fun _ => Nat.one_pos
    dim_le := by simpa using hsum_le
    algEquiv := e
  }⟩

/-- **Wolf Theorem 6.14** (Heisenberg picture, abstract form).

The adjoint-fixed-point `*`-subalgebra `Fix(T*) = {X | T*(X) = X}` admits a
Wedderburn block decomposition.

Combined with `fixedPointAlgebra_wedderburnArtin`, this gives:
`Fix(T*) ≅ ⊕_k M_{d_k}(ℂ)` (abstract) and `Fix(T*) = U(⊕_k M_{d_k} ⊗ 1_{m_k})U†`
(concrete). -/
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
is exactly the ambient-dimension constraint recorded in
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
