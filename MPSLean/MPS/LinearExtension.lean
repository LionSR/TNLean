import MPSLean.MPS.TracePairing

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear extension of the map A i ↦ B i

This file proves two key lemmas for the Fundamental Theorem of MPS:

1. **Existence and uniqueness** of the linear extension `T` with `T(A i) = B i`,
   under the assumption that `A` is injective and `SameMPV A B`.
2. **Multiplicativity** of `T`: the SameMPV condition forces `T(MN) = T(M)T(N)`.

Both proofs use the `traceMulRightPi` machinery from `TracePairing.lean`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Lemma 1 (paper proof sketch):

If `A` is injective (its matrices span the full matrix algebra) and `A` and `B` generate the same
MPV family, then there exists a *unique* linear map `T` sending `A i` to `B i`.

The key point is that `SameMPV` provides compatibility of all trace pairings
`trace (A i * A j) = trace (B i * B j)`, which lets us construct `T` via a left inverse of the map
`M ↦ (i ↦ trace (M * B i))`.
-/
theorem linearExtension_exists_unique {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) :
    ∃! T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      (∀ i : Fin d, T (A i) = B i) := by
  classical
  let V := Matrix (Fin D) (Fin D) ℂ
  -- Shorthand for the key linear maps.
  let ΦA : V →ₗ[ℂ] (Fin d → ℂ) := traceMulRightPi (d := d) (D := D) A
  let ΦB : V →ₗ[ℂ] (Fin d → ℂ) := traceMulRightPi (d := d) (D := D) B
  let lcA : (Fin d → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ A
  let lcB : (Fin d → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ B
  have hSpanA : Submodule.span ℂ (Set.range A) = (⊤ : Submodule ℂ V) := by
    simpa [IsInjective, V] using hA
  have hSurj_lcA : Function.Surjective (Fintype.linearCombination ℂ A) := by
    -- `IsInjective` is exactly the spanning condition needed for surjectivity.
    simpa [hSpanA] using
      (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := ℂ) (v := A))
  -- The two "Gram matrix" maps `Φ ∘ lc` coincide.
  have hComp : (ΦA ∘ₗ lcA) = (ΦB ∘ₗ lcB) := by
    ext c j
    simp only [LinearMap.comp_apply, lcA, lcB, ΦA, ΦB,
      Fintype.linearCombination_apply, map_sum, map_smul, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply]
    apply Finset.sum_congr rfl; intro x _; congr 1
    exact sameMPV_trace_word2 hAB x j
  -- `range ΦA ≤ range ΦB` because `ΦA ∘ lcA = ΦB ∘ lcB` and `lcA` is surjective.
  have hRangeLe : ΦA.range ≤ ΦB.range := by
    have hTop : lcA.range = ⊤ := LinearMap.range_eq_top.2 hSurj_lcA
    calc
      ΦA.range = Submodule.map ΦA ⊤ := (LinearMap.range_eq_map ΦA)
      _ = Submodule.map ΦA lcA.range := by rw [hTop]
      _ = (ΦA ∘ₗ lcA).range := by simp [LinearMap.range_comp]
      _ = (ΦB ∘ₗ lcB).range := by rw [hComp]
      _ ≤ ΦB.range := LinearMap.range_comp_le_range lcB ΦB
  -- `ΦA` is injective, and the range inclusion forces `ΦB` to be injective too.
  have hKerΦA : ΦA.ker = ⊥ := traceMulRightPi_ker_eq_bot hA
  have hKerΦB : ΦB.ker = ⊥ := ker_bot_of_range_le ΦA ΦB hKerΦA hRangeLe
  -- Choose a left inverse `g` of `ΦB`.
  obtain ⟨g, hg⟩ := ΦB.exists_leftInverse_of_injective hKerΦB
  let T : V →ₗ[ℂ] V := g.comp ΦA
  have hT : ∀ i : Fin d, T (A i) = B i := by
    intro i
    -- First show `ΦA (A i) = ΦB (B i)` componentwise.
    have hΦ : ΦA (A i) = ΦB (B i) := by
      ext j
      -- Unfold `ΦA`/`ΦB` explicitly so `traceMulRightPi_apply` fires.
      change traceMulRightPi (d := d) (D := D) A (A i) j =
           traceMulRightPi (d := d) (D := D) B (B i) j
      simp [sameMPV_trace_word2 hAB i j]
    -- Now apply the left inverse property.
    have : (g.comp ΦB) (B i) = B i := by
      simpa using congrArg (fun f => f (B i)) hg
    calc
      T (A i) = g (ΦA (A i)) := rfl
      _ = g (ΦB (B i)) := by rw [hΦ]
      _ = (g.comp ΦB) (B i) := rfl
      _ = B i := this
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  -- Uniqueness: two linear maps agreeing on a spanning family are equal.
  apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
  intro i
  calc
    T' (A i) = B i := hT' i
    _ = T (A i) := (hT i).symm

/-- Lemma 4 (paper proof sketch, now proved):

If `T` is the linear extension with `T(A i)=B i` and `SameMPV A B`, then `T` is
multiplicative.

The proof is trace-based:

* Using `SameMPV` for length-2 words, we show
  `traceMulRightPi B (T (A i)) = traceMulRightPi A (A i)`;
  by spanning this extends to `traceMulRightPi B ∘ T = traceMulRightPi A`.
* Injectivity of `A` implies `traceMulRightPi A` is injective, hence has
  full-rank range. The range inclusion above forces `traceMulRightPi B` to
  have trivial kernel.
* Using length-3 trace identities and injectivity of `traceMulRightPi B`, we
  get `T (A i * A j) = B i * B j`, and then extend bilinearly using spanning.
-/
theorem linearExtension_mul {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B)
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : ∀ i : Fin d, T (A i) = B i) :
    ∀ M N : Matrix (Fin D) (Fin D) ℂ, T (M * N) = T M * T N := by
  classical
  let V := Matrix (Fin D) (Fin D) ℂ
  let ΦA : V →ₗ[ℂ] (Fin d → ℂ) := traceMulRightPi (d := d) (D := D) A
  let ΦB : V →ₗ[ℂ] (Fin d → ℂ) := traceMulRightPi (d := d) (D := D) B
  have hSpanA : Submodule.span ℂ (Set.range A) = (⊤ : Submodule ℂ V) := by
    simpa [IsInjective, V] using hA
  -- Trace identities for length-3 words.
  have htr3 : ∀ i j k : Fin d,
      Matrix.trace (A i * A j * A k) = Matrix.trace (B i * B j * B k) := by
    intro i j k
    have h := SameMPV.trace_evalWord (d := d) (D := D) hAB [i, j, k]
    simpa [evalWord, Matrix.mul_assoc] using h
  -- Compatibility of the trace pairing: `ΦB ∘ T = ΦA`.
  have hΦComp : (ΦB ∘ₗ T) = ΦA := by
    apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
    intro i; ext j
    -- Reduce to the length-2 trace identity.
    change traceMulRightPi (d := d) (D := D) B (T (A i)) j =
         traceMulRightPi (d := d) (D := D) A (A i) j
    simp [hT i, sameMPV_trace_word2 hAB i j]
  have hΦ_apply : ∀ M : V, ΦB (T M) = ΦA M := by
    intro M
    simpa [LinearMap.comp_apply] using congrArg (fun f => f M) hΦComp
  -- `ΦA` is injective, and `ΦA = ΦB ∘ T` forces `ΦB` to be injective too.
  have hKerΦA : ΦA.ker = ⊥ := traceMulRightPi_ker_eq_bot hA
  have hRangeLe : ΦA.range ≤ ΦB.range := by
    have : (ΦB ∘ₗ T).range ≤ ΦB.range := LinearMap.range_comp_le_range T ΦB
    simpa [hΦComp] using this
  have hKerΦB : ΦB.ker = ⊥ := ker_bot_of_range_le ΦA ΦB hKerΦA hRangeLe
  have hΦB_inj : Function.Injective ΦB := (LinearMap.ker_eq_bot).1 hKerΦB
  -- First, multiplicativity on generators.
  have hMul_gen : ∀ i j : Fin d, T (A i * A j) = B i * B j := by
    intro i j; apply hΦB_inj; ext k
    calc
      ΦB (T (A i * A j)) k
          = ΦA (A i * A j) k := by
              simpa using congrArg (· k) (hΦ_apply (A i * A j))
      _   = Matrix.trace ((A i * A j) * A k) := by
              rw [show ΦA = traceMulRightPi A from rfl, traceMulRightPi_apply]
      _   = Matrix.trace (A i * A j * A k) := by ring_nf
      _   = Matrix.trace (B i * B j * B k) := htr3 i j k
      _   = Matrix.trace ((B i * B j) * B k) := by ring_nf
      _   = ΦB (B i * B j) k := by
              rw [show ΦB = traceMulRightPi B from rfl, traceMulRightPi_apply]
  -- Extend to all right factors (first for generators, then by spanning).
  have hMul_right_gen : ∀ j : Fin d, ∀ M : V, T (M * A j) = T M * B j := by
    intro j
    have hfg :
        T.comp (LinearMap.mulRight ℂ (A j)) =
          (LinearMap.mulRight ℂ (B j)).comp T := by
      apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
      intro i
      simpa [LinearMap.comp_apply, hT i] using (hMul_gen i j)
    intro M
    simpa [LinearMap.comp_apply] using congrArg (fun f => f M) hfg
  -- Now extend to all left factors by spanning in the second argument.
  intro M N
  have hfg :
      T.comp (LinearMap.mulLeft ℂ M) =
        (LinearMap.mulLeft ℂ (T M)).comp T := by
    apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
    intro j
    simpa [LinearMap.comp_apply, hT j] using (hMul_right_gen j M)
  simpa [LinearMap.comp_apply] using congrArg (fun f => f N) hfg

end MPSTensor
