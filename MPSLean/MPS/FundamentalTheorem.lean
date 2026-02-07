import MPSLean.MPS.Defs
import MPSLean.MPS.Injective
import MPSLean.MPS.TraceNondeg

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Lemma 2 (paper proof sketch): `SameMPV` implies agreement of traces of all products.

We formulate this directly for `evalWord` on arbitrary lists. -/
lemma SameMPV.trace_evalWord {A B : MPSTensor d D} (h : SameMPV A B) (w : List (Fin d)) :
    Matrix.trace (evalWord A w) = Matrix.trace (evalWord B w) := by
  -- Use the `SameMPV` equality on the configuration `σ := w.get`.
  simpa [mpv, coeff, List.ofFn_get] using h w.length w.get

/-- Lemma 3 (helper): nondegeneracy of the trace pairing on `D×D` complex matrices. -/
lemma trace_mul_right_eq_zero {M : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ N : Matrix (Fin D) (Fin D) ℂ, Matrix.trace (M * N) = 0) : M = 0 := by
  simpa using (Matrix.trace_mul_right_eq_zero_iff (n := Fin D) M).1 h

/-!
## Linear-algebraic preparation

We will construct linear maps out of trace pairings.
-/

/-- The linear map `M ↦ (i ↦ trace (M * A i))`. -/
noncomputable def traceMulRightPi (A : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i : Fin d =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulRight ℂ (A i))

@[simp]
lemma traceMulRightPi_apply (A : MPSTensor d D)
    (M : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    traceMulRightPi (d := d) (D := D) A M i = Matrix.trace (M * A i) := by
  simp [traceMulRightPi, Matrix.traceLinearMap_apply]

/-!
## Shared helper lemmas for the linear extension construction

These factor out the repeated arguments that appear in both `linearExtension_exists_unique`
and `linearExtension_mul`.
-/

/-- `SameMPV` implies agreement of traces for all length-2 words. -/
lemma sameMPV_trace_word2 {A B : MPSTensor d D} (hAB : SameMPV A B) (i j : Fin d) :
    Matrix.trace (A i * A j) = Matrix.trace (B i * B j) := by
  have h := SameMPV.trace_evalWord (d := d) (D := D) (A := A) (B := B) hAB [i, j]
  simpa [evalWord, Matrix.mul_assoc] using h

/-- If `A` is injective, then `traceMulRightPi A` has trivial kernel.

The proof uses nondegeneracy of the trace pairing: if `trace (M * A i) = 0` for all `i`,
and the `A i` span the full matrix algebra, then `trace (M * N) = 0` for all `N`, hence `M = 0`. -/
theorem traceMulRightPi_ker_eq_bot {A : MPSTensor d D} (hA : IsInjective A) :
    (traceMulRightPi (d := d) (D := D) A).ker = ⊥ := by
  classical
  let V := Matrix (Fin D) (Fin D) ℂ
  let ΦA : V →ₗ[ℂ] (Fin d → ℂ) := traceMulRightPi (d := d) (D := D) A
  have hSpanA : Submodule.span ℂ (Set.range A) = (⊤ : Submodule ℂ V) := by
    simpa [IsInjective, V] using hA
  apply (LinearMap.ker_eq_bot').2
  intro M hM
  -- Define the linear functional `N ↦ trace (M * N)`.
  let φ : V →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ M)
  have hφ : φ = 0 := by
    apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
    intro i
    -- `φ (A i) = trace (M * A i)`, and this is `0` since `M ∈ ker ΦA`.
    have hi : Matrix.trace (M * A i) = 0 := by
      have := congrArg (fun f : Fin d → ℂ => f i) hM
      simpa [ΦA] using this
    simp [φ, hi]
  -- Use trace nondegeneracy.
  exact trace_mul_right_eq_zero (D := D) (M := M) fun N => by
    simpa [φ, Matrix.traceLinearMap_apply] using congrArg (· N) hφ

/-- If `ΦA` is injective and `range ΦA ≤ range ΦB`, then `ΦB` has trivial kernel.

This is the "finrank dance": `ker ΦA = ⊥` implies `finrank (range ΦA) = finrank V`,
and the range inclusion forces `finrank (range ΦB) ≥ finrank V`, so by rank-nullity `ker ΦB = ⊥`. -/
theorem ker_bot_of_range_le {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ΦA ΦB : V →ₗ[ℂ] W) (hKerA : ΦA.ker = ⊥) (hRange : ΦA.range ≤ ΦB.range) :
    ΦB.ker = ⊥ := by
  -- From ker ΦA = ⊥, get finrank(range ΦA) = finrank V.
  have hFinrankRangeA : Module.finrank ℂ ↥ΦA.range = Module.finrank ℂ V := by
    have hRN := LinearMap.finrank_range_add_finrank_ker (f := ΦA)
    simp [hKerA] at hRN; omega
  -- Range inclusion gives finrank(range ΦB) ≥ finrank V.
  have hFinrankRangeB_ge : Module.finrank ℂ V ≤ Module.finrank ℂ ↥ΦB.range := by
    calc Module.finrank ℂ V = Module.finrank ℂ ↥ΦA.range := hFinrankRangeA.symm
    _ ≤ Module.finrank ℂ ↥ΦB.range := Submodule.finrank_mono hRange
  -- By rank-nullity, finrank(range ΦB) ≤ finrank V, so finrank(ker ΦB) = 0.
  have hRN := LinearMap.finrank_range_add_finrank_ker (f := ΦB)
  have hle : Module.finrank ℂ ↥ΦB.range ≤ Module.finrank ℂ V := LinearMap.finrank_range_le ΦB
  have : Module.finrank ℂ ↥ΦB.ker = 0 := by omega
  exact (Submodule.finrank_eq_zero (S := ΦB.ker)).1 this

/-!
## Linear extension and multiplicativity

The next two lemmas are the key algebraic steps in the single-block Fundamental Theorem.
-/

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
    simp [ΦA, ΦB, lcA, lcB, Fintype.linearCombination_apply, Finset.sum_mul,
      Matrix.trace_sum, Matrix.trace_smul, sameMPV_trace_word2 hAB]

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
      simpa [ΦA, ΦB, sameMPV_trace_word2 hAB i j] using
        (rfl : (Matrix.trace (A i * A j)) = Matrix.trace (A i * A j))
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

If `T` is the linear extension with `T(A i)=B i` and `SameMPV A B`, then `T` is multiplicative.

The proof is trace-based:

* Using `SameMPV` for length-2 words, we show `traceMulRightPi B (T (A i)) = traceMulRightPi A (A i)`;
  by spanning this extends to `traceMulRightPi B ∘ T = traceMulRightPi A`.
* Injectivity of `A` implies `traceMulRightPi A` is injective, hence has full-rank range. The
  range inclusion above forces `traceMulRightPi B` to have trivial kernel.
* Using length-3 trace identities and injectivity of `traceMulRightPi B`, we get
  `T (A i * A j) = B i * B j`, and then extend bilinearly using spanning.
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
    have h := SameMPV.trace_evalWord (d := d) (D := D) (A := A) (B := B) hAB [i, j, k]
    simpa [evalWord, Matrix.mul_assoc] using h

  -- Compatibility of the trace pairing: `ΦB ∘ T = ΦA`.
  have hΦComp : (ΦB ∘ₗ T) = ΦA := by
    apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
    intro i
    ext j
    -- Reduce to the length-2 trace identity.
    simpa [ΦA, ΦB, LinearMap.comp_apply, hT i] using (sameMPV_trace_word2 hAB i j).symm

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
    intro i j
    apply hΦB_inj
    ext k
    calc
      ΦB (T (A i * A j)) k
          = ΦA (A i * A j) k := by
              simpa using congrArg (fun f : Fin d → ℂ => f k) (hΦ_apply (A i * A j))
      _   = Matrix.trace ((A i * A j) * A k) := by
              simp [ΦA]
      _   = Matrix.trace (A i * A j * A k) := by
              simp [Matrix.mul_assoc]
      _   = Matrix.trace (B i * B j * B k) := by
              simpa using htr3 i j k
      _   = Matrix.trace ((B i * B j) * B k) := by
              simp [Matrix.mul_assoc]
      _   = ΦB (B i * B j) k := by
              simp [ΦB]

  -- Extend to all right factors (first for generators, then by spanning).
  have hMul_right_gen : ∀ j : Fin d, ∀ M : V, T (M * A j) = T M * B j := by
    intro j
    have hfg : T.comp (LinearMap.mulRight ℂ (A j)) = (LinearMap.mulRight ℂ (B j)).comp T := by
      apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
      intro i
      simpa [LinearMap.comp_apply, hT i] using (hMul_gen i j)
    intro M
    simpa [LinearMap.comp_apply] using congrArg (fun f => f M) hfg

  -- Now extend to all left factors by spanning in the second argument.
  intro M N
  have hfg : T.comp (LinearMap.mulLeft ℂ M) = (LinearMap.mulLeft ℂ (T M)).comp T := by
    apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
    intro j
    simpa [LinearMap.comp_apply, hT j] using (hMul_right_gen j M)
  simpa [LinearMap.comp_apply] using congrArg (fun f => f N) hfg

/-- Lemma 5 (paper proof sketch, now proved):

A nonzero multiplicative `ℂ`-linear endomorphism of `D×D` matrices is bijective.

*Proof idea:* Multiplicativity makes `T` a (non-unital) ring endomorphism; its kernel is a two-sided
ideal, so by simplicity of the matrix ring it is either `⊥` or `⊤`. The latter would force
`T = 0`, hence the kernel is `⊥` and `T` is injective; finite-dimensionality upgrades injective to
surjective.
-/
theorem linear_mul_endomorphism_bijective
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hMul : ∀ M N, T (M * N) = T M * T N)
    (hNonzero : T ≠ 0) : Function.Bijective T := by
  classical
  cases D with
  | zero =>
      -- The `0×0` matrix algebra is a subsingleton, so any endomorphism is bijective.
      simpa using
        (Function.bijective_of_subsingleton
          (f := (T : Matrix (Fin 0) (Fin 0) ℂ → Matrix (Fin 0) (Fin 0) ℂ)))
  | succ D' =>
      -- Package `T` as a non-unital ring hom.
      let f :
          Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ →ₙ+*
            Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ :=
        { toFun := T
          map_zero' := by simpa using (T.map_zero)
          map_add' := by intro A B; simpa using (T.map_add A B)
          map_mul' := hMul }

      -- The kernel is either `⊥` or `⊤`; `⊤` would force `T = 0`.
      have hker : TwoSidedIdeal.ker f = ⊥ := by
        rcases (eq_bot_or_eq_top (TwoSidedIdeal.ker f)) with h | h
        · exact h
        · exact absurd (LinearMap.ext fun A => by
            simpa [f] using (TwoSidedIdeal.mem_ker (f := f)).1
              (by simpa [h] using (show A ∈ (⊤ : TwoSidedIdeal _) from by simp))) hNonzero

      exact ⟨by simpa [f] using (TwoSidedIdeal.ker_eq_bot (f := f)).1 hker,
             LinearMap.surjective_of_injective (by simpa [f] using
               (TwoSidedIdeal.ker_eq_bot (f := f)).1 hker)⟩

/-- Lemma 6 (Skolem–Noether for matrices, *proved*): any `ℂ`-algebra automorphism of
`Matrix n n ℂ` is inner.

We use the Mathlib theorem `AlgEquiv.eq_linearEquivConjAlgEquiv` on endomorphism algebras, and the
canonical algebra equivalence `Matrix.toLinAlgEquiv'`. -/
theorem skolemNoether_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (f : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) :
    ∃ X : GL n ℂ, ∀ M : Matrix n n ℂ,
      f M = (X : Matrix n n ℂ) * M * ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
  classical
  -- Transport `f` to an automorphism of endomorphisms of `n → ℂ`.
  let e : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv'
  let fEnd : Module.End ℂ (n → ℂ) ≃ₐ[ℂ] Module.End ℂ (n → ℂ) := e.symm.trans (f.trans e)
  obtain ⟨T, hT⟩ := AlgEquiv.eq_linearEquivConjAlgEquiv (f := fEnd)
  -- Turn the linear equivalence `T` into an invertible matrix `X`.
  let X : GL n ℂ :=
    (Matrix.GeneralLinearGroup.toLin (n := n) (R := ℂ)).symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv T)
  refine ⟨X, ?_⟩
  intro M
  -- We show equality after applying the algebra equivalence `e : Matrix ≃ₐ End`, and then use
  -- injectivity.
  apply e.injective
  -- First rewrite `e (f M)` using the definition of `fEnd`.
  have hfEnd : fEnd (e M) = e (f M) := by
    -- `fEnd` is defined as `e.symm ≫ f ≫ e`.
    simp [fEnd]
  -- Next rewrite `fEnd` as conjugation by `T`.
  have hconj : fEnd (e M) = (T.conjAlgEquiv ℂ) (e M) := by
    -- `hT : fEnd = T.conjAlgEquiv ℂ`.
    simpa [hT] using congrArg (fun g => g (e M)) hT
  -- Identify `e X` with the underlying linear map of `T`.
  have hX_toLin : Matrix.GeneralLinearGroup.toLin X = LinearMap.GeneralLinearGroup.ofLinearEquiv T := by
    -- By construction of `X`.
    simp [X]
  have hX_lin : e (X : Matrix n n ℂ) = (T : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
    -- `toLin` is `Units.mapEquiv` of `e.toMulEquiv`.
    -- We extract the underlying map on units and then coerce to linear maps.
    --
    -- The key simp lemma is `Units.coe_mapEquiv`.
    have := congrArg (fun u : LinearMap.GeneralLinearGroup ℂ (n → ℂ) =>
      (↑u : (n → ℂ) →ₗ[ℂ] n → ℂ)) hX_toLin
    -- Unfold `Matrix.GeneralLinearGroup.toLin`.
    --
    -- `simp` turns `toLin` into `Units.mapEquiv`, and then `Units.coe_mapEquiv` gives the coercion
    -- to endomorphisms.
    simpa [Matrix.GeneralLinearGroup.toLin, Units.coe_mapEquiv, e] using this

  have hX_lin_inv :
      e ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) = (T.symm : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
    -- First identify the inverse in the general linear groups.
    have hX_toLin_inv :
        Matrix.GeneralLinearGroup.toLin (X⁻¹) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm := by
      calc
        Matrix.GeneralLinearGroup.toLin (X⁻¹)
            = (Matrix.GeneralLinearGroup.toLin X)⁻¹ := by
                simpa using
                  (MulEquiv.map_inv (Matrix.GeneralLinearGroup.toLin (n := n) (R := ℂ)) X)
        _   = (LinearMap.GeneralLinearGroup.ofLinearEquiv T)⁻¹ := by
                simpa [hX_toLin]
        _   = LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm := by
                simpa using
                  (LinearMap.GeneralLinearGroup.ofLinearEquiv_inv (f := T)).symm
    -- Now coerce to linear maps.
    have := congrArg (fun u : LinearMap.GeneralLinearGroup ℂ (n → ℂ) =>
      (↑u : (n → ℂ) →ₗ[ℂ] n → ℂ)) hX_toLin_inv
    simpa [Matrix.GeneralLinearGroup.toLin, Units.coe_mapEquiv, e] using this

  -- Now compute both sides under `e`.
  -- Left: `e (f M)`
  -- Right: `e (X * M * X⁻¹)`
  -- Use multiplicativity of `e` and the `conjAlgEquiv` formula.
  calc
    e (f M)
        = fEnd (e M) := by simpa [hfEnd]
    _   = (T.conjAlgEquiv ℂ) (e M) := by simpa [hconj]
    _   = (T : (n → ℂ) →ₗ[ℂ] n → ℂ) ∘ₗ e M ∘ₗ (T.symm : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
          -- `conjAlgEquiv` is `x ↦ T ∘ x ∘ T⁻¹`.
          simpa [LinearEquiv.conjAlgEquiv_apply]
    _   = e (X : Matrix n n ℂ) * e M * e ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          -- Turn compositions into multiplication in `Module.End` and rewrite using `hX_lin`.
          -- (Multiplication in `Module.End` is composition.)
          simp [Module.End.mul_eq_comp, LinearMap.comp_assoc, hX_lin, hX_lin_inv]
    _   = e ((X : Matrix n n ℂ) * M * ((X⁻¹ : GL n ℂ) : Matrix n n ℂ)) := by
          -- Use multiplicativity of `e`.
          simp [mul_assoc]

/-!
## The single-block Fundamental Theorem (injective case)

In the full paper proof, the key steps are:

1. Extend the assignment `A i ↦ B i` to a linear map `T` on the whole matrix algebra (using
   spanning + compatibility).
2. Use `SameMPV` to show `T` is multiplicative.
3. Use simplicity of `Matrix (Fin D) (Fin D) ℂ` to show `T` is bijective.
4. Apply Skolem–Noether to conclude `T` is conjugation by an invertible matrix.

All four steps are fully proved as the lemmas above.
-/

/-- Build an `ℂ`-algebra homomorphism from a multiplicative `ℂ`-linear map.

The only nontrivial field is `map_one'`, which follows from surjectivity: if `T` is surjective, then
`T 1` acts as a two-sided identity on the codomain, hence must equal `1`. -/
noncomputable def linearMapToAlgHom
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hMul : ∀ M N, T (M * N) = T M * T N)
    (hSurj : Function.Surjective T) :
    Matrix (Fin D) (Fin D) ℂ →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ := by
  classical
  -- First prove `T 1 = 1`.
  have hOne : T (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    rcases hSurj (1 : Matrix (Fin D) (Fin D) ℂ) with ⟨x, hx⟩
    have : (1 : Matrix (Fin D) (Fin D) ℂ) = T 1 := by
      calc (1 : Matrix (Fin D) (Fin D) ℂ)
          = T x := hx.symm
        _ = T (x * 1) := by rw [mul_one]
        _ = T x * T 1 := hMul x 1
        _ = 1 * T 1 := by rw [hx]
        _ = T 1 := one_mul _
    exact this.symm

  -- Now package as an algebra hom.
  refine
    { toRingHom :=
        { toFun := T
          map_one' := hOne
          map_mul' := hMul
          map_zero' := by simpa using (T.map_zero)
          map_add' := by
            intro M N
            simpa using (T.map_add M N) }
      commutes' := ?_ }
  intro c
  -- `algebraMap` is `c • 1`, and `T` is `ℂ`-linear.
  simp [Algebra.algebraMap_eq_smul_one, hOne]

/-- If `T = 0` and `T(A i) = B i` with `SameMPV A B`, then `trace 1 = 0`, contradicting `D > 0`.

This is the `T ≠ 0` argument used in the single-block theorem: `T = 0` forces `B = 0`, hence
`trace (A i) = 0` for all `i`; since the `A i` span, this means `trace` vanishes on everything,
but `trace 1 = D ≠ 0`. -/
private theorem linearExtension_nonzero {A B : MPSTensor d (Nat.succ D')}
    (hA : IsInjective A) (hAB : SameMPV A B)
    {T : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ →ₗ[ℂ]
         Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ}
    (hT : ∀ i : Fin d, T (A i) = B i) : T ≠ 0 := by
  intro h0
  -- `T = 0` implies `B i = 0` for all `i`.
  have hBzero : ∀ i : Fin d, B i = 0 := fun i => by simpa [h0] using (hT i).symm
  -- Hence `trace (A i) = 0` for all `i` (from `SameMPV` on length-one words).
  have hTraceA : ∀ i : Fin d, Matrix.trace (A i) = 0 := fun i => by
    have htr := SameMPV.trace_evalWord (d := d) (D := Nat.succ D') hAB [i]
    simpa [evalWord, hBzero i] using htr
  -- The trace linear functional vanishes on a spanning set, hence on everything.
  let tr := Matrix.traceLinearMap (Fin (Nat.succ D')) ℂ ℂ
  have htr_zero : tr = 0 := by
    apply LinearMap.ext_on_range (v := A)
      (hv := by simpa [IsInjective] using hA)
    intro i; simpa [tr, Matrix.traceLinearMap_apply] using hTraceA i
  -- But `trace 1 = D' + 1 ≠ 0`.
  have : Matrix.trace (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) = 0 := by
    simpa [tr, Matrix.traceLinearMap_apply] using congrArg (· 1) htr_zero
  exact absurd this (by
    simpa [Matrix.trace_one, Fintype.card_fin] using
      (Nat.cast_ne_zero (R := ℂ) (n := Nat.succ D')).2 (Nat.succ_ne_zero D'))

/-- Single-block (injective) Fundamental Theorem of MPS:

If `A` is injective and `A` and `B` generate the same MPV family, then they are gauge equivalent,
meaning `B i = X * A i * X⁻¹` for some invertible matrix `X`. -/
theorem fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B := by
  classical
  -- The bond dimension `D = 0` is a degenerate subsingleton case.
  cases D with
  | zero =>
      refine ⟨1, ?_⟩
      intro i
      -- All `0×0` matrices are equal.
      simpa using (Subsingleton.elim (B i) (A i))
  | succ D' =>
      -- Obtain the linear extension `T` with `T (A i) = B i`.
      rcases (linearExtension_exists_unique (d := d) (D := Nat.succ D') (A := A) (B := B) hA) with
        ⟨T, hT, -⟩
      -- Multiplicativity.
      have hMul : ∀ M N : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ,
          T (M * N) = T M * T N :=
        linearExtension_mul (d := d) (D := Nat.succ D') (A := A) (B := B) hA hAB (T := T) hT
      -- `T` is nonzero: if `T = 0` then all `trace (A i) = 0`, contradicting injectivity.
      have hNonzero : T ≠ 0 := linearExtension_nonzero hA hAB hT
      have hBij : Function.Bijective T :=
        linear_mul_endomorphism_bijective (D := Nat.succ D') T hMul hNonzero
      -- Promote `T` to an algebra equivalence.
      let fHom : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ →ₐ[ℂ]
          Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ :=
        linearMapToAlgHom (D := Nat.succ D') T hMul hBij.surjective
      let f : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ ≃ₐ[ℂ]
          Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ :=
        AlgEquiv.ofBijective fHom hBij
      -- Apply Skolem–Noether.
      rcases skolemNoether_matrix (n := Fin (Nat.succ D')) f with ⟨X, hX⟩
      refine ⟨X, ?_⟩
      intro i
      -- `B i = T (A i) = f (A i) = X * A i * X⁻¹`.
      have hfi : f (A i) = B i := by
        -- `simp` uses `AlgEquiv.ofBijective_apply`.
        simpa [f, fHom] using (hT i)
      -- Use the conjugation formula from Skolem–Noether.
      simpa [hfi] using (hX (A i))

end MPSTensor
