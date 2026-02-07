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

  -- From `SameMPV`, we get agreement of traces of all length-2 words.
  have htr2 : ∀ i j : Fin d, Matrix.trace (A i * A j) = Matrix.trace (B i * B j) := by
    intro i j
    have h := SameMPV.trace_evalWord (d := d) (D := D) (A := A) (B := B) hAB [i, j]
    simpa [evalWord, Matrix.mul_assoc] using h

  -- The two "Gram matrix" maps `Φ ∘ lc` coincide.
  have hComp : (ΦA ∘ₗ lcA) = (ΦB ∘ₗ lcB) := by
    ext c j
    simp [ΦA, ΦB, lcA, lcB, Fintype.linearCombination_apply, Finset.sum_mul,
      Matrix.trace_sum, Matrix.trace_smul, htr2]

  -- `ΦA` has the same range as `ΦA ∘ lcA` because `lcA` is surjective.
  have hRangeΦA : ΦA.range = (ΦA ∘ₗ lcA).range := by
    have hTop : lcA.range = ⊤ := LinearMap.range_eq_top.2 hSurj_lcA
    -- `range (ΦA ∘ lcA) = map ΦA (range lcA) = map ΦA ⊤ = range ΦA`.
    have : (ΦA ∘ₗ lcA).range = ΦA.range := by
      calc
        (ΦA ∘ₗ lcA).range = Submodule.map ΦA lcA.range := by
          simp [LinearMap.range_comp]
        _ = Submodule.map ΦA ⊤ := by
          simp [hTop]
        _ = ΦA.range := (LinearMap.range_eq_map ΦA).symm
    exact this.symm

  -- Therefore `range ΦA ≤ range ΦB`.
  have hRangeLe : ΦA.range ≤ ΦB.range := by
    calc
      ΦA.range = (ΦA ∘ₗ lcA).range := hRangeΦA
      _ = (ΦB ∘ₗ lcB).range := by
            simpa [hComp] using congrArg LinearMap.range hComp
      _ ≤ ΦB.range := LinearMap.range_comp_le_range lcB ΦB

  -- `ΦA` is injective: if `trace (M * A i) = 0` for all `i`, then `M = 0`.
  have hKerΦA : ΦA.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.2
    intro M hM
    -- Define the linear functional `N ↦ trace (M * N)`.
    let tr : V →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
    let φ : V →ₗ[ℂ] ℂ := tr.comp (LinearMap.mulLeft ℂ M)
    have hφ : φ = 0 := by
      apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
      intro i
      -- `φ (A i) = trace (M * A i)`, and this is `0` since `M ∈ ker ΦA`.
      have hi : Matrix.trace (M * A i) = 0 := by
        have := congrArg (fun f : Fin d → ℂ => f i) (show ΦA M = 0 by simpa [LinearMap.mem_ker] using hM)
        simpa [ΦA] using this
      simp [φ, tr, hi]
    have hAll : ∀ N : V, Matrix.trace (M * N) = 0 := by
      intro N
      have : φ N = 0 := by
        simp [hφ]
      simpa [φ, tr, Matrix.traceLinearMap_apply] using this
    -- Use trace nondegeneracy.
    exact trace_mul_right_eq_zero (D := D) (M := M) hAll

  have hFinrankKerΦA : Module.finrank ℂ ↥ΦA.ker = 0 := by
    have hEq : Module.finrank ℂ ↥ΦA.ker = Module.finrank ℂ ↥(⊥ : Submodule ℂ V) :=
      LinearEquiv.finrank_eq (LinearEquiv.ofEq ΦA.ker (⊥ : Submodule ℂ V) hKerΦA)
    simpa [finrank_bot] using hEq

  have hFinrankRangeΦA : Module.finrank ℂ ↥ΦA.range = Module.finrank ℂ V := by
    have hRN := LinearMap.finrank_range_add_finrank_ker (f := ΦA)
    have : Module.finrank ℂ ↥ΦA.range + 0 = Module.finrank ℂ V := by
      simpa [hFinrankKerΦA] using hRN
    simpa using this

  -- Compare finranks to conclude `ker ΦB = ⊥`.
  have hFinrankRangeLe : Module.finrank ℂ ↥ΦA.range ≤ Module.finrank ℂ ↥ΦB.range :=
    Submodule.finrank_mono (hst := hRangeLe)

  have hFinrankRangeΦB_ge : Module.finrank ℂ V ≤ Module.finrank ℂ ↥ΦB.range := by
    simpa [hFinrankRangeΦA] using hFinrankRangeLe

  have hFinrankRangeΦB_le : Module.finrank ℂ ↥ΦB.range ≤ Module.finrank ℂ V :=
    Nat.le.intro (Module.finrank ℂ ↥ΦB.ker) (LinearMap.finrank_range_add_finrank_ker (f := ΦB))

  have hFinrankRangeΦB : Module.finrank ℂ ↥ΦB.range = Module.finrank ℂ V :=
    le_antisymm hFinrankRangeΦB_le hFinrankRangeΦB_ge

  have hFinrankKerΦB : Module.finrank ℂ ↥ΦB.ker = 0 := by
    -- rank-nullity + `finrank range = finrank V`
    have hRN := LinearMap.finrank_range_add_finrank_ker (f := ΦB)
    have hRN' : Module.finrank ℂ V + Module.finrank ℂ ↥ΦB.ker = Module.finrank ℂ V := by
      simpa [hFinrankRangeΦB] using hRN
    have hRN'' : Module.finrank ℂ V + Module.finrank ℂ ↥ΦB.ker = Module.finrank ℂ V + 0 := by
      simpa using hRN'
    exact Nat.add_left_cancel hRN''

  have hKerΦB : ΦB.ker = ⊥ := (Submodule.finrank_eq_zero (S := ΦB.ker)).1 hFinrankKerΦB

  -- Choose a left inverse `g` of `ΦB`.
  obtain ⟨g, hg⟩ := ΦB.exists_leftInverse_of_injective hKerΦB
  let T : V →ₗ[ℂ] V := g.comp ΦA

  have hT : ∀ i : Fin d, T (A i) = B i := by
    intro i
    -- First show `ΦA (A i) = ΦB (B i)` componentwise.
    have hΦ : ΦA (A i) = ΦB (B i) := by
      ext j
      simpa [ΦA, ΦB, htr2 i j] using (rfl : (Matrix.trace (A i * A j)) = Matrix.trace (A i * A j))
    -- Now apply the left inverse property.
    have : (g.comp ΦB) (B i) = B i := by
      simpa using congrArg (fun f => f (B i)) hg
    calc
      T (A i) = g (ΦA (A i)) := rfl
      _ = g (ΦB (B i)) := by simpa [hΦ]
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

  -- Trace identities for length-2 and length-3 words.
  have htr2 : ∀ i j : Fin d, Matrix.trace (A i * A j) = Matrix.trace (B i * B j) := by
    intro i j
    have h := SameMPV.trace_evalWord (d := d) (D := D) (A := A) (B := B) hAB [i, j]
    simpa [evalWord, Matrix.mul_assoc] using h

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
    simpa [ΦA, ΦB, LinearMap.comp_apply, hT i] using (htr2 i j).symm

  have hΦ_apply : ∀ M : V, ΦB (T M) = ΦA M := by
    intro M
    -- Apply the linear-map equality at `M`.
    simpa [LinearMap.comp_apply] using congrArg (fun f => f M) hΦComp

  -- `ΦA` is injective (nondegeneracy of trace + spanning of `A`).
  have hKerΦA : ΦA.ker = ⊥ := by
    apply (LinearMap.ker_eq_bot').2
    intro M hM
    -- Define the linear functional `N ↦ trace (M * N)`.
    let tr : V →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
    let φ : V →ₗ[ℂ] ℂ := tr.comp (LinearMap.mulLeft ℂ M)
    have hφ : φ = 0 := by
      apply LinearMap.ext_on_range (v := A) (hv := hSpanA)
      intro i
      have hi : Matrix.trace (M * A i) = 0 := by
        have := congrArg (fun f : Fin d → ℂ => f i) hM
        simpa [ΦA] using this
      simp [φ, tr, hi]
    have hAll : ∀ N : V, Matrix.trace (M * N) = 0 := by
      intro N
      have : φ N = 0 := by
        simp [hφ]
      simpa [φ, tr, Matrix.traceLinearMap_apply] using this
    -- Use trace nondegeneracy.
    exact trace_mul_right_eq_zero (D := D) (M := M) hAll

  have hFinrankRangeΦA : Module.finrank ℂ ↥ΦA.range = Module.finrank ℂ V := by
    have hRN := LinearMap.finrank_range_add_finrank_ker (f := ΦA)
    have : Module.finrank ℂ ↥ΦA.range + 0 = Module.finrank ℂ V := by
      simpa [hKerΦA] using hRN
    simpa using this

  -- Range inclusion `range ΦA ≤ range ΦB` is immediate from `ΦA = ΦB ∘ T`.
  have hRangeLe : ΦA.range ≤ ΦB.range := by
    have : (ΦB ∘ₗ T).range ≤ ΦB.range := LinearMap.range_comp_le_range T ΦB
    simpa [hΦComp] using this

  -- Therefore `ΦB` is injective (dimension count).
  have hFinrankRangeΦB_ge : Module.finrank ℂ V ≤ Module.finrank ℂ ↥ΦB.range := by
    have hmono : Module.finrank ℂ ↥ΦA.range ≤ Module.finrank ℂ ↥ΦB.range :=
      Submodule.finrank_mono (hst := hRangeLe)
    simpa [hFinrankRangeΦA] using hmono

  have hFinrankRangeΦB_le : Module.finrank ℂ ↥ΦB.range ≤ Module.finrank ℂ V :=
    LinearMap.finrank_range_le (f := ΦB)

  have hFinrankRangeΦB : Module.finrank ℂ ↥ΦB.range = Module.finrank ℂ V :=
    le_antisymm hFinrankRangeΦB_le hFinrankRangeΦB_ge

  have hFinrankKerΦB : Module.finrank ℂ ↥ΦB.ker = 0 := by
    have hRN := LinearMap.finrank_range_add_finrank_ker (f := ΦB)
    have hRN' : Module.finrank ℂ V + Module.finrank ℂ ↥ΦB.ker = Module.finrank ℂ V := by
      simpa [hFinrankRangeΦB] using hRN
    have hRN'' : Module.finrank ℂ V + Module.finrank ℂ ↥ΦB.ker = Module.finrank ℂ V + 0 := by
      simpa using hRN'
    exact Nat.add_left_cancel hRN''

  have hKerΦB : ΦB.ker = ⊥ := (Submodule.finrank_eq_zero (S := ΦB.ker)).1 hFinrankKerΦB
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
        · have hTzero : T = 0 := by
            apply LinearMap.ext
            intro A
            have hA : f A = 0 := by
              have hAker : A ∈ TwoSidedIdeal.ker f := by
                -- `A ∈ ⊤`, then rewrite using `h : ker f = ⊤`.
                simpa [h] using (show A ∈ (⊤ : TwoSidedIdeal _) from by simp)
              exact (TwoSidedIdeal.mem_ker (f := f)).1 hAker
            simpa [f] using hA
          exact (hNonzero hTzero).elim

      have hinj : Function.Injective T := by
        -- `ker f = ⊥` implies `f` is injective.
        simpa [f] using (TwoSidedIdeal.ker_eq_bot (f := f)).1 hker

      have hsurj : Function.Surjective T :=
        LinearMap.surjective_of_injective (f := T) hinj

      exact ⟨hinj, hsurj⟩

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
  --
  -- Start from `e (f M)` and rewrite.
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

At the moment, steps (1), (2), (3) are recorded as axioms above; step (4) is proved as
`skolemNoether_matrix`.
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
    have hx' : T x = (1 : Matrix (Fin D) (Fin D) ℂ) := hx
    have hxMul : T x = T x * T (1 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa [mul_one] using (hMul x (1 : Matrix (Fin D) (Fin D) ℂ))
    have : (1 : Matrix (Fin D) (Fin D) ℂ) = (1 : Matrix (Fin D) (Fin D) ℂ) * T 1 := by
      simpa [hx'] using hxMul
    -- `1 * T 1 = T 1`.
    have : (1 : Matrix (Fin D) (Fin D) ℂ) = T (1 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa using this
    simpa using this.symm

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
      have hNonzero : T ≠ 0 := by
        intro h0
        -- Then `B i = 0` for all `i`.
        have hBzero : ∀ i : Fin d, B i = 0 := by
          intro i
          simpa [h0] using (hT i).symm
        -- Hence `trace (A i) = 0` for all `i` (from `SameMPV` on length-one words).
        have hTraceA : ∀ i : Fin d, Matrix.trace (A i) = 0 := by
          intro i
          have htr := SameMPV.trace_evalWord (d := d) (D := Nat.succ D') (A := A) (B := B) hAB [i]
          -- `evalWord A [i] = A i` and `evalWord B [i] = B i`.
          simpa [evalWord, hBzero i] using htr
        -- Consider the trace as a linear functional.
        let tr : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ →ₗ[ℂ] ℂ :=
          Matrix.traceLinearMap (Fin (Nat.succ D')) ℂ ℂ
        have hRange : Set.range A ⊆ (tr.ker : Set (Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) := by
          rintro M ⟨i, rfl⟩
          -- Show `tr (A i) = 0`.
          have : tr (A i) = 0 := by
            simpa [tr, Matrix.traceLinearMap_apply, hTraceA i]
          simpa [LinearMap.mem_ker] using this
        have hSpanLe :
            Submodule.span ℂ (Set.range A)
              ≤ (tr.ker : Submodule ℂ (Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) :=
          (Submodule.span_le.2 hRange)
        have hTopLe :
            (⊤ : Submodule ℂ (Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) ≤ tr.ker := by
          -- Rewrite the left-hand side using injectivity (`span (range A) = ⊤`).
          have hAspan :
              Submodule.span ℂ (Set.range A) =
                (⊤ : Submodule ℂ (Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) := by
            simpa [IsInjective] using hA
          -- Now the claim is exactly `hSpanLe`.
          -- (`rw [← hAspan]` turns `⊤ ≤ tr.ker` into `span (range A) ≤ tr.ker`.)
          simpa [← hAspan] using hSpanLe
        have hOneMem : (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) ∈ tr.ker :=
          hTopLe (by simp)
        have hTraceOne : Matrix.trace (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) = 0 := by
          -- Membership in the kernel means `tr 1 = 0`.
          have : tr (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) = 0 := by
            simpa [LinearMap.mem_ker] using hOneMem
          simpa [tr, Matrix.traceLinearMap_apply] using this
        -- But `trace 1 = card (Fin (succ D'))` is nonzero.
        have hCard : (Matrix.trace (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) ≠ 0 := by
          -- `trace 1 = (succ D' : ℂ)`.
          simpa [Matrix.trace_one, Fintype.card_fin] using
            (Nat.cast_ne_zero (R := ℂ) (n := Nat.succ D')).2 (Nat.succ_ne_zero D')
        exact hCard hTraceOne

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
