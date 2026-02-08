import MPSLean.MPS.LinearExtension
import MPSLean.MPS.SkolemNoether

/-!
# The single-block Fundamental Theorem of Matrix Product States

This file assembles the main result: if `A` is an injective MPS tensor and `B` generates the same
MPV family (`SameMPV A B`), then `A` and `B` are gauge equivalent (`GaugeEquiv A B`), i.e.
`B i = X * A i * X⁻¹` for some invertible matrix `X`.

The proof combines:

1. **Linear extension** (`LinearExtension.lean`): there is a unique linear `T` with `T(Aⁱ) = Bⁱ`,
   and `T` is multiplicative.
2. **Simplicity** (`SkolemNoether.lean`): a nonzero multiplicative endomorphism of a matrix algebra
   is bijective, so `T` is an algebra automorphism.
3. **Skolem–Noether** (`SkolemNoether.lean`): every automorphism of `Matrix n n ℂ` is inner.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

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
      rcases (linearExtension_exists_unique hA hAB) with
        ⟨T, hT, -⟩
      -- Multiplicativity.
      have hMul : ∀ M N : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ,
          T (M * N) = T M * T N :=
        linearExtension_mul hA hAB hT
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
