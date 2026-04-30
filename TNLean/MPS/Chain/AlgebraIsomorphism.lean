import TNLean.MPS.Chain.VirtualInsertion
import TNLean.MPS.Chain.Defs
import TNLean.MPS.Structure.LinearExtension
import TNLean.Algebra.SkolemNoether
/-!
# Algebra isomorphism between virtual bond algebras (Lemma 1)

For two injective MPS chains whose combined tensor generates the same MPV family,
virtual insertions on bond 0–1 are related by conjugation (Skolem–Noether).

## Overview of the proof

1. Combine the site-local tensors `A₁, A₂, A₃` into a single family
   `chainCombinedTensor A` indexed by `Fin (3 * d)` via `finProdFinEquiv`.
2. Apply the linear extension theorem (`linearExtension_exists_unique`) to
   obtain the unique linear map `T` with `T(Aₖ(σ)) = Bₖ(σ)` for all sites
   `k` and physical indices `σ`.
3. Apply `linearExtension_mul` to show `T` is multiplicative.
4. By simplicity of the matrix algebra (`linear_mul_endomorphism_bijective`),
   `T` is bijective.
5. Apply Skolem–Noether (`skolemNoether_matrix`) to extract the gauge
   matrix `W` with `T(M) = W M W⁻¹`.
6. The virtual-insertion identity follows from multiplicativity of `T` and
   trace-cyclicity.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Lemma 1
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Combined tensor for the linear-extension approach -/

/-- The combined MPS tensor for a chain: packs site index `k : Fin n` and
physical index `σ : Fin d` into a single index in `Fin (n * d)` via
`finProdFinEquiv`. This lets us apply the single-tensor `linearExtension`
construction to a non-translation-invariant chain. -/
noncomputable def chainCombinedTensor {n : ℕ} (A : Fin n → MPSTensor d D) :
    MPSTensor (n * d) D :=
  fun i => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp]
lemma chainCombinedTensor_apply {n : ℕ} (A : Fin n → MPSTensor d D)
    (k : Fin n) (σ : Fin d) :
    chainCombinedTensor A (finProdFinEquiv (k, σ)) = A k σ := by
  simp [chainCombinedTensor]

/-- If any site tensor is injective, the combined tensor is injective.
This is because `{Aₖ(σ)} ⊆ {chainCombinedTensor A (i)}`, so the
larger set spans if the smaller one does. -/
theorem chainCombinedTensor_isInjective {n : ℕ} (A : Fin n → MPSTensor d D)
    (k : Fin n) (hk : IsInjective (A k)) :
    IsInjective (chainCombinedTensor A) := by
  rw [IsInjective, eq_top_iff]
  intro M _
  have hM := hk.span_eq_top ▸ Submodule.mem_top (x := M)
  refine Submodule.span_mono ?_ hM
  intro x hx
  obtain ⟨σ, rfl⟩ := hx
  exact Set.mem_range.mpr ⟨finProdFinEquiv (k, σ), by simp [chainCombinedTensor]⟩

/-! ### The main theorem -/

/-- **Lemma 1 (arXiv:1804.04964)**: Virtual bond gauge theorem.

For two injective MPS chains whose combined tensors generate the same MPV
family (`SameMPV` on `chainCombinedTensor`), virtual insertions on bond 0–1
are related by conjugation: there exists `Z ∈ GL(D,ℂ)` such that for all `X`
and all physical configurations `σ`,
```
virtualInsertCoeff A₁ A₂ A₃ σ X = virtualInsertCoeff B₁ B₂ B₃ σ (Z⁻¹ X Z)
```

The hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`
requires trace agreement for all mixed-site words of all lengths:
`tr(A_{s₁}(σ₁) ⋯ A_{sₙ}(σₙ)) = tr(B_{s₁}(σ₁) ⋯ B_{sₙ}(σₙ))`
for arbitrary site-index sequences `s₁, …, sₙ`.

The proof constructs the linear extension `T` with `T(Aₖ(σ)) = Bₖ(σ)`,
shows it is multiplicative, promotes it to a bijective algebra endomorphism
(by simplicity of the matrix ring), and applies Skolem–Noether to extract `Z`. -/
theorem virtual_bond_gauge [NeZero D]
    (A B : Fin 3 → MPSTensor d D)
    (hA : ∀ k, IsInjective (A k)) (_hB : ∀ k, IsInjective (B k))
    (hEq : SameMPV (chainCombinedTensor A) (chainCombinedTensor B)) :
    ∃ Z : GL (Fin D) ℂ, ∀ (X : Matrix (Fin D) (Fin D) ℂ) (σ : Fin 3 → Fin d),
      virtualInsertCoeff (A 0) (A 1) (A 2) σ X =
      virtualInsertCoeff (B 0) (B 1) (B 2) σ
        ((↑Z⁻¹ : Matrix _ _ ℂ) * X * (↑Z : Matrix _ _ ℂ)) := by
  classical
  -- The combined tensor is injective (inherited from A 0).
  have hCA : IsInjective (chainCombinedTensor A) :=
    chainCombinedTensor_isInjective A 0 (hA 0)
  -- Linear extension: unique T with T(CA i) = CB i for all combined indices i.
  obtain ⟨T, hT, _⟩ := linearExtension_exists_unique hCA hEq
  -- Extract the per-site form: T(Aₖ(σ)) = Bₖ(σ).
  have hT_site : ∀ (k : Fin 3) (σ : Fin d), T (A k σ) = B k σ := by
    intro k σ
    have := hT (finProdFinEquiv (k, σ))
    simpa [chainCombinedTensor] using this
  -- T is multiplicative (from linearExtension_mul).
  have hMul : ∀ M N, T (M * N) = T M * T N :=
    linearExtension_mul hCA hEq hT
  -- T is nonzero: if T = 0 then all Bₖ(σ) = 0, contradicting injectivity of B.
  have hNz : T ≠ 0 := by
    intro hT0
    have hCBzero : ∀ i, chainCombinedTensor B i = 0 := fun i => by
      rw [← hT i, hT0]; simp
    exact trace_ne_zero_of_injective hCA hEq hCBzero
  -- T is bijective (simplicity of the matrix algebra).
  have hBij := linear_mul_endomorphism_bijective T hMul hNz
  -- Promote T to an algebra homomorphism.
  let Talg := linearMapToAlgHom T hMul hBij.2
  -- Build the algebra equivalence.
  let Tequiv : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    AlgEquiv.ofBijective Talg hBij
  -- Apply Skolem–Noether: Tequiv is conjugation by some W.
  obtain ⟨W, hW⟩ := skolemNoether_matrix Tequiv
  -- Extract T(M) = W * M * W⁻¹.
  have hTM : ∀ M, T M =
      (W : Matrix _ _ ℂ) * M * ((W⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
    intro M
    have := hW M
    change Tequiv M = _ at this
    simp only [Tequiv, AlgEquiv.ofBijective_apply, Talg] at this
    exact this
  -- trace(T(M)) = trace(M) since conjugation preserves trace.
  have hTr : ∀ M, Matrix.trace (T M) = Matrix.trace M := by
    intro M; rw [hTM M]; exact trace_conj_eq W M
  -- Provide Z = W⁻¹ as the gauge.
  refine ⟨W⁻¹, fun X σ => ?_⟩
  simp only [virtualInsertCoeff_eq, inv_inv]
  -- Goal: tr(A₀ X A₁ A₂) = tr(B₀ (W X W⁻¹) B₁ B₂)
  -- Step 1: T(A₀ X A₁ A₂) = B₀ (TX) B₁ B₂ by multiplicativity.
  have hTprod : T (A 0 (σ 0) * X * A 1 (σ 1) * A 2 (σ 2)) =
      B 0 (σ 0) * T X * B 1 (σ 1) * B 2 (σ 2) := by
    rw [hMul, hMul, hMul, hT_site 0 (σ 0), hT_site 1 (σ 1), hT_site 2 (σ 2)]
  -- Step 2: Chain the equalities using trace preservation.
  -- tr(A₀ X A₁ A₂) = tr(T(A₀ X A₁ A₂))  [trace preservation]
  --                  = tr(B₀ (TX) B₁ B₂)   [multiplicativity]
  --                  = tr(B₀ (W X W⁻¹) B₁ B₂)  [Skolem–Noether]
  rw [← hTM X, ← hTprod, hTr]

end MPSTensor
