import TNLean.MPS.Chain.VirtualInsertion
import TNLean.MPS.Chain.Defs
import TNLean.MPS.Structure.LinearExtension
import TNLean.Algebra.SkolemNoether
/-!
# Algebra isomorphism between virtual bond algebras

For two 3-site injective periodic MPS chains
`A = (A₀, A₁, A₂)` and `B = (B₀, B₁, B₂)` whose combined tensors generate
the same MPV family, the virtual-insertion coefficients on bond 0–1 are
related by conjugation through an invertible matrix `Z ∈ GL(D, ℂ)`:
$$
  \operatorname{tr}(A_0^{\sigma_0} X A_1^{\sigma_1} A_2^{\sigma_2})
  =
  \operatorname{tr}(B_0^{\sigma_0} Z^{-1} X Z B_1^{\sigma_1} B_2^{\sigma_2}).
$$
for all `X ∈ M_D(ℂ)` and physical configurations `σ`.  The proof uses the
linear extension from `SameMPV`, multiplicativity, simplicity of `M_D(ℂ)`,
and Skolem–Noether.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Lemma 1
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Combined tensor for a chain -/

/-- The combined MPS tensor for a chain: packs site index `k : Fin n` and
physical index `σ : Fin d` into a single index in `Fin (n * d)` via
`finProdFinEquiv`. -/
noncomputable def chainCombinedTensor {n : ℕ} (A : Fin n → MPSTensor d D) :
    MPSTensor (n * d) D :=
  fun i => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp]
lemma chainCombinedTensor_apply {n : ℕ} (A : Fin n → MPSTensor d D)
    (k : Fin n) (σ : Fin d) :
    chainCombinedTensor A (finProdFinEquiv (k, σ)) = A k σ := by
  simp [chainCombinedTensor]

/-- If any site tensor is injective, the combined tensor is injective. -/
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

/-- **Virtual bond gauge** (Lemma 1 of arXiv:1804.04964).

For two 3-site injective periodic MPS chains `A = (A₀, A₁, A₂)` and
`B = (B₀, B₁, B₂)` whose combined tensors generate the same MPV family,
there exists `Z ∈ GL(D, ℂ)` such that for all `X ∈ M_D(ℂ)` and all
physical configurations `σ : Fin 3 → Fin d`,
$$
  \operatorname{virtualInsertCoeff}(A_0,A_1,A_2;\sigma,X)
  =
  \operatorname{virtualInsertCoeff}(B_0,B_1,B_2;\sigma,Z^{-1}XZ).
$$
where the hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`
is trace agreement for all mixed-site words of all lengths. -/
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
