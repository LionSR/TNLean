import TNLean.MPS.Chain.VirtualInsertion
import TNLean.Algebra.SkolemNoether
import TNLean.Algebra.TracePairing

/-!
# Algebra isomorphism between virtual bond algebras (Lemma 1)

For two 3-site injective MPS chains generating the same state, the map
`T : M_D → M_D` defined by matching virtual-insertion coefficients is an
algebra isomorphism — hence conjugation by some invertible matrix `Z`
(Skolem–Noether).

## Overview of the proof

1. Define the "3-site trace pairing" maps `Φ_A`, `Φ_B` that send a virtual
   insertion `X` to the function `(i,j,k) ↦ tr(A₁(i) X A₂(j) A₃(k))`.
2. Show `Φ_B` is injective (using injectivity of `B₁`, `B₂`, `B₃`).
3. Show `range Φ_A ⊆ range Φ_B` (using `SameState` + decomposition maps).
4. Define `T = Φ_B⁻¹ ∘ Φ_A` and show it is multiplicative via the
   trace-pairing technique from `LinearExtension.lean`.
5. Apply `linear_mul_endomorphism_bijective` + `skolemNoether_matrix`.

## References

* [arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Lemma 1
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Three-site trace pairing maps -/

/-- The three-site trace pairing map for a triple `(A₁, A₂, A₃)` of MPS tensors:
`Φ(X)(i,j,k) = tr(A₁(i) * X * A₂(j) * A₃(k))`. This is linear in `X`. -/
noncomputable def chainTracePairing (A₁ A₂ A₃ : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin d → Fin d → Fin d → ℂ) :=
  LinearMap.pi fun i =>
    LinearMap.pi fun j =>
      LinearMap.pi fun k =>
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulRight ℂ (A₃ k)).comp
            ((LinearMap.mulRight ℂ (A₂ j)).comp
              (LinearMap.mulLeft ℂ (A₁ i))))

@[simp]
lemma chainTracePairing_apply (A₁ A₂ A₃ : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (i j k : Fin d) :
    chainTracePairing A₁ A₂ A₃ X i j k =
      Matrix.trace (A₁ i * X * A₂ j * A₃ k) := by
  simp [chainTracePairing, Matrix.traceLinearMap_apply, Matrix.mul_assoc]

/-- The three-site trace pairing is injective when all three tensors are injective.

If `Φ(Y) = 0` then for all `i,j,k`: `tr(A₁(i) Y A₂(j) A₃(k)) = 0`.
Since `A₂` and `A₃` are injective, `{A₂(j) A₃(k)}` spans `M_D`.
Hence for all `i` and all `M`: `tr(A₁(i) Y M) = 0`, giving `A₁(i) Y = 0`.
Since `{A₁(i)}` spans `M_D`, this forces `Y = 0`. -/
theorem chainTracePairing_ker_eq_bot
    {A₁ A₂ A₃ : MPSTensor d D}
    (h₁ : IsInjective A₁) (h₂ : IsInjective A₂) (h₃ : IsInjective A₃) :
    (chainTracePairing A₁ A₂ A₃).ker = ⊥ := by
  classical
  rw [LinearMap.ker_eq_bot']
  intro Y hY
  -- Step 1: For all i,j,k: tr(A₁(i) * Y * A₂(j) * A₃(k)) = 0
  have h_all : ∀ i j k, Matrix.trace (A₁ i * Y * A₂ j * A₃ k) = 0 := by
    intro i j k
    have := congrFun (congrFun (congrFun hY i) j) k
    simpa using this
  -- Step 2: For all i, for all M: tr(A₁(i) * Y * M) = 0
  have h_mid : ∀ i, ∀ M : Matrix (Fin D) (Fin D) ℂ,
      Matrix.trace (A₁ i * Y * M) = 0 := by
    intro i
    -- The map N ↦ tr(A₁(i) * Y * N) vanishes on {A₂(j) * A₃(k)}.
    -- The products {A₂(j) * A₃(k)} span M_D since A₂ and A₃ are injective.
    have hSpan23 : Submodule.span ℂ (Set.range fun (p : Fin d × Fin d) =>
        A₂ p.1 * A₃ p.2) = ⊤ := by
      rw [eq_top_iff]
      intro M _
      -- A₃ is injective so {A₃ k} spans M_D
      -- A₂ is injective so {A₂ j} spans M_D
      -- For any M, decompose as M = ∑ k, c_k • A₃ k (wrong direction, we need products)
      -- Actually: any M is in span of {A₂ j} via A₂ injective.
      -- Then A₂ j * (anything) can reach anything via A₃.
      -- Let's use that span(A₂) = ⊤ means any matrix is ∑ c_j • A₂ j
      -- and span(A₃) = ⊤ means any matrix is ∑ d_k • A₃ k
      -- So any product MN = (∑ c_j • A₂ j)(∑ d_k • A₃ k) = ∑ c_j d_k • A₂ j * A₃ k
      -- Since 1 = (∑ c_j • A₂ j) ∈ span(A₂), for any M: M = M * 1 = M * ∑ d_k • A₃ k
      -- Hmm, we need that M is in span of products.
      -- Since {A₂ j} spans ⊤ and {A₃ k} spans ⊤, the set {A₂ j * A₃ k} spans ⊤
      -- because it contains a spanning set times a spanning set, and the product of
      -- the full matrix algebra with itself is the full algebra.
      sorry
    -- The linear functional vanishes on a spanning set, hence is zero.
    apply LinearMap.ext_on_range
      (v := fun (p : Fin d × Fin d) => A₂ p.1 * A₃ p.2) (hv := hSpan23)
    intro ⟨j, k⟩
    simp [Matrix.mul_assoc, h_all i j k]
  -- Step 3: For all i: A₁(i) * Y = 0
  have h_left : ∀ i, A₁ i * Y = 0 := by
    intro i
    exact trace_mul_right_eq_zero (fun N => by rw [Matrix.mul_assoc]; exact h_mid i N)
  -- Step 4: Y = 0 since {A₁(i)} spans M_D
  exact trace_mul_right_eq_zero fun N => by
    -- tr(Y * N) = 0 because for all i: A₁(i) * Y = 0 and {A₁(i)} spans
    have hφ : (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ Y) = 0 := by
      apply LinearMap.ext_on_range (v := A₁) (hv := h₁.span_eq_top)
      intro i
      simp [Matrix.traceLinearMap_apply, h_left i]
    simpa [Matrix.traceLinearMap_apply] using congrArg (· N) hφ

/-! ### Range inclusion -/

/-- **Range inclusion**: for any `X`, the 3-site trace pairing of `A` applied to `X` is
in the range of the 3-site trace pairing of `B`, provided `A` and `B` produce
the same 3-site state and both `A₁`, `B₁` are injective.

The idea: decompose `A₁(i) * X = ∑_l c_l(i) * A₁(l)` using `A₁`'s decomposition map,
then use `SameState` to transfer to `B`, and reconstruct `Y` via `B₁`'s decomposition map. -/
theorem chainTracePairing_range_le
    {A₁ A₂ A₃ B₁ B₂ B₃ : MPSTensor d D}
    (hA₁ : IsInjective A₁) (hB₁ : IsInjective B₁)
    (hEq : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (A₁ (σ 0) * A₂ (σ 1) * A₃ (σ 2)) =
      Matrix.trace (B₁ (σ 0) * B₂ (σ 1) * B₃ (σ 2))) :
    (chainTracePairing A₁ A₂ A₃).range ≤ (chainTracePairing B₁ B₂ B₃).range := by
  classical
  -- Use the decomposition map (right inverse of linear combination) for A₁ and B₁.
  let lcA₁ := Fintype.linearCombination ℂ A₁
  let lcB₁ := Fintype.linearCombination ℂ B₁
  let ΦA := chainTracePairing A₁ A₂ A₃
  let ΦB := chainTracePairing B₁ B₂ B₃
  -- The composition ΦA ∘ lcA₁ = ΦB ∘ lcB₁ because SameState
  have hComp : ΦA.comp lcA₁ = ΦB.comp lcB₁ := by
    ext c i j k
    simp only [LinearMap.comp_apply, lcA₁, lcB₁, ΦA, ΦB,
      Fintype.linearCombination_apply, map_sum, map_smul]
    simp only [chainTracePairing_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro l _
    congr 1
    have := hEq (fun idx => Fin.cons l (Fin.cons j (Fin.cons k Fin.elim0)) idx)
    simp at this
    exact this
  -- Since lcA₁ is surjective (A₁ injective), range ΦA = range (ΦA ∘ lcA₁)
  rw [show ΦA.range = (ΦA.comp lcA₁).range from by
    simp [LinearMap.range_comp, LinearMap.range_eq_top.2 hA₁.linearCombination_surjective],
    hComp]
  exact LinearMap.range_comp_le_range lcB₁ ΦB

/-! ### The cross-chain transfer map -/

/-- The cross-chain transfer map `T : M_D → M_D`, defined as `Φ_B⁻¹ ∘ Φ_A`
where `Φ_A`, `Φ_B` are the 3-site trace pairing maps. -/
noncomputable def crossChainTransfer
    (A₁ A₂ A₃ B₁ B₂ B₃ : MPSTensor d D)
    (hB₁ : IsInjective B₁) (hB₂ : IsInjective B₂) (hB₃ : IsInjective B₃)
    (hA₁ : IsInjective A₁)
    (hEq : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (A₁ (σ 0) * A₂ (σ 1) * A₃ (σ 2)) =
      Matrix.trace (B₁ (σ 0) * B₂ (σ 1) * B₃ (σ 2))) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ := by
  classical
  let ΦA := chainTracePairing A₁ A₂ A₃
  let ΦB := chainTracePairing B₁ B₂ B₃
  have hKerΦB : ΦB.ker = ⊥ := chainTracePairing_ker_eq_bot hB₁ hB₂ hB₃
  obtain ⟨g, hg⟩ := ΦB.exists_leftInverse_of_injective hKerΦB
  exact g.comp ΦA

/-- The cross-chain transfer map satisfies `Φ_B(T(X)) = Φ_A(X)`. -/
theorem crossChainTransfer_spec
    {A₁ A₂ A₃ B₁ B₂ B₃ : MPSTensor d D}
    (hB₁ : IsInjective B₁) (hB₂ : IsInjective B₂) (hB₃ : IsInjective B₃)
    (hA₁ : IsInjective A₁)
    (hEq : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (A₁ (σ 0) * A₂ (σ 1) * A₃ (σ 2)) =
      Matrix.trace (B₁ (σ 0) * B₂ (σ 1) * B₃ (σ 2)))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    ∀ i j k : Fin d,
      Matrix.trace (B₁ i * crossChainTransfer A₁ A₂ A₃ B₁ B₂ B₃ hB₁ hB₂ hB₃ hA₁ hEq X *
        B₂ j * B₃ k) =
      Matrix.trace (A₁ i * X * A₂ j * A₃ k) := by
  sorry

/-! ### Multiplicativity of the transfer map -/

/-- The cross-chain transfer map is multiplicative:
`T(M * N) = T(M) * T(N)`.

The proof follows the trace-pairing technique from `linearExtension_mul`:
1. Show `T(A₂(j) * A₃(k)) = B₂(j) * B₃(k)` from `SameState`.
2. Extend to `T(M * A₃(k)) = T(M) * B₃(k)` by spanning.
3. Extend to `T(M * N) = T(M) * T(N)` by spanning. -/
theorem crossChainTransfer_mul
    {A₁ A₂ A₃ B₁ B₂ B₃ : MPSTensor d D}
    (hA₁ : IsInjective A₁) (hA₂ : IsInjective A₂) (hA₃ : IsInjective A₃)
    (hB₁ : IsInjective B₁) (hB₂ : IsInjective B₂) (hB₃ : IsInjective B₃)
    (hEq : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (A₁ (σ 0) * A₂ (σ 1) * A₃ (σ 2)) =
      Matrix.trace (B₁ (σ 0) * B₂ (σ 1) * B₃ (σ 2))) :
    let T := crossChainTransfer A₁ A₂ A₃ B₁ B₂ B₃ hB₁ hB₂ hB₃ hA₁ hEq
    ∀ M N : Matrix (Fin D) (Fin D) ℂ, T (M * N) = T M * T N := by
  sorry

/-- The cross-chain transfer map is nonzero when `D ≥ 1`.

Since `T` preserves the trace pairing and the trace pairing is nontrivial
(it distinguishes `1` from `0`), `T` cannot be the zero map. -/
theorem crossChainTransfer_nonzero [NeZero D]
    {A₁ A₂ A₃ B₁ B₂ B₃ : MPSTensor d D}
    (hA₁ : IsInjective A₁) (hA₂ : IsInjective A₂) (hA₃ : IsInjective A₃)
    (hB₁ : IsInjective B₁) (hB₂ : IsInjective B₂) (hB₃ : IsInjective B₃)
    (hEq : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (A₁ (σ 0) * A₂ (σ 1) * A₃ (σ 2)) =
      Matrix.trace (B₁ (σ 0) * B₂ (σ 1) * B₃ (σ 2))) :
    crossChainTransfer A₁ A₂ A₃ B₁ B₂ B₃ hB₁ hB₂ hB₃ hA₁ hEq ≠ 0 := by
  sorry

/-! ### The main theorem -/

/-- **Lemma 1 (arXiv:1804.04964)**: Virtual bond gauge theorem.

For two 3-site injective MPS chains generating the same state, virtual insertions
on bond 0–1 are related by conjugation: there exists `Z ∈ GL(D,ℂ)` such that
for all `X` and all physical configurations `σ`,
```
virtualInsertCoeff A₁ A₂ A₃ σ X = virtualInsertCoeff B₁ B₂ B₃ σ (Z⁻¹ X Z)
```

The proof constructs the cross-chain transfer map `T`, shows it is a nonzero
multiplicative linear endomorphism (hence bijective by simplicity), promotes it
to an algebra automorphism, and applies Skolem–Noether to extract the gauge `Z`. -/
theorem virtual_bond_gauge [NeZero D]
    (A B : Fin 3 → MPSTensor d D)
    (hA : ∀ k, IsInjective (A k)) (hB : ∀ k, IsInjective (B k))
    (hEq : MPSChainTensor.SameState A B) :
    ∃ Z : GL (Fin D) ℂ, ∀ (X : Matrix (Fin D) (Fin D) ℂ) (σ : Fin 3 → Fin d),
      virtualInsertCoeff (A 0) (A 1) (A 2) σ X =
      virtualInsertCoeff (B 0) (B 1) (B 2) σ
        ((↑Z⁻¹ : Matrix _ _ ℂ) * X * (↑Z : Matrix _ _ ℂ)) := by
  classical
  -- Extract the SameState condition in pointwise form.
  have hEq' : ∀ σ : Fin 3 → Fin d,
      Matrix.trace (A 0 (σ 0) * A 1 (σ 1) * A 2 (σ 2)) =
      Matrix.trace (B 0 (σ 0) * B 1 (σ 1) * B 2 (σ 2)) := by
    intro σ
    have := hEq σ
    simp [MPSChainTensor.coeff, MPSChainTensor.eval] at this
    simpa [Fin.prod] using this
  -- Build the cross-chain transfer map.
  let T := crossChainTransfer (A 0) (A 1) (A 2) (B 0) (B 1) (B 2)
    (hB 0) (hB 1) (hB 2) (hA 0) hEq'
  -- T is multiplicative.
  have hMul : ∀ M N, T (M * N) = T M * T N :=
    crossChainTransfer_mul (hA 0) (hA 1) (hA 2) (hB 0) (hB 1) (hB 2) hEq'
  -- T is nonzero.
  have hNz : T ≠ 0 :=
    crossChainTransfer_nonzero (hA 0) (hA 1) (hA 2) (hB 0) (hB 1) (hB 2) hEq'
  -- T is bijective (simplicity of matrix algebra).
  have hBij := linear_mul_endomorphism_bijective T hMul hNz
  -- Promote T to an algebra homomorphism.
  let Talg := linearMapToAlgHom T hMul hBij.2
  -- Build the algebra equivalence.
  let Tequiv : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    AlgEquiv.ofBijective Talg hBij
  -- Apply Skolem–Noether: Tequiv is conjugation by some Z.
  obtain ⟨Z, hZ⟩ := skolemNoether_matrix Tequiv
  -- Z conjugates as X * M * X⁻¹, but we need Z⁻¹ * M * Z form.
  -- From hZ: T(M) = Z * M * Z⁻¹, so M = Z⁻¹ * T(M) * Z
  -- We need: virtualInsertCoeff A σ X = virtualInsertCoeff B σ (Z⁻¹ * X * Z)
  -- Since T satisfies Φ_B(T(X)) = Φ_A(X), i.e.
  --   tr(B₁(i) * T(X) * B₂(j) * B₃(k)) = tr(A₁(i) * X * A₂(j) * A₃(k))
  -- and T(X) = Z * X * Z⁻¹, we get
  --   virtualInsertCoeff B σ (Z * X * Z⁻¹) = virtualInsertCoeff A σ X
  -- We want: virtualInsertCoeff A σ X = virtualInsertCoeff B σ (Z⁻¹ * X * Z)
  -- So we use Z⁻¹ in place of Z.
  refine ⟨Z⁻¹, fun X σ => ?_⟩
  -- Now ↑(Z⁻¹)⁻¹ = ↑Z and ↑(Z⁻¹) = ↑(Z⁻¹)
  have hTspec := crossChainTransfer_spec (hB 0) (hB 1) (hB 2) (hA 0) hEq' X
    (σ 0) (σ 1) (σ 2)
  simp only [virtualInsertCoeff_eq]
  -- T(X) = Z * X * Z⁻¹ by Skolem-Noether
  have hTX : T X = (Z : Matrix _ _ ℂ) * X * ((Z⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
    have := hZ X
    change Tequiv X = _ at this
    simp only [Tequiv, AlgEquiv.ofBijective_apply, Talg] at this
    exact this
  -- The spec gives: tr(B₁(i) * T(X) * B₂(j) * B₃(k)) = tr(A₁(i) * X * A₂(j) * A₃(k))
  -- Substituting T(X) = Z * X * Z⁻¹:
  -- tr(A₁(i) * X * A₂(j) * A₃(k)) = tr(B₁(i) * (Z * X * Z⁻¹) * B₂(j) * B₃(k))
  -- We want: tr(A₁(i) * X * A₂(j) * A₃(k)) = tr(B₁(i) * (Z⁻¹⁻¹ * X * Z⁻¹) * B₂(j) * B₃(k))
  -- Since Z⁻¹⁻¹ = Z as GL elements, this matches.
  rw [← hTspec, hTX]
  congr 1
  simp [Matrix.mul_assoc, inv_inv]

end MPSTensor
