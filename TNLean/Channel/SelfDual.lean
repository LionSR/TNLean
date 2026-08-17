/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.TransferMatrix

/-!
# Self-dual channels (Wolf §2.3, Proposition 2.6)

Let $T : M_d(\mathbb C) \to M_d(\mathbb C)$ be completely positive and let $T^*$ be
its dual, characterized by
\(\operatorname{tr}[A\, T^*(B)] = \operatorname{tr}[T(A)\, B]\). Wolf's
Proposition 2.6 states that

1. $T = T^*$,
2. the transfer matrix \(\operatorname{tr}[\sigma_\alpha^\dagger T(\sigma_\beta)]\)
   is Hermitian,
3. \(T(X) = \sum_j K_j X K_j^\dagger\) for a family of Hermitian $K_j$

are equivalent.

## Basis convention

Wolf's transfer matrix \(\operatorname{tr}[F_\alpha^\dagger T(G_\beta)]\)
(Equation (2.20)) is built from two orthonormal families; condition 2 is the special
case $F_\alpha = G_\alpha = \sigma_\alpha$. Orthonormality is with respect to the
Hilbert-Schmidt inner product
\(\operatorname{tr}[\sigma_\alpha^\dagger \sigma_\beta] = \delta_{\alpha\beta}\)
(Equation (2.18) with $P = \mathbf 1$), and this is the convention carried by
`HilbertSchmidtOrthonormal`. Hermiticity of the family plays no role in the
equivalence; a Hermitian Hilbert-Schmidt orthonormal basis is precisely a
`TracePairingSelfDualBasis`, since for $\sigma_\alpha^\dagger = \sigma_\alpha$ the
two pairings \(\operatorname{tr}[\sigma_\alpha^\dagger X]\) and
\(\operatorname{tr}[\sigma_\alpha X]\) coincide.

## Main definitions

* `HilbertSchmidtOrthonormal` —
  \(\operatorname{tr}[\sigma_\alpha^\dagger \sigma_\beta] = \delta_{\alpha\beta}\)
  (Wolf Equation (2.18) with $P = \mathbf 1$)
* `transferMatrixOfBasis` — Wolf Equation (2.20) for identical families
  $F_\alpha = G_\alpha$

## Main results

* `self_dual_tfae` — Wolf Proposition 2.6: the three-way equivalence
* `transferMatrixOfBasis_isHermitian_iff` — condition 1 versus condition 2
* `transferMatrix_isHermitian_iff_traceAdjointMap_eq_self` — condition 2 for the
  matrix-unit transfer matrix of `TNLean.Channel.TransferMatrix`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3,
  Proposition 2.6][Wolf2012Quantum]
-/

open scoped Matrix BigOperators Kronecker

variable {D : ℕ}

/-! ### Hilbert-Schmidt orthonormal families -/

/-- A family of matrices is **Hilbert-Schmidt orthonormal** when
\(\operatorname{tr}[\sigma_\alpha^\dagger \sigma_\beta] = \delta_{\alpha\beta}\)
(Wolf Equation (2.18) with $P = \mathbf 1$). -/
def HilbertSchmidtOrthonormal {ι : Type*} [DecidableEq ι]
    (σ : ι → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ α β, Matrix.trace ((σ α)ᴴ * σ β) = if α = β then 1 else 0

namespace HilbertSchmidtOrthonormal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {σ : Module.Basis ι ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- In a Hilbert-Schmidt orthonormal basis the coordinates of $X$ are the pairings
\(\operatorname{tr}[\sigma_\alpha^\dagger X]\). -/
theorem repr_apply (hσ : HilbertSchmidtOrthonormal (σ ·))
    (X : Matrix (Fin D) (Fin D) ℂ) (α : ι) :
    σ.repr X α = Matrix.trace ((σ α)ᴴ * X) := by
  conv_rhs => rw [← σ.sum_repr X]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul, hσ α, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  simp

/-- A Hermitian Hilbert-Schmidt orthonormal basis is trace-self-dual: for
$\sigma_\alpha^\dagger = \sigma_\alpha$ the coordinate functionals are
$X \mapsto \operatorname{tr}[\sigma_\alpha X]$. -/
theorem tracePairingSelfDualBasis (hσ : HilbertSchmidtOrthonormal (σ ·))
    (hherm : ∀ α, (σ α)ᴴ = σ α) : TracePairingSelfDualBasis σ := by
  intro α X
  rw [hσ.repr_apply X α, hherm]

/-- A matrix pairing to zero against every member of a Hilbert-Schmidt orthonormal
basis is zero. -/
theorem eq_zero_of_trace_conjTranspose_mul (hσ : HilbertSchmidtOrthonormal (σ ·))
    {X : Matrix (Fin D) (Fin D) ℂ} (h : ∀ α, Matrix.trace ((σ α)ᴴ * X) = 0) :
    X = 0 := by
  refine σ.repr.injective ?_
  ext α
  simp [hσ.repr_apply X α, h α]

end HilbertSchmidtOrthonormal

/-! ### The transfer matrix in a single orthonormal family -/

/-- The **transfer matrix** of $T$ in the family $\sigma$ used on both sides,
\(\operatorname{tr}[\sigma_\alpha^\dagger T(\sigma_\beta)]\). This is Wolf
Equation (2.20) with $F_\alpha = G_\alpha = \sigma_\alpha$. -/
noncomputable def transferMatrixOfBasis {ι : Type*}
    (σ : ι → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun α β => Matrix.trace ((σ α)ᴴ * T (σ β))

@[simp]
theorem transferMatrixOfBasis_apply {ι : Type*}
    (σ : ι → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (α β : ι) :
    transferMatrixOfBasis σ T α β = Matrix.trace ((σ α)ᴴ * T (σ β)) := rfl

/-- For a Hermiticity-preserving map the dual map is represented by the Hermitian
conjugate transfer matrix (Wolf §2.3, paragraph following Equation (2.20)). -/
theorem transferMatrixOfBasis_conjTranspose {ι : Type*}
    (σ : ι → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hHP : ∀ X, T Xᴴ = (T X)ᴴ) :
    (transferMatrixOfBasis σ T)ᴴ =
      transferMatrixOfBasis σ (Matrix.traceAdjointMap T) := by
  ext α β
  rw [Matrix.conjTranspose_apply, transferMatrixOfBasis_apply,
    transferMatrixOfBasis_apply, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← hHP,
    Matrix.trace_mul_comm, Matrix.trace_mul_comm ((σ α)ᴴ)]
  exact (Matrix.trace_traceAdjointMap_mul T (σ β) ((σ α)ᴴ)).symm

/-- The transfer matrix in a Hilbert-Schmidt orthonormal basis determines the map:
\(\widehat T = \widehat S\) forces $T = S$. Pairing the difference against every
basis element gives \(\operatorname{tr}[\sigma_\alpha^\dagger (T - S)(\sigma_\beta)]
= 0\), and nondegeneracy of the Hilbert-Schmidt pairing forces
\((T - S)(\sigma_\beta) = 0\) on a basis. -/
private theorem transferMatrixOfBasis_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Module.Basis ι ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hσ : HilbertSchmidtOrthonormal (σ ·)) :
    Function.Injective (transferMatrixOfBasis (D := D) (σ ·)) := by
  intro S T h
  refine σ.ext fun β => ?_
  refine sub_eq_zero.mp (hσ.eq_zero_of_trace_conjTranspose_mul fun α => ?_)
  have hαβ := congrFun (congrFun h α) β
  rw [transferMatrixOfBasis_apply, transferMatrixOfBasis_apply] at hαβ
  rw [Matrix.mul_sub, Matrix.trace_sub, hαβ]
  simp

/-- **Wolf Proposition 2.6, conditions 1 and 2**: for a Hermiticity-preserving map the
transfer matrix in a Hilbert-Schmidt orthonormal basis used on both sides is
Hermitian exactly when the map equals its dual. -/
theorem transferMatrixOfBasis_isHermitian_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : Module.Basis ι ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hσ : HilbertSchmidtOrthonormal (σ ·))
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hHP : ∀ X, T Xᴴ = (T X)ᴴ) :
    (transferMatrixOfBasis (σ ·) T).IsHermitian ↔ Matrix.traceAdjointMap T = T := by
  show (transferMatrixOfBasis (σ ·) T)ᴴ = transferMatrixOfBasis (σ ·) T ↔ _
  rw [transferMatrixOfBasis_conjTranspose (σ ·) T hHP]
  exact ⟨fun h => transferMatrixOfBasis_injective hσ h, fun h => by rw [h]⟩

/-! ### Kraus families and the dual map -/

/-- The dual map of \(T(X) = \sum_i K_i X K_i^\dagger\) is
\(T^*(X) = \sum_i K_i^\dagger X K_i\): the Kraus operators of $T$ and $T^*$ differ
by Hermitian conjugation (Wolf §2.2, remark following Proposition 2.4). -/
theorem traceAdjointMap_of_kraus {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.traceAdjointMap T X = ∑ i : Fin r, (K i)ᴴ * X * K i := by
  refine Matrix.ext_iff_trace_mul_right.mpr fun N => ?_
  rw [Matrix.trace_traceAdjointMap_mul, hK, Finset.sum_mul, Matrix.trace_sum,
    Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hleft : X * (K i * N * (K i)ᴴ) = X * K i * N * (K i)ᴴ := by
    simp [Matrix.mul_assoc]
  have hright : (K i)ᴴ * X * K i * N = (K i)ᴴ * (X * K i * N) := by
    simp [Matrix.mul_assoc]
  rw [hleft, hright, Matrix.trace_mul_comm]

/-- A map with a Kraus representation preserves Hermiticity. -/
theorem map_conjTranspose_of_kraus {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    T Xᴴ = (T X)ᴴ := by
  simp [hK, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A completely positive map preserves Hermiticity. -/
theorem IsCPMap.map_conjTranspose
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsCPMap T) (X : Matrix (Fin D) (Fin D) ℂ) : T Xᴴ = (T X)ᴴ := by
  obtain ⟨r, K, hK⟩ := hT
  exact map_conjTranspose_of_kraus K T hK X

/-- **Wolf Proposition 2.6, direction \(1 \to 3\)**: a map with the two Kraus
representations \(T(X) = \sum_j K_j X K_j^\dagger\) and
\(T(X) = \sum_j K_j^\dagger X K_j\) is written as
\(T(X) = \frac{1}{2} \sum_j (K_j X K_j^\dagger + K_j^\dagger X K_j)\), and the
unitary recombination \((a, b) \mapsto ((a + b)/\sqrt{2},\ i(a - b)/\sqrt{2})\)
turns every pair \((K_j, K_j^\dagger)/\sqrt{2}\) into the Hermitian pair
\((K_j + K_j^\dagger)/2\), \(i(K_j - K_j^\dagger)/2\). -/
theorem exists_hermitian_kraus_of_self_dual {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ)
    (hKdual : ∀ X, T X = ∑ i : Fin r, (K i)ᴴ * X * K i) :
    ∃ (s : ℕ) (L : Fin s → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, (L j)ᴴ = L j) ∧ ∀ X, T X = ∑ j : Fin s, L j * X * (L j)ᴴ := by
  classical
  set c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hc
  have hcstar : star c = c := by
    rw [hc, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hcc : c * c = (2 : ℂ)⁻¹ := by
    rw [hc, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  -- the symmetrized Kraus family `(Kⱼ, Kⱼ†)/√2`
  set A : Fin r × Bool → Matrix (Fin D) (Fin D) ℂ :=
    fun p => c • (if p.2 then (K p.1)ᴴ else K p.1) with hA
  -- the recombination `(a, b) ↦ ((a + b)/√2, i(a - b)/√2)`
  set W : Matrix Bool Bool ℂ :=
    fun b b' => if b then (if b' then -Complex.I else Complex.I) else 1 with hW
  have hWunit : Wᴴ * W = (2 : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    ext b b'
    change (∑ x : Bool, star (W x b) * W x b') =
      (2 : ℂ) * (if b = b' then 1 else 0)
    cases b <;> cases b' <;>
      simp [hW, Complex.I_mul_I] <;>
      norm_num
  set U : Matrix (Fin r × Bool) (Fin r × Bool) ℂ :=
    (1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ (c • W) with hU
  have hUunit : Uᴴ * U = 1 := by
    have hV : (c • W)ᴴ * (c • W) = 1 := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hWunit,
        smul_smul, smul_smul, hcstar, hcc]
      norm_num
    rw [hU, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, hV, Matrix.one_kronecker_one]
  set B : Fin r × Bool → Matrix (Fin D) (Fin D) ℂ :=
    fun p => ∑ q : Fin r × Bool, U p q • A q with hB
  have hAtrue : ∀ i : Fin r, A (i, true) = c • (K i)ᴴ := by intro i; simp [hA]
  have hAfalse : ∀ i : Fin r, A (i, false) = c • K i := by intro i; simp [hA]
  have hexp : ∀ (i : Fin r) (b : Bool),
      B (i, b) = (c * W b true) • A (i, true) + (c * W b false) • A (i, false) := by
    intro i b
    rw [hB]
    simp only [hU, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, ite_mul, one_mul, zero_mul, ite_smul, zero_smul,
      Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hBfalse : ∀ i : Fin r, B (i, false) = ((2 : ℂ)⁻¹) • (K i + (K i)ᴴ) := by
    intro i
    have hW1 : W false true = 1 := by simp [hW]
    have hW2 : W false false = 1 := by simp [hW]
    rw [hexp i false, hW1, hW2, hAtrue i, hAfalse i]
    simp only [mul_one, smul_smul, hcc]
    module
  have hBtrue : ∀ i : Fin r, B (i, true) = (Complex.I / 2) • (K i - (K i)ᴴ) := by
    intro i
    have hW1 : W true true = -Complex.I := by simp [hW]
    have hW2 : W true false = Complex.I := by simp [hW]
    rw [hexp i true, hW1, hW2, hAtrue i, hAfalse i]
    simp only [smul_smul]
    rw [show c * -Complex.I * c = -(Complex.I * (c * c)) by ring,
      show c * Complex.I * c = Complex.I * (c * c) by ring, hcc]
    module
  have hBherm : ∀ p : Fin r × Bool, (B p)ᴴ = B p := by
    rintro ⟨i, b⟩
    cases b with
    | false =>
        rw [hBfalse i, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
          Matrix.conjTranspose_conjTranspose,
          show star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ by norm_num, add_comm]
    | true =>
        rw [hBtrue i, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_conjTranspose,
          show star (Complex.I / 2) = -(Complex.I / 2) by
            simp [Complex.conj_I, neg_div], neg_smul, ← smul_neg,
          neg_sub]
  have hAB : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ p : Fin r × Bool, B p * X * (B p)ᴴ =
        ∑ q : Fin r × Bool, A q * X * (A q)ᴴ :=
    kraus_same_map_of_unitary_combination B A U hUunit fun p => rfl
  have hAT : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ q : Fin r × Bool, A q * X * (A q)ᴴ = T X := by
    intro X
    have hterm : ∀ i : Fin r,
        A (i, true) * X * (A (i, true))ᴴ + A (i, false) * X * (A (i, false))ᴴ =
          ((2 : ℂ)⁻¹) • ((K i)ᴴ * X * K i) + ((2 : ℂ)⁻¹) • (K i * X * (K i)ᴴ) := by
      intro i
      rw [hAtrue i, hAfalse i]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.conjTranspose_conjTranspose, hcstar, hcc]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, hterm]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← hK X,
      ← hKdual X, ← add_smul]
    norm_num
  refine ⟨r * 2, fun m =>
    B (((Equiv.prodCongr (Equiv.refl (Fin r)) finTwoEquiv.symm).trans
      finProdFinEquiv).symm m), fun m => hBherm _, fun X => ?_⟩
  rw [← hAT X, ← hAB X]
  exact (Equiv.sum_comp
    ((Equiv.prodCongr (Equiv.refl (Fin r)) finTwoEquiv.symm).trans finProdFinEquiv).symm
    fun p => B p * X * (B p)ᴴ).symm

/-! ### The self-dual channel proposition -/

/-- **Wolf Proposition 2.6 (self-dual channels)**: for a completely positive map
$T : M_d(\mathbb C) \to M_d(\mathbb C)$ the following are equivalent.

1. $T$ equals its dual $T^*$, characterized by
   \(\operatorname{tr}[A\, T^*(B)] = \operatorname{tr}[T(A)\, B]\).
2. The transfer matrix \(\operatorname{tr}[\sigma_\alpha^\dagger T(\sigma_\beta)]\)
   in one Hilbert-Schmidt orthonormal basis $\sigma$ used on both sides is
   Hermitian.
3. $T$ admits a family of Hermitian Kraus operators. -/
theorem self_dual_tfae {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsCPMap T)
    {σ : Module.Basis ι ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hσ : HilbertSchmidtOrthonormal (σ ·)) :
    List.TFAE [
      Matrix.traceAdjointMap T = T,
      (transferMatrixOfBasis (σ ·) T).IsHermitian,
      ∃ (r : ℕ) (K : Fin r → Matrix (Fin D) (Fin D) ℂ),
        (∀ j, (K j)ᴴ = K j) ∧ ∀ X, T X = ∑ j : Fin r, K j * X * (K j)ᴴ
    ] := by
  tfae_have h21 : 2 ↔ 1 :=
    transferMatrixOfBasis_isHermitian_iff hσ hT.map_conjTranspose
  tfae_have h31 : 3 → 1 := by
    rintro ⟨r, K, hherm, hK⟩
    refine LinearMap.ext fun X => ?_
    rw [traceAdjointMap_of_kraus K T hK X, hK X]
    exact Finset.sum_congr rfl fun i _ => by rw [hherm i]
  tfae_have h13 : 1 → 3 := by
    intro h1
    obtain ⟨r, K, hK⟩ := hT
    have hKdual : ∀ X, T X = ∑ i : Fin r, (K i)ᴴ * X * K i := by
      intro X
      conv_lhs => rw [← h1]
      exact traceAdjointMap_of_kraus K T hK X
    exact exists_hermitian_kraus_of_self_dual K T hK hKdual
  tfae_finish

/-! ### Condition 2 in the basis of matrix units -/

/-- For a Hermiticity-preserving map the matrix-unit transfer matrix of the dual
map is the Hermitian conjugate transfer matrix (Wolf §2.3, paragraph following
Equation (2.20)). -/
theorem transferMatrix_conjTranspose_eq_traceAdjointMap
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hHP : ∀ X, T Xᴴ = (T X)ᴴ) :
    (transferMatrix T)ᴴ = transferMatrix (Matrix.traceAdjointMap T) := by
  ext ⟨j, i⟩ ⟨l, k⟩
  rw [Matrix.conjTranspose_apply, transferMatrix_apply, transferMatrix_apply,
    Matrix.traceAdjointMap_apply_apply, Matrix.trace_single_mul]
  have hswap := hHP (Matrix.single i j (1 : ℂ))
  rw [Matrix.conjTranspose_single, star_one] at hswap
  rw [hswap]
  simp

/-- **Wolf Proposition 2.6, conditions 1 and 2 in matrix units**: a completely positive
map equals its dual exactly when its matrix-unit transfer matrix is Hermitian. -/
theorem transferMatrix_isHermitian_iff_traceAdjointMap_eq_self
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsCPMap T) :
    (transferMatrix T).IsHermitian ↔ Matrix.traceAdjointMap T = T := by
  show (transferMatrix T)ᴴ = transferMatrix T ↔ _
  rw [transferMatrix_conjTranspose_eq_traceAdjointMap T hT.map_conjTranspose]
  exact ⟨fun h => transferMatrix_injective h, fun h => by rw [h]⟩
