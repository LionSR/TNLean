/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Uncle.UncleBoundaryProduct
import TNLean.MPS.Tensor.GroundSpace.IntersectionProperty
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import QICLean.Channel.Schwarz.Basic
import QICLean.Channel.Schwarz.RussoDye
import QICLean.Kraus.MixedMap.SpectralRadius
import QICLean.Channel.OperatorMean.BlockDiagonal
import QICLean.Spectral.Radius.PowerDecay
import TNLean.MPS.ParentHamiltonian.Uncle.UncleBoundaryTraceClosure
import TNLean.MPS.Tensor.GroundSpace.CyclicTranslation

/-!
# The four finite-chain uncle boundary sectors

The boundary words contain diagonal all-A and all-B products, together with
exactly one R or L wall summed over its possible positions. Their trace
boundary-map range is the source space \(S_n\). These words use the explicit
single-wall coefficient product, not ordinary products of the two-site
uncle tensor.

Source: arXiv:1210.6613, equation (Sn-def), lines 1077–1095, and Appendix
intersection-closure, lines 1768–1940. Full perturbation injectivity supplies
identity coefficients, which prove full word span at every positive length.

It also contains the following results.

* `MPSTensor.uncleBoundaryLetter_mixedMapSpectralRadius_lt_one`,
  `MPSTensor.uncleBoundaryLetter_mixedMapSpectralRadius_reverse_lt_one`: mixed damping from full
  source perturbation span.
* `MPSTensor.uncleBoundaryMap_scalar_blocks`, `MPSTensor.uncleBoundarySpace_inf_cyclicTranslate`:
  periodic closure of the actual single-domain-wall boundary space.
-/

open MPTensor

section UncleBoundaryWords

open scoped Matrix BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {a b : ℕ}

/-- The full one-site letter in the source injective-perturbation condition;
arXiv:1210.6613, equation (inj-condition-tensor), lines 973–983. -/
noncomputable def uncleBoundaryLetter (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (i : α) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  uncleBlockMatrix (A i) (R i) (L i) (B i)

/-- An ordered coefficient word with at most one wall; source equation
(Sn-def), Appendix intersection-closure, arXiv:1210.6613. -/
noncomputable def uncleBoundaryWord (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) :
    List α → Matrix (Fin (a + b)) (Fin (a + b)) ℂ
  | [] => 1
  | i :: w => uncleBoundaryMul (uncleBoundaryLetter A B R L i)
      (uncleBoundaryWord A B R L w)

@[simp] theorem uncleBoundaryWord_nil (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) : uncleBoundaryWord A B R L [] = 1 := rfl

@[simp] theorem uncleBoundaryWord_singleton (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (i : α) :
    uncleBoundaryWord A B R L [i] = uncleBoundaryLetter A B R L i :=
  uncleBoundaryMul_one _

/-- Concatenation multiplies the source single-wall coefficients. -/
theorem uncleBoundaryWord_append (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (u v : List α) :
    uncleBoundaryWord A B R L (u ++ v) =
      uncleBoundaryMul (uncleBoundaryWord A B R L u) (uncleBoundaryWord A B R L v) := by
  induction u with
  | nil => simp [one_uncleBoundaryMul]
  | cons i u ih =>
      simp only [List.cons_append, uncleBoundaryWord, ih, uncleBoundaryMul_assoc]

/-- Appending a physical site is right multiplication by its source letter. -/
theorem uncleBoundaryWord_ofFn_snoc (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) {n : ℕ}
    (w : Fin n → α) (i : α) :
    uncleBoundaryWord A B R L (List.ofFn (Fin.snoc w i)) =
      uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn w))
        (uncleBoundaryLetter A B R L i) := by
  rw [List.ofFn_snoc, uncleBoundaryWord_append, uncleBoundaryWord_singleton]

/-- Prepending a physical site is left multiplication by its source letter. -/
theorem uncleBoundaryWord_ofFn_cons (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) {n : ℕ}
    (i : α) (w : Fin n → α) :
    uncleBoundaryWord A B R L (List.ofFn (Fin.cons i w)) =
      uncleBoundaryMul (uncleBoundaryLetter A B R L i)
        (uncleBoundaryWord A B R L (List.ofFn w)) := by
  rw [List.ofFn_cons]
  rfl

/-- The explicit rectangular sum with one wall, padded by A on the left
and B on the right; source equation (Sn-def), arXiv:1210.6613. -/
noncomputable def uncleDomainWallWord (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ) :
    List α → Matrix (Fin a) (Fin b) ℂ
  | [] => 0
  | i :: w => A i * uncleDomainWallWord A B R w + R i * Kraus.evalWord B w

/-- Every wall position occurs exactly once in the source domain-wall sum. -/
theorem uncleDomainWallWord_eq_sum (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ) (w : List α) :
    uncleDomainWallWord A B R w =
      ∑ k : Fin w.length, Kraus.evalWord A (w.take k) * R (w.get k) *
        Kraus.evalWord B (w.drop (k + 1)) := by
  induction w with
  | nil => simp [uncleDomainWallWord]
  | cons i w ih =>
      simp [uncleDomainWallWord, ih, Fin.sum_univ_succ, Matrix.mul_sum,
        Matrix.mul_assoc, add_comm]

/-- The actual four blocks of the source coefficient word. In particular
the off-diagonal terms contain a single wall, not alternating walls. -/
theorem uncleBoundaryWord_block (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (w : List α) :
    uncleBoundaryWord A B R L w =
      uncleBlockMatrix (Kraus.evalWord A w) (uncleDomainWallWord A B R w)
        (uncleDomainWallWord B A L w) (Kraus.evalWord B w) := by
  induction w with
  | nil => simp [uncleDomainWallWord, Kraus.evalWord, uncleBlockMatrix_one]
  | cons i w ih =>
      simp [uncleBoundaryWord, uncleBoundaryLetter, ih, uncleBoundaryMul_block,
        uncleDomainWallWord, Kraus.evalWord, add_comm]

/-- At length two the source coefficient word is exactly the existing uncle letter. -/
theorem uncleBoundaryWord_two (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (i j : α) :
    uncleBoundaryWord A B R L [i, j] =
      uncleTensor A B R L ((decodeBlockEquiv d 2).symm ![i, j]) := by
  simp [uncleBoundaryWord, uncleBoundaryLetter, uncleBoundaryMul_block, uncleTensor,
    uncleBoundaryMul_one]

/-- The coefficient on any original two-site configuration is the existing
uncle-tensor letter with that blocked physical index. -/
theorem uncleBoundaryWord_ofFn_two (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (σ : Fin 2 → α) :
    uncleBoundaryWord A B R L (List.ofFn σ) =
      uncleTensor A B R L ((decodeBlockEquiv d 2).symm σ) := by
  have hσ : σ = ![σ 0, σ 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hσ]
  simpa [List.ofFn_succ] using uncleBoundaryWord_two A B R L (σ 0) (σ 1)

/-- The full perturbation span supplies coefficients for the identity. -/
theorem exists_uncleBoundary_identity_coefficients
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) :
    ∃ c : α → ℂ, ∑ i, c i • uncleBoundaryLetter A B R L i = 1 := by
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
  rw [hPert.span_eq_top]
  exact Submodule.mem_top

/-- Contracting the first physical site against identity coefficients
removes it without adding a wall. This is the inverse-coefficient step in
the Appendix intersection proof of arXiv:1210.6613. -/
theorem sum_smul_uncleBoundaryWord_cons
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (c : α → ℂ) (hc : ∑ i, c i • uncleBoundaryLetter A B R L i = 1)
    (w : List α) :
    (∑ i, c i • uncleBoundaryWord A B R L (i :: w)) = uncleBoundaryWord A B R L w := by
  calc
    _ = uncleBoundaryMulRight (uncleBoundaryWord A B R L w)
        (∑ i, c i • uncleBoundaryLetter A B R L i) := by
      simp [uncleBoundaryWord, map_sum, map_smul]
    _ = _ := by rw [hc]; exact one_uncleBoundaryMul _

/-- Full perturbation injectivity gives full coefficient span at every
positive word length, as required in the Appendix intersection and closure
proofs of arXiv:1210.6613, lines 1925–1940. -/
theorem uncleBoundary_span_eq_top_succ
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ) :
    Submodule.span ℂ (Set.range fun σ : Fin (n + 1) → α ↦
      uncleBoundaryWord A B R L (List.ofFn σ)) = ⊤ := by
  classical
  obtain ⟨c, hc⟩ := exists_uncleBoundary_identity_coefficients A B R L hPert
  induction n with
  | zero =>
      apply top_unique
      rw [← hPert.span_eq_top]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨fun _ : Fin 1 ↦ i, by simp [List.ofFn_succ]⟩
  | succ n ih =>
      apply top_unique
      rw [← ih]
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      change uncleBoundaryWord A B R L (List.ofFn σ) ∈ _
      rw [← sum_smul_uncleBoundaryWord_cons A B R L c hc (List.ofFn σ)]
      refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ (c i) ?_
      exact Submodule.subset_span ⟨Fin.cons i σ, by
        change uncleBoundaryWord A B R L (List.ofFn (Fin.cons i σ)) = _
        rw [List.ofFn_cons]⟩

/-- The trace boundary map for the four source sectors \(S_n\). -/
noncomputable def uncleBoundaryMap (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (n : ℕ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] NSiteSpace α n where
  toFun X σ := Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * X)
  map_add' X Y := by ext σ; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by ext σ; simp [Matrix.trace_smul]

/-- The actual four-sector source boundary space, equation (Sn-def) of
arXiv:1210.6613. Its word-block formula separates \(A_n,B_n,R_n,L_n\). -/
noncomputable def uncleBoundarySpace (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (n : ℕ) : Submodule ℂ (NSiteSpace α n) :=
  LinearMap.range (uncleBoundaryMap A B R L n)

@[simp] theorem uncleBoundaryMap_apply (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (n : ℕ)
    (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) (σ : Fin n → α) :
    uncleBoundaryMap A B R L n X σ =
      Matrix.trace (uncleBoundaryWord A B R L (List.ofFn σ) * X) := rfl

/-- The length-two source boundary map is exactly the blocked uncle map,
written on the original pair of physical indices. -/
theorem uncleBoundaryMap_two (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) (σ : Fin 2 → α) :
    uncleBoundaryMap A B R L 2 X σ =
      groundSpaceMap (uncleTensor A B R L) 1 X
        (fun _ ↦ (decodeBlockEquiv d 2).symm σ) := by
  rw [uncleBoundaryMap_apply, uncleBoundaryWord_ofFn_two]
  simp only [groundSpaceMap_apply, List.ofFn_succ, List.ofFn_zero, Kraus.evalWord_cons,
    Kraus.evalWord_nil, Matrix.mul_one]

end MPSTensor

end UncleBoundaryWords

section UncleMixedDamping

/-!
## Mixed damping from full source perturbation span

The full perturbation span separates the two diagonal blocks. A peripheral
mixed eigenvector would intertwine their adjoint letters, by equality in
the weighted Schwarz inequality for the block-diagonal channel. Contracting
that identity with coefficients isolating one block forces the vector to
vanish. Thus strict mixed damping follows from the source span and canonical
normalization; it is not an additional spectral assumption. The
conclusion is \(r(\mathcal E_{AB})<1\) for the mixed transfer map
\(\mathcal E_{AB}(X)=\sum_iA_iXB_i^\dagger\), and likewise
\(r(\mathcal E_{BA})<1\).

This is not a formalization of the source's Lemma offdiagonal-damping
(lines 1175–1177), which derives the same bound from block injectivity of the
unperturbed diagonal blocks alone. The hypothesis here is full span of the
perturbed letters, which suffices for the two-wall trial argument.

Source: arXiv:1210.6613, Lemma exptransferoperator and the normalized
two-block setting of Lemma lowenergystates, lines 1165–1265.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace ENNReal

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {a b : ℕ}

private theorem uncleBoundary_separating_coefficients
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) :
    ∃ c : α → ℂ, (∑ i, c i • (A i)ᴴ) = 0 ∧ (∑ i, c i • (B i)ᴴ) = 1 := by
  classical
  have hmem : uncleBlockMatrix (a := a) (b := b) 0 0 0 1 ∈
      Submodule.span ℂ (Set.range (uncleBoundaryLetter A B R L)) := by
    rw [hPert.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  have hA : ∑ i, c i • A i = 0 := by
    ext j k
    have h := congrArg (fun M ↦ M (e (Sum.inl j)) (e (Sum.inl k))) hc
    simpa [e, Matrix.sum_apply, uncleBoundaryLetter, uncleBlockMatrix,
      Matrix.reindex_apply] using h
  have hB : ∑ i, c i • B i = 1 := by
    ext j k
    have h := congrArg (fun M ↦ M (e (Sum.inr j)) (e (Sum.inr k))) hc
    simpa [e, Matrix.sum_apply, uncleBoundaryLetter, uncleBlockMatrix,
      Matrix.reindex_apply] using h
  refine ⟨fun i ↦ star (c i), ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hA
  · simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hB

/-- The full perturbation span and unital canonical blocks imply
strict mixed-transfer damping. Faithful stationary dual densities suffice;
their trace normalization is not needed for this implication. No
nonvanishing of the block dimensions is assumed: when one of them vanishes,
the mixed map acts on the zero space and its spectral radius is zero.
Source: arXiv:1210.6613, Lemma exptransferoperator. -/
theorem uncleBoundaryLetter_mixedMapSpectralRadius_lt_one
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB) :
    Kraus.mixedMapSpectralRadius A B < 1 := by
  classical
  rcases subsingleton_or_nontrivial (Matrix (Fin a) (Fin b) ℂ) with hV | hV
  · unfold Kraus.mixedMapSpectralRadius
    rw [spectrum.SpectralRadius.of_subsingleton]
    exact zero_lt_one
  let K : α → Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ :=
    fun i ↦ Matrix.fromBlocks (A i) 0 0 (B i)
  let ρ : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ :=
    Matrix.fromBlocks ρA 0 0 ρB
  have hKA : ∑ i, A i * (A i)ᴴ = 1 := by
    simpa only [Kraus.mapLM_apply, Kraus.map_apply, Matrix.mul_one] using hUA
  have hKB : ∑ i, B i * (B i)ᴴ = 1 := by
    simpa only [Kraus.mapLM_apply, Kraus.map_apply, Matrix.mul_one] using hUB
  have hKU : Kraus.IsUnital K := by
    change (∑ i, K i * (K i)ᴴ) = 1
    have hsum : (∑ i, K i * (K i)ᴴ) = Matrix.fromBlocks
        (∑ i, A i * (A i)ᴴ) 0 0 (∑ i, B i * (B i)ᴴ) := by
      ext (i | i) (j | j) <;>
        simp [K, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    rw [hsum, hKA, hKB, Matrix.fromBlocks_one]
  have hρ : ρ.PosDef := hρA.fromBlocks_diag hρB
  have hF : Kraus.adjointMap K ρ = ρ := by
    have hsum : Kraus.adjointMap K ρ = Matrix.fromBlocks
        (Kraus.adjointMap A ρA) 0 0 (Kraus.adjointMap B ρB) := by
      ext (i | i) (j | j) <;>
        simp [Kraus.adjointMap, K, ρ, Matrix.sum_apply, Matrix.fromBlocks_multiply,
          Matrix.fromBlocks_conjTranspose]
    rw [hsum, hFA, hFB]
  have hCP := Matrix.rectangularKrausMap_isKrausCP K
  have hOne : Matrix.rectangularKrausMap K 1 = 1 := by
    change (∑ i, K i * 1 * (K i)ᴴ) = 1
    simpa only [Kraus.IsUnital, Matrix.mul_one] using hKU
  unfold Kraus.mixedMapSpectralRadius
  apply spectralRadius_lt_one_of_eigenvalues_lt_one
  intro μ hμ
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hEX : Kraus.mixedMapLM A B X = μ • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  let M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := Matrix.fromBlocks 0 X 0 0
  have hEM : Kraus.map K M = μ • M := by
    have hsum : Kraus.map K M = Matrix.fromBlocks 0 (Kraus.mixedMapLM A B X) 0 0 := by
      ext (i | i) (j | j) <;>
        simp [Kraus.map, Kraus.mixedMapLM_apply, K, M, Matrix.sum_apply,
          Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    rw [hsum, hEX]
    ext (i | i) (j | j) <;> simp [M]
  have hMne : M ≠ 0 := by
    intro hM
    apply hX.2
    ext i j
    exact congrArg (fun T ↦ T (Sum.inl i) (Sum.inr j)) hM
  have hEK : Module.End.HasEigenvalue (Matrix.rectangularKrausMap K) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hEM, hMne⟩
  have hle := hCP.eigenvalue_norm_le_one_of_map_one_eq_one hOne μ hEK
  by_contra hn
  have hnorm : ‖μ‖ = 1 := le_antisymm hle (le_of_not_gt hn)
  have hKS := Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
    K hKU hρ hF M μ hEM hnorm
  have hComm := Kraus.kraus_commute_of_ks_equality K hKU M hKS
  have hInter (i : α) : X * (B i)ᴴ = μ • ((A i)ᴴ * X) := by
    ext j k
    have h := congrArg (fun T ↦ T (Sum.inl j) (Sum.inr k)) (hComm i)
    rw [hEM] at h
    simpa [K, M, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] using h
  obtain ⟨c, hcA, hcB⟩ := uncleBoundary_separating_coefficients A B R L hPert
  have hzero : X = 0 := by
    calc
      X = X * (∑ i, c i • (B i)ᴴ) := by rw [hcB, Matrix.mul_one]
      _ = ∑ i, c i • (X * (B i)ᴴ) := by
        rw [Matrix.mul_sum]
        simp_rw [Matrix.mul_smul]
      _ = ∑ i, c i • (μ • ((A i)ᴴ * X)) := by simp_rw [hInter]
      _ = μ • ((∑ i, c i • (A i)ᴴ) * X) := by
        rw [Matrix.sum_mul, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.smul_mul]
        exact smul_comm (c i) μ ((A i)ᴴ * X)
      _ = 0 := by rw [hcA, Matrix.zero_mul, smul_zero]
  exact hX.2 hzero

/-- Full source perturbation span also gives strict mixed damping in the
reverse orientation. The conjugate-transpose mixed eigenvector reduces
this to the preceding block-separation argument.
Source: arXiv:1210.6613, Lemma exptransferoperator. -/
theorem uncleBoundaryLetter_mixedMapSpectralRadius_reverse_lt_one
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L))
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (ρA : Matrix (Fin a) (Fin a) ℂ) (hρA : ρA.PosDef)
    (ρB : Matrix (Fin b) (Fin b) ℂ) (hρB : ρB.PosDef)
    (hFA : Kraus.adjointMap A ρA = ρA) (hFB : Kraus.adjointMap B ρB = ρB) :
    Kraus.mixedMapSpectralRadius B A < 1 := by
  have hgap := uncleBoundaryLetter_mixedMapSpectralRadius_lt_one
    A B R L hPert hUA hUB ρA hρA ρB hρB hFA hFB
  rcases subsingleton_or_nontrivial (Matrix (Fin b) (Fin a) ℂ) with hV | hV
  · unfold Kraus.mixedMapSpectralRadius
    rw [spectrum.SpectralRadius.of_subsingleton]
    exact zero_lt_one
  unfold Kraus.mixedMapSpectralRadius
  apply spectralRadius_lt_one_of_eigenvalues_lt_one
  intro μ hμ
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hEX : Kraus.mixedMapLM B A X = μ • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  have hEXstar : Kraus.mixedMapLM A B Xᴴ = star μ • Xᴴ := by
    have h := congrArg Matrix.conjTranspose hEX
    simpa only [Kraus.mixedMapLM_apply, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.mul_assoc] using h
  have hne : Xᴴ ≠ 0 := by
    intro h
    exact hX.2 (by simpa only [Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose h)
  have hEig : Module.End.HasEigenvalue (Kraus.mixedMapLM A B) (star μ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hEXstar, hne⟩
  have hSpec : star μ ∈ spectrum ℂ (Kraus.mixedMapLM A B) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp hEig
  have hQspec : star μ ∈ quasispectrum ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin a) (Fin b) ℂ))
        (Kraus.mixedMapLM A B)) := by
    apply spectrum_subset_quasispectrum ℂ _
    rw [AlgEquiv.spectrum_eq (R := ℂ)]
    exact hSpec
  have hbound : (‖star μ‖₊ : ℝ≥0∞) ≤ Kraus.mixedMapSpectralRadius A B := by
    unfold Kraus.mixedMapSpectralRadius spectralRadius
    exact le_iSup_of_le (star μ) (le_iSup_of_le hQspec le_rfl)
  have hlt := hbound.trans_lt hgap
  simpa only [norm_star] using (show ‖star μ‖ < 1 by exact_mod_cast hlt)

end MPSTensor

end UncleMixedDamping

section UnclePeriodicClosure

/-!
## Periodic closure of the actual single-domain-wall boundary space

For an injective full perturbation letter, the intersection of the actual
source space \(S_N\) and its one-site cyclic translate consists of the two
periodic sector vectors, for every \(N\ge2\), the domain starting from the
source two-site uncle interaction. Full coefficient spans extend
the cyclic word identity to arbitrary pairs of coefficient matrices. The
boundary trace classification then removes both walls and makes the two
diagonal boundaries scalar.

Source: arXiv:1210.6613, Lemma "closure", source lines 1117–1127, and
Appendix "intersection-closure", source lines 1943–1984.
-/

noncomputable section

open scoped Matrix BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {a b : ℕ}

private theorem cyclicTranslateCfg_cons_append (n : ℕ) (i : α)
    (τ : Fin (n + 1) → α) :
    cyclicTranslateCfg (1 : Fin (n + 2)) (Fin.cons i τ) =
      Fin.append τ (fun _ : Fin 1 ↦ i) := by
  have h1 : (1 : Fin (n + 2)).val = 1 := by
    change 1 % (n + 2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  funext k
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · have hlast : (Fin.last (n + 1) : Fin (n + 2)) + 1 = 0 := by
      apply Fin.ext
      rw [Fin.val_add_eq_ite]
      simp only [Fin.val_last, h1, Fin.val_zero]
      rw [ite_eq_left (by omega)]
      omega
    change Fin.cons (α := fun _ : Fin (n + 2) ↦ α) i τ
      (Fin.last (n + 1) + 1) = _
    rw [hlast, Fin.cons_zero]
    exact (Fin.append_right τ (fun _ : Fin 1 ↦ i) 0).symm
  · have hsite : (j.castSucc : Fin (n + 2)) + 1 = j.succ := by
      apply Fin.ext
      rw [Fin.val_add_eq_ite]
      simp only [Fin.val_castSucc, Fin.val_succ, h1]
      rw [ite_eq_right (by omega)]
    change Fin.cons (α := fun _ : Fin (n + 2) ↦ α) i τ (j.castSucc + 1) = _
    rw [hsite, Fin.cons_succ]
    exact (Fin.append_left τ (fun _ : Fin 1 ↦ i) j).symm

private def uncleTracePair (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin (a + b)) ℂ ℂ).comp (LinearMap.mulRight ℂ X)

private theorem uncleBoundary_cyclic_pairing_of_word_pairing
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ)
    (X Y : Matrix (Fin (a + b)) (Fin (a + b)) ℂ)
    (hword : ∀ i : α, ∀ τ : Fin (n + 1) → α,
      Matrix.trace (uncleBoundaryMul (uncleBoundaryLetter A B R L i)
          (uncleBoundaryWord A B R L (List.ofFn τ)) * X) =
        Matrix.trace (uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn τ))
          (uncleBoundaryLetter A B R L i) * Y)) :
    ∀ M N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ,
      Matrix.trace (uncleBoundaryMul M N * X) =
        Matrix.trace (uncleBoundaryMul N M * Y) := by
  have hletter (i : α) (N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) :
      Matrix.trace (uncleBoundaryMul (uncleBoundaryLetter A B R L i) N * X) =
        Matrix.trace (uncleBoundaryMul N (uncleBoundaryLetter A B R L i) * Y) := by
    have heq : (uncleTracePair X).comp (uncleBoundaryMulLeft (uncleBoundaryLetter A B R L i)) =
        (uncleTracePair Y).comp (uncleBoundaryMulRight (uncleBoundaryLetter A B R L i)) :=
      LinearMap.ext_on_range (uncleBoundary_span_eq_top_succ A B R L hPert n) (hword i)
    exact congrArg (fun f ↦ f N) heq
  intro M N
  have heq : (uncleTracePair X).comp (uncleBoundaryMulRight N) =
      (uncleTracePair Y).comp (uncleBoundaryMulLeft N) :=
    LinearMap.ext_on_range hPert.span_eq_top (fun i ↦ hletter i N)
  exact congrArg (fun f ↦ f M) heq

/-- Scalar sector boundaries give exactly the two actual MPS vectors.
Source: arXiv:1210.6613, Appendix closure proof, lines 1943–1984. -/
theorem uncleBoundaryMap_scalar_blocks
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ) (N : ℕ) (α β : ℂ) :
    uncleBoundaryMap A B R L N
        (uncleBlockMatrix (Matrix.scalar (Fin a) α) 0 0 (Matrix.scalar (Fin b) β)) =
      α • (mpv A : NSiteSpace α N) + β • (mpv B : NSiteSpace α N) := by
  funext σ
  rw [uncleBoundaryMap_apply, uncleBoundaryWord_block, trace_uncleBlockMatrix_mul]
  simp [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.trace_smul, mpv, coeff, smul_eq_mul]

private theorem cyclicTranslateState_one_mpv (A : MPTensor α (Fin a)) (n : ℕ) :
    cyclicTranslateState (1 : Fin (n + 2)) (mpv A : NSiteSpace α (n + 2)) = mpv A := by
  funext σ
  obtain ⟨i, τ, rfl⟩ := Fin.exists_cons σ
  change Matrix.trace (Kraus.evalWord A
    (List.ofFn (cyclicTranslateCfg (1 : Fin (n + 2)) (Fin.cons i τ)))) =
      Matrix.trace (Kraus.evalWord A (List.ofFn (Fin.cons i τ)))
  rw [cyclicTranslateCfg_cons_append, Fin.append_right_eq_snoc,
    List.ofFn_snoc, List.ofFn_cons]
  simp only [Kraus.evalWord_append, Kraus.evalWord_cons, Kraus.evalWord_nil, mul_one]
  exact Matrix.trace_mul_comm _ _

/-- The source periodic closure is derived from full perturbation injectivity
for every chain length at least two. Source: arXiv:1210.6613, Lemma "closure",
lines 1117–1127 and Appendix closure proof, lines 1943–1984. -/
theorem uncleBoundarySpace_inf_cyclicTranslate
    (A : MPTensor α (Fin a)) (B : MPTensor α (Fin b))
    (R : α → Matrix (Fin a) (Fin b) ℂ)
    (L : α → Matrix (Fin b) (Fin a) ℂ)
    (hPert : Kraus.IsInjective (uncleBoundaryLetter A B R L)) (n : ℕ) :
    uncleBoundarySpace A B R L (n + 2) ⊓
        (uncleBoundarySpace A B R L (n + 2)).map
          (cyclicTranslateState (1 : Fin (n + 2))) =
      Submodule.span ℂ {(mpv A : NSiteSpace α (n + 2)), mpv B} := by
  apply le_antisymm
  · rintro ψ ⟨⟨X, rfl⟩, hrotate⟩
    obtain ⟨_, ⟨Y, rfl⟩, hY⟩ := hrotate
    have hword (i : α) (τ : Fin (n + 1) → α) :
        Matrix.trace (uncleBoundaryMul (uncleBoundaryLetter A B R L i)
            (uncleBoundaryWord A B R L (List.ofFn τ)) * X) =
          Matrix.trace (uncleBoundaryMul (uncleBoundaryWord A B R L (List.ofFn τ))
            (uncleBoundaryLetter A B R L i) * Y) := by
      have hc := (congrFun hY (Fin.cons i τ)).symm
      change Matrix.trace (uncleBoundaryWord A B R L (List.ofFn (Fin.cons i τ)) * X) =
        Matrix.trace (uncleBoundaryWord A B R L
          (List.ofFn (cyclicTranslateCfg (1 : Fin (n + 2)) (Fin.cons i τ))) * Y) at hc
      rw [cyclicTranslateCfg_cons_append, Fin.append_right_eq_snoc,
        uncleBoundaryWord_ofFn_cons, uncleBoundaryWord_ofFn_snoc] at hc
      exact hc
    have hpair := uncleBoundary_cyclic_pairing_of_word_pairing A B R L hPert n X Y hword
    have hXY := eq_of_uncleBoundary_cyclic_pairing X Y hpair
    obtain ⟨α, β, hX⟩ := exists_scalar_blocks_of_uncleBoundary_trace_cyclic X
      (by simpa only [← hXY] using hpair)
    rw [hX, uncleBoundaryMap_scalar_blocks]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  · apply Submodule.span_le.mpr
    rintro ψ (rfl | rfl)
    · have hA : (mpv A : NSiteSpace α (n + 2)) ∈ uncleBoundarySpace A B R L (n + 2) := by
        refine ⟨uncleBlockMatrix (Matrix.scalar (Fin a) 1) 0 0
          (Matrix.scalar (Fin b) 0), ?_⟩
        simpa using uncleBoundaryMap_scalar_blocks A B R L (n + 2) 1 0
      exact ⟨hA, ⟨mpv A, hA, cyclicTranslateState_one_mpv A n⟩⟩
    · have hB : (mpv B : NSiteSpace α (n + 2)) ∈ uncleBoundarySpace A B R L (n + 2) := by
        refine ⟨uncleBlockMatrix (Matrix.scalar (Fin a) 0) 0 0
          (Matrix.scalar (Fin b) 1), ?_⟩
        simpa using uncleBoundaryMap_scalar_blocks A B R L (n + 2) 0 1
      exact ⟨hB, ⟨mpv B, hB, cyclicTranslateState_one_mpv B n⟩⟩

end MPSTensor

end

end UnclePeriodicClosure
