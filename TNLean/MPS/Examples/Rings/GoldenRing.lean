/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.AdjoinRoot
import TNLean.MPS.FundamentalTheorem.Compression.ExplicitGauge
import TNLean.MPS.Operator.Product.OperatorProduct
import QICLean.Algebra.Matrix.GoldenInt

/-!
# Golden integers: the ring `ℤ[σ]` with `σ = φ^{-1/2}`

**Source.** Construction of this development. The ring is chosen to hold the Fibonacci data of
Bultinck et al. (arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex`
lines 1244–1260: quantum dimension `d_τ = φ = (1 + √5)/2`, F-symbols
`F^{τττ}_{τ11} = 1/φ`, `F^{τττ}_{ττ1} = F^{τττ}_{τ1τ} = 1/√φ`, `F^{τττ}_{τττ} = -1/φ`, and
`G`-symbols `G^{abc}_{def} = F^{abc}_{def}/(v_e v_f)` with `v_i = √d_i`. The same F-matrix
appears in Feiguin et al. (arXiv:cond-mat/0612341),
`References/cond-mat_0612341/source/fibonacci.tex` lines 163–167.
Review: arXiv:2011.12127, Appendix A, "The MPO for the Fibonacci model"
(`Papers/2011.12127/TN-Review-main.tex` lines 2613–2625).

**Formalized here.** Every such entry lies in the degree-four field `ℚ(σ)`, where `σ = φ^{-1/2}`
satisfies `σ⁴ + σ² - 1 = 0`, and is in fact a `ℤ`-linear combination of `1, σ, σ², σ³`, because
the golden ratio is a unit of that ring, `φ = 1 + σ²` and `φ⁻¹ = σ²`. The file builds the exact
arithmetic of that ring in two layers.

The computational layer is `GoldenInt`, the ring `ℤ[σ]` presented by the four integer
coordinates of an element in the basis `1, σ, σ², σ³`, with the multiplication obtained by
reducing `σ⁴ = 1 - σ²`, `σ⁵ = σ - σ³` and `σ⁶ = 2σ² - 1`. Equality of golden integers is
decidable, so every matrix identity between explicit matrices over `ℤ[σ]` is decidable, exactly
as an identity between integer matrices is.

The algebraic layer identifies those coordinates with an actual algebraic number. The quotient
`ℚ[X] ⧸ (X⁴ + X² - 1)` receives `ℤ[σ]` by a ring homomorphism, and it maps to `ℂ` by sending the
class of `X` to the positive real root `√((√5 - 1)/2)`. The composite `goldenToComplex` is the
embedding along which a matrix over `ℤ[σ]` becomes a complex matrix, and identities proved by
decision over `ℤ[σ]` transport to the complex matrices.

## Main definitions

* `GoldenInt`: the ring `ℤ[σ]` in coordinates.
* `GoldenInt.sigma`: the generator `σ = φ^{-1/2}`.
* `goldenPoly`, `GoldenAdjoin`, `adjoinSigma`: the quartic, the quotient ring it presents, and
  the class of `X` in it.
* `GoldenInt.toAdjoin`, `goldenAdjoinToComplex`, `goldenToComplex`: the two layers of the
  embedding and their composite.
* `MPSTensor.complexOfGolden`, `MPSTensor.mulGoldenTensor`, `MPSTensor.evalWordGolden`: the
  entrywise image of a matrix over `ℤ[σ]` in the complex matrices, the bond-space product and
  word evaluation over `ℤ[σ]`, as the instances at `goldenToComplex` of the general
  `Matrix.complexOfRing`, `MPSTensor.mulTensorR` and `MPSTensor.evalWordR`.

## Main results

* `GoldenInt.sigma_quartic`, `adjoinSigma_quartic`, `goldenSigmaReal_quartic`: the quartic
  relation in the three models.
* `goldenSigmaReal_sq`, `goldenSigmaReal_eq_inv_sqrt_goldenRatio`: `σ² = φ⁻¹` and `σ = 1/√φ`
  for the golden ratio `φ`.
* `goldenMulRule`: the multiplication rule of `ℤ[σ]` in any commutative ring carrying a root of
  the quartic.
* `MPSTensor.complexOfGolden_mul`, `MPSTensor.complexOfGolden_one`: the embedding of matrices is
  multiplicative and unital.
* `MPSTensor.mulTensor_complexOfGolden`, `MPSTensor.evalWord_complexOfGolden`: the bond-space
  product and word evaluation commute with the embedding.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:cond-mat/0612341](https://arxiv.org/abs/cond-mat/0612341) -- A. Feiguin, S. Trebst,
  A. W. W. Ludwig, M. Troyer, A. Kitaev, Z. Wang, M. H. Freedman, *Interacting anyons in
  topological quantum liquids: The golden chain*
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*

## Golden compression: compression data with gauges over `ℤ[σ]`

**Source.** Construction of this development; no paper prints it. It packages the exact
arithmetic shared by the Fibonacci examples (`Examples/Fibonacci.lean`,
`Examples/FibonacciUnit.lean`, `Examples/FibonacciAction.lean`), whose entries come from the
F-symbols of arXiv:1511.08090, Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex`
lines 1250–1260.

**Formalized here.** In the worked examples over the ring `ℤ[σ]` of `GoldenRing.lean`, the
letters of the source tensor, of the target blocks, of the change of bond coordinates and of its
inverse are explicit matrices over `ℤ[σ]`, the conjugated letters `G B^i G⁻¹` are explicit
block-triangular matrices recorded through `B^i G⁻¹ = G⁻¹ K^i`, and every identity between them
is decided in exact arithmetic. The datum is the ring-generic
`MPSTensor.MultiBlockCompression.ofRing` along the embedding `goldenToComplex`.

### Main definitions

* `MPSTensor.MultiBlockCompression.ofGolden`: the multi-block compression datum assembled from a
  gauge over `ℤ[σ]` and the decided block structure of the conjugated letters.

### References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

section

open scoped Matrix

namespace MPSTensor

/-- The entrywise image of a matrix over the golden integers in the complex matrices. -/
noncomputable abbrev complexOfGolden {m n : Type*} (X : Matrix m n GoldenInt) : Matrix m n ℂ :=
  Matrix.complexOfRing goldenToComplex X

@[simp] theorem complexOfGolden_apply {m n : Type*} (X : Matrix m n GoldenInt) (i : m) (j : n) :
    complexOfGolden X i j = goldenToComplex (X i j) := rfl

theorem complexOfGolden_mul {m n o : Type*} [Fintype n] (X : Matrix m n GoldenInt)
    (Y : Matrix n o GoldenInt) :
    complexOfGolden (X * Y) = complexOfGolden X * complexOfGolden Y :=
  Matrix.complexOfRing_mul goldenToComplex X Y

theorem complexOfGolden_one {n : Type*} [DecidableEq n] :
    complexOfGolden (1 : Matrix n n GoldenInt) = 1 :=
  Matrix.complexOfRing_one goldenToComplex

theorem complexOfGolden_zero {m n : Type*} :
    complexOfGolden (0 : Matrix m n GoldenInt) = 0 :=
  Matrix.complexOfRing_zero goldenToComplex

variable {d D D₁ D₂ : ℕ}

/-- Word evaluation of a tensor over the golden integers. -/
abbrev evalWordGolden (A : Fin d → Matrix (Fin D) (Fin D) GoldenInt) :
    List (Fin d) → Matrix (Fin D) (Fin D) GoldenInt :=
  evalWordR A

/-- Word evaluation commutes with the entrywise embedding of the golden integers. -/
theorem evalWord_complexOfGolden (A : Fin d → Matrix (Fin D) (Fin D) GoldenInt)
    (w : List (Fin d)) :
    Kraus.evalWord (fun i => complexOfGolden (A i)) w = complexOfGolden (evalWordGolden A w) :=
  evalWord_complexOfRing goldenToComplex A w

/-- The bond-space product of two tensors over the golden integers,
`(M · N)^{ik} = ∑_j M^{ij} ⊗ N^{jk}`, in the bond order of `finProdFinEquiv`. -/
abbrev mulGoldenTensor (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) GoldenInt)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) GoldenInt) (i k : Fin d) :
    Matrix (Fin (D₁ * D₂)) (Fin (D₁ * D₂)) GoldenInt :=
  mulTensorR M N i k

/-- The bond-space product commutes with the entrywise embedding of the golden integers. -/
theorem mulTensor_complexOfGolden (M : Fin d → Fin d → Matrix (Fin D₁) (Fin D₁) GoldenInt)
    (N : Fin d → Fin d → Matrix (Fin D₂) (Fin D₂) GoldenInt) (i k : Fin d) :
    MPOTensor.mulTensor (Function.uncurry fun i j => complexOfGolden (M i j))
        (Function.uncurry fun i j => complexOfGolden (N i j)) (i, k) =
      complexOfGolden (mulGoldenTensor M N i k) :=
  mulTensor_complexOfRing goldenToComplex M N i k

end MPSTensor

end

section

open scoped Matrix

namespace MPSTensor

variable {d DB : ℕ} {ι : Type*} [DecidableEq ι] {Dι : ι → ℕ} {S : Finset ι}

/-- **A multi-block compression datum from a gauge over `ℤ[σ]`.** The letters of the source
`B` and of the targets `C s` are the entrywise embeddings of the matrices `Bg` and `Cg` over
`ℤ[σ]`; the matrices `G` and `Ginv` over `ℤ[σ]` are mutually inverse; the conjugated letters
`G Bg^i Ginv` are the matrices `K i`, recorded through the identity `Bg^i Ginv = Ginv K^i`; and,
read along the bond coordinates `τ`, each `K i` is block upper triangular for the ordering `ord`
with the target `Cg s` on the diagonal block of the slot `s` and zero on every zero slot. This
is `MultiBlockCompression.ofRing` for the gauge `gaugeOfRingMatrix` over `ℤ[σ]`. -/
noncomputable def MultiBlockCompression.ofGolden {B : MPSTensor d DB}
    {C : ∀ s, MPSTensor d (Dι s)} (z : ℕ) (ord : BlockIndex S z ≃ Fin (S.card + z))
    (τ : BlockSpace Dι S z ≃ Fin DB) (Bg : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt)
    (hB : ∀ i, B i = complexOfGolden (Bg i))
    (Cg : ∀ s, Fin d → Matrix (Fin (Dι s)) (Fin (Dι s)) GoldenInt)
    (hC : ∀ s i, C s i = complexOfGolden (Cg s i))
    (G Ginv : Matrix (Fin DB) (Fin DB) GoldenInt) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (K : Fin d → Matrix (Fin DB) (Fin DB) GoldenInt) (hK : ∀ i, Bg i * Ginv = Ginv * K i)
    (htri : ∀ (i : Fin d) (x y : BlockSpace Dι S z), ord y.1 < ord x.1 → K i (τ x) (τ y) = 0)
    (hmatched : ∀ (i : Fin d) (s : ι) (hs : s ∈ S) (p q : Fin (Dι s)),
      K i (τ ⟨Sum.inl ⟨s, hs⟩, p⟩) (τ ⟨Sum.inl ⟨s, hs⟩, q⟩) = Cg s i p q)
    (hunmatched : ∀ (i : Fin d) (t : Fin z) (p q : Fin 1),
      K i (τ ⟨Sum.inr t, p⟩) (τ ⟨Sum.inr t, q⟩) = 0) :
    MultiBlockCompression B S C :=
  MultiBlockCompression.ofRing goldenToComplex ord τ
    (gaugeOfRingMatrix goldenToComplex τ G Ginv hG hG') K (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix goldenToComplex τ hG hG' (hB i), Matrix.mul_assoc, hK,
        ← Matrix.mul_assoc, hG, Matrix.one_mul])
    Cg hC htri (fun i s p q => hmatched i s.1 s.2 p q) hunmatched

end MPSTensor

end
