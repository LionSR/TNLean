/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingDimension
import TNLean.MPS.MPDO.BondSimilarity
import TNLean.MPS.MPDO.SimpleScaling

/-!
# Ising string-net: the source's G-symbol tensors and the F-symbol blocks

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Appendix D.2 ("Ising string-net"), `References/1511.08090/AnyonsPEPS.tex`
lines 1305–1323: the Ising labels `1, σ, ψ`, the quantum dimensions `d_1 = d_ψ = 1`,
`d_σ = √2`, the F-symbols `F^{σσσ}_{σef} = ± 1/√2` and `F^{ψσψ}_{σσσ} = F^{σψσ}_{ψσσ} = -1`, and
the statement that the operator tensors are built from the G-symbols "similarly as for the
Fibonacci model"; for Fibonacci (lines 1257–1268) the G-symbols are
`G^{abc}_{def} = F^{abc}_{def}/(v_e v_f)`, `v_i = √d_i`, and the operator tensor (figure file
`StringNetMPO_RHS.pdf`) is the crossing of the operator line `f` with a vertical edge line `e`,
with corner plaquettes `b` (upper left), `a` (upper right), `c` (lower left) and `d` (lower
right), and entry `G^{abc}_{def} √(v_a v_b v_c v_d)`.

**Formalized here.** The Ising F-symbols and G-symbols with the factors `v_a = d_a^{1/2}`, the
tetrahedral symmetry `G^{abc}_{def} = G^{fce}_{abd}`, and the source's tensor of each block
`f ∈ {1, ψ, σ}` on the fusion-tree labels `(x', ρ, x)` of the formal tensors: the upper label
`(b, e, a)` is the ket index and the lower label `(c, e, d)` the bra index. A diagonal bond
similarity `g(u, l) = (v_u / v_l)^{1/2}` carries every letter of the source's tensor to the
letter of the block `isingBlock f`, that is `A_1`, `A_ψ` and `(√2)⁻¹ (√2 A_σ)`. Hence the periodic
operators of the source's tensors equal those of `isingBlock` at every length, the source's
tensors form the Ising fusion algebra, and the source's `σ` operator is `(√2)^{-L}` times that of
the stored tensor `isingSigma`. The factors `v_e v_f` omitted by the formal tensors therefore do
not change the periodic operators.

The physical legs of the drawn tensor are double lines carrying the plaquette labels on both
sides of the vertical line; the fusion-tree label `(x', ρ, x)` records the left plaquette, the
edge label and the right plaquette, and the bond letters of the block `f` record the pair of
plaquettes above and below the operator line with `N_{ul}^f > 0`, which is the removal of zero
rows and columns of line 1266.

## Main definitions

* `IsingTwist.isingLoopFactor`: the closed-loop factors `v_a = √d_a`.
* `IsingTwist.isingFSymbol`, `IsingTwist.isingGSymbol`: the complex F-symbols and G-symbols.
* `IsingTwist.isingBondLetter`: the bond letters `(u, l)` of each block.
* `IsingTwist.isingStringNetTensor`: the source's tensor `G^{abc}_{def} √(v_a v_b v_c v_d)`.
* `IsingTwist.isingStringNetGauge`: the diagonal bond gauge `(v_u / v_l)^{1/2}`.

## Main results

* `IsingTwist.isingGSymbol_tetrahedral`: `G^{abc}_{def} = G^{fce}_{abd}`.
* `IsingTwist.isingBlock_apply_eq_fSymbol`: the letters of the formal blocks are F-symbols.
* `IsingTwist.isingStringNetTensor_conj`: the diagonal bond similarity to the formal blocks.
* `IsingTwist.mpo_isingStringNetTensor`: equal periodic operators at every length.
* `IsingTwist.isMPOFusionAlgebra_isingStringNetTensor`: the source's tensors form the Ising
  fusion algebra.
* `IsingTwist.mpo_isingStringNetTensor_sigma`: the source's `σ` operator is `(√2)^{-L}` times
  the operator of `isingSigma`.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

noncomputable section

open scoped Matrix

namespace IsingTwist

open MPOTensor MPSTensor Zsqrtd

/-! ### Closed-loop factors, F-symbols and G-symbols -/

/-- The exponent of `2^{1/4}` in the closed-loop factor: `v_a = (2^{1/4})^{n_a}` with
`n_1 = n_ψ = 0`, `n_σ = 1`. -/
def isingLoopExp : Fin 3 → ℕ := ![0, 0, 1]

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1049–1050 and 1257–1260. The closed-loop
factors `v_a = √d_a` of the Ising quantum dimensions `isingDimension` (line 1312). -/
def isingLoopFactor (a : Fin 3) : ℝ := Real.sqrt (isingDimension a)

/-- The square root `v_a^{1/2} = d_a^{1/4}` of the closed-loop factor. -/
def isingLoopFactorSqrt (a : Fin 3) : ℝ := Real.sqrt (isingLoopFactor a)

theorem isingLoopFactor_pos (a : Fin 3) : 0 < isingLoopFactor a :=
  Real.sqrt_pos.2 (isingDimension_pos a)

theorem isingLoopFactorSqrt_pos (a : Fin 3) : 0 < isingLoopFactorSqrt a :=
  Real.sqrt_pos.2 (isingLoopFactor_pos a)

theorem isingLoopFactor_eq_sq (a : Fin 3) : isingLoopFactor a = isingLoopFactorSqrt a ^ 2 :=
  (Real.sq_sqrt (Real.sqrt_nonneg _)).symm

/-- `√(v_a v_b v_c v_d)` is the product of the square roots of the four factors. -/
theorem sqrt_isingLoopFactor_mul (a b c e : Fin 3) :
    Real.sqrt (isingLoopFactor a * isingLoopFactor b * isingLoopFactor c * isingLoopFactor e) =
      isingLoopFactorSqrt a * isingLoopFactorSqrt b * isingLoopFactorSqrt c *
        isingLoopFactorSqrt e := by
  have h : ∀ x, 0 ≤ isingLoopFactor x := fun x => Real.sqrt_nonneg _
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (h a) (h b)) (h c)),
    Real.sqrt_mul (mul_nonneg (h a) (h b)), Real.sqrt_mul (h a)]
  rfl

/-- Every closed-loop factor is a power of `v_σ = 2^{1/4}`. -/
theorem isingLoopFactor_eq_pow (a : Fin 3) :
    isingLoopFactor a = isingLoopFactor 2 ^ isingLoopExp a := by
  fin_cases a <;> simp [isingLoopFactor, isingLoopExp, isingDimension]

/-- `v_σ² = √2`. -/
theorem isingLoopFactor_two_sq : isingLoopFactor 2 ^ 2 = Real.sqrt 2 := by
  rw [isingLoopFactor, Real.sq_sqrt (isingDimension_pos 2).le]
  simp [isingDimension]

/-- The Ising F-symbols scaled by `√2`, over `ℤ[√2]`. Source: arXiv:1511.08090,
`AnyonsPEPS.tex` lines 1245–1250 (the selection rule `δ_{abe} δ_{cde} δ_{adf} δ_{bcf}`, with
`δ_{ijk} = 1` when `N_{ij}^k > 0`) and lines 1314–1321 (the values): `√2 F^{σσσ}_{σef}` is `-1`
at `e = f = ψ` and `1` otherwise, `√2 F^{ψσψ}_{σσσ} = √2 F^{σψσ}_{ψσσ} = -√2`, and every other
admissible entry is `√2`. -/
def isingFSymbolZ (a b c d e f : Fin 3) : ℤ√2 :=
  if 0 < isingFusion a b e ∧ 0 < isingFusion c d e ∧ 0 < isingFusion a d f ∧
      0 < isingFusion b c f then
    if a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 2 then
      if e = 1 ∧ f = 1 then -1 else 1
    else if (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 2 ∧ e = 2 ∧ f = 2) ∨
        (a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 1 ∧ e = 2 ∧ f = 2) then -sqrtd
    else sqrtd
  else 0

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1245–1250 and 1314–1321. The complex
Ising F-symbols `F^{abc}_{def}`, labels in the order `1, ψ, σ`. -/
def isingFSymbol (a b c d e f : Fin 3) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ * zsqrt2ToComplex (isingFSymbolZ a b c d e f)

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1257–1260, eq. `eq:Gsymbol`, applied to the
Ising category as prescribed at line 1323. The complex G-symbols
`G^{abc}_{def} = F^{abc}_{def}/(v_e v_f)`. -/
def isingGSymbol (a b c d e f : Fin 3) : ℂ :=
  isingFSymbol a b c d e f / ((isingLoopFactor e : ℂ) * (isingLoopFactor f : ℂ))

/-- The scaled form of the tetrahedral symmetry: `F^{abc}_{def} (2^{1/4})^{n_b + n_d}` equals
`F^{fce}_{abd} (2^{1/4})^{n_e + n_f}`, written with even exponents so that it is an identity in
`ℤ[√2]`. -/
private theorem isingFSymbolZ_tetrahedral : ∀ a b c d e f : Fin 3,
    (isingFSymbolZ a b c d e f = 0 ∧ isingFSymbolZ f c e a b d = 0) ∨
      ((isingLoopExp b + isingLoopExp d + isingLoopExp e + isingLoopExp f) % 2 = 0 ∧
        isingFSymbolZ a b c d e f *
            sqrtd ^ ((isingLoopExp b + isingLoopExp d + isingLoopExp e + isingLoopExp f) / 2) =
          isingFSymbolZ f c e a b d * sqrtd ^ (isingLoopExp e + isingLoopExp f)) := by
  decide +kernel

/-- The Ising G-symbols have the tetrahedral symmetry `G^{abc}_{def} = G^{fce}_{abd}`. -/
theorem isingGSymbol_tetrahedral (a b c d e f : Fin 3) :
    isingGSymbol a b c d e f = isingGSymbol f c e a b d := by
  set t : ℂ := (isingLoopFactor 2 : ℂ) with ht_def
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.2 (isingLoopFactor_pos 2).ne'
  have hv : ∀ x, (isingLoopFactor x : ℂ) = t ^ isingLoopExp x := fun x => by
    rw [ht_def, ← Complex.ofReal_pow, ← isingLoopFactor_eq_pow]
  have ht2 : t ^ 2 = zsqrt2ToComplex sqrtd := by
    rw [zsqrt2ToComplex_sqrtd, ht_def, ← Complex.ofReal_pow, isingLoopFactor_two_sq]
  simp only [isingGSymbol, isingFSymbol, hv]
  rcases isingFSymbolZ_tetrahedral a b c d e f with ⟨h1, h2⟩ | ⟨hpar, hkey⟩
  · simp [h1, h2]
  · have hk := congrArg zsqrt2ToComplex hkey
    simp only [map_mul, map_pow] at hk
    rw [← ht2, ← pow_mul, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hpar)] at hk
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
    rw [div_eq_div_iff (by simp [ht]) (by simp [ht])]
    apply mul_right_cancel₀ (pow_ne_zero (isingLoopExp e + isingLoopExp f) ht)
    calc _ = (Real.sqrt 2 : ℂ)⁻¹ * (zsqrt2ToComplex (isingFSymbolZ a b c d e f) *
          t ^ (isingLoopExp b + isingLoopExp d + isingLoopExp e + isingLoopExp f)) := by ring
      _ = _ := by rw [hk]; ring

/-! ### The formal blocks as F-symbol tensors -/

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 1266. The bond letters of the block `f`: the
pairs `(u, l)` of plaquettes above and below the operator line with `N_{ul}^f > 0`, in the bond
order of the formal tensors `isingOneZ`, `isingPsiZ`, `isingSigmaZ`. -/
def isingBondLetter : (f : Fin 3) → Fin (isingDim f) → Fin 3 × Fin 3
  | 0 => ![(0, 0), (1, 1), (2, 2)]
  | 1 => ![(1, 0), (0, 1), (2, 2)]
  | 2 => ![(2, 0), (2, 1), (0, 2), (1, 2)]

/-- The letters of the formal blocks over `ℤ[√2]`, the `σ` block stored as `√2 A_σ`. -/
def isingBlockLetterZ :
    (f : Fin 3) → Fin 10 → Fin 10 → Matrix (Fin (isingDim f)) (Fin (isingDim f)) (ℤ√2)
  | 0 => isingOneZ
  | 1 => isingPsiZ
  | 2 => isingSigmaZ

/-- The factor that puts the formal letters of `isingBlockLetterZ` on the scale `√2 F`. -/
def isingBlockScaleZ : Fin 3 → ℤ√2 := ![sqrtd, sqrtd, 1]

/-- The letters of the formal blocks are the F-symbols `√2 F^{f c e}_{a b d}` at the upper label
`(b, e, a)` and the lower label `(c, e, d)`, with bond letters `(b, c)` and `(a, d)`. -/
private theorem isingBlockLetterZ_eq_fSymbol : ∀ (f : Fin 3) (h h' : Fin 10)
    (p q : Fin (isingDim f)),
    isingBlockScaleZ f * isingBlockLetterZ f h h' p q =
      if isingRho h = isingRho h' ∧ isingBondLetter f p = (isingLeft h, isingLeft h') ∧
          isingBondLetter f q = (isingRight h, isingRight h') then
        isingFSymbolZ f (isingLeft h') (isingRho h) (isingRight h) (isingLeft h) (isingRight h')
      else 0 := by
  decide +kernel

/-- Bridge: every entry of the block `isingBlock f` is the F-symbol `F^{f c e}_{a b d}` at the
upper label `h = (b, e, a)`, the lower label `h' = (c, e, d)` and the bond letters `p = (b, c)`,
`q = (a, d)`, and zero otherwise. -/
theorem isingBlock_apply_eq_fSymbol (f : Fin 3) (h h' : Fin 10) (p q : Fin (isingDim f)) :
    isingBlock f h h' p q =
      if isingRho h = isingRho h' ∧ isingBondLetter f p = (isingLeft h, isingLeft h') ∧
          isingBondLetter f q = (isingRight h, isingRight h') then
        isingFSymbol f (isingLeft h') (isingRho h) (isingRight h) (isingLeft h) (isingRight h')
      else 0 := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have key : isingBlock f h h' p q = (Real.sqrt 2 : ℂ)⁻¹ *
      zsqrt2ToComplex (isingBlockScaleZ f * isingBlockLetterZ f h h' p q) := by
    match f, p, q with
    | 0, p, q =>
      simp [isingBlock, isingBlockScaleZ, isingBlockLetterZ, isingOne, hs]
      rfl
    | 1, p, q =>
      simp [isingBlock, isingBlockScaleZ, isingBlockLetterZ, isingPsi, hs]
      rfl
    | 2, p, q =>
      simp [isingBlock, isingBlockScaleZ, isingBlockLetterZ, isingSigma]
      rfl
  rw [key, isingBlockLetterZ_eq_fSymbol]
  split_ifs <;> simp [isingFSymbol]

/-! ### The source's tensor and the bond similarity -/

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` lines 1262–1266 (figure file
`StringNetMPO_RHS.pdf`) and line 1323. The string-net operator tensor of the block `f`: at the
upper label `h = (b, e, a)` (ket), the lower label `h' = (c, e', d)` (bra), the left bond letter
`p` and the right bond letter `q`, its entry is `G^{abc}_{def} √(v_a v_b v_c v_d)` when the edge
label passes through, `e' = e`, and `p = (b, c)`, `q = (a, d)`, and zero otherwise. -/
def isingStringNetTensor (f : Fin 3) : MPOTensor 10 (isingDim f) := fun h h' =>
  Matrix.of fun p q =>
    if isingRho h = isingRho h' ∧ isingBondLetter f p = (isingLeft h, isingLeft h') ∧
        isingBondLetter f q = (isingRight h, isingRight h') then
      isingGSymbol (isingRight h) (isingLeft h) (isingLeft h') (isingRight h') (isingRho h) f *
        ((Real.sqrt (isingLoopFactor (isingRight h) * isingLoopFactor (isingLeft h) *
          isingLoopFactor (isingLeft h') * isingLoopFactor (isingRight h')) : ℝ) : ℂ)
    else 0

/-- The diagonal bond gauge `g(u, l) = (v_u / v_l)^{1/2}` of the block `f`. -/
def isingStringNetGauge (f : Fin 3) (p : Fin (isingDim f)) : ℂ :=
  ((isingLoopFactorSqrt (isingBondLetter f p).1 / isingLoopFactorSqrt (isingBondLetter f p).2 :
    ℝ) : ℂ)

theorem isingStringNetGauge_ne_zero (f : Fin 3) (p : Fin (isingDim f)) :
    isingStringNetGauge f p ≠ 0 :=
  Complex.ofReal_ne_zero.2 (div_pos (isingLoopFactorSqrt_pos _) (isingLoopFactorSqrt_pos _)).ne'

/-- Bridge: the diagonal bond similarity `g(u, l) = (v_u/v_l)^{1/2}` carries every letter of the
source's tensor (arXiv:1511.08090, `AnyonsPEPS.tex` lines 1262–1266) to the letter of the formal
block: `g S^{h h'} g⁻¹ = isingBlock f h h'`. The G-symbol is moved to the F-symbol slots of
`isingBlock_apply_eq_fSymbol` by the tetrahedral symmetry, and the factors
`√(v_a v_b v_c v_d)/(v_b v_d)` are absorbed by `g`. -/
theorem isingStringNetTensor_conj (f : Fin 3) (h h' : Fin 10) :
    Matrix.diagonal (isingStringNetGauge f) * isingStringNetTensor f h h' *
        Matrix.diagonal (isingStringNetGauge f)⁻¹ = isingBlock f h h' := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, isingBlock_apply_eq_fSymbol]
  simp only [isingStringNetTensor, Matrix.of_apply]
  split_ifs with hc
  · obtain ⟨-, hp, hq⟩ := hc
    rw [isingGSymbol_tetrahedral, isingGSymbol, sqrt_isingLoopFactor_mul,
      isingLoopFactor_eq_sq (isingLeft h), isingLoopFactor_eq_sq (isingRight h')]
    simp only [isingStringNetGauge, hp, hq, Pi.inv_apply]
    have h1 := (isingLoopFactorSqrt_pos (isingLeft h)).ne'
    have h2 := (isingLoopFactorSqrt_pos (isingLeft h')).ne'
    have h3 := (isingLoopFactorSqrt_pos (isingRight h)).ne'
    have h4 := (isingLoopFactorSqrt_pos (isingRight h')).ne'
    push_cast
    field_simp
    rw [div_eq_iff (by simp [h1, h2, h3, h4])]
    ring
  · simp

/-- Bridge: the periodic operators of the source's tensors (arXiv:1511.08090, `AnyonsPEPS.tex`
lines 1262–1266 and 1323) equal those of the formal blocks `isingBlock`, at every length, by
`MPOTensor.mpo_eq_of_conj`. -/
theorem mpo_isingStringNetTensor (f : Fin 3) (L : ℕ) :
    mpo (isingStringNetTensor f) L = mpo (isingBlock f) L := by
  have hg := isingStringNetGauge_ne_zero f
  refine mpo_eq_of_conj ?_ ?_ (isingStringNetTensor_conj f) L
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun p => mul_inv_cancel₀ (hg p))
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun p => inv_mul_cancel₀ (hg p))

/-- The analogue of arXiv:1511.08090, `AnyonsPEPS.tex` line 1268, for the Ising category
(line 1323): the source's tensors of the blocks `1, ψ, σ` satisfy the Ising fusion rules at every
positive length. This is `isMPOFusionAlgebra_ising` transported along
`mpo_isingStringNetTensor`. -/
theorem isMPOFusionAlgebra_isingStringNetTensor :
    IsMPOFusionAlgebra isingStringNetTensor isingFusion := by
  intro a b L hL
  simp only [mpo_isingStringNetTensor]
  exact isMPOFusionAlgebra_ising a b L hL

/-- Bridge: the periodic operator of the source's `σ` tensor is `(√2)^{-L}` times that of the
stored tensor `isingSigma = √2 A_σ`, the scalar of the Local fix (sigma scaling). -/
theorem mpo_isingStringNetTensor_sigma (L : ℕ) :
    mpo (isingStringNetTensor 2) L = ((Real.sqrt 2 : ℂ)⁻¹) ^ L • mpo isingSigma L := by
  rw [mpo_isingStringNetTensor]
  exact mpo_smul _ _ _

end IsingTwist
