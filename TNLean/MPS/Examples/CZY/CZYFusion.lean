/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.GeneralizeDecide
import TNLean.MPS.Examples.CZY.CZYReduced

/-!
# CZY fusion maps and associativity on the physical images

The printed fusion matrices in arXiv:2509.03600, Section II and Appendix B,
satisfy the local intertwining identities, and the two full bond-space fusions
at `(1,1,1)` differ by a minus sign.

**Local fix (associativity):** The printed relation for every triple fails on the full
virtual space. At `(0,0,0)` no complex scalar relates the two maps. After a change of
normalization the expected phase relation holds on the images of the three-layer physical
letters. This corrected statement is proved over the integers and complexes and extends to all
nonempty physical words; the scalar is `-1`
exactly at `(1,1,1)`. The source assertion, counterexample and corrected formulation are
recorded in `docs/paper-gaps/lmsvkl25_czy_associator.tex`.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators

namespace CZYCompression

open MPSTensor CZXCompression

/-- The first three rows of the integer matrix `√2 X₁₁`
(arXiv:2509.03600, Appendix B, main.tex lines 664–673 and 716). -/
def czyY11Int : Matrix (Fin 3) (Fin 4) ℤ := czyX11Int.submatrix Fin.castSucc id

/-- The first two rows of `X₀₁`
(arXiv:2509.03600, Appendix B, main.tex lines 675–687 and 716). -/
def czyY01Int : Matrix (Fin 2) (Fin 6) ℤ := !![0, 0, 1, 0, 0, -1; 0, 0, 0, 1, -1, 0]

/-- The first two rows of `X₁₀`
(arXiv:2509.03600, Appendix B, main.tex lines 689–701 and 716). -/
def czyY10Int : Matrix (Fin 2) (Fin 6) ℤ := !![0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 1, 0]

/-- The printed fusion map `Y₁₁`, with normalization `1 / √2`
(arXiv:2509.03600, Appendix B, main.tex lines 664–673 and 716). -/
def czyY11 : Matrix (Fin 3) (Fin 4) ℂ := Complex.invSqrtTwo • complexOfInt czyY11Int

/-- The printed fusion map `Y₀₁`
(arXiv:2509.03600, Appendix B, main.tex lines 675–687 and 716). -/
def czyY01 : Matrix (Fin 2) (Fin 6) ℂ := complexOfInt czyY01Int

/-- The printed fusion map `Y₁₀`
(arXiv:2509.03600, Appendix B, main.tex lines 689–701 and 716). -/
def czyY10 : Matrix (Fin 2) (Fin 6) ℂ := complexOfInt czyY10Int

/-- The fusion map is precisely the first three rows of the existing change of basis. -/
theorem czyY11_eq_submatrix : czyY11 = czyX11.submatrix Fin.castSucc id := by rfl

private theorem czyY11Int_fusion (i k : Fin 2) :
    czyY11Int * mulIntTensor czyIntTensor czyIntTensor i k =
    czyReducedIntTensor i k * czyY11Int := by
  revert_decide_kernel i k

private theorem czyY01Int_fusion (i k : Fin 2) :
    czyY01Int * mulIntTensor czyReducedIntTensor czyIntTensor i k =
    czyIntTensor i k * czyY01Int := by
  revert_decide_kernel i k

private theorem czyY10Int_fusion (i k : Fin 2) :
    czyY10Int * mulIntTensor czyIntTensor czyReducedIntTensor i k =
    czyIntTensor i k * czyY10Int := by
  revert_decide_kernel i k

/-- The two printed fusions at `(1,1,1)` differ by a minus sign
(arXiv:2509.03600, Section II, main.tex lines 283–294). This is an equality on the full
triple bond space; it does not assert the scalar relation at other triples. -/
theorem czyFusion_nontrivial_triple :
    czyY01 * (czyY11 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm =
    -(czyY10 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ czyY11).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [czyY01, czyY10, czyY11, czyY01Int, czyY10Int, czyY11Int, czyX11Int,
      complexOfInt, complexOfRing, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.one_apply]

/-- No scalar relates the printed fusions at `(0,0,0)`: the entry `(0,24)` is two on the
left and zero on the right. This refutes the unrestricted relation in arXiv:2509.03600,
Section II, main.tex lines 283–294; see `docs/paper-gaps/lmsvkl25_czy_associator.tex`. -/
theorem czyFusion_printed_neutral_no_scalar : ¬ ∃ ω : ℂ,
    complexOfInt czyY00Int *
      ((complexOfInt czyY00Int) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm =
    ω • (complexOfInt czyY00Int *
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (complexOfInt czyY00Int)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  rintro ⟨ω, h⟩
  have he := congrArg (fun M => M 0 24) h
  norm_num [czyY00Int, complexOfInt, complexOfRing, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.one_apply] at he

/-- The printed one-sided fusion identity
(arXiv:2509.03600, Section II, eq:Ydef, main.tex lines 249–253). -/
theorem czyY01_fusion (i k : Fin 2) : czyY01 * MPOTensor.mulTensor czyReducedTensor czyTensor i k =
    czyTensor i k * czyY01 := by
  rw [show MPOTensor.mulTensor czyReducedTensor czyTensor i k =
      complexOfInt (mulIntTensor czyReducedIntTensor czyIntTensor i k) from
    mulTensor_complexOfRing _ czyReducedIntTensor czyIntTensor i k]
  simpa only [czyY01, czyTensor, complexOfInt_mul]
    using congrArg complexOfInt (czyY01Int_fusion i k)

/-- The printed one-sided fusion identity
(arXiv:2509.03600, Section II, eq:Ydef, main.tex lines 249–253). -/
theorem czyY10_fusion (i k : Fin 2) : czyY10 * MPOTensor.mulTensor czyTensor czyReducedTensor i k =
    czyTensor i k * czyY10 := by
  rw [show MPOTensor.mulTensor czyTensor czyReducedTensor i k =
      complexOfInt (mulIntTensor czyIntTensor czyReducedIntTensor i k) from
    mulTensor_complexOfRing _ czyIntTensor czyReducedIntTensor i k]
  simpa only [czyY10, czyTensor, complexOfInt_mul]
    using congrArg complexOfInt (czyY10Int_fusion i k)

/-- The printed one-sided fusion identity
(arXiv:2509.03600, Section II, eq:Ydef, main.tex lines 249–253). -/
theorem czyY11_fusion (i k : Fin 2) : czyY11 * MPOTensor.mulTensor czyTensor czyTensor i k =
    czyReducedTensor i k * czyY11 := by
  rw [show MPOTensor.mulTensor czyTensor czyTensor i k =
      complexOfInt (mulIntTensor czyIntTensor czyIntTensor i k) from
    mulTensor_complexOfRing _ czyIntTensor czyIntTensor i k]
  simp only [czyY11, czyReducedTensor, Matrix.smul_mul, Matrix.mul_smul,
    ← complexOfInt_mul]
  exact congrArg (fun M => Complex.invSqrtTwo • complexOfInt M) (czyY11Int_fusion i k)

/-! ### Associativity on the physical images -/

/-- Bond dimensions of the existing tensors `A₀` and `A₁`. -/
def czyDim : Fin 2 → ℕ
  | 0 => 3
  | 1 => 2

/-- The existing integer tensors of arXiv:2509.03600, Section II, main.tex lines 203–240. -/
def czyFamilyInt (a : Fin 2) : Fin 2 → Fin 2 → Matrix (Fin (czyDim a)) (Fin (czyDim a)) ℤ :=
  match a with
  | 0 => czyReducedIntTensor
  | 1 => czyIntTensor

/-- An integer normalization of the fusion maps: `F₀₀ = Y₀₀`, `F₀₁ = 2Y₀₁`,
`F₁₀ = 2Y₁₀`, and `F₁₁ = 2√2 Y₁₁`, with product bond coordinates.
The scalar associator relation holds after one physical-site contraction; see
`docs/paper-gaps/lmsvkl25_czy_associator.tex` for the correction to arXiv:2509.03600,
Section II, main.tex lines 283–294. -/
def czyFusionInt (a b : Fin 2) :
    Matrix (Fin (czyDim (a + b))) (Fin (czyDim a) × Fin (czyDim b)) ℤ :=
  match a, b with
  | 0, 0 => czyY00Int.submatrix id finProdFinEquiv
  | 0, 1 => (2 • czyY01Int).submatrix id finProdFinEquiv
  | 1, 0 => (2 • czyY10Int).submatrix id finProdFinEquiv
  | 1, 1 => (2 • czyY11Int).submatrix id finProdFinEquiv

/-- The three-layer tensor with bond order `((a,b),c)`. -/
def czyTripleInt (a b c i k : Fin 2) :
    Matrix ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c))
      ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c)) ℤ :=
  ∑ j : Fin 2, ∑ l : Fin 2,
    (czyFamilyInt a i j ⊗ₖ czyFamilyInt b j l) ⊗ₖ czyFamilyInt c l k

/-- The left fusion `Fₐ₊ᵦ,𝒸 (Fₐ,ᵦ ⊗ I𝒸)` in the product bond coordinates. -/
def czyLeftInt (a b c : Fin 2) :
    Matrix (Fin (czyDim (a + b + c)))
      ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c)) ℤ :=
  czyFusionInt (a + b) c * (czyFusionInt a b ⊗ₖ (1 : Matrix (Fin (czyDim c)) _ ℤ))

/-- The right fusion `Fₐ,ᵦ₊𝒸 (Iₐ ⊗ Fᵦ,𝒸)`, with both bond orders identified. -/
def czyRightInt (a b c : Fin 2) :
    Matrix (Fin (czyDim (a + b + c)))
      ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c)) ℤ :=
  (czyFusionInt a (b + c) * ((1 : Matrix (Fin (czyDim a)) _ ℤ) ⊗ₖ czyFusionInt b c)).submatrix
    (Fin.cast (congrArg czyDim (add_assoc a b c))) (fun x => (x.1.1, x.1.2, x.2))

private theorem czyFusion_supported_associativity_int_000 (i k : Fin 2) :
    czyLeftInt 0 0 0 * czyTripleInt 0 0 0 i k =
      (1 : ℤ) • (czyRightInt 0 0 0 * czyTripleInt 0 0 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_001 (i k : Fin 2) :
    czyLeftInt 0 0 1 * czyTripleInt 0 0 1 i k =
      (1 : ℤ) • (czyRightInt 0 0 1 * czyTripleInt 0 0 1 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_010 (i k : Fin 2) :
    czyLeftInt 0 1 0 * czyTripleInt 0 1 0 i k =
      (1 : ℤ) • (czyRightInt 0 1 0 * czyTripleInt 0 1 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_011 (i k : Fin 2) :
    czyLeftInt 0 1 1 * czyTripleInt 0 1 1 i k =
      (1 : ℤ) • (czyRightInt 0 1 1 * czyTripleInt 0 1 1 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_100 (i k : Fin 2) :
    czyLeftInt 1 0 0 * czyTripleInt 1 0 0 i k =
      (1 : ℤ) • (czyRightInt 1 0 0 * czyTripleInt 1 0 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_101 (i k : Fin 2) :
    czyLeftInt 1 0 1 * czyTripleInt 1 0 1 i k =
      (1 : ℤ) • (czyRightInt 1 0 1 * czyTripleInt 1 0 1 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_110 (i k : Fin 2) :
    czyLeftInt 1 1 0 * czyTripleInt 1 1 0 i k =
      (1 : ℤ) • (czyRightInt 1 1 0 * czyTripleInt 1 1 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_111 (i k : Fin 2) :
    czyLeftInt 1 1 1 * czyTripleInt 1 1 1 i k =
      ((-1 : ℤ) : ℤ) • (czyRightInt 1 1 1 * czyTripleInt 1 1 1 i k) := by
  revert_decide_kernel i k

/-- The normalized fusion maps have phase `-1` exactly at the nontrivial triple
after contraction with a physical letter. This is the restricted correction to
arXiv:2509.03600, Section II, main.tex lines 283–294, described in
`docs/paper-gaps/lmsvkl25_czy_associator.tex`.

The finite certificate is split by fusion triple, so that the eight kernel checks are
independent declarations. -/
theorem czyFusion_supported_associativity_int (a b c i k : Fin 2) :
    czyLeftInt a b c * czyTripleInt a b c i k =
      (if a = 1 ∧ b = 1 ∧ c = 1 then (-1 : ℤ) else 1) •
        (czyRightInt a b c * czyTripleInt a b c i k) := by
  match a, b, c with
  | 0, 0, 0 => exact czyFusion_supported_associativity_int_000 i k
  | 0, 0, 1 => exact czyFusion_supported_associativity_int_001 i k
  | 0, 1, 0 => exact czyFusion_supported_associativity_int_010 i k
  | 0, 1, 1 => exact czyFusion_supported_associativity_int_011 i k
  | 1, 0, 0 => exact czyFusion_supported_associativity_int_100 i k
  | 1, 0, 1 => exact czyFusion_supported_associativity_int_101 i k
  | 1, 1, 0 => exact czyFusion_supported_associativity_int_110 i k
  | 1, 1, 1 => exact czyFusion_supported_associativity_int_111 i k

/-- Complex form of the normalized associator relation on one physical-site image.
This is the corrected formulation documented in
`docs/paper-gaps/lmsvkl25_czy_associator.tex`. -/
theorem czyFusion_supported_associativity (a b c i k : Fin 2) :
    complexOfInt (czyLeftInt a b c) * complexOfInt (czyTripleInt a b c i k) =
      (if a = 1 ∧ b = 1 ∧ c = 1 then (-1 : ℂ) else 1) •
        (complexOfInt (czyRightInt a b c) * complexOfInt (czyTripleInt a b c i k)) := by
  have h := congrArg complexOfInt (czyFusion_supported_associativity_int a b c i k)
  split_ifs at h ⊢ <;>
    simpa only [complexOfInt_zsmul, complexOfInt_mul, Int.cast_neg, Int.cast_one] using h

/-- The corrected scalar relation holds after contraction with every nonempty physical
word. Thus it holds on the sum of their image subspaces; see
`docs/paper-gaps/lmsvkl25_czy_associator.tex`. -/
theorem czyFusion_supported_associativity_word (a b c : Fin 2) (w : List (Fin 2 × Fin 2))
    (hw : w ≠ []) :
    complexOfInt (czyLeftInt a b c) *
      (w.map fun p => complexOfInt (czyTripleInt a b c p.1 p.2)).prod =
    (if a = 1 ∧ b = 1 ∧ c = 1 then (-1 : ℂ) else 1) •
      (complexOfInt (czyRightInt a b c) *
      (w.map fun p => complexOfInt (czyTripleInt a b c p.1 p.2)).prod) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons p w =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, czyFusion_supported_associativity,
      Matrix.smul_mul, Matrix.mul_assoc]

end CZYCompression
