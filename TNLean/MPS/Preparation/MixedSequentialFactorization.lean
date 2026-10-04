/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SequentialFactorization
import QICLean.Algebra.MatrixIsometryKronecker

/-!
# Two-sided sequential factorization with a central input

For a matrix product map, the inverse polar factor can be placed at any chosen
physical site. Successive isometric decompositions run inward from the two
boundaries and leave a central tensor whose input is the original virtual pair.
The central tensor is itself an isometry whenever the whole map is one.

The left and right bond dimensions are bounded by `D²`. No monotonicity of
successive bond dimensions is asserted. The physical sites of the right chain
are listed from the right boundary toward the centre.

Source: arXiv:2307.01696, equations (13)–(15), especially footnote 4.

**Scope restriction (injective polar input):** the polar-factorization theorems below
assume the blocked tensor is injective. Footnote 3 also allows non-injective tensors
using the pseudoinverse; their mixed factorization on the polar support is not proved here.
Documented in `docs/paper-gaps/mswc24_mixed_polar_injectivity_scope.tex`.
-/

open scoped BigOperators Matrix Kronecker

namespace MPSPreparation

open MPSChainTensor (eval)
open MPSTensor (virtualPairEquiv)

variable {d D n : ℕ}

/-- The entries of a chain product, with its two virtual indices joined into one. -/
def chainPairMatrix (A : MPSChainTensor d D n) :
    Matrix (Fin n → Fin d) (Fin (D * D)) ℂ :=
  Matrix.of fun σ x => eval A σ (virtualPairEquiv D x).1 (virtualPairEquiv D x).2

/-- Evaluation of an isometric chain on its final bond block and first boundary row. -/
def sequentialEvaluation (hD : 0 < D) (b : Fin (n + 1) → ℕ)
    (Q : MPSChainTensor d D n) (hb : b (Fin.last n) ≤ D) :
    Matrix (Fin n → Fin d) (Fin (b (Fin.last n))) ℂ :=
  Matrix.of fun σ x => eval Q σ ⟨0, hD⟩ (Fin.castLE hb x)

/-- The columns of an isometric chain, restricted to its final bond block,
are orthonormal when its first bond is one-dimensional. -/
theorem sequentialEvaluation_isIsometry (hD : 0 < D) (b : Fin (n + 1) → ℕ)
    (Q : MPSChainTensor d D n) (hb : b (Fin.last n) ≤ D) (h0 : b 0 = 1)
    (hrow : ∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i))
    (hiso : ∀ p, IsIsometryOn (b p.succ) (Q p)) :
    (sequentialEvaluation hD b Q hb).IsIsometry := by
  classical
  let e (x : Fin (b (Fin.last n))) : Fin D → ℂ := Pi.single (Fin.castLE hb x) 1
  have hs (x : Fin (b (Fin.last n))) : IsSupportedBelow (b (Fin.last n)) (e x) := by
    intro β hβ
    have hne : β ≠ Fin.castLE hb x := by
      intro heq
      subst β
      exact (not_le.mpr x.isLt) hβ
    simp [e, hne]
  change (sequentialEvaluation hD b Q hb)ᴴ * sequentialEvaluation hD b Q hb = 1
  ext x y
  have h := sum_star_eval_mulVec_dotProduct b Q hrow hiso (e x) (e y) (hs x) (hs y)
  have hz (σ : Fin n → Fin d) :
      star (eval Q σ *ᵥ e x) ⬝ᵥ (eval Q σ *ᵥ e y) =
        star (sequentialEvaluation hD b Q hb σ x) * sequentialEvaluation hD b Q hb σ y := by
    have hsupport := isSupportedBelow_eval_mulVec b Q hrow (e x) (hs x) σ
    rw [h0] at hsupport
    rw [dotProduct, Finset.sum_eq_single ⟨0, hD⟩]
    · simp [sequentialEvaluation, e]
    · intro β _ hβ
      rw [Pi.star_apply, hsupport β (Nat.one_le_iff_ne_zero.mpr fun h => hβ (Fin.ext h))]
      simp
    · simp
  simp_rw [hz] at h
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, e, ← Pi.single_star,
    Pi.single_apply, Fin.ext_iff, Matrix.one_apply, eq_comm] using h

/-- Successive decompositions of a chain factor its matrix of virtual-pair
coefficients as an isometric sequential evaluation times one remainder matrix.
Every intermediate bond is bounded by `D²`. -/
theorem exists_chainPairMatrix_factorization (hD : 0 < D) (A : MPSChainTensor d D n) :
    ∃ (b : Fin (n + 1) → ℕ) (Q : MPSChainTensor d (D * D) n)
      (hb : ∀ k, b k ≤ D * D)
      (R : Matrix (Fin (b (Fin.last n))) (Fin (D * D)) ℂ),
      b 0 = 1 ∧
      (∀ p i, IsRowSupportedBelow (b p.castSucc) (Q p i)) ∧
      (∀ p i α β, b p.succ ≤ β.val → Q p i α β = 0) ∧
      (∀ p, IsIsometryOn (b p.succ) (Q p)) ∧
      (sequentialEvaluation (Nat.mul_pos hD hD) b Q (hb _)).IsIsometry ∧
      chainPairMatrix A = sequentialEvaluation (Nat.mul_pos hD hD) b Q (hb _) * R := by
  classical
  have hDD := Nat.mul_pos hD hD
  let J : Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
    Matrix.vecMulVec (Pi.single ⟨0, hDD⟩ 1) (pairJoin D)
  have hJ : IsRowSupportedBelow 1 J := by
    intro α β hα
    simp [J, Matrix.vecMulVec_apply, Fin.ext_iff,
      show α.val ≠ 0 by omega]
  obtain ⟨b, Q, R, h0, hb, -, hrow, hcol, hiso, hR, hprod⟩ :=
    exists_isometric_chain_mul n 1 hDD J hJ fun p i => pairEmbed D (A p i)
  refine ⟨b, Q, hb, R.submatrix (Fin.castLE (hb _)) id, h0, hrow, hcol, hiso,
    sequentialEvaluation_isIsometry hDD b Q (hb _) h0 hrow hiso, ?_⟩
  ext σ x
  have h := congrFun₂ (hprod σ) ⟨0, hDD⟩ x
  rw [eval_pairEmbed, Matrix.mul_apply] at h
  have hj : ∑ j, J ⟨0, hDD⟩ j * pairEmbed D (eval A σ) j x = chainPairMatrix A σ x := by
    simpa [J, Matrix.vecMulVec_apply, chainPairMatrix] using
      sum_pairJoin_mul_pairEmbed (eval A σ) x
  rw [hj] at h
  rw [h, Matrix.mul_apply, Matrix.mul_apply]
  rw [Fin.sum_castLE_extend_zero _ (hb (Fin.last n))]
  refine Finset.sum_congr rfl fun β _ => ?_
  split_ifs with hβ
  · rfl
  · simp [hR β x (not_lt.mp hβ)]

/-- The central site with the virtual-pair input attached. The right virtual pair
is ordered from the right boundary toward the centre. -/
def centralInputMatrix (A : MPSTensor d D)
    (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) :
    Matrix (Fin (D * D) × Fin d × Fin (D * D)) (Fin (D * D)) ℂ :=
  Matrix.of fun z x => A z.2.1 (virtualPairEquiv D z.1).2 (virtualPairEquiv D z.2.2).2 *
    G ((virtualPairEquiv D).symm
      ((virtualPairEquiv D z.1).1, (virtualPairEquiv D z.2.2).1)) x

/-- A matrix product with a distinguished central physical site. Both side chains
are indexed from their outer boundary inward, so the right product is transposed. -/
def mixedProductMap {l r : ℕ} (L : MPSChainTensor d D l) (A : MPSTensor d D)
    (R : MPSChainTensor d D r) (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) :
    Matrix ((Fin l → Fin d) × Fin d × (Fin r → Fin d)) (Fin (D * D)) ℂ :=
  (chainPairMatrix L ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ chainPairMatrix R)) *
    centralInputMatrix A G

/-- The central placement leaves the original matrix product coefficients unchanged. -/
theorem mixedProductMap_apply {l r : ℕ} (L : MPSChainTensor d D l) (A : MPSTensor d D)
    (R : MPSChainTensor d D r) (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (σ : (Fin l → Fin d) × Fin d × (Fin r → Fin d)) (x : Fin (D * D)) :
    mixedProductMap L A R G σ x =
      ∑ a, (eval L σ.1 * A σ.2.1 * (eval R σ.2.2)ᵀ)
        (virtualPairEquiv D a).1 (virtualPairEquiv D a).2 * G a x := by
  classical
  simp only [mixedProductMap, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, centralInputMatrix, Matrix.of_apply,
    chainPairMatrix, mul_ite, one_mul, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp_rw [← (virtualPairEquiv D).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Equiv.apply_symm_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun β _ => by ring

/-- A local isometry at the centre, followed by isometric site maps extending
to the left and right boundaries. Both outer bonds are one-dimensional and all
bonds are bounded by `D²`. The input virtual pair belongs to the central map. -/
def HasMixedSequentialFactorization {l r : ℕ} (hD : 0 < D)
    (V : Matrix ((Fin l → Fin d) × Fin d × (Fin r → Fin d)) (Fin (D * D)) ℂ) : Prop :=
    ∃ (bL : Fin (l + 1) → ℕ) (QL : MPSChainTensor d (D * D) l)
      (hbL : ∀ k, bL k ≤ D * D)
      (bR : Fin (r + 1) → ℕ) (QR : MPSChainTensor d (D * D) r)
      (hbR : ∀ k, bR k ≤ D * D)
      (C : Matrix (Fin (bL (Fin.last l)) × Fin d × Fin (bR (Fin.last r)))
        (Fin (D * D)) ℂ),
      bL 0 = 1 ∧ bR 0 = 1 ∧
      (∀ p i, IsRowSupportedBelow (bL p.castSucc) (QL p i)) ∧
      (∀ p i α β, bL p.succ ≤ β.val → QL p i α β = 0) ∧
      (∀ p, IsIsometryOn (bL p.succ) (QL p)) ∧
      (∀ p i, IsRowSupportedBelow (bR p.castSucc) (QR p i)) ∧
      (∀ p i α β, bR p.succ ≤ β.val → QR p i α β = 0) ∧
      (∀ p, IsIsometryOn (bR p.succ) (QR p)) ∧ C.IsIsometry ∧
      V =
        (sequentialEvaluation (Nat.mul_pos hD hD) bL QL (hbL _) ⊗ₖ
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
            sequentialEvaluation (Nat.mul_pos hD hD) bR QR (hbR _))) * C

/-- Two independent inward sweeps give the mixed canonical form. The centre retains
all input indices and is an isometry whenever the full matrix product map is one.
The local isometries on both sides have bond dimensions at most `D²`.

Source: arXiv:2307.01696, footnote 4 to equations (13)–(15). -/
theorem exists_mixed_isometric_factorization {l r : ℕ} (hD : 0 < D)
    (L : MPSChainTensor d D l) (A : MPSTensor d D) (R : MPSChainTensor d D r)
    (G : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
    (hV : (mixedProductMap L A R G).IsIsometry) :
    HasMixedSequentialFactorization hD (mixedProductMap L A R G) := by
  classical
  obtain ⟨bL, QL, hbL, RL, hL0, hLrow, hLcol, hLiso, hEL, hL⟩ :=
    exists_chainPairMatrix_factorization hD L
  obtain ⟨bR, QR, hbR, RR, hR0, hRrow, hRcol, hRiso, hER, hR⟩ :=
    exists_chainPairMatrix_factorization hD R
  let EL := sequentialEvaluation (Nat.mul_pos hD hD) bL QL (hbL _)
  let ER := sequentialEvaluation (Nat.mul_pos hD hD) bR QR (hbR _)
  let E := EL ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ ER)
  let C := (RL ⊗ₖ ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ RR)) * centralInputMatrix A G
  have hE : E.IsIsometry := hEL.kronecker _ _
    ((show (1 : Matrix (Fin d) (Fin d) ℂ).IsIsometry by simp [Matrix.IsIsometry]).kronecker
      _ _ hER)
  have hfac : mixedProductMap L A R G = E * C := by
    simp only [mixedProductMap, E, C, EL, ER, hL, hR, ← Matrix.mul_assoc,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hC : C.IsIsometry := by
    change Cᴴ * C = 1
    calc
      Cᴴ * C = Cᴴ * (Eᴴ * E) * C := by rw [hE]; simp
      _ = (E * C)ᴴ * (E * C) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [← hfac]; exact hV
  exact ⟨bL, QL, hbL, bR, QR, hbR, C, hL0, hR0, hLrow, hLcol, hLiso,
    hRrow, hRcol, hRiso, hC, hfac⟩

/-- A right-to-left chain expressed in the usual left-to-right matrix order. -/
def reverseTransposeChain (A : MPSChainTensor d D n) : MPSChainTensor d D n :=
  fun p i => (A (Fin.rev p) i)ᵀ

/-- Reversing both the sites and matrix orientation transposes the full product. -/
theorem eval_reverseTransposeChain (A : MPSChainTensor d D n) (σ : Fin n → Fin d) :
    eval (reverseTransposeChain A) σ = (eval A (fun p => σ (Fin.rev p)))ᵀ := by
  simp [MPSChainTensor.eval_eq_prod_ofFn, Matrix.transpose_list_prod, List.map_ofFn,
    List.ofFn_reverse, reverseTransposeChain, Function.comp_def]

/-- Joining a left chain, one central site, and a chain indexed from the right boundary. -/
def mixedChain {l r : ℕ} (L : MPSChainTensor d D l) (A : MPSTensor d D)
    (R : MPSChainTensor d D r) : MPSChainTensor d D (l + (r + 1)) :=
  Fin.append L (Fin.cons A (reverseTransposeChain R))

/-- The physical configurations, with the right part read from its outer boundary. -/
def mixedConfigurationEquiv (d l r : ℕ) :
    ((Fin l → Fin d) × Fin d × (Fin r → Fin d)) ≃ (Fin (l + (r + 1)) → Fin d) :=
  (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr Fin.revPerm (Equiv.refl _))).trans
      (Fin.consEquiv fun _ : Fin (r + 1) => Fin d))).trans (Fin.appendEquiv l (r + 1))

/-- The left, central, and reversed-right configurations in the physical chain order. -/
theorem mixedConfigurationEquiv_apply {l r : ℕ}
    (σ : (Fin l → Fin d) × Fin d × (Fin r → Fin d)) :
    mixedConfigurationEquiv d l r σ =
      Fin.append σ.1 (Fin.cons σ.2.1 (fun p => σ.2.2 (Fin.rev p))) :=
  rfl

private theorem eval_append {l r : ℕ} (L : MPSChainTensor d D l)
    (R : MPSChainTensor d D r) (σ : Fin l → Fin d) (τ : Fin r → Fin d) :
    eval (Fin.append L R) (Fin.append σ τ) = eval L σ * eval R τ := by
  have h : (fun k => Fin.append L R k (Fin.append σ τ k)) =
      Fin.append (fun k => L k (σ k)) (fun k => R k (τ k)) := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
  simp only [MPSChainTensor.eval_eq_prod_ofFn, h, List.ofFn_fin_append, List.prod_append]

/-- Evaluation of the split chain is the product of its left, central and right factors. -/
theorem eval_mixedChain {l r : ℕ} (L : MPSChainTensor d D l) (A : MPSTensor d D)
    (R : MPSChainTensor d D r) (σ : (Fin l → Fin d) × Fin d × (Fin r → Fin d)) :
    eval (mixedChain L A R) (mixedConfigurationEquiv d l r σ) =
      eval L σ.1 * A σ.2.1 * (eval R σ.2.2)ᵀ := by
  rw [mixedChain, mixedConfigurationEquiv_apply, eval_append, MPSChainTensor.eval_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, eval_reverseTransposeChain, Fin.rev_rev,
    Matrix.mul_assoc]

/-- The polar isometry with physical configurations separated at a chosen central site. -/
noncomputable def mixedPolarIsoMatrix {l r : ℕ} (L : MPSChainTensor d D l)
    (A : MPSTensor d D) (R : MPSChainTensor d D r) :
    Matrix ((Fin l → Fin d) × Fin d × (Fin r → Fin d)) (Fin (D * D)) ℂ :=
  Matrix.reindex ((MPSTensor.decodeBlockEquiv d (l + (r + 1))).trans
    (mixedConfigurationEquiv d l r).symm) (Equiv.refl _)
      (MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor (mixedChain L A R)))

/-- Moving the inverse polar factor to the central site does not change the polar isometry.
The two outer chains remain independent of that inverse.

**Scope restriction (injective polar input):** this uses the ordinary inverse, not the
pseudoinverse allowed by arXiv:2307.01696, footnote 3 to equations (13)–(15).
See `docs/paper-gaps/mswc24_mixed_polar_injectivity_scope.tex`. -/
theorem mixedPolarIsoMatrix_eq_mixedProductMap {l r : ℕ} (L : MPSChainTensor d D l)
    (A : MPSTensor d D) (R : MPSChainTensor d D r)
    (hB : Kraus.IsInjective (MPSChainTensor.blockTensor (mixedChain L A R))) :
    mixedPolarIsoMatrix L A R = mixedProductMap L A R
      ((Matrix.polarPos (MPSTensor.physicalMatrix
        (MPSChainTensor.blockTensor (mixedChain L A R))))⁻¹.submatrix
          (virtualPairEquiv D) (virtualPairEquiv D)) := by
  ext σ x
  change MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor (mixedChain L A R))
      ((MPSTensor.decodeBlockEquiv d (l + (r + 1))).symm
        (mixedConfigurationEquiv d l r σ)) x = _
  rw [polarIsoMatrix_chainBlockTensor_eq_sum _ hB, mixedProductMap_apply, eval_mixedChain]

/-- **Mixed-canonical sequential factorization of the polar isometry.**
For an injective blocked matrix product, any chosen physical site can carry the
virtual-pair input. Independent inward sweeps on the sites to its left and right
produce local isometries with bonds bounded by `D²`; the remaining central map
from the input pair to the two inward bonds and the central physical site is an
isometry too. Contracting these maps is exactly the original polar isometry.

Source: arXiv:2307.01696, footnote 4 to equations (13)–(15). Unlike the
one-sided factorization, both external bonds are one-dimensional: the
`D²`-dimensional input is at the central site.

**Scope restriction (injective polar input):** the non-injective extension of source
footnote 3 is not included; see `docs/paper-gaps/mswc24_mixed_polar_injectivity_scope.tex`. -/
theorem exists_mixed_sequential_polarIsoMatrix_of_split {l r : ℕ} (hD : 0 < D)
    (L : MPSChainTensor d D l) (A : MPSTensor d D) (R : MPSChainTensor d D r)
    (hB : Kraus.IsInjective (MPSChainTensor.blockTensor (mixedChain L A R))) :
    HasMixedSequentialFactorization hD (mixedPolarIsoMatrix L A R) := by
  have hV : (mixedPolarIsoMatrix L A R).IsIsometry :=
    (MPSTensor.isIsometry_polarIsoMatrix_of_isInjective hB).reindex _
      ((MPSTensor.decodeBlockEquiv d (l + (r + 1))).trans
        (mixedConfigurationEquiv d l r).symm) (Equiv.refl _)
  rw [mixedPolarIsoMatrix_eq_mixedProductMap L A R hB] at hV ⊢
  exact exists_mixed_isometric_factorization hD L A R _ hV

/-- The polar isometry of a site-dependent chain with injective blocked tensor has a mixed
sequential factorization with its input at the site after the first `l` physical sites.
This includes both endpoint choices.

Source: arXiv:2307.01696, footnote 4 to equations (13)–(15).

**Scope restriction (injective polar input):** the non-injective extension of source
footnote 3 is not included; see `docs/paper-gaps/mswc24_mixed_polar_injectivity_scope.tex`. -/
theorem exists_mixed_sequential_polarIsoMatrix {l r : ℕ} (hD : 0 < D)
    (A : MPSChainTensor d D (l + (r + 1)))
    (hB : Kraus.IsInjective (MPSChainTensor.blockTensor A)) :
    HasMixedSequentialFactorization hD
      (Matrix.reindex ((MPSTensor.decodeBlockEquiv d (l + (r + 1))).trans
        (mixedConfigurationEquiv d l r).symm) (Equiv.refl _)
          (MPSTensor.polarIsoMatrix (MPSChainTensor.blockTensor A))) := by
  let L : MPSChainTensor d D l := fun p => A (Fin.castAdd (r + 1) p)
  let M : MPSTensor d D := A (Fin.natAdd l 0)
  let R : MPSChainTensor d D r := fun p i => (A (Fin.natAdd l (Fin.rev p).succ) i)ᵀ
  have hA : mixedChain L M R = A := by
    funext p i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) p
    · simp [mixedChain, L]
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [mixedChain, M]
      · simp [mixedChain, reverseTransposeChain, R]
  have h := exists_mixed_sequential_polarIsoMatrix_of_split hD L M R
    (by simpa only [hA] using hB)
  simpa only [mixedPolarIsoMatrix, hA] using h

end MPSPreparation
