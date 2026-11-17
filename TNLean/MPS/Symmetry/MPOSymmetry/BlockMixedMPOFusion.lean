/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.BlockMixedMPO
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPOFusion

/-!
# Fusion of the common MPO of the block-injective mixed path

GLM23 asserts, for the block-injective path (`REsubmission.tex`,
lines 1724--1726): "The previous MPO tensors define an MPO representation of
$\mathcal{C}$ if $L^0=L^1$ and $F^0=F^1$, this can be seen as in the
injective case."

The endpoint blocks are square-alphabet injective tensors placed in the
sectors of the restricted local Hilbert space, so the simultaneous span of
their letters is already full. The actual L matrices of the two endpoints are
indexed by the shared block labels and multiplicities; equality of the chosen
raw L matrices for every pair of blocks gives the cross sectors of the
fusion, exactly as in the injective case. The diagonal sectors use the
endpoint fusion decompositions. The fusion maps are the direct sums of the
endpoint fusion maps, so the F-symbols they define are the common ones once
`F⁰ = F¹` holds; that gauge statement is not needed for exact fusion.

**Scope restriction (sector-separated blocks):** the endpoint blocks are
square-alphabet tensors placed in disjoint physical sectors, that is, the
local Hilbert space is already the span `⊕ₓ ℂ^{D^p_x} ⊗ ℂ^{D^p_x}` of the
block-diagonal tensor. The source takes this restriction without loss of
generality (lines 317 and 1584--1586); its derivation from block-injective
tensors on an arbitrary common physical alphabet is not formalized. The
injectivity of the common MPO, the ground space of the path Hamiltonians, and
their commutation with the common MPO are not asserted. See
`docs/paper-gaps/glm23_block_injective_mixed_path.tex`.

Source: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
lines 1695--1726, using `fusiontensors`, `eq:orthoW`, `fusiontensors2`,
`eq:orthoV`, and `eq:F_symbol2`.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor.MPOSymmetry

section Span

variable {s : ℕ} {n D : Fin s → ℕ}

/-- Square-alphabet injective blocks placed in the sectors of the direct sum
have full simultaneous one-letter span. -/
theorem wordTupleSpanTop_sectorTensor (A : ∀ y, MPSTensor (n y) (D y))
    (hInj : ∀ y, Kraus.IsInjective (A y)) :
    WordTupleSpanTop (sectorTensor A) 1 := by
  classical
  let S := Submodule.span ℂ (Set.range (wordTuple (sectorTensor A) 1))
  have hsingle : ∀ y (Z : Matrix (Fin (D y)) (Fin (D y)) ℂ), Pi.single y Z ∈ S := by
    intro y Z
    have hZ : Z ∈ Submodule.span ℂ (Set.range (A y)) := (hInj y) ▸ Submodule.mem_top
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
        obtain ⟨t, rfl⟩ := hZ
        refine Submodule.subset_span ⟨fun _ => finSigmaFinEquiv ⟨y, t⟩, ?_⟩
        funext k
        simp only [wordTuple, List.ofFn_succ, List.ofFn_zero, Kraus.evalWord_cons,
          Kraus.evalWord_nil, Matrix.mul_one]
        by_cases hk : k = y
        · subst hk
          simp
        · rw [sectorTensor_of_ne A (Ne.symm hk), Pi.single_eq_of_ne hk]
    | zero => simp
    | add Z Z' _ _ hZ hZ' => simpa [Pi.single_add] using S.add_mem hZ hZ'
    | smul c Z _ hZ => simpa [Pi.single_smul] using S.smul_mem c hZ
  rw [WordTupleSpanTop, eq_top_iff]
  intro F _
  rw [← Finset.univ_sum_single F]
  exact S.sum_mem fun y _ => hsingle y (F y)

end Span

section TreeMaps

variable {r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- Sequential-action analysis of a path with initial block `x` and final
block `y`, with the final bond typed by `y`. -/
noncomputable abbrev blockSequentialAnalysis
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (a b : Fin r) (x y : Fin s) (p : MPOTensor.SequentialActionMultiplicity M a b x y) :
    Matrix (Fin (D y)) (Fin (χ a * χ b * D x)) ℂ :=
  MPOTensor.sequentialActionAnalysis VA a b x (MPOTensor.sequentialActionPathEquiv a b x ⟨y, p⟩)

/-- Sequential-action synthesis of a path with initial block `x` and final
block `y`. -/
noncomputable abbrev blockSequentialSynthesis
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b : Fin r) (x y : Fin s) (p : MPOTensor.SequentialActionMultiplicity M a b x y) :
    Matrix (Fin (χ a * χ b * D x)) (Fin (D y)) ℂ :=
  MPOTensor.sequentialActionSynthesis WA a b x (MPOTensor.sequentialActionPathEquiv a b x ⟨y, p⟩)

/-- Fusion-then-action analysis of a path with initial block `x` and final
block `y`. -/
noncomputable abbrev blockFusionThenActionAnalysis
    (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (a b : Fin r) (x y : Fin s) (q : MPOTensor.FusionActionMultiplicity N M a b x y) :
    Matrix (Fin (D y)) (Fin (χ a * χ b * D x)) ℂ :=
  MPOTensor.fusionThenActionAnalysis VF VA a b x (MPOTensor.fusionActionPathEquiv a b x ⟨y, q⟩)

/-- Fusion-then-action synthesis of a path with initial block `x` and final
block `y`. -/
noncomputable abbrev blockFusionThenActionSynthesis
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b : Fin r) (x y : Fin s) (q : MPOTensor.FusionActionMultiplicity N M a b x y) :
    Matrix (Fin (χ a * χ b * D x)) (Fin (D y)) ℂ :=
  MPOTensor.fusionThenActionSynthesis WF WA a b x (MPOTensor.fusionActionPathEquiv a b x ⟨y, q⟩)

theorem blockSequentialSynthesis_apply
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (u : Fin (D y)) :
    blockSequentialSynthesis WA a b x y ⟨z, (i, j)⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) u =
      ∑ v : Fin (D z), WA b x z j (finProdFinEquiv (xb, xx)) v *
        WA a z y i (finProdFinEquiv (xa, v)) u :=
  MPOTensor.sequentialActionSynthesis_apply WA a b x y z i j xa xb xx u

theorem blockSequentialAnalysis_apply
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (a b : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (u : Fin (D y)) :
    blockSequentialAnalysis VA a b x y ⟨z, (i, j)⟩ u
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) =
      ∑ v : Fin (D z), VA a z y i u (finProdFinEquiv (xa, v)) *
        VA b x z j v (finProdFinEquiv (xb, xx)) :=
  MPOTensor.sequentialActionAnalysis_apply VA a b x y z i j xa xb xx u

theorem blockFusionThenActionSynthesis_apply
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b c : Fin r) (x y : Fin s) (k : Fin (M c x y)) (mu : Fin (N a b c))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (u : Fin (D y)) :
    blockFusionThenActionSynthesis WF WA a b x y ⟨c, (k, mu)⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) u =
      ∑ v : Fin (χ c), WF a b c mu (finProdFinEquiv (xa, xb)) v *
        WA c x y k (finProdFinEquiv (v, xx)) u :=
  MPOTensor.fusionThenActionSynthesis_apply WF WA a b c x y mu k xa xb xx u

theorem blockFusionThenActionAnalysis_apply
    (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (a b c : Fin r) (x y : Fin s) (k : Fin (M c x y)) (mu : Fin (N a b c))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (u : Fin (D y)) :
    blockFusionThenActionAnalysis VF VA a b x y ⟨c, (k, mu)⟩ u
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) =
      ∑ v : Fin (χ c), VA c x y k u (finProdFinEquiv (v, xx)) *
        VF a b c mu v (finProdFinEquiv (xa, xb)) :=
  MPOTensor.fusionThenActionAnalysis_apply VF VA a b c x y mu k xa xb xx u

end TreeMaps

section Relations

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (hF : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    IsBiorthogonalDecomposition (MPOTensor.actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
  (hInj : ∀ y, Kraus.IsInjective (A y)) (hD : ∀ y, 0 < D y)
  {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L)

include hF hA hInj hD hL hSpan in
/-- The two L relations of one fixed initial and final block, for injective
blocks with a positive simultaneous word span. Source: GLM23
`eq:F_symbol2` and `1Fsymbol`. -/
theorem block_actionLMatrix_relations (a b : Fin r) (x y : Fin s) :
    (∀ p : MPOTensor.SequentialActionMultiplicity M a b x y,
      ∑ q : MPOTensor.FusionActionMultiplicity N M a b x y,
        MPOTensor.actionLMatrix WF VA WA a b x y p q •
          blockFusionThenActionAnalysis VF VA a b x y q =
        blockSequentialAnalysis VA a b x y p) ∧
    (∀ q : MPOTensor.FusionActionMultiplicity N M a b x y,
      ∑ p : MPOTensor.SequentialActionMultiplicity M a b x y,
        MPOTensor.actionLMatrix WF VA WA a b x y p q •
          blockSequentialSynthesis WA a b x y p =
        blockFusionThenActionSynthesis WF WA a b x y q) := by
  constructor
  · intro p
    refine Matrix.ext fun u v => ?_
    have h := congrArg (fun Z ↦ Z ⟨y, p, u⟩ v)
      (MPOTensor.actionLMatrix_analysis VF WF VA WA
        hF hA (fun y ↦ (hInj y).isNormal) hD a b x hL hSpan)
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single y
      (fun y' _ hy' => Finset.sum_eq_zero fun w _ => by
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hy'), zero_mul]) (by simp)] at h
    simp only [Matrix.blockDiagonal'_apply_eq, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Matrix.submatrix_apply,
      MPSTensor.decompositionAnalysis, MPOTensor.fusionActionCoordinateEquiv,
      MPOTensor.sequentialActionCoordinateEquiv, Equiv.coe_fn_mk, id_eq] at h
    refine Eq.trans ?_ h
    erw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    erw [Matrix.smul_apply, smul_eq_mul]
  · intro q
    refine Matrix.ext fun u v => ?_
    have h := congrArg (fun Z ↦ Z u ⟨y, q, v⟩)
      (MPOTensor.actionLMatrix_synthesis VF WF VA WA
        hF hA (fun y ↦ (hInj y).isNormal) hD a b x hL hSpan)
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single y
      (fun y' _ hy' => Finset.sum_eq_zero fun w _ => by
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hy', mul_zero]) (by simp)] at h
    simp only [Matrix.blockDiagonal'_apply_eq, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.submatrix_apply,
      MPSTensor.decompositionSynthesis, MPOTensor.fusionActionCoordinateEquiv,
      MPOTensor.sequentialActionCoordinateEquiv, Equiv.coe_fn_mk, id_eq] at h
    refine Eq.trans ?_ h
    erw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    erw [Matrix.smul_apply, smul_eq_mul, mul_comm]

end Relations

section CrossEndpoint

variable {d₀ d₁ r s : ℕ} {χ₀ χ₁ : Fin r → ℕ} {D₀ D₁ : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ a * D₀ x)) ℂ)
  (WA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ₀ a * D₀ x)) (Fin (D₀ y)) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a x y, Fin (M a x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ a * D₁ x)) ℂ)
  (WA₁ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ₁ a * D₁ x)) (Fin (D₁ y)) ℂ)
  {O₀ : ∀ a, MPOTensor d₀ (χ₀ a)} {A₀ : ∀ x, MPSTensor d₀ (D₀ x)}
  {O₁ : ∀ a, MPOTensor d₁ (χ₁ a)} {A₁ : ∀ x, MPSTensor d₁ (D₁ x)}
  (hF₀ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a x,
    IsBiorthogonalDecomposition (MPOTensor.actTensor (O₀ a) (A₀ x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A₀ q.1)
      (fun q ↦ VA₀ a x q.1 q.2) (fun q ↦ WA₀ a x q.1 q.2))
  (hF₁ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a x,
    IsBiorthogonalDecomposition (MPOTensor.actTensor (O₁ a) (A₁ x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A₁ q.1)
      (fun q ↦ VA₁ a x q.1 q.2) (fun q ↦ WA₁ a x q.1 q.2))
  (hInj₀ : ∀ y, Kraus.IsInjective (A₀ y)) (hInj₁ : ∀ y, Kraus.IsInjective (A₁ y))
  (hD₀ : ∀ y, 0 < D₀ y) (hD₁ : ∀ y, 0 < D₁ y)
  {L₀ L₁ : ℕ} (hL₀ : 0 < L₀) (hL₁ : 0 < L₁)
  (hSpan₀ : WordTupleSpanTop A₀ L₀) (hSpan₁ : WordTupleSpanTop A₁ L₁)

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ hL₀ hL₁ hSpan₀ hSpan₁ in
/-- Equal actual raw L matrices of a pair of corresponding blocks identify
the two endpoint-crossed tree contractions for every rectangular final-bond
matrix. Source: GLM23, `REsubmission.tex`, lines 1695--1726, using
`eq:F_symbol2`. -/
theorem blockCrossEndpoint_actionTree_contraction (a b : Fin r) (x y : Fin s)
    (hL : MPOTensor.actionLMatrix WF₀ VA₀ WA₀ a b x y =
      MPOTensor.actionLMatrix WF₁ VA₁ WA₁ a b x y)
    (X : Matrix (Fin (D₀ y)) (Fin (D₁ y)) ℂ) :
    (∑ p : MPOTensor.SequentialActionMultiplicity M a b x y,
      blockSequentialSynthesis WA₀ a b x y p * X * blockSequentialAnalysis VA₁ a b x y p) =
    ∑ q : MPOTensor.FusionActionMultiplicity N M a b x y,
      blockFusionThenActionSynthesis WF₀ WA₀ a b x y q * X *
        blockFusionThenActionAnalysis VF₁ VA₁ a b x y q := by
  have hS := (block_actionLMatrix_relations VF₀ WF₀ VA₀ WA₀
    hF₀ hA₀ hInj₀ hD₀ hL₀ hSpan₀ a b x y).2
  have hH := (block_actionLMatrix_relations VF₁ WF₁ VA₁ WA₁
    hF₁ hA₁ hInj₁ hD₁ hL₁ hSpan₁ a b x y).1
  calc
    _ = ∑ p : MPOTensor.SequentialActionMultiplicity M a b x y,
        blockSequentialSynthesis WA₀ a b x y p * X *
          (∑ q : MPOTensor.FusionActionMultiplicity N M a b x y,
            MPOTensor.actionLMatrix WF₁ VA₁ WA₁ a b x y p q •
              blockFusionThenActionAnalysis VF₁ VA₁ a b x y q) := by simp_rw [hH]
    _ = ∑ q : MPOTensor.FusionActionMultiplicity N M a b x y,
        (∑ p : MPOTensor.SequentialActionMultiplicity M a b x y,
          MPOTensor.actionLMatrix WF₀ VA₀ WA₀ a b x y p q •
            blockSequentialSynthesis WA₀ a b x y p) * X *
          blockFusionThenActionAnalysis VF₁ VA₁ a b x y q := by
      simp_rw [Matrix.mul_sum, Matrix.mul_smul, Matrix.sum_mul, Matrix.smul_mul, hL]
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [hS]

private theorem sum_rectangular_sandwich_apply'
    {ι α β γ δ : Type*} [Fintype ι] [Fintype β] [Fintype γ]
    (S : ι → Matrix α β ℂ) (X : Matrix β γ ℂ) (H : ι → Matrix γ δ ℂ)
    (x : α) (y : δ) :
    (∑ i, S i * X * H i) x y = ∑ i, ∑ u, ∑ v, S i x u * X u v * H i v y := by
  simp only [Matrix.sum_apply, Matrix.mul_assoc, Matrix.mul_apply,
    Finset.mul_sum, mul_assoc]

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ hL₀ hL₁ hSpan₀ hSpan₁ in
/-- The block cross-endpoint contraction in physical leg coordinates.
Source: GLM23, lines 1695--1726. -/
theorem blockCrossEndpoint_actionTree_contraction_apply (a b : Fin r) (x y : Fin s)
    (hL : MPOTensor.actionLMatrix WF₀ VA₀ WA₀ a b x y =
      MPOTensor.actionLMatrix WF₁ VA₁ WA₁ a b x y)
    (X : Matrix (Fin (D₀ y)) (Fin (D₁ y)) ℂ)
    (xa₀ : Fin (χ₀ a)) (xb₀ : Fin (χ₀ b)) (x₀ : Fin (D₀ x))
    (xa₁ : Fin (χ₁ a)) (xb₁ : Fin (χ₁ b)) (x₁ : Fin (D₁ x)) :
    (∑ z : Fin s, ∑ i : Fin (M a z y), ∑ j : Fin (M b x z),
      ∑ u : Fin (D₀ y), ∑ v : Fin (D₁ y),
      (∑ t : Fin (D₀ z),
        WA₀ b x z j (finProdFinEquiv (xb₀, x₀)) t *
          WA₀ a z y i (finProdFinEquiv (xa₀, t)) u) * X u v *
      (∑ t : Fin (D₁ z),
        VA₁ a z y i v (finProdFinEquiv (xa₁, t)) *
          VA₁ b x z j t (finProdFinEquiv (xb₁, x₁)))) =
    ∑ c : Fin r, ∑ k : Fin (M c x y), ∑ mu : Fin (N a b c),
      ∑ u : Fin (D₀ y), ∑ v : Fin (D₁ y),
        (∑ t : Fin (χ₀ c),
          WF₀ a b c mu (finProdFinEquiv (xa₀, xb₀)) t *
            WA₀ c x y k (finProdFinEquiv (t, x₀)) u) * X u v *
        (∑ t : Fin (χ₁ c),
          VA₁ c x y k v (finProdFinEquiv (t, x₁)) *
            VF₁ a b c mu t (finProdFinEquiv (xa₁, xb₁))) := by
  have h := congrArg
    (fun Z ↦ Z (finProdFinEquiv (finProdFinEquiv (xa₀, xb₀), x₀))
      (finProdFinEquiv (finProdFinEquiv (xa₁, xb₁), x₁)))
    (blockCrossEndpoint_actionTree_contraction
      VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ hF₀ hA₀ hF₁ hA₁
      hInj₀ hInj₁ hD₀ hD₁ hL₀ hL₁ hSpan₀ hSpan₁ a b x y hL X)
  rw [sum_rectangular_sandwich_apply', sum_rectangular_sandwich_apply'] at h
  simpa only [Fintype.sum_sigma, Fintype.sum_prod_type, blockSequentialSynthesis_apply,
    blockSequentialAnalysis_apply, blockFusionThenActionSynthesis_apply,
    blockFusionThenActionAnalysis_apply] using h

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ hL₀ hL₁ hSpan₀ hSpan₁ in
/-- The cross-sector fusion identity of a pair of corresponding blocks, with
the intermediate block `z` summed. It follows by selecting one matrix unit in
the block cross-endpoint contraction. Source: GLM23, `REsubmission.tex`,
lines 1724--1726: "this can be seen as in the injective case". -/
theorem blockCrossEndpoint_fusion_entry (a b : Fin r) (x y : Fin s)
    (hL : MPOTensor.actionLMatrix WF₀ VA₀ WA₀ a b x y =
      MPOTensor.actionLMatrix WF₁ VA₁ WA₁ a b x y)
    (r₀ : Fin (D₀ y)) (k₀ : Fin (D₀ x)) (s₁ : Fin (D₁ y)) (l₁ : Fin (D₁ x))
    (α₀ : Fin (χ₀ a)) (γ₀ : Fin (χ₀ b)) (β₁ : Fin (χ₁ a)) (δ₁ : Fin (χ₁ b)) :
    (∑ z : Fin s, ∑ u : Fin (D₀ z), ∑ v : Fin (D₁ z),
      (∑ i : Fin (M a z y),
        WA₀ a z y i (finProdFinEquiv (α₀, u)) r₀ *
          VA₁ a z y i s₁ (finProdFinEquiv (β₁, v))) *
      (∑ j : Fin (M b x z),
        WA₀ b x z j (finProdFinEquiv (γ₀, k₀)) u *
          VA₁ b x z j v (finProdFinEquiv (δ₁, l₁)))) =
    ∑ c : Fin r, ∑ mu : Fin (N a b c),
      ∑ ξ : Fin (χ₀ c), ∑ η : Fin (χ₁ c),
        WF₀ a b c mu (finProdFinEquiv (α₀, γ₀)) ξ *
          (∑ h : Fin (M c x y),
            WA₀ c x y h (finProdFinEquiv (ξ, k₀)) r₀ *
              VA₁ c x y h s₁ (finProdFinEquiv (η, l₁))) *
          VF₁ a b c mu η (finProdFinEquiv (β₁, δ₁)) := by
  classical
  have h := blockCrossEndpoint_actionTree_contraction_apply
    VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ hF₀ hA₀ hF₁ hA₁
    hInj₀ hInj₁ hD₀ hD₁ hL₀ hL₁ hSpan₀ hSpan₁ a b x y hL (Matrix.single r₀ s₁ 1)
    α₀ γ₀ k₀ β₁ δ₁ l₁
  simp only [Matrix.single_apply, ite_and, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_const_zero,
    Finset.mem_univ, ite_true] at h
  calc
    _ = ∑ z : Fin s, ∑ i : Fin (M a z y), ∑ j : Fin (M b x z),
        (∑ u : Fin (D₀ z),
          WA₀ b x z j (finProdFinEquiv (γ₀, k₀)) u *
            WA₀ a z y i (finProdFinEquiv (α₀, u)) r₀) *
        (∑ v : Fin (D₁ z),
          VA₁ a z y i s₁ (finProdFinEquiv (β₁, v)) *
            VA₁ b x z j v (finProdFinEquiv (δ₁, l₁))) := by
      refine Finset.sum_congr rfl fun (z : Fin s) _ ↦ ?_
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [Fintype.sum_last_two_first_four]
      refine Finset.sum_congr rfl fun (i : Fin (M a z y)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (j : Fin (M b x z)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (u : Fin (D₀ z)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (v : Fin (D₁ z)) _ ↦ ?_
      ring
    _ = ∑ c : Fin r, ∑ k : Fin (M c x y), ∑ mu : Fin (N a b c),
        (∑ ξ : Fin (χ₀ c),
          WF₀ a b c mu (finProdFinEquiv (α₀, γ₀)) ξ *
            WA₀ c x y k (finProdFinEquiv (ξ, k₀)) r₀) *
        (∑ η : Fin (χ₁ c),
          VA₁ c x y k s₁ (finProdFinEquiv (η, l₁)) *
            VF₁ a b c mu η (finProdFinEquiv (β₁, δ₁))) := h
    _ = _ := by
      refine Finset.sum_congr rfl fun (c : Fin r) _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (mu : Fin (N a b c)) _ ↦ ?_
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (ξ : Fin (χ₀ c)) _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (η : Fin (χ₁ c)) _ ↦ ?_
      refine Finset.sum_congr rfl fun (k : Fin (M c x y)) _ ↦ ?_
      ring

end CrossEndpoint


section Fusion

variable {r s : ℕ} {χ₀ χ₁ : Fin r → ℕ} {D₀ D₁ : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (O₀ : ∀ a, MPOTensor (∑ x, D₀ x * D₀ x) (χ₀ a))
  (O₁ : ∀ a, MPOTensor (∑ x, D₁ x * D₁ x) (χ₁ a))
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ a * D₀ x)) ℂ)
  (WA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ₀ a * D₀ x)) (Fin (D₀ y)) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a x y, Fin (M a x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ a * D₁ x)) ℂ)
  (WA₁ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ₁ a * D₁ x)) (Fin (D₁ y)) ℂ)

set_option maxHeartbeats 1600000 in
-- Sixteen physical sectors and sixteen bond sectors are split explicitly.
/-- Fusion reconstruction of one block sector of the common MPOs, in
direct-sum coordinates, with the intermediate block summed. The diagonal
sectors use the endpoint fusion relations; the cross sectors use the block
cross-endpoint relations. Source: GLM23, lines 1724--1726. -/
theorem blockMixedMPOLetter_fusion (a b : Fin r) (y x : Fin s)
    (hdiag₀ : ∀ (r₀ s₀ : Fin (D₀ y)) (k₀ l₀ : Fin (D₀ x))
        (α γ : Fin (χ₀ a)) (β δ : Fin (χ₀ b)),
      (∑ z : Fin s, ∑ u : Fin (D₀ z), ∑ v : Fin (D₀ z),
        operatorSector (O₀ a) y z (finProdFinEquiv (r₀, s₀)) (finProdFinEquiv (u, v)) α γ *
          operatorSector (O₀ b) z x (finProdFinEquiv (u, v)) (finProdFinEquiv (k₀, l₀)) β δ) =
        ∑ c, ∑ μ : Fin (N a b c),
          (WF₀ a b c μ * (operatorSector (O₀ c) y x (finProdFinEquiv (r₀, s₀))
            (finProdFinEquiv (k₀, l₀)) * VF₀ a b c μ))
            (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)))
    (hdiag₁ : ∀ (r₁ s₁ : Fin (D₁ y)) (k₁ l₁ : Fin (D₁ x))
        (α γ : Fin (χ₁ a)) (β δ : Fin (χ₁ b)),
      (∑ z : Fin s, ∑ u : Fin (D₁ z), ∑ v : Fin (D₁ z),
        operatorSector (O₁ a) y z (finProdFinEquiv (r₁, s₁)) (finProdFinEquiv (u, v)) α γ *
          operatorSector (O₁ b) z x (finProdFinEquiv (u, v)) (finProdFinEquiv (k₁, l₁)) β δ) =
        ∑ c, ∑ μ : Fin (N a b c),
          (WF₁ a b c μ * (operatorSector (O₁ c) y x (finProdFinEquiv (r₁, s₁))
            (finProdFinEquiv (k₁, l₁)) * VF₁ a b c μ))
            (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)))
    (hcross₀₁ : ∀ (r₀ : Fin (D₀ y)) (k₀ : Fin (D₀ x)) (s₁ : Fin (D₁ y)) (l₁ : Fin (D₁ x))
        (α₀ : Fin (χ₀ a)) (γ₀ : Fin (χ₀ b)) (β₁ : Fin (χ₁ a)) (δ₁ : Fin (χ₁ b)),
      (∑ z : Fin s, ∑ u : Fin (D₀ z), ∑ v : Fin (D₁ z),
        (∑ i : Fin (M a z y),
          WA₀ a z y i (finProdFinEquiv (α₀, u)) r₀ *
            VA₁ a z y i s₁ (finProdFinEquiv (β₁, v))) *
        (∑ j : Fin (M b x z),
          WA₀ b x z j (finProdFinEquiv (γ₀, k₀)) u *
            VA₁ b x z j v (finProdFinEquiv (δ₁, l₁)))) =
      ∑ c : Fin r, ∑ mu : Fin (N a b c),
        ∑ ξ : Fin (χ₀ c), ∑ η : Fin (χ₁ c),
          WF₀ a b c mu (finProdFinEquiv (α₀, γ₀)) ξ *
            (∑ h : Fin (M c x y),
              WA₀ c x y h (finProdFinEquiv (ξ, k₀)) r₀ *
                VA₁ c x y h s₁ (finProdFinEquiv (η, l₁))) *
            VF₁ a b c mu η (finProdFinEquiv (β₁, δ₁)))
    (hcross₁₀ : ∀ (r₁ : Fin (D₁ y)) (k₁ : Fin (D₁ x)) (s₀ : Fin (D₀ y)) (l₀ : Fin (D₀ x))
        (α₁ : Fin (χ₁ a)) (γ₁ : Fin (χ₁ b)) (β₀ : Fin (χ₀ a)) (δ₀ : Fin (χ₀ b)),
      (∑ z : Fin s, ∑ u : Fin (D₁ z), ∑ v : Fin (D₀ z),
        (∑ i : Fin (M a z y),
          WA₁ a z y i (finProdFinEquiv (α₁, u)) r₁ *
            VA₀ a z y i s₀ (finProdFinEquiv (β₀, v))) *
        (∑ j : Fin (M b x z),
          WA₁ b x z j (finProdFinEquiv (γ₁, k₁)) u *
            VA₀ b x z j v (finProdFinEquiv (δ₀, l₀)))) =
      ∑ c : Fin r, ∑ mu : Fin (N a b c),
        ∑ ξ : Fin (χ₁ c), ∑ η : Fin (χ₀ c),
          WF₁ a b c mu (finProdFinEquiv (α₁, γ₁)) ξ *
            (∑ h : Fin (M c x y),
              WA₁ c x y h (finProdFinEquiv (ξ, k₁)) r₁ *
                VA₀ c x y h s₀ (finProdFinEquiv (η, l₀))) *
            VF₀ a b c mu η (finProdFinEquiv (β₀, δ₀)))
    (p₁ p₂ : Fin (D₀ y) ⊕ Fin (D₁ y)) (q₁ q₂ : Fin (D₀ x) ⊕ Fin (D₁ x))
    (α γ : Fin (χ₀ a) ⊕ Fin (χ₁ a)) (β δ : Fin (χ₀ b) ⊕ Fin (χ₁ b)) :
    (∑ z : Fin s, ∑ u : Fin (D₀ z) ⊕ Fin (D₁ z), ∑ v : Fin (D₀ z) ⊕ Fin (D₁ z),
      blockMixedMPOLetter (operatorSector (O₀ a) y z) (operatorSector (O₁ a) y z)
        (VA₀ a z y) (VA₁ a z y) (WA₀ a z y) (WA₁ a z y) p₁ p₂ u v α γ *
      blockMixedMPOLetter (operatorSector (O₀ b) z x) (operatorSector (O₁ b) z x)
        (VA₀ b x z) (VA₁ b x z) (WA₀ b x z) (WA₁ b x z) u v q₁ q₂ β δ) =
      ∑ c, ∑ μ : Fin (N a b c),
        (mixedEndpointFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ) *
          blockMixedMPOLetter (operatorSector (O₀ c) y x) (operatorSector (O₁ c) y x)
            (VA₀ c x y) (VA₁ c x y) (WA₀ c x y) (WA₁ c x y) p₁ p₂ q₁ q₂ *
          mixedEndpointFusionAnalysis (VF₀ a b c μ) (VF₁ a b c μ)) (α, β) (γ, δ) := by
  classical
  simp_rw [Matrix.mul_assoc]
  cases p₁ <;> cases p₂ <;> cases q₁ <;> cases q₂ <;>
    simp only [Matrix.mul_apply,
      Fintype.sum_sum_type, blockMixedMPOLetter, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add, add_zero]
  all_goals
    cases α <;> cases β <;> cases γ <;> cases δ <;>
      simp only [mixedEndpointFusionAnalysis, mixedEndpointFusionSynthesis,
        zero_mul, mul_zero, Finset.sum_const_zero]
  · simpa only [Matrix.mul_apply, ← finProdFinEquiv.sum_comp,
      Fintype.sum_prod_type] using hdiag₀ _ _ _ _ _ _ _ _
  · simpa only [Finset.mul_sum, Finset.sum_mul, mul_assoc] using
      hcross₀₁ _ _ _ _ _ _ _ _
  · simpa only [Finset.mul_sum, Finset.sum_mul, mul_assoc] using
      hcross₁₀ _ _ _ _ _ _ _ _
  · simpa only [Matrix.mul_apply, ← finProdFinEquiv.sum_comp,
      Fintype.sum_prod_type] using hdiag₁ _ _ _ _ _ _ _ _

end Fusion


/-- The sector form of an endpoint fusion decomposition, with the
intermediate physical letter split into its block and its two registers. -/
theorem operatorSector_fusion_entry {r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
    {N : Fin r → Fin r → Fin r → ℕ}
    (O : ∀ a, MPOTensor (∑ x, D x * D x) (χ a))
    (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (a b : Fin r)
    (h : IsBiorthogonalDecomposition (MPOTensor.mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (y x : Fin s) (r₀ s₀ : Fin (D y)) (k₀ l₀ : Fin (D x))
    (α γ : Fin (χ a)) (β δ : Fin (χ b)) :
    (∑ z : Fin s, ∑ u : Fin (D z), ∑ v : Fin (D z),
      operatorSector (O a) y z (finProdFinEquiv (r₀, s₀)) (finProdFinEquiv (u, v)) α γ *
        operatorSector (O b) z x (finProdFinEquiv (u, v)) (finProdFinEquiv (k₀, l₀)) β δ) =
      ∑ c, ∑ μ : Fin (N a b c),
        (WF a b c μ * (operatorSector (O c) y x (finProdFinEquiv (r₀, s₀))
          (finProdFinEquiv (k₀, l₀)) * VF a b c μ))
          (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)) := by
  have he := congrArg
    (fun Z ↦ Z (finProdFinEquiv (α, β)) (finProdFinEquiv (γ, δ)))
    (h.letter (finProdFinEquiv (finSigmaFinEquiv ⟨y, finProdFinEquiv (r₀, s₀)⟩,
      finSigmaFinEquiv ⟨x, finProdFinEquiv (k₀, l₀)⟩)))
  simp only [MPOTensor.toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, MPOTensor.mulTensor, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_sigma, Matrix.mul_assoc] at he
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma] at he
  simp only [operatorSector]
  rw [← he]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]

section Global

variable {r s : ℕ} {χ₀ χ₁ : Fin r → ℕ} {D₀ D₁ : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  (O₀ : ∀ a, MPOTensor (∑ x, D₀ x * D₀ x) (χ₀ a))
  (O₁ : ∀ a, MPOTensor (∑ x, D₁ x * D₁ x) (χ₁ a))
  (A₀ : ∀ x, MPSTensor (D₀ x * D₀ x) (D₀ x))
  (A₁ : ∀ x, MPSTensor (D₁ x * D₁ x) (D₁ x))
  (VF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ c)) (Fin (χ₀ a * χ₀ b)) ℂ)
  (WF₀ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₀ a * χ₀ b)) (Fin (χ₀ c)) ℂ)
  (VA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (D₀ y)) (Fin (χ₀ a * D₀ x)) ℂ)
  (WA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ₀ a * D₀ x)) (Fin (D₀ y)) ℂ)
  (VF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ c)) (Fin (χ₁ a * χ₁ b)) ℂ)
  (WF₁ : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ₁ a * χ₁ b)) (Fin (χ₁ c)) ℂ)
  (VA₁ : ∀ a x y, Fin (M a x y) → Matrix (Fin (D₁ y)) (Fin (χ₁ a * D₁ x)) ℂ)
  (WA₁ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ₁ a * D₁ x)) (Fin (D₁ y)) ℂ)
  (hF₀ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₀ a) (O₀ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₀ q.1).toMPSTensor)
      (fun q ↦ VF₀ a b q.1 q.2) (fun q ↦ WF₀ a b q.1 q.2))
  (hA₀ : ∀ a x,
    IsBiorthogonalDecomposition (MPOTensor.actTensor (O₀ a) (sectorTensor A₀ x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ sectorTensor A₀ q.1)
      (fun q ↦ VA₀ a x q.1 q.2) (fun q ↦ WA₀ a x q.1 q.2))
  (hF₁ : ∀ a b,
    IsBiorthogonalDecomposition (MPOTensor.mulTensor (O₁ a) (O₁ b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O₁ q.1).toMPSTensor)
      (fun q ↦ VF₁ a b q.1 q.2) (fun q ↦ WF₁ a b q.1 q.2))
  (hA₁ : ∀ a x,
    IsBiorthogonalDecomposition (MPOTensor.actTensor (O₁ a) (sectorTensor A₁ x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ sectorTensor A₁ q.1)
      (fun q ↦ VA₁ a x q.1 q.2) (fun q ↦ WA₁ a x q.1 q.2))
  (hInj₀ : ∀ x, Kraus.IsInjective (A₀ x)) (hInj₁ : ∀ x, Kraus.IsInjective (A₁ x))
  (hD₀ : ∀ x, 0 < D₀ x) (hD₁ : ∀ x, 0 < D₁ x)

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- The common MPOs of the block-injective path fuse exactly into copies of
the labelled common MPOs, with the original fusion multiplicities and the
direct sums of the endpoint fusion maps, provided the chosen raw L matrices
of the two endpoints agree for the selected labels and every pair of
corresponding blocks. Source: GLM23, `REsubmission.tex`, lines 1724--1726:
"The previous MPO tensors define an MPO representation of $\mathcal{C}$ if
$L^0=L^1$ and $F^0=F^1$, this can be seen as in the injective case." -/
theorem isBiorthogonalDecomposition_blockMixedMPO (a b : Fin r)
    (hL : ∀ x y, MPOTensor.actionLMatrix WF₀ VA₀ WA₀ a b x y =
      MPOTensor.actionLMatrix WF₁ VA₁ WA₁ a b x y) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor
        (blockMixedMPO (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a))
        (blockMixedMPO (O₀ b) (O₁ b) (VA₀ b) (VA₁ b) (WA₀ b) (WA₁ b))).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦
        (blockMixedMPO (O₀ q.1) (O₁ q.1) (VA₀ q.1) (VA₁ q.1)
          (WA₀ q.1) (WA₁ q.1)).toMPSTensor)
      (fun q ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b q.1 q.2) (VF₁ a b q.1 q.2))
      (fun q ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b q.1 q.2) (WF₁ a b q.1 q.2)) where
  retract q := by
    rw [mixedEndpointMPOFusionAnalysis_mul_synthesis, (hF₀ a b).retract q,
      (hF₁ a b).retract q, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  orthogonal q t hqt := by
    rw [mixedEndpointMPOFusionAnalysis_mul_synthesis,
      (hF₀ a b).orthogonal q t hqt, (hF₁ a b).orthogonal q t hqt,
      Matrix.fromBlocks_zero]
    rfl
  letter p := by
    classical
    have hInj₀' : ∀ x, Kraus.IsInjective (sectorTensor A₀ x) :=
      fun x => (isInjective_sectorTensor_iff A₀ x).2 (hInj₀ x)
    have hInj₁' : ∀ x, Kraus.IsInjective (sectorTensor A₁ x) :=
      fun x => (isInjective_sectorTensor_iff A₁ x).2 (hInj₁ x)
    have hSpan₀ := wordTupleSpanTop_sectorTensor A₀ hInj₀
    have hSpan₁ := wordTupleSpanTop_sectorTensor A₁ hInj₁
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    simp only [MPOTensor.toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat]
    obtain ⟨⟨y, t⟩, rfl⟩ := finSigmaFinEquiv.surjective i
    obtain ⟨⟨x, u⟩, rfl⟩ := finSigmaFinEquiv.surjective j
    obtain ⟨⟨p₁, p₂⟩, rfl⟩ := (mixedEndpointPhysicalEquiv (D₀ y) (D₁ y)).surjective t
    obtain ⟨⟨q₁, q₂⟩, rfl⟩ := (mixedEndpointPhysicalEquiv (D₀ x) (D₁ x)).surjective u
    ext e f
    obtain ⟨⟨α, β⟩, rfl⟩ :=
      (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)).surjective e
    obtain ⟨⟨γ, δ⟩, rfl⟩ :=
      (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)).surjective f
    simp only [MPOTensor.mulTensor, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.kroneckerMap_apply]
    rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp only [blockMixedMPO_finSigmaFinEquiv]
    have hz : ∀ z : Fin s,
        (∑ w : Fin ((D₀ z + D₁ z) * (D₀ z + D₁ z)),
          blockMixedMPOSector (operatorSector (O₀ a) y z) (operatorSector (O₁ a) y z)
              (VA₀ a z y) (VA₁ a z y) (WA₀ a z y) (WA₁ a z y)
              (mixedEndpointPhysicalEquiv (D₀ y) (D₁ y) (p₁, p₂)) w
              (finProdFinEquiv.symm (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)
                (α, β))).1
              (finProdFinEquiv.symm (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)
                (γ, δ))).1 *
            blockMixedMPOSector (operatorSector (O₀ b) z x) (operatorSector (O₁ b) z x)
              (VA₀ b x z) (VA₁ b x z) (WA₀ b x z) (WA₁ b x z) w
              (mixedEndpointPhysicalEquiv (D₀ x) (D₁ x) (q₁, q₂))
              (finProdFinEquiv.symm (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)
                (α, β))).2
              (finProdFinEquiv.symm (mixedEndpointActedEquiv (χ₀ a) (χ₁ a) (χ₀ b) (χ₁ b)
                (γ, δ))).2) =
        ∑ u : Fin (D₀ z) ⊕ Fin (D₁ z), ∑ v : Fin (D₀ z) ⊕ Fin (D₁ z),
          blockMixedMPOLetter (operatorSector (O₀ a) y z) (operatorSector (O₁ a) y z)
            (VA₀ a z y) (VA₁ a z y) (WA₀ a z y) (WA₁ a z y) p₁ p₂ u v α γ *
          blockMixedMPOLetter (operatorSector (O₀ b) z x) (operatorSector (O₁ b) z x)
            (VA₀ b x z) (VA₁ b x z) (WA₀ b x z) (WA₁ b x z) u v q₁ q₂ β δ := by
      intro z
      rw [← (mixedEndpointPhysicalEquiv (D₀ z) (D₁ z)).sum_comp, Fintype.sum_prod_type]
      simp [blockMixedMPOSector, mixedEndpointActedEquiv]
    simp only [hz]
    simp only [blockMixedMPOSector,
      mixedEndpointMPOFusion_sandwich, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Fintype.sum_sigma]
    simpa [mixedEndpointActedEquiv] using
      blockMixedMPOLetter_fusion O₀ O₁ VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ a b y x
        (operatorSector_fusion_entry O₀ VF₀ WF₀ a b (hF₀ a b) y x)
        (operatorSector_fusion_entry O₁ VF₁ WF₁ a b (hF₁ a b) y x)
        (blockCrossEndpoint_fusion_entry VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁
          hF₀ hA₀ hF₁ hA₁ hInj₀' hInj₁' hD₀ hD₁ one_pos one_pos hSpan₀ hSpan₁ a b x y
          (hL x y))
        (blockCrossEndpoint_fusion_entry VF₁ WF₁ VA₁ WA₁ VF₀ WF₀ VA₀ WA₀
          hF₁ hA₁ hF₀ hA₀ hInj₁' hInj₀' hD₁ hD₀ one_pos one_pos hSpan₁ hSpan₀ a b x y
          (hL x y).symm)
        p₁ p₂ q₁ q₂ α γ β δ

include hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ in
/-- With equal chosen raw L matrices for every pair of labels and every pair
of corresponding blocks, the common MPOs of the block-injective path satisfy
the original fusion rules at every positive length. Source: GLM23,
`REsubmission.tex`, lines 1724--1726. -/
theorem isMPOFusionAlgebra_blockMixedMPO
    (hL : ∀ a b x y, MPOTensor.actionLMatrix WF₀ VA₀ WA₀ a b x y =
      MPOTensor.actionLMatrix WF₁ VA₁ WA₁ a b x y) :
    MPOTensor.IsMPOFusionAlgebra
      (fun a ↦ blockMixedMPO (O₀ a) (O₁ a) (VA₀ a) (VA₁ a) (WA₀ a) (WA₁ a)) N :=
  MPOTensor.isMPOFusionAlgebra_of_biorthogonalDecompositions
    (fun a b c μ ↦ mixedEndpointMPOFusionAnalysis (VF₀ a b c μ) (VF₁ a b c μ))
    (fun a b c μ ↦ mixedEndpointMPOFusionSynthesis (WF₀ a b c μ) (WF₁ a b c μ))
    (fun a b ↦ isBiorthogonalDecomposition_blockMixedMPO O₀ O₁ A₀ A₁
      VF₀ WF₀ VA₀ WA₀ VF₁ WF₁ VA₁ WA₁ hF₀ hA₀ hF₁ hA₁ hInj₀ hInj₁ hD₀ hD₁ a b (hL a b))

end Global

end MPSTensor.MPOSymmetry
