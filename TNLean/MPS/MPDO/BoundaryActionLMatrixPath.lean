/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixEntrywiseDeriv
import TNLean.MPS.MPDO.BoundaryActionLMatrixGauge

/-!
# The L-symbols along a differentiable symmetric path

Along a path of symmetric states, with the operator blocks and fusion maps
fixed, the first-order change of the L matrix is an infinitesimal gauge
transformation. This is the invariance step of the classification of
symmetric phases in Garre-Rubio, Lootens and Molnár, Section 5.2
("MPSs with inequivalent L-symbols belong to different phases").

The source fixes a point `γ` of the path and writes, after a basis change
of the action multiplicity spaces, `V(γ + dγ) = V(γ) + ∑ X V(γ) dγ`
(lines 1387--1405). It then differentiates the defining relation of the
L-symbols, `eq:F_symbol3`, and applies the inverse L-symbols. The
conclusion, lines 1537--1551, is

`L'^{zij}_{cμk} = ∑ L^{z î ĵ}_{c μ k̂} [δδδ + (X_{bx}^z)^j_ĵ δδ`
`  + (X_{az}^y)^i_î δδ - (X_{cx}^y)^k̂_k δδ]`,

"which means that the L'-symbol is in the same class as the L-symbol
since they are related by a (differentiable) gauge transformation."

The formal route avoids the left inverses along the path. At a parameter
`γ`, pairing the defining relation with the synthesis maps of the base
point gives `R(γ) = L(γ) P(γ)` for finite matrices `R` and `P` that are
linear in the analysis maps, with `P(γ₀) = 1` by biorthogonality.
Cramer's rule makes `L` differentiable at `γ₀`, and the product rule gives
its derivative. Only the analysis maps are assumed differentiable; the
synthesis maps at other parameters are arbitrary exact companions.

The index convention is that of `actionLMatrix_regauge`: the source's
`(X_{ax}^y)_{i'}^{i}` is `X a x y i i'`.

## Main results

* `MPOTensor.hasDerivAt_actionLMatrix`: the derivative of every L entry
  along the path is `X_{az}^y L + X_{bx}^z L - L X_{cx}^y`, GLM23
  lines 1352--1551.
* `MPOTensor.hasDerivAt_actionLMatrix_gaugeCurve`: the same expression is
  the velocity of the gauge orbit `t ↦` (gauge law with `1 + t X`).

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
  lines 1352--1578 (invariance of the L-symbol class) and 593--605 (the
  gauge law of the L-symbols).
-/

open Filter Topology
open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

private theorem hasDerivAt_idKron_entries {m n : ℕ} (E : ℕ) {t : ℝ}
    {V : ℝ → Matrix (Fin m) (Fin n) ℂ} {V' : Matrix (Fin m) (Fin n) ℂ}
    (hV : ∀ i j, HasDerivAt (fun s ↦ V s i j) (V' i j) t) (i : Fin (E * m)) (j : Fin (E * n)) :
    HasDerivAt (fun s ↦ idKron E (V s) i j) (idKron E V' i j) t := by
  simp only [idKron, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  exact (hV _ _).const_mul _

private theorem hasDerivAt_kronId_entries {m n : ℕ} (E : ℕ) {t : ℝ}
    {V : ℝ → Matrix (Fin m) (Fin n) ℂ} {V' : Matrix (Fin m) (Fin n) ℂ}
    (hV : ∀ i j, HasDerivAt (fun s ↦ V s i j) (V' i j) t) (i : Fin (m * E)) (j : Fin (n * E)) :
    HasDerivAt (fun s ↦ kronId (V s) E i j) (kronId V' E i j) t := by
  simp only [kronId, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  exact (hV _ _).mul_const _

private theorem hasDerivAt_const_entries {m n : Type*} {t : ℝ} (C : Matrix m n ℂ) (i : m)
    (j : n) : HasDerivAt (fun _ : ℝ ↦ C i j) ((0 : Matrix m n ℂ) i j) t :=
  hasDerivAt_const _ _

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  {O : ∀ a, MPOTensor d (χ a)} {A : ℝ → ∀ x, MPSTensor d (D x)}
  {VA : ℝ → ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
  {WA : ℝ → ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}

/-- At one point, sequential analysis is the L matrix applied to
fusion-then-action analysis, within one final block. -/
private theorem sequentialActionAnalysis_eq_sum_actionLMatrix
    {A : ∀ x, MPSTensor d (D x)}
    {VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
    {WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hne : MPSTensor.BlocksNotGaugePhaseEquiv A)
    (hD : ∀ x, 0 < D x) (a b : Fin r) (x y : Fin s)
    (p : SequentialActionMultiplicity M a b x y) :
    (sequentialActionAnalysis VA a b x ⟨⟨p.1, p.2.2⟩, ⟨y, p.2.1⟩⟩ :
        Matrix (Fin (D y)) (Fin (χ a * χ b * D x)) ℂ) =
      ∑ q, actionLMatrix WF VA WA a b x y p q •
        (fusionThenActionAnalysis VF VA a b x ⟨⟨q.1, q.2.2⟩, ⟨y, q.2.1⟩⟩ :
          Matrix (Fin (D y)) (Fin (χ a * χ b * D x)) ℂ) := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hD hne
  have h := actionLMatrix_analysis VF WF VA WA hF hA (fun y ↦ (hInj y).isNormal) hD a b x hL
    hSpan
  refine Matrix.ext fun (u : Fin (D y)) w ↦ ?_
  have hu := congrFun (congrFun h ⟨y, p, u⟩) w
  rw [Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_eq_single y] at hu
  · simp only [Matrix.blockDiagonal'_apply_eq, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul] at hu
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hu
    erw [Matrix.sum_apply]
    exact hu.symm
  · intro y' hy'
    rw [Finset.sum_eq_zero]
    intro q _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hy'), zero_mul]

/-- Sequential analysis at one parameter paired against fusion-then-action
synthesis at another, within one final block. At equal parameters this is
the L matrix. -/
private noncomputable def sequentialPairing
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b : Fin r) (x y : Fin s) :
    Matrix (SequentialActionMultiplicity M a b x y) (FusionActionMultiplicity N M a b x y) ℂ :=
  Matrix.of fun p q ↦ (D y : ℂ)⁻¹ * Matrix.trace
    (sequentialActionAnalysis VA a b x ⟨⟨p.1, p.2.2⟩, ⟨y, p.2.1⟩⟩ *
      fusionThenActionSynthesis WF WA a b x ⟨⟨q.1, q.2.2⟩, ⟨y, q.2.1⟩⟩)

/-- Fusion-then-action analysis at one parameter paired against
fusion-then-action synthesis at another, within one final block. -/
private noncomputable def fusionPairing
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (a b : Fin r) (x y : Fin s) :
    Matrix (FusionActionMultiplicity N M a b x y) (FusionActionMultiplicity N M a b x y) ℂ :=
  Matrix.of fun q q' ↦ (D y : ℂ)⁻¹ * Matrix.trace
    (fusionThenActionAnalysis VF VA a b x ⟨⟨q.1, q.2.2⟩, ⟨y, q.2.1⟩⟩ *
      fusionThenActionSynthesis WF WA a b x ⟨⟨q'.1, q'.2.2⟩, ⟨y, q'.2.1⟩⟩)

private theorem sequentialPairing_eq_mul
    {A : ∀ x, MPSTensor d (D x)}
    {VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
    {WA WA₀ : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (hInj : ∀ x, Kraus.IsInjective (A x)) (hne : MPSTensor.BlocksNotGaugePhaseEquiv A)
    (hD : ∀ x, 0 < D x) (a b : Fin r) (x y : Fin s) :
    sequentialPairing WF VA WA₀ a b x y =
      actionLMatrix WF VA WA a b x y * fusionPairing VF WF VA WA₀ a b x y := by
  refine Matrix.ext fun p q' ↦ ?_
  rw [Matrix.mul_apply]
  simp only [sequentialPairing, fusionPairing, Matrix.of_apply]
  rw [sequentialActionAnalysis_eq_sum_actionLMatrix VF WF hF hA hInj hne hD a b x y p]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

private theorem fusionAnalysis_mul_synthesis
    {A : ∀ x, MPSTensor d (D x)}
    {VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
    {WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (a b : Fin r) (x y : Fin s) (q q' : FusionActionMultiplicity N M a b x y) :
    fusionThenActionAnalysis VF VA a b x ⟨⟨q.1, q.2.2⟩, ⟨y, q.2.1⟩⟩ *
        fusionThenActionSynthesis WF WA a b x ⟨⟨q'.1, q'.2.2⟩, ⟨y, q'.2.1⟩⟩ =
      if q = q' then 1 else 0 := by
  have hbi := fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x
  split_ifs with h
  · subst h
    exact hbi.retract _
  · refine hbi.orthogonal _ _ fun h' ↦ h ?_
    obtain ⟨c, k, μ⟩ := q
    obtain ⟨c', k', μ'⟩ := q'
    simp only [Sigma.mk.injEq] at h'
    obtain ⟨⟨rfl, hμ⟩, -, hk⟩ := h'
    simp_all

private theorem fusionPairing_self
    {A : ∀ x, MPSTensor d (D x)}
    {VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
    {WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (hD : ∀ x, 0 < D x) (a b : Fin r) (x y : Fin s) :
    fusionPairing VF WF VA WA a b x y = 1 := by
  refine Matrix.ext fun q q' ↦ ?_
  simp only [fusionPairing, Matrix.of_apply, fusionAnalysis_mul_synthesis VF WF hF hA,
    Matrix.one_apply]
  have hDy : (D y : ℂ) ≠ 0 := by exact_mod_cast (hD y).ne'
  split_ifs <;> simp [hDy]

/-- **The first-order change of the L-symbols is a gauge transformation.**
Fix the operator blocks `O`, the exact fusion maps `VF, WF`, and positive
bond dimensions `D`. Let the state blocks `A γ` be injective and pairwise
inequivalent near `γ₀`, with exact action maps `VA γ, WA γ`. If the
analysis maps are differentiable at `γ₀` with derivative in the span of the
action tensors at `γ₀`, `dV^i = ∑_{i'} X[i,i'] V^{i'}`, then every L entry
is differentiable at `γ₀`, with derivative

`∑_{i'} X_{az}^y[i,i'] L^{z i' j} + ∑_{j'} X_{bx}^z[j,j'] L^{z i j'}`
`  - ∑_{k'} L_{c k' μ} X_{cx}^y[k',k]`.

Source: GLM23, `REsubmission.tex`, lines 1387--1405 and 1537--1551:

"Since one can always find a left inverse tensor such that it is
continuous we can find without loss of generality a basis change, where
$V_{a,x}^{y,i}$ is also continuous (using the fact that the action tensors
are linearly independent). Let us absorb this basis change and assume (see
below for generalization) that the action tensors are differentiable:
[$V(\gamma+d\gamma)^i = V(\gamma)^i + \sum_{i'} (X_{ax}^y)_{i'}^i
V(\gamma)^{i'} d\gamma$], where we have spanned the term in $d\gamma$ using
the orthogonal set of action tensors $\{ V_{a,x}^{y,i}, i=1,{\cdots},
M_{a,x}^y\}$ of the subspace of the block $y$. [...] Therefore
$L'^{zij}_{c\mu k} = \sum_{\hat i,\hat j,\hat k}
(L_{abx}^y)^{z\hat i\hat j}_{c\mu\hat k} [\delta_{i,\hat i}\delta_{j,\hat j}
\delta_{k,\hat k} + (X_{bx}^z)_{\hat j}^{j} \delta_{i,\hat i}\delta_{k,\hat k}
+ (X_{az}^y)_{\hat i}^{i} \delta_{j,\hat j}\delta_{k,\hat k}
- (X_{cx}^y)^{\hat k}_{k} \delta_{i,\hat i}\delta_{j,\hat j}]$, which means
that the $L'$-symbol is in the same class as the $L$-symbol since they are
related by a (differentiable) gauge transformation."

The hypotheses are the source's: fixed operators and fusion maps
(line 1359), exact action tensors at every point near `γ₀`
(`fusiontensors2`), injective and pairwise inequivalent blocks, a fixed
bond dimension (line 1361), and the span assumption on the derivative.
Differentiability of the left inverses is not assumed; the source's
claim that the `L'`-symbols are differentiable (line 1440) is derived. -/
theorem hasDerivAt_actionLMatrix
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    {γ₀ : ℝ}
    (hA : ∀ᶠ γ in 𝓝 γ₀, ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A γ x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A γ q.1)
        (fun q ↦ VA γ a x q.1 q.2) (fun q ↦ WA γ a x q.1 q.2))
    (hInj : ∀ᶠ γ in 𝓝 γ₀, ∀ x, Kraus.IsInjective (A γ x))
    (hne : ∀ᶠ γ in 𝓝 γ₀, MPSTensor.BlocksNotGaugePhaseEquiv (A γ))
    (hD : ∀ x, 0 < D x)
    (X : ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ)
    (hdV : ∀ a x y i u v, HasDerivAt (fun γ ↦ VA γ a x y i u v)
      ((∑ i', X a x y i i' • VA γ₀ a x y i') u v) γ₀)
    (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
    (k : Fin (M c x y)) (μ : Fin (N a b c)) :
    HasDerivAt (fun γ ↦ actionLMatrix WF (VA γ) (WA γ) a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩)
      (∑ i', X a z y i i' * actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i', j⟩ ⟨c, k, μ⟩ +
        ∑ j', X b x z j j' * actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i, j'⟩ ⟨c, k, μ⟩ -
        ∑ k', actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i, j⟩ ⟨c, k', μ⟩ * X c x y k' k)
      γ₀ := by
  have hA₀ := hA.self_of_nhds
  -- Entrywise derivatives of the action analysis maps.
  set dV : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ :=
    fun a x y i ↦ ∑ i', X a x y i i' • VA γ₀ a x y i' with hdVdef
  -- The fixed synthesis maps of the base point.
  set FS : ∀ q : FusionActionMultiplicity N M a b x y,
      Matrix (Fin (χ a * χ b * D x)) (Fin (D y)) ℂ :=
    fun q ↦ fusionThenActionSynthesis WF (WA γ₀) a b x ⟨⟨q.1, q.2.2⟩, ⟨y, q.2.1⟩⟩ with hFS
  set R' : Matrix (SequentialActionMultiplicity M a b x y)
      (FusionActionMultiplicity N M a b x y) ℂ := Matrix.of fun p q ↦ (D y : ℂ)⁻¹ * Matrix.trace
    ((((dV a p.1 y p.2.1 * idKron (χ a) (VA γ₀ b x p.1 p.2.2) +
          VA γ₀ a p.1 y p.2.1 * idKron (χ a) (dV b x p.1 p.2.2)) *
          mulTensorAssocInvMatrix (χ a) (χ b) (D x) +
        (VA γ₀ a p.1 y p.2.1 * idKron (χ a) (VA γ₀ b x p.1 p.2.2)) *
          (0 : Matrix (Fin (χ a * (χ b * D x))) (Fin (χ a * χ b * D x)) ℂ)) * FS q +
      sequentialActionAnalysis (VA γ₀) a b x ⟨⟨p.1, p.2.2⟩, ⟨y, p.2.1⟩⟩ *
        (0 : Matrix (Fin (χ a * χ b * D x)) (Fin (D y)) ℂ))) with hR'
  set P' : Matrix (FusionActionMultiplicity N M a b x y)
      (FusionActionMultiplicity N M a b x y) ℂ := Matrix.of fun q q' ↦ (D y : ℂ)⁻¹ * Matrix.trace
    ((dV q.1 x y q.2.1 * kronId (VF a b q.1 q.2.2) (D x) +
        VA γ₀ q.1 x y q.2.1 * (0 : Matrix (Fin (χ q.1 * D x)) (Fin (χ a * χ b * D x)) ℂ)) *
          FS q' +
      fusionThenActionAnalysis VF (VA γ₀) a b x ⟨⟨q.1, q.2.2⟩, ⟨y, q.2.1⟩⟩ *
        (0 : Matrix (Fin (χ a * χ b * D x)) (Fin (D y)) ℂ)) with hP'
  have hRd : ∀ p q, HasDerivAt (fun γ ↦ sequentialPairing WF (VA γ) (WA γ₀) a b x y p q)
      (R' p q) γ₀ := by
    intro p q
    refine HasDerivAt.const_mul _ (Matrix.hasDerivAt_trace_of_entries fun u w ↦ ?_)
    refine Matrix.hasDerivAt_mul_entries (G := fun _ ↦ FS q) (fun u v ↦ ?_)
      (hasDerivAt_const_entries _) u w
    exact Matrix.hasDerivAt_mul_entries (G := fun _ ↦ mulTensorAssocInvMatrix (χ a) (χ b) (D x))
      (Matrix.hasDerivAt_mul_entries (hdV _ _ _ _)
        (hasDerivAt_idKron_entries _ (hdV _ _ _ _))) (hasDerivAt_const_entries _) u v
  have hPd : ∀ q q', HasDerivAt (fun γ ↦ fusionPairing VF WF (VA γ) (WA γ₀) a b x y q q')
      (P' q q') γ₀ := by
    intro q q'
    refine HasDerivAt.const_mul _ (Matrix.hasDerivAt_trace_of_entries fun u w ↦ ?_)
    refine Matrix.hasDerivAt_mul_entries (G := fun _ ↦ FS q') (fun u v ↦ ?_)
      (hasDerivAt_const_entries _) u w
    exact Matrix.hasDerivAt_mul_entries (G := fun _ ↦ kronId (VF a b q.1 q.2.2) (D x))
      (hdV _ _ _ _) (hasDerivAt_const_entries _) u v
  have hRP : ∀ᶠ γ in 𝓝 γ₀, sequentialPairing WF (VA γ) (WA γ₀) a b x y =
      actionLMatrix WF (VA γ) (WA γ) a b x y * fusionPairing VF WF (VA γ) (WA γ₀) a b x y := by
    filter_upwards [hA, hInj, hne] with γ h₁ h₂ h₃
    exact sequentialPairing_eq_mul VF WF hF h₁ h₂ h₃ hD a b x y
  have key := Matrix.hasDerivAt_entries_of_eventually_eq_mul hRP
    (fusionPairing_self VF WF hF hA₀ hD a b x y) hRd hPd ⟨z, i, j⟩ ⟨c, k, μ⟩
  convert key using 1
  have hR'v : R' ⟨z, i, j⟩ ⟨c, k, μ⟩ =
      ∑ i', X a z y i i' * actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i', j⟩ ⟨c, k, μ⟩ +
        ∑ j', X b x z j j' * actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i, j'⟩ ⟨c, k, μ⟩ := by
    simp only [hR', Matrix.of_apply, Matrix.mul_zero, add_zero, actionLMatrix_apply,
      sequentialActionAnalysis, hdVdef, idKron_sum_smul, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul, mul_add, Finset.mul_sum, hFS]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hDy : (D y : ℂ) ≠ 0 := by exact_mod_cast (hD y).ne'
  have hP'v : ∀ c₁ k₁ μ₁, P' ⟨c₁, k₁, μ₁⟩ ⟨c, k, μ⟩ = ∑ k', X c₁ x y k₁ k' *
      if (⟨c₁, k', μ₁⟩ : FusionActionMultiplicity N M a b x y) = ⟨c, k, μ⟩ then 1 else 0 := by
    intro c₁ k₁ μ₁
    simp only [hP', Matrix.of_apply, Matrix.mul_zero, add_zero, hdVdef,
      Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
      Finset.mul_sum, hFS]
    refine Finset.sum_congr rfl fun k' _ ↦ ?_
    have h := fusionAnalysis_mul_synthesis VF WF hF hA₀ a b x y ⟨c₁, k', μ₁⟩ ⟨c, k, μ⟩
    simp only [fusionThenActionAnalysis] at h
    rw [h]
    split_ifs
    · rw [Matrix.trace_one, Fintype.card_fin]
      field_simp
    · simp
  have hsum : ∑ q, actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i, j⟩ q * P' q ⟨c, k, μ⟩ =
      ∑ k', actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i, j⟩ ⟨c, k', μ⟩ * X c x y k' k := by
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type, hP'v]
    rw [Fintype.sum_eq_single c]
    · simp [Sigma.mk.injEq, ite_and]
    · intro c₁ hc₁
      simp [Sigma.mk.injEq, hc₁]
  rw [Matrix.sub_apply, hR'v, Matrix.mul_apply, hsum]


/-- **The first-order term is tangent to a gauge orbit.** The gauge law
`actionLMatrix_regauge`, with action analysis gauge `1 + t X`, action
synthesis gauge the transpose of `1 - t X` (the inverse to first order), and
trivial fusion gauge, moves the L matrix along a curve whose velocity at
`t = 0` is the expression of `hasDerivAt_actionLMatrix`. Source: GLM23,
`REsubmission.tex`, lines 1537--1551 and 593--605. -/
theorem hasDerivAt_actionLMatrix_gaugeCurve {a b : Fin r} {x y : Fin s}
    (L : SequentialActionMultiplicity M a b x y → FusionActionMultiplicity N M a b x y → ℂ)
    (X : ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ)
    (z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z)) (c : Fin r) (k : Fin (M c x y))
    (μ : Fin (N a b c)) :
    HasDerivAt (fun t : ℝ ↦ ∑ i', ∑ j', ∑ k',
        (1 + (t : ℂ) • X a z y) i i' * (1 + (t : ℂ) • X b x z) j j' *
          (1 - (t : ℂ) • X c x y) k' k * L ⟨z, i', j'⟩ ⟨c, k', μ⟩)
      (∑ i', X a z y i i' * L ⟨z, i', j⟩ ⟨c, k, μ⟩ +
        ∑ j', X b x z j j' * L ⟨z, i, j'⟩ ⟨c, k, μ⟩ -
        ∑ k', L ⟨z, i, j⟩ ⟨c, k', μ⟩ * X c x y k' k) 0 := by
  have hlin : ∀ {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (σ : ℂ) (u v : Fin m),
      HasDerivAt (fun t : ℝ ↦ ((1 : Matrix (Fin m) (Fin m) ℂ) + σ • (t : ℂ) • Y) u v)
        (σ * Y u v) 0 := by
    intro m Y σ u v
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (σ * Y u v)).const_add
      ((1 : Matrix (Fin m) (Fin m) ℂ) u v)
    convert h using 1
    · ext t; simp; ring
    · simp
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i' _ ↦ HasDerivAt.fun_sum
    (u := Finset.univ) fun j' _ ↦ HasDerivAt.fun_sum (u := Finset.univ) fun k' _ ↦
      ((((hlin (X a z y) 1 i i').fun_mul (hlin (X b x z) 1 j j')).fun_mul
        (hlin (X c x y) (-1) k' k)).mul_const (L ⟨z, i', j'⟩ ⟨c, k', μ⟩))
  convert h using 1
  · ext t
    simp only [one_smul, neg_smul, sub_eq_add_neg]
  · simp [Matrix.one_apply, add_mul, mul_add, ite_mul, mul_ite, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, sub_eq_add_neg, mul_comm]

end MPOTensor
