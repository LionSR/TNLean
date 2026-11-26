/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Calculus.MatrixEntrywiseDeriv
import QICLean.Analysis.Calculus.MatrixFrameDeriv
import QICLean.Analysis.Calculus.MatrixLinearODE
import TNLean.MPS.MPDO.MPOAction.BoundaryActionLMatrixGauge
import QICLean.Analysis.Exponential.UnitaryEvolution

/-!
# The L-symbols along a differentiable symmetric path

Along a path of symmetric states, with the operator blocks and fusion maps
fixed, the first-order change of the L matrix is an infinitesimal gauge
transformation. This is the first-order computation in the invariance step
of the classification of symmetric phases in Garre-Rubio, Lootens and
Molnár, Section 5.2 ("MPSs with inequivalent L-symbols belong to different
phases").

The source's conclusion at line 1551, that the gauge class of the
L-symbols is constant along the path, is proved here with the same
hypotheses at every point of a connected open parameter set. The source
does not integrate its first-order law; the integration below needs no
continuity of the generators. Along the path the action analysis maps move
by invertible changes of basis, since near each parameter their trace
pairings `Q` against the synthesis maps there satisfy `Q' = X Q` and
`Q⁻¹ V` is locally constant. See
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

The source fixes a point `γ` of the path and writes, after a basis change
of the action multiplicity spaces, `V(γ + dγ) = V(γ) + ∑ X V(γ) dγ`
(lines 1387--1405). It then differentiates the defining relation of the
L-symbols, `eq:F_symbol3`, and applies the inverse L-symbols. The
conclusion, lines 1537--1551, is

`L'^{zij}_{cμk} = ∑ L^{z i' j'}_{c μ k'} [δδδ + (X_{bx}^z)^j_{j'} δδ`
`  + (X_{az}^y)^i_{i'} δδ - (X_{cx}^y)^{k'}_k δδ]`,

(the source's hatted summation indices are written primed),

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
  lines 1387--1551.
* `MPOTensor.hasDerivAt_actionLMatrix_gaugeCurve`: the same expression is
  the velocity of the gauge orbit `t ↦` (gauge law with `1 + t X`).
* `MPOTensor.exists_actionLMatrix_regauge_of_hasDerivAt`: the L matrices at
  any two points of the path are related by the gauge law with invertible
  gauges, GLM23 line 1551.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `REsubmission.tex`,
  lines 1352--1578 (invariance of the L-symbol class) and 593--605 (the
  gauge law of the L-symbols).

## Constructing gauges for L-symbol invariance

For globally bounded continuously differentiable span generators, the
matrix ODE existence theorem constructs fundamental solutions. These
implement the L-symbol gauge law on any closed interval satisfying the
first-order symmetric-path hypotheses.

This is a scope restriction of GLM23, arXiv:2203.12563v3, Section 5.2,
line 1551: the source does not state boundedness or continuous
differentiability of the generators.
-/

section

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

The hypotheses are the source's:
* fixed operators and fusion maps: "by assumption, the symmetry operators
  are the same along such path" (line 1359);
* exact action tensors near `γ₀`: "We further assume that there are action
  tensors locally realizing this symmetry, i.e. Eq. (fusiontensors2) is
  satisfied", for paths "that have an exact MPS ground space through the
  whole path, so that a set of L-symbols can also be defined all along"
  (lines 1269--1272);
* injective, pairwise inequivalent blocks: "we restrict w.l.o.g. to MPSs
  whose blocks are injective and orthogonal between each other"
  (line 317) and "we can assume that the MPS tensors are injective and
  orthogonal between them" (line 1332); for injective blocks,
  orthogonality in the thermodynamic limit is pairwise
  non-proportionality, `BlocksNotGaugePhaseEquiv`;
* a fixed bond dimension: "we assume for now that the bond dimension does
  not change" (line 1361);
* the span assumption on the derivative (lines 1387--1405).

Differentiability of the left inverses is not assumed; the source's
claim that the `L'`-symbols are differentiable (line 1440) is derived.
The conclusion is first order. The source's final step, that the class of
the L-symbols is constant along the path (line 1551), is
`exists_actionLMatrix_regauge_of_hasDerivAt`. -/
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

/-- Products of the exact action maps of one block are the identity on equal
multiplicity labels and zero otherwise. -/
private theorem actionAnalysis_mul_synthesis
    {A : ∀ x, MPSTensor d (D x)}
    {VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
    {WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (a : Fin r) (x y : Fin s) (i k : Fin (M a x y)) :
    VA a x y i * WA a x y k = if i = k then 1 else 0 := by
  split_ifs with h
  · subst h
    exact (hA a x).retract ⟨y, i⟩
  · exact (hA a x).orthogonal ⟨y, i⟩ ⟨y, k⟩ fun h' ↦ h (by simpa using h')

/-- **The class of the L-symbols is constant along a symmetric path.**
Fix the operator blocks `O`, the exact fusion maps `VF, WF`, and positive
bond dimensions `D`. On a connected open parameter set `U`, let the state
blocks `A γ` be injective and pairwise inequivalent with exact action maps
`VA γ, WA γ`, and let the analysis maps be differentiable at every `γ ∈ U`
with derivative in the span of the action tensors at `γ`,
`dV^i = ∑_{i'} X(γ)[i,i'] V^{i'}(γ)`. Then for any `γ₀, γ ∈ U` there are
invertible multiplicity gauges `G` with

`L(γ)^{z,ij}_{c,kμ} = ∑ G^y_{az}[i,i'] G^z_{bx}[j,j'] (G^y_{cx})⁻¹[k',k]`
`L(γ₀)^{z,i'j'}_{c,k'μ}`,

the gauge law `actionLMatrix_regauge` with transposed inverse synthesis
gauge and trivial fusion gauge.

Source: GLM23, `REsubmission.tex`, line 1551:

"which means that the ${L}'$-symbol is in the same class as the
${L}$-symbol since they are related by a (differentiable) gauge
transformation."

The hypotheses are those of `hasDerivAt_actionLMatrix`, the source's, at
every point of the path: fixed operators and fusion maps (line 1359), exact
action tensors along the whole path (lines 1269--1272), injective blocks
orthogonal between each other (lines 317 and 1332), a fixed bond dimension
(line 1361), and the span assumption on the derivative of the action
tensors at every point (lines 1387--1405). The last two are the source's
assumptions at line 1361, "we assume for now that the bond dimension does
not change", and at lines 1387--1405: "Let us absorb this basis change and
assume [...] that the action tensors are differentiable", followed by the
displayed expansion `V(γ + dγ)^i = V(γ)^i + ∑_{i'} (X_{ax}^y)_{i'}^i V(γ)^{i'} dγ`
(lines 1388--1404), "where we have spanned the term in $d\gamma$ using the
orthogonal set of action tensors" (line 1405). No continuity of the generators
`X` is assumed. The source gives no integration argument; here, near each
parameter the pairing matrices `Q` of the analysis maps against the
synthesis maps there satisfy `Q' = X Q`, so `Q⁻¹ V` is locally constant,
and the parameter set is connected (`Matrix.exists_eq_sum_smul_of_hasDerivAt`).
The source's extensions to action tensors that are only continuous and to a
growing bond dimension (line 1551) are not covered. -/
theorem exists_actionLMatrix_regauge_of_hasDerivAt
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    {U : Set ℝ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hA : ∀ γ ∈ U, ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A γ x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A γ q.1)
        (fun q ↦ VA γ a x q.1 q.2) (fun q ↦ WA γ a x q.1 q.2))
    (hInj : ∀ γ ∈ U, ∀ x, Kraus.IsInjective (A γ x))
    (hne : ∀ γ ∈ U, MPSTensor.BlocksNotGaugePhaseEquiv (A γ))
    (hD : ∀ x, 0 < D x)
    (X : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ)
    (hdV : ∀ γ ∈ U, ∀ a x y i u v, HasDerivAt (fun γ' ↦ VA γ' a x y i u v)
      ((∑ i', X γ a x y i i' • VA γ a x y i') u v) γ)
    {γ₀ γ : ℝ} (hγ₀ : γ₀ ∈ U) (hγ : γ ∈ U) :
    ∃ G : ∀ a x y, GL (Fin (M a x y)) ℂ,
      ∀ (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
        (k : Fin (M c x y)) (μ : Fin (N a b c)),
        actionLMatrix WF (VA γ) (WA γ) a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
          ∑ i', ∑ j', ∑ k',
            (↑(G a z y) : Matrix (Fin (M a z y)) (Fin (M a z y)) ℂ) i i' *
              (↑(G b x z) : Matrix (Fin (M b x z)) (Fin (M b x z)) ℂ) j j' *
              (↑((G c x y)⁻¹) : Matrix (Fin (M c x y)) (Fin (M c x y)) ℂ) k' k *
              actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i', j'⟩ ⟨c, k', μ⟩ := by
  have hDy : ∀ y, (D y : ℂ) ≠ 0 := fun y ↦ by exact_mod_cast (hD y).ne'
  -- The action analysis maps at `γ` are an invertible change of basis of those at `γ₀`.
  choose G hG using fun a x y ↦ Matrix.exists_eq_sum_smul_of_hasDerivAt hUo hUc
    (V := fun γ ↦ VA γ a x y) (X := fun γ ↦ X γ a x y) (fun s hs ↦ hdV s hs a x y)
    (fun s hs ↦ ⟨WA s a x y, (D y : ℂ)⁻¹, fun i k ↦ by
      rw [actionAnalysis_mul_synthesis (hA s hs) a x y i k]
      split_ifs <;> simp [hDy y]⟩) hγ₀ hγ
  refine ⟨G, fun a b c x y z i j k μ ↦ ?_⟩
  -- Synthesis maps dual to the transported analysis maps.
  set WA' : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ :=
    fun a x y k ↦ ∑ k', (↑((G a x y)⁻¹) : Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ) k' k •
      WA γ₀ a x y k' with hWA'
  have hprod : ∀ (c : Fin r) (k₁ k₂ : Fin (M c x y)),
      VA γ c x y k₁ * WA' c x y k₂ =
        (if k₁ = k₂ then 1 else 0 : Matrix (Fin (D y)) (Fin (D y)) ℂ) := by
    intro c k₁ k₂
    have hGG := Units.mul_inv (G c x y)
    have hentry := congrFun (congrFun hGG k₁) k₂
    rw [Matrix.mul_apply, Matrix.one_apply] at hentry
    simp only [hG c x y k₁, hWA', Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
      Matrix.mul_smul, actionAnalysis_mul_synthesis (hA γ₀ hγ₀), smul_smul, smul_ite,
      smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_smul]
    simp_rw [mul_comm _ ((↑(G c x y) : Matrix (Fin (M c x y)) (Fin (M c x y)) ℂ) k₁ _)]
    rw [hentry]
    split_ifs <;> simp
  -- With these synthesis maps the fusion-then-action pairing is the identity.
  have hfus : fusionPairing VF WF (VA γ) WA' a b x y = 1 := by
    ext ⟨c₁, k₁, μ₁⟩ ⟨c₂, k₂, μ₂⟩
    simp only [fusionPairing, Matrix.of_apply, fusionThenActionAnalysis,
      fusionThenActionSynthesis]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kronId _ _), kronId_mul]
    by_cases hcμ : (⟨c₁, μ₁⟩ : (c : Fin r) × Fin (N a b c)) = ⟨c₂, μ₂⟩
    · obtain ⟨rfl, hμ⟩ := Sigma.mk.inj_iff.1 hcμ
      obtain rfl := eq_of_heq hμ
      have hret := (hF a b).retract ⟨c₁, μ₁⟩
      simp only at hret
      rw [hret, kronId_one, Matrix.one_mul, hprod, Matrix.one_apply]
      split_ifs with h₁ h₂ h₂
      · simp [hDy y]
      · exact absurd (by rw [h₁]) h₂
      · exact absurd (by simpa using h₂) h₁
      · simp
    · have horth := (hF a b).orthogonal ⟨c₁, μ₁⟩ ⟨c₂, μ₂⟩ hcμ
      simp only at horth
      rw [horth, Matrix.one_apply, ite_eq_right fun h ↦ hcμ (by
        simp only [Sigma.mk.inj_iff] at h ⊢
        obtain ⟨rfl, h⟩ := h
        simpa using (Prod.ext_iff.1 (eq_of_heq h)).2)]
      simp [kronId]
  have hseq := sequentialPairing_eq_mul VF WF (WA₀ := WA') hF (hA γ hγ) (hInj γ hγ)
    (hne γ hγ) hD a b x y
  rw [hfus, Matrix.mul_one] at hseq
  have hL : actionLMatrix WF (VA γ) (WA γ) a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
      actionLMatrix WF (VA γ) WA' a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ := by
    rw [← hseq]
    rfl
  rw [hL, actionLMatrix_regauge
    (X := fun a x y ↦ (↑(G a x y) : Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ))
    (Xh := fun a x y k k' ↦ (↑((G a x y)⁻¹) : Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ) k' k)
    (Yh := fun _ _ _ ↦ 1) (WF := WF) (WF' := WF) (WA := WA γ₀) (WA' := WA')
    (fun a x y i ↦ hG a x y i) (fun _ _ _ _ ↦ rfl)
    (fun a b c μ ↦ by simp [Matrix.one_apply])]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Constancy of the L-symbol gauge class along an interval.**
Assume the first-order path hypotheses at every point of `[α, β]`, and
continuous span coefficients `X`. Given fundamental solutions
`g' = X g`, `g γ₀ = 1` on the action multiplicity spaces, they are
invertible everywhere on the interval and implement exactly the gauge law
of `actionLMatrix_regauge`, with fixed fusion gauge and synthesis gauge
`(g⁻¹)ᵀ`.

**Scope restriction (continuous generators and given ODE solutions):**
This integrates the infinitesimal law of GLM23, `REsubmission.tex`, lines
1387--1551. Continuity of the generators is an additional assumption not
stated in the source; existence of the fundamental solutions is explicit.
See `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`. No regularity of the
synthesis maps is assumed. The unrestricted source claim, including merely
continuous paths and changing bond dimensions, is not asserted here. -/
theorem actionLMatrix_gaugeEquiv_of_continuous
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    {α β γ₀ : ℝ} (hγ₀ : γ₀ ∈ Set.Icc α β)
    (hA : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A γ x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A γ q.1)
        (fun q ↦ VA γ a x q.1 q.2) (fun q ↦ WA γ a x q.1 q.2))
    (hInj : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, ∀ x, Kraus.IsInjective (A γ x))
    (hne : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, MPSTensor.BlocksNotGaugePhaseEquiv (A γ))
    (hD : ∀ x, 0 < D x)
    (X g : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ)
    (hX : ∀ a x y, ContinuousOn (fun t ↦ X t a x y) (Set.Icc α β))
    (hdV : ∀ t ∈ Set.Icc α β, ∀ a x y i u v,
      HasDerivAt (fun γ ↦ VA γ a x y i u v)
        ((∑ i', X t a x y i i' • VA t a x y i') u v) t)
    (hg₀ : ∀ a x y, g γ₀ a x y = 1)
    (hg : ∀ t ∈ Set.Icc α β, ∀ a x y i j,
      HasDerivAt (fun γ ↦ g γ a x y i j) ((X t a x y * g t a x y) i j) t)
    {t : ℝ} (ht : t ∈ Set.Icc α β) :
    (∀ a x y, IsUnit (g t a x y)) ∧
      ∀ (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
        (k : Fin (M c x y)) (μ : Fin (N a b c)),
        actionLMatrix WF (VA t) (WA t) a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
          ∑ i', ∑ j', ∑ k', g t a z y i i' * g t b x z j j' * (g t c x y)⁻¹ k' k *
            actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i', j'⟩ ⟨c, k', μ⟩ := by
  have hg' (a : Fin r) (x y : Fin s) (u : ℝ) (hu : u ∈ Set.Icc α β) :
      HasDerivAt (fun γ ↦ g γ a x y) (X u a x y * g u a x y) u :=
    hasDerivAt_pi.mpr fun i ↦ hasDerivAt_pi.mpr fun j ↦ hg u hu a x y i j
  refine ⟨fun a x y ↦ Matrix.isUnit_of_hasDerivAt_mul
    (hX a x y) (hg' a x y) hγ₀ (hg₀ a x y) ht, ?_⟩
  intro a b c x y z i j k μ
  let L : ℝ → Matrix (Fin (M a z y) × Fin (M b x z)) (Fin (M c x y)) ℂ :=
    fun u p q ↦ actionLMatrix WF (VA u) (WA u) a b x y ⟨z, p.1, p.2⟩ ⟨c, q, μ⟩
  have hL := Matrix.eq_kronecker_mul_initial_mul_inv_of_hasDerivAt (L := L)
    (hX a z y) (hX b x z) (hX c x y) (hg' a z y) (hg' b x z) (hg' c x y)
    (fun u hu i j k ↦ hasDerivAt_actionLMatrix VF WF hF (hA u hu) (hInj u hu)
      (hne u hu) hD (X u) (hdV u hu) a b c x y z i j k μ)
    hγ₀ (hg₀ a z y) (hg₀ b x z) (hg₀ c x y) ht
  have heq := congrFun (congrFun hL (i, j)) k
  change L t (i, j) k = _
  rw [heq]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ ↦ Finset.sum_congr rfl fun k' _ ↦ ?_
  dsimp only [L]
  ring

end MPOTensor

end

section

open Filter Topology
open scoped Matrix BigOperators NNReal Matrix.Norms.L2Operator

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  {O : ∀ a, MPOTensor d (χ a)} {A : ℝ → ∀ x, MPSTensor d (D x)}
  {VA : ℝ → ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ}
  {WA : ℝ → ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ}

/-- **Scope restriction (bounded continuously differentiable generators):**
The L-symbol gauge class is constant, with the fundamental gauges
constructed rather than assumed. All generators are defined on the real
line, continuously differentiable, and uniformly bounded (with a bound
allowed to depend on the multiplicity space). The tensor-path assumptions
are needed only near the chosen closed interval.

This supplies an existence-based version of the integration of GLM23,
`REsubmission.tex`, lines 1387--1551. The additional regularity and
boundedness assumptions are absent from the source; see
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`. -/
theorem exists_actionLMatrix_gaugeEquiv_of_contDiff
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    {α β γ₀ : ℝ} (hγ₀ : γ₀ ∈ Set.Icc α β)
    (hA : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A γ x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A γ q.1)
        (fun q ↦ VA γ a x q.1 q.2) (fun q ↦ WA γ a x q.1 q.2))
    (hInj : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, ∀ x, Kraus.IsInjective (A γ x))
    (hne : ∀ t ∈ Set.Icc α β, ∀ᶠ γ in 𝓝 t, MPSTensor.BlocksNotGaugePhaseEquiv (A γ))
    (hD : ∀ x, 0 < D x)
    (X : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ)
    (hX : ∀ a x y, ContDiff ℝ 1 (fun t ↦ X t a x y))
    (hbound : ∀ a x y, ∃ C : ℝ≥0, ∀ t, ‖X t a x y‖ ≤ C)
    (hdV : ∀ t ∈ Set.Icc α β, ∀ a x y i u v,
      HasDerivAt (fun γ ↦ VA γ a x y i u v)
        ((∑ i', X t a x y i i' • VA t a x y i') u v) t) :
    ∃ g : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ,
      (∀ a x y, g γ₀ a x y = 1) ∧
      (∀ t a x y, HasDerivAt (fun u ↦ g u a x y) (X t a x y * g t a x y) t) ∧
      ∀ t ∈ Set.Icc α β,
        (∀ a x y, IsUnit (g t a x y)) ∧
          ∀ (a b c : Fin r) (x y z : Fin s) (i : Fin (M a z y)) (j : Fin (M b x z))
            (k : Fin (M c x y)) (μ : Fin (N a b c)),
            actionLMatrix WF (VA t) (WA t) a b x y ⟨z, i, j⟩ ⟨c, k, μ⟩ =
              ∑ i', ∑ j', ∑ k', g t a z y i i' * g t b x z j j' * (g t c x y)⁻¹ k' k *
                actionLMatrix WF (VA γ₀) (WA γ₀) a b x y ⟨z, i', j'⟩ ⟨c, k', μ⟩ := by
  have hex (a : Fin r) (x y : Fin s) :
      ∃ U : ℝ → Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ,
        U 0 = 1 ∧ ∀ t, HasDerivAt U (X (γ₀ + t) a x y * U t) t := by
    obtain ⟨C, hC⟩ := hbound a x y
    exact MatrixEvolution.exists_solution (fun t ↦ X (γ₀ + t) a x y)
      ((hX a x y).comp (contDiff_const.add contDiff_id)) C (fun t ↦ hC (γ₀ + t)) 1
  choose U hU₀ hU using hex
  let g : ℝ → ∀ a x y, Matrix (Fin (M a x y)) (Fin (M a x y)) ℂ :=
    fun t a x y ↦ U a x y (t - γ₀)
  have hg₀ (a : Fin r) (x y : Fin s) : g γ₀ a x y = 1 := by
    simp only [g, sub_self, hU₀]
  have hg (t : ℝ) (a : Fin r) (x y : Fin s) :
      HasDerivAt (fun u ↦ g u a x y) (X t a x y * g t a x y) t := by
    have hshift : γ₀ + (t - γ₀) = t := by ring
    simpa only [g, Function.comp_def, id_eq, hshift, one_smul] using
      (hU a x y (t - γ₀)).scomp t ((hasDerivAt_id t).sub_const γ₀)
  refine ⟨g, hg₀, hg, fun t ht ↦ ?_⟩
  exact actionLMatrix_gaugeEquiv_of_continuous VF WF hF hγ₀ hA hInj hne hD X g
    (fun a x y ↦ (hX a x y).continuous.continuousOn) hdV hg₀
    (fun u _ a x y i j ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp (hg u a x y) i) j) ht

end MPOTensor

end
