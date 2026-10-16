/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GappedGroundState
import TNLean.Algebra.MatrixReindexGap
import QICLean.Analysis.RegionalLowDefectProjection
import QICLean.Analysis.RegionalRoughLowerNorm
import QICLean.Analysis.RegionalSharpLowerNorm
import QICLean.Entropy.AuxiliaryPairEntropy
import QICLean.Entropy.SelectedSchmidtEntropy
import QICLean.Entropy.TypicalDensity
import QICLean.Representation.CompressedTypicalLabelMass
import QICLean.Representation.RegionalAuxiliaryLabels
import QICLean.Representation.ReplicaPrevectorRoughUpper
import QICLean.Representation.ReplicaPrevectorSharpUpper
import QICLean.Representation.ReplicaSymmetricBandCommute
import QICLean.Analysis.OperatorMean.TreeDerivative

/-!
# Data of the norm comparisons from an auxiliary pair

The objects and hypotheses of Proposition 8.1 for a finite product system: the vector
`pre_k`, the leaf factors `A_{j,g}`, the mean-tree root with leaves `A_j = ∏_g A_{j,g}` and
its band factorization, the common auxiliary labels, the typical Schmidt set, the status
family, the prefix data and the marginal moment data, together with the scalar steps of
the two lower comparisons.

## Main definitions

* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsTypicalSchmidtSet`: `comparator:typical-set`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsStatusFamily`: status partitions obeying
  `comparator:nesting`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsPrefixData`: `comparator:prefix-data`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsMarginalMomentData`: `comparator:mgf-data`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.prevector`: the vector `pre_k`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.bandMetric`: the leaf factor `A_{j,g}`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.meanRoot`: the mean-tree root `𝓜`.
* `Matrix.MeanTree.restrict`: a mean tree read on a finite set containing its leaf labels.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.Comparators.meanRoot_eq_listProd`: `𝓜 = ∏_g 𝓜_g`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.exists_prevector_labels`: the common labels.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 13–214, revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are written from the
manuscript; no Lean declaration of the accompanying development is reused.
-/

noncomputable section

open Filter Topology Matrix TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  symmDiff
namespace Matrix.MeanTree

variable {ι : Type*} [DecidableEq ι]

/-- The same tree with its leaf labels read in a finite set containing all of them. -/
def restrict (s : Finset ι) : (T : MeanTree ι) → (∀ j ∈ T.labels, j ∈ s) → MeanTree s
  | leaf j, h => leaf ⟨j, h j (List.mem_singleton_self j)⟩
  | node p l r, h => node p (l.restrict s fun j hj ↦ h j (List.mem_append_left _ hj))
      (r.restrict s fun j hj ↦ h j (List.mem_append_right _ hj))

omit [DecidableEq ι] in
theorem eval_restrict {n : Type*} [Fintype n] [DecidableEq n] (A : ι → Matrix n n ℂ)
    (s : Finset ι) : (T : MeanTree ι) → (h : ∀ j ∈ T.labels, j ∈ s) →
    (T.restrict s h).eval (fun j ↦ A j.val) = T.eval A
  | leaf _, _ => rfl
  | node p l r, h => by
    simp only [restrict, eval_node, eval_restrict A s l, eval_restrict A s r]

theorem weight_restrict (s : Finset ι) : (T : MeanTree ι) → (h : ∀ j ∈ T.labels, j ∈ s) →
    ∀ j : s, (T.restrict s h).weight j = T.weight j.val
  | leaf j, h, i => by
    by_cases hij : i.val = j
    · have hi : i = ⟨j, h j (List.mem_singleton_self j)⟩ := Subtype.ext hij
      subst hi
      simp [restrict]
    · have hi : i ≠ ⟨j, h j (List.mem_singleton_self j)⟩ := fun hi ↦ hij (by simp [hi])
      simp [restrict, hi, hij]
  | node p l r, h, i => by
    simp only [restrict, weight_node, weight_restrict s l, weight_restrict s r]

/-- A weighted sum over the leaf labels of a restricted tree is the weighted sum over all
labels. -/
theorem sum_weight_restrict_mul [Fintype ι] (T : MeanTree ι) (f : ι → ℝ) :
    ∑ j : T.labels.toFinset,
        (T.restrict T.labels.toFinset fun _ hj ↦ List.mem_toFinset.mpr hj).weight j * f j.val =
      ∑ j, T.weight j * f j := by
  simp only [weight_restrict]
  rw [Finset.sum_coe_sort T.labels.toFinset (fun j ↦ T.weight j * f j)]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ by
    rw [weight_eq_zero_of_not_mem (fun h ↦ hj (List.mem_toFinset.mpr h)), zero_mul]

end Matrix.MeanTree

namespace TNLean.PEPS.AreaLaw.Scan.Comparators

/-- Compressing a product of operators that each intertwine an isometry with a compressed
operator gives the product of the compressed operators. -/
theorem conjTranspose_mul_listProd_ofFn_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {K : ℕ} (A : Fin K → Matrix m m ℂ) (B : Fin K → Matrix n n ℂ) (Z : Matrix m n ℂ)
    (hZ : Zᴴ * Z = 1) (h : ∀ g, A g * Z = Z * B g) :
    Zᴴ * (List.ofFn A).prod * Z = (List.ofFn B).prod := by
  have hprod : ∀ {K : ℕ} (A : Fin K → Matrix m m ℂ) (B : Fin K → Matrix n n ℂ),
      (∀ g, A g * Z = Z * B g) → (List.ofFn A).prod * Z = Z * (List.ofFn B).prod := by
    intro K
    induction K with
    | zero => intro A B _; simp
    | succ K ih =>
      intro A B h
      simp only [List.ofFn_succ, List.prod_cons]
      rw [Matrix.mul_assoc, ih _ _ fun g ↦ h g.succ, ← Matrix.mul_assoc, h 0,
        Matrix.mul_assoc]
  rw [Matrix.mul_assoc, hprod A B h, ← Matrix.mul_assoc, hZ, Matrix.one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The one-copy sites `V = phys ⊗ C ⊗ R`: the label `some none` is the auxiliary system
`C`, the label `none` is `R`, and both have dimension `d`
(`07-comparators.tex`, lines 87–95). -/
abbrev siteSpace (d : ℕ) : Option (Option ι) → Type :=
  addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)

/-- The vector `pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k}` of `comparator:prevector`, with
`Bell_{CR} = d^{-1/2} ∑_i |i⟩_C|i⟩_R` and the Schur-label projection on the `R` copies
(`07-comparators.tex`, lines 87–90 and 133–140), in the configuration coordinates of
`k` copies of `V`. -/
def prevector (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (d : ℕ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (k : ℕ) :
    EuclideanSpace ℂ (Config k (siteSpace β d)) :=
  WithLp.toLp 2 (replicaPrevector Ω d k (ell k) ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)

/-- The leaf factor `A_{j,g} = (W_P⁻¹ W_F⁻¹ W_Y)²` of `comparator:metrics` for one
partition `X, U, Y, V`, with `P = CXU` and `F = RV`, and the common-dimension Schur metrics
`W = W_{·,k}` at parameter `t` (`07-comparators.tex`, lines 91–106). -/
def bandMetric (d k : ℕ) (t : ℝ) (X U Y V : Finset ι) :
    Matrix (Config k (siteSpace β d)) (Config k (siteSpace β d)) ℂ :=
  let W := replicaMetric (siteSpace β d) t k
  ((W (insert (some none) ((X ∪ U).image fun x ↦ some (some x))))⁻¹ *
    (W (insert none (V.image fun x ↦ some (some x))))⁻¹ *
      W (Y.image fun x ↦ some (some x))) ^ 2

/-- The mean-tree root `𝓜` with leaves `A_j = ∏_g A_{j,g}` (`07-comparators.tex`,
lines 101–117). The operators act on the symmetric space `𝒮_k = Sym^k 𝒱` through the
isometric coordinates `Z`, whose range is the symmetric subspace. -/
def meanRoot {St : Type} {K : ℕ} (d k : ℕ) (t : ℝ) (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) {n : ℕ}
    (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ) (T : MeanTree St) :
    Matrix (Fin n) (Fin n) ℂ :=
  T.eval fun j ↦ Zᴴ * (List.ofFn fun g ↦ bandMetric β d k t X (U j g) (Y j g) (V j g)).prod * Z

open Classical in
/-- The band factorization of the mean-tree root: on the symmetric space the leaves
`A_j = ∏_g A_{j,g}` factor into commuting bands, so `𝓜 = ∏_g 𝓜_g`, where `𝓜_g` is the
root of the same tree with leaves `A_{j,g}` (`07-comparators.tex`, lines 114–117). The
far region and the middle region may be given in any spelling equal to `RV` and `Y`. -/
theorem meanRoot_eq_listProd [∀ v, Nonempty (β v)] {St : Type} {K : ℕ}
    {d k n : ℕ} [NeZero d] {t : ℝ} (ht : 0 ≤ t) (X : Finset ι)
    (U Y V : St → Fin K → Finset ι)
    (hdisj : ∀ j l, Disjoint (X ∪ U j l) (Y j l))
    (hV : ∀ j l, V j l = (X ∪ U j l ∪ Y j l)ᶜ)
    (hnest : ∀ j j' l l', l < l' → X ∪ U j l ∪ Y j l ⊆ X ∪ U j' l')
    (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k))
    (T : MeanTree St) (F Ymid : St → Fin K → Finset (Option (Option ι)))
    (hF : ∀ j l, F j l = insert none ((V j l).image fun x ↦ some (some x)))
    (hY : ∀ j l, Ymid j l = (Y j l).image fun x ↦ some (some x)) :
    let W := replicaMetric (siteSpace β d) t k
    let P := fun j l ↦ insert (some none) ((X ∪ U j l).image fun x ↦ some (some x))
    meanRoot β d k t X U Y V Z T =
      (List.ofFn fun l ↦ T.eval fun j ↦
        Zᴴ * ((W (P j l))⁻¹ * (W (F j l))⁻¹ * W (Ymid j l)) ^ 2 * Z).prod := by
  intro W P
  obtain ⟨hPE, hfar, hnestP⟩ :=
    replicaMetric_lifted_region_geometry K (fun j l ↦ X ∪ U j l) Y hdisj hnest
  have hFeq : ∀ j l, F j l = (P j l ∪ Ymid j l)ᶜ := fun j l ↦ by
    rw [hF, hV, hY]
    exact hfar j l
  have : ∀ o, Nonempty (siteSpace β d o) := fun
    | none => ⟨(0 : Fin d)⟩
    | some none => ⟨(0 : Fin d)⟩
    | some (some x) => ‹∀ v, Nonempty (β v)› x
  obtain ⟨hleaf, hcomm⟩ := replicaMetric_symProj_compressions_posDef_commute
    (siteSpace β d) k n Z hZ hZZ ht K P Ymid
    (fun j l ↦ by simpa only [hY] using hPE j l)
    (fun j j' l l' hll' ↦ by simpa only [hY] using hnestP j j' l l' hll')
  have hband : ∀ j l, bandMetric β d k t X (U j l) (Y j l) (V j l) =
      ((W (P j l))⁻¹ * (W (P j l ∪ Ymid j l)ᶜ)⁻¹ * W (Ymid j l)) ^ 2 := fun j l ↦ by
    rw [← hFeq j l, hF j l, hY j l]
    rfl
  have hcompress : ∀ j, Zᴴ * (List.ofFn fun l ↦ bandMetric β d k t X (U j l) (Y j l)
      (V j l)).prod * Z = (List.ofFn fun l ↦ Zᴴ * ((W (P j l))⁻¹ *
        (W (P j l ∪ Ymid j l)ᶜ)⁻¹ * W (Ymid j l)) ^ 2 * Z).prod := fun j ↦ by
    simp only [hband]
    exact conjTranspose_mul_listProd_ofFn_mul _ _ Z hZ fun l ↦ (hleaf j l).2.1
  simp only [meanRoot, hcompress, hFeq]
  exact MeanTree.eval_listProd_ofFn (fun j l ↦ (hleaf j l).1) hcomm T

open Classical in
/-- The common auxiliary labels of `comparator:prevector` (`07-comparators.tex`,
lines 130–142 and 240–281) for a finite product system: one label sequence, selected by
the normalized typical Schmidt vector, for which every `pre_k` with `k > 0` is nonzero,
symmetric and of norm at most one, has physical mean energy exactly `E₀`, and carries the
label `λ_k` on both auxiliary systems. The selected labels retain an inverse-polynomial
mass and the logarithmic dimension `k S' + o(k)`. -/
theorem exists_prevector_labels
    (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ)
    (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (E₀ : ℝ)
    (hΩ : ‖Ω‖ = 1) (hE : H *ᵥ Ω.ofLp = (E₀ : ℂ) • Ω.ofLp)
    (X : Finset ι) (E : Finset (FiniteProduct.Configuration β X))
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass
      E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let ξ := prevector β Ω E.card ell k
        ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 ∧
          symProj (copyPerm ((o : Option (Option ι)) → siteSpace β E.card o) k) *ᵥ ξ = ξ ∧
          globalReplicaMeanHamiltonian β (Fin E.card) (Fin E.card) H k *ᵥ ξ =
            (E₀ : ℂ) • ξ.ofLp ∧
          labelProj (subsystemPerm k (siteSpace β E.card) {some none}) (ell k) *ᵥ ξ = ξ ∧
          labelProj (subsystemPerm k (siteSpace β E.card) {none}) (ell k) *ᵥ ξ = ξ) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
              (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ ↦ (k : ℝ)) := by
  intro ΩX ψ
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodComm E (FiniteProduct.Configuration β Xᶜ)).trans
        ((Equiv.refl (FiniteProduct.Configuration β Xᶜ)).prodCongr
          (Finset.equivFin E)))).norm_map
      (compressedTypicalPureState ΩX E)).trans
      (norm_compressedTypicalPureState ΩX E hz)
  obtain ⟨ell, hpre, hmass, hdim⟩ :=
    exists_label_sequence_replicaPrevector Ω hΩ ψ hψ H E₀ hE
  refine ⟨ell, fun k hk ↦ ?_, hmass, hdim⟩
  intro ξ
  let d := E.card
  let eₖ := globalReplicaCopiesEquiv β (Fin d) (Fin d) k
  let u := replicaPrevector Ω d k (ell k)
  obtain ⟨hne, hnorm, henergy, hC, hR, hsym⟩ := hpre k hk
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eₖ.symm
  have hξ : ξ = U (WithLp.toLp 2 u) := rfl
  have hξne : ξ ≠ 0 := fun h ↦ hne
    (U.injective (((hξ.symm.trans h).trans U.map_zero.symm)))
  have hξnorm : ‖ξ‖ ≤ 1 :=
    (congrArg norm hξ).trans_le ((U.norm_map (WithLp.toLp 2 u)).trans_le hnorm)
  have htransport
      (K : Matrix ((Fin k → (v : ι) → β v) × ((Fin k → Fin d) × (Fin k → Fin d)))
        ((Fin k → (v : ι) → β v) × ((Fin k → Fin d) × (Fin k → Fin d))) ℂ)
      (c : ℂ) (hu : K *ᵥ u = c • u) :
      K.submatrix eₖ eₖ *ᵥ ξ = c • ξ.ofLp := by
    exact congrArg
      (fun v : EuclideanSpace ℂ (Config k (siteSpace β d)) ↦ v.ofLp)
      ((toEuclideanLin_reindex_piLpCongrLeft eₖ.symm K
        (WithLp.toLp 2 u)).trans
        ((congrArg U (show toEuclideanLin K (WithLp.toLp 2 u) =
            c • WithLp.toLp 2 u from WithLp.ofLp_injective 2 hu)).trans
          (U.map_smul c (WithLp.toLp 2 u))))
  have hjoint : symProj (replicaJointCopyPerm ((v : ι) → β v) (Fin d) (Fin d) k) *ᵥ u = u :=
    symProj_mulVec_of_mem _ fun σ ↦ by
      rw [permOp_replicaJointCopyPerm]
      exact hsym σ
  obtain ⟨hbridgeC, hbridgeR⟩ :=
    labelProj_globalReplicaCopiesEquiv_auxiliary β (Fin d) (Fin d) k (ell k) (ell k)
  refine ⟨hξne, hξnorm, ?_, htransport _ (E₀ : ℂ) henergy, ?_, ?_⟩
  · rw [← symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv
      β (Fin d) (Fin d) k]
    simpa only [one_smul] using
      htransport (symProj (replicaJointCopyPerm ((v : ι) → β v) (Fin d) (Fin d) k)) 1
        (by simpa only [one_smul] using hjoint)
  · rw [← hbridgeC]
    simpa only [one_smul] using htransport _ 1 (by simpa only [one_smul] using hC)
  · rw [← hbridgeR]
    simpa only [one_smul] using htransport _ 1 (by simpa only [one_smul] using hR)

open Classical in
/-- The selected entropy `S' = -∑_{i ∈ E} p'_i log p'_i`, `p'_i = p_i / z`, of
`comparator:typical-set` (`07-comparators.tex`, line 45) is the entropy of the auxiliary
marginal of the normalized typical Schmidt vector, whose labels are selected. -/
theorem vonNeumannEntropy_compressedTypicalPureState_eq_sum
    (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (X : Finset ι)
    (E : Finset (FiniteProduct.Configuration β X))
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass
      E) :
    let p := (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
        (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian =
      ∑ i ∈ E, Real.negMulLog (p i / ∑ j ∈ E, p j) := by
  intro p ΩX ψ
  refine (entropy_compressedTypicalPureState_equivFin_swap ΩX E hz).trans
    (((posSemidef_vecMulVec_self_star ΩX).partialTraceRight.entropy_normalizedSpectralRestriction
      E hz).trans ?_)
  rw [Entropy.probabilityEntropy]
  exact Finset.sum_coe_sort E fun i ↦ Real.negMulLog (p i / ∑ j ∈ E, p j)

/-- With only positive eigenvalues retained, `Tr ρ^{1-u}` is the moment of the surprisal
(`07-comparators.tex`, lines 77–83). -/
theorem surprisalMoment_eq_sum_rpow {n : Type*} [Fintype n] (p : n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (u : ℝ) :
    Entropy.surprisalMoment p u = ∑ i, if 0 < p i then p i ^ (1 - u) else 0 := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs with h
  · rw [Real.rpow_sub h, Real.rpow_one, Real.rpow_def_of_pos h, div_eq_mul_inv,
      ← Real.exp_neg]
    ring_nf
  · simp [le_antisymm (not_lt.mp h) (hp i)]

/-- **A typical Schmidt set** of `X` for `Ω`, `comparator:typical-set`
(`07-comparators.tex`, lines 37–45). The `p_i` are the eigenvalues of the reduced density
of `X`, that is, the squared Schmidt coefficients across `X`. -/
structure IsTypicalSchmidtSet (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (X : Finset ι)
    (E : Finset (FiniteProduct.Configuration β X)) (w : ℝ) : Prop where
  /-- `E` is a nonempty set of Schmidt indices of `X` (line 38). -/
  nonempty : E.Nonempty
  /-- Its indices are positive Schmidt indices, `p_i > 0` (line 38). -/
  pos : ∀ i ∈ E, 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues i
  /-- The width satisfies `w ≥ 0` (line 39). -/
  width_nonneg : 0 ≤ w
  /-- `e^{-S_X-w} ≤ p_i ≤ e^{-S_X+w}` for `i ∈ E`, with `S_X = S(X)` (lines 38–41). -/
  window : ∀ i ∈ E,
    Real.exp (-FiniteProduct.entropy β Ω X - w) ≤
        (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues i ∧
      (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues i ≤
        Real.exp (-FiniteProduct.entropy β Ω X + w)
  /-- The mass `z = ∑_{i ∈ E} p_i` is positive (line 42). -/
  mass_pos : 0 < ∑ i ∈ E, (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues i

/-- **A finite collection of status partitions** with target `X`
(`07-comparators.tex`, lines 19–31). A status `j` consists of `K` partitions
`H_phys = H_X ⊗ H_{U_{j,g}} ⊗ H_{Y_{j,g}} ⊗ H_{V_{j,g}}`. -/
structure IsStatusFamily {St : Type} {K : ℕ} (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) : Prop where
  /-- The four factors are disjoint: `X` and `U_{j,g}` (lines 22–23). -/
  disjoint_XU : ∀ j g, Disjoint X (U j g)
  /-- `X` and `Y_{j,g}` are disjoint (lines 22–23). -/
  disjoint_XY : ∀ j g, Disjoint X (Y j g)
  /-- `X` and `V_{j,g}` are disjoint (lines 22–23). -/
  disjoint_XV : ∀ j g, Disjoint X (V j g)
  /-- `U_{j,g}` and `Y_{j,g}` are disjoint (lines 22–23). -/
  disjoint_UY : ∀ j g, Disjoint (U j g) (Y j g)
  /-- `U_{j,g}` and `V_{j,g}` are disjoint (lines 22–23). -/
  disjoint_UV : ∀ j g, Disjoint (U j g) (V j g)
  /-- `Y_{j,g}` and `V_{j,g}` are disjoint (lines 22–23). -/
  disjoint_YV : ∀ j g, Disjoint (Y j g) (V j g)
  /-- The four factors cover all physical sites (lines 22–23). -/
  cover : ∀ j g, X ∪ U j g ∪ Y j g ∪ V j g = Finset.univ
  /-- `comparator:nesting`: for every two allowed statuses and every `g < g'`,
  `XU_gY_g ⊆ XU_{g'}` as sets of physical sites (lines 26–31). -/
  nesting : ∀ j j' g g', g < g' → X ∪ U j g ∪ Y j g ⊆ X ∪ U j' g'

/-- **The prefix data** of the rough upper bound, `comparator:prefix-data`
(`07-comparators.tex`, lines 56–68). -/
structure IsPrefixData (Ω : EuclideanSpace ℂ ((v : ι) → β v)) {St : Type} {K : ℕ}
    (X : Finset ι) (U Y : St → Fin K → Finset ι) (R : Finset (Finset ι))
    (Bsh Bexc : ℝ) : Prop where
  /-- `𝓡` is a nested collection: any two members are comparable (lines 56–57). -/
  nested : ∀ B ∈ R, ∀ B' ∈ R, B ⊆ B' ∨ B' ⊆ B
  /-- Every member of `𝓡` is disjoint from `X` (line 57). -/
  disjoint : ∀ B ∈ R, Disjoint X B
  /-- `S(B) ≤ B_sh` for `B ∈ 𝓡` (line 61). -/
  entropy_le : ∀ B ∈ R, FiniteProduct.entropy β Ω B ≤ Bsh
  /-- For every status and band, each of `Q = U_g` and `Q = U_gY_g` has a matched member
  `B` of `𝓡` containing it or contained in it, with
  `1 + log dim H_{B △ Q} ≤ B_exc` (lines 57–65). -/
  matched : ∀ j g (Q : Finset ι), Q = U j g ∨ Q = U j g ∪ Y j g →
    ∃ B ∈ R, (B ⊆ Q ∨ Q ⊆ B) ∧
      1 + Real.log (Fintype.card (FiniteProduct.Configuration β (B ∆ Q))) ≤ Bexc

/-- **The marginal moment assumption** of the sharp bounds, `comparator:mgf-data`
(`07-comparators.tex`, lines 70–85): for every `Q ∈ {XU_g, V_g, Y_g, U_g, U_gY_g}` the
marginal `ρ_Q` of `Ω` satisfies `log Tr ρ_Q^{1-u} ≤ u S(Q) + C₀ 𝓑 u²` for
`|u| ≤ c₀ / √𝓑`, with only positive eigenvalues in the trace. -/
structure IsMarginalMomentData (Ω : EuclideanSpace ℂ ((v : ι) → β v)) {St : Type} {K : ℕ}
    (X : Finset ι) (U Y V : St → Fin K → Finset ι) (C₀ c₀ B : ℝ) : Prop where
  /-- `𝓑 ≥ 1` (line 76). -/
  one_le : 1 ≤ B
  /-- The moment bound for the five marginals of every status and band (lines 71–83). -/
  moment : ∀ j g (Q : Finset ι),
    Q = X ∪ U j g ∨ Q = V j g ∨ Q = Y j g ∨ Q = U j g ∨ Q = U j g ∪ Y j g →
    ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
      Real.log (∑ i, if 0 < (FiniteProduct.reducedPure_posSemidef β Ω Q).isHermitian.eigenvalues i
          then (FiniteProduct.reducedPure_posSemidef β Ω Q).isHermitian.eigenvalues i ^ (1 - u)
          else 0) ≤
        u * FiniteProduct.entropy β Ω Q + C₀ * B * u ^ 2

namespace IsStatusFamily

variable {β} {St : Type} {K : ℕ} {X : Finset ι} {U Y V : St → Fin K → Finset ι}

theorem far_eq_compl (h : IsStatusFamily X U Y V) (j : St) (l : Fin K) :
    V j l = (X ∪ U j l ∪ Y j l)ᶜ := by
  ext x
  simp only [Finset.mem_compl, Finset.mem_union]
  constructor
  · rintro hx ((hX | hU) | hY)
    · exact Finset.disjoint_left.mp (h.disjoint_XV j l) hX hx
    · exact Finset.disjoint_left.mp (h.disjoint_UV j l) hU hx
    · exact Finset.disjoint_left.mp (h.disjoint_YV j l) hY hx
  · intro hx
    have hmem : x ∈ X ∪ U j l ∪ Y j l ∪ V j l := (h.cover j l).symm ▸ Finset.mem_univ x
    simp only [Finset.mem_union] at hmem
    tauto

theorem disjoint_inner_middle (h : IsStatusFamily X U Y V) (j : St) (l : Fin K) :
    Disjoint (X ∪ U j l) (Y j l) :=
  Finset.disjoint_union_left.mpr ⟨h.disjoint_XY j l, h.disjoint_UY j l⟩

theorem union_subset_later (h : IsStatusFamily X U Y V) (j j' : St) (l l' : Fin K) (hll : l < l') :
    U j l ∪ Y j l ⊆ U j' l' := by
  intro x hx
  have hxX : x ∉ X := fun hX ↦ by
    rcases Finset.mem_union.mp hx with hU | hY
    · exact Finset.disjoint_left.mp (h.disjoint_XU j l) hX hU
    · exact Finset.disjoint_left.mp (h.disjoint_XY j l) hX hY
  have := h.nesting j j' l l' hll (by
    rw [Finset.union_assoc]; exact Finset.mem_union_right _ hx)
  rcases Finset.mem_union.mp this with hX | hU
  · exact absurd hX hxX
  · exact hU

end IsStatusFamily

/-- The scalar step of the rough lower comparison: the explicit finite-copy estimate gives
the source form with coefficient four. -/
theorem rough_lower_scalar (K a k S L h δ τ r Nlog : ℝ) (hK : 0 ≤ K) (ha : 0 < a)
    (ha1 : a ≤ 1) (hk : 0 < k) (hS : 0 ≤ S) (hL : 0 ≤ L) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hτ : 0 < τ)
    (hbound : 2 * (1 / 4) * K * (2 * (a / 2) * k *
      ((2 * S - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h) - δ / τ * max 0 (2 * S)) - r) ≤
        Nlog) :
    2 * (1 / 4) * (a * K) * (2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S) -
        (K / 2 * r) / k ≤ Nlog / k := by
  rw [max_eq_right (by linarith), show 1 / (2 * (a / 2)) = 1 / a by ring] at hbound
  rw [le_div_iff₀ hk]
  have hha : h ≤ h / a := le_div_self hh ha ha1
  have hcore : 2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S ≤
      2 * S - τ * (L + L) - (3 + 1 / a) * h - δ / τ * (2 * S) := by
    have hδS : 0 ≤ δ / τ * S := mul_nonneg (div_nonneg hδ hτ.le) hS
    have : (3 + 1 / a) * h = 3 * h + h / a := by ring
    nlinarith [mul_nonneg hτ.le hL]
  have hcoef : 0 ≤ 2 * (1 / 4) * (a * K) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcore hcoef
  have hexpand : (2 * (1 / 4) * (a * K) * (2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S) -
      K / 2 * r / k) * k = 2 * (1 / 4) * (a * K) *
        (2 * S - 4 * (τ * L + h / a) - 4 * (δ / τ) * S) * k - K / 2 * r := by
    field_simp
  rw [hexpand]
  have : 2 * (1 / 4) * K * (2 * (a / 2) * k *
      ((2 * S - τ * (L + L) - (3 + 1 / a) * h) - δ / τ * (2 * S)) - r) =
      2 * (1 / 4) * (a * K) * (2 * S - τ * (L + L) - (3 + 1 / a) * h - δ / τ * (2 * S)) * k -
        K / 2 * r := by ring
  nlinarith [mul_le_mul_of_nonneg_right hmul hk.le]

/-- The moment assumption in the form of the surprisal moment. -/
theorem IsMarginalMomentData.surprisalMoment_le {Ω : EuclideanSpace ℂ ((v : ι) → β v)}
    {St : Type} {K : ℕ} {X : Finset ι} {U Y V : St → Fin K → Finset ι} {C₀ c₀ B : ℝ}
    (h : IsMarginalMomentData β Ω X U Y V C₀ c₀ B) (j : St) (l : Fin K) (Q : Finset ι)
    (hQ : Q = X ∪ U j l ∨ Q = V j l ∨ Q = Y j l ∨ Q = U j l ∨ Q = U j l ∪ Y j l)
    (u : ℝ) (hu : |u| ≤ c₀ / Real.sqrt B) :
    Real.log (Entropy.surprisalMoment
      (FiniteProduct.reducedPure_posSemidef β Ω Q).isHermitian.eigenvalues u) ≤
        u * FiniteProduct.entropy β Ω Q + C₀ * B * u ^ 2 := by
  rw [surprisalMoment_eq_sum_rpow _ (FiniteProduct.reducedPure_posSemidef β Ω Q).eigenvalues_nonneg]
  exact h.moment j l Q hQ u hu

/-- A band-and-tree average times the total weight is the weight times the weighted sum. -/
theorem mul_avg_eq {St : Type} [Fintype St] [DecidableEq St] {K : ℕ} (a : ℝ)
    (T : MeanTree St) (f : St → Fin K → ℝ) :
    a * K * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * f j l) = a * ∑ l, ∑ j, T.weight j * f j l := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · field_simp

/-- The scalar step of the sharp lower comparison: the explicit finite-copy estimate gives the
source form with a constant `C' ≥ 4` that also dominates the moment coefficient. -/
theorem sharp_lower_scalar {K : ℕ} (a k S L τ h δ gm C₀ B C' r Nlog : ℝ) (A : Fin K → ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hk : 0 < k) (hS : 0 ≤ S) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hgm : 0 ≤ gm) (hB : 0 ≤ B) (hC'4 : 4 ≤ C')
    (hC'0 : 25 * C₀ ≤ C')
    (hbound : 2 * (1 / 4) * ∑ l, (2 * (a / 2) * k *
      ((2 * S + (1 - τ) * A l - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h -
        50 * (C₀ * B) * (a / 2)) - δ / τ * max 0 (2 * S + gm)) - r) ≤ Nlog) :
    2 * (1 / 4) * (a * K) * (2 * S + (1 - τ) * ((1 / (K : ℝ)) * ∑ l, A l) -
        C' * (τ * L + h / a + a * B) - C' * (δ / τ) * (S + gm)) - (K / 2 * r) / k ≤
      Nlog / k := by
  set P := 2 * (a / 2) * k with hP
  set X0 := 2 * S - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h - 50 * (C₀ * B) * (a / 2)
    with hX0
  set D0 := δ / τ * max 0 (2 * S + gm) with hD0
  have hsum : ∑ l, (P * ((2 * S + (1 - τ) * A l - τ * (L + L) - (3 + 1 / (2 * (a / 2))) * h -
        50 * (C₀ * B) * (a / 2)) - D0) - r) =
      K * (P * (X0 - D0) - r) + P * (1 - τ) * ∑ l, A l := by
    calc _ = ∑ l, ((P * (X0 - D0) - r) + P * (1 - τ) * A l) :=
          Finset.sum_congr rfl fun l _ ↦ by rw [hX0]; ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum] at hbound
  have havg : a * K * ((1 / (K : ℝ)) * ∑ l, A l) = a * ∑ l, A l := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · field_simp
  have hha : h ≤ h / a := le_div_self hh ha ha1
  have hcore : 2 * S - C' * (τ * L + h / a + a * B) - C' * (δ / τ) * (S + gm) ≤ X0 - D0 := by
    rw [hX0, hD0, max_eq_right (by linarith), show 1 / (2 * (a / 2)) = 1 / a by ring]
    have hδτ : 0 ≤ δ / τ := div_nonneg hδ hτ.le
    have h1 : δ / τ * (2 * S + gm) ≤ C' * (δ / τ) * (S + gm) := by
      have h0 : 2 * S + gm ≤ C' * (S + gm) := by nlinarith
      calc δ / τ * (2 * S + gm) ≤ δ / τ * (C' * (S + gm)) :=
            mul_le_mul_of_nonneg_left h0 hδτ
        _ = C' * (δ / τ) * (S + gm) := by ring
    have h2 : τ * (L + L) ≤ C' * (τ * L) := by nlinarith [mul_nonneg hτ.le hL]
    have h3 : (3 + 1 / a) * h ≤ C' * (h / a) := by
      have : (3 + 1 / a) * h = 3 * h + h / a := by ring
      nlinarith [div_nonneg hh ha.le]
    have h4 : 50 * (C₀ * B) * (a / 2) ≤ C' * (a * B) := by nlinarith [mul_nonneg ha.le hB]
    nlinarith
  rw [le_div_iff₀ hk]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hcoef : 0 ≤ 2 * (1 / 4) * (a * K) * k := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcore hcoef
  have hexpand : (2 * (1 / 4) * (a * K) * (2 * S + (1 - τ) * ((1 / (K : ℝ)) * ∑ l, A l) -
      C' * (τ * L + h / a + a * B) - C' * (δ / τ) * (S + gm)) - K / 2 * r / k) * k =
      2 * (1 / 4) * (a * K) * k * (2 * S - C' * (τ * L + h / a + a * B) -
        C' * (δ / τ) * (S + gm)) + 2 * (1 / 4) * (1 - τ) * k * (a * K * ((1 / (K : ℝ)) *
          ∑ l, A l)) - K / 2 * r := by
    rw [sub_mul, div_mul_cancel₀ _ hk.ne']
    ring
  rw [hexpand, havg]
  have hb : 2 * (1 / 4) * (K * (P * (X0 - D0) - r) + P * (1 - τ) * ∑ l, A l) =
      2 * (1 / 4) * (a * K) * k * (X0 - D0) + 2 * (1 / 4) * (1 - τ) * k * (a * ∑ l, A l) -
        K / 2 * r := by
    rw [hP]; ring
  linarith [hmul, hb, hbound]

end TNLean.PEPS.AreaLaw.Scan.Comparators
