/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.GappedGroundState
import TNLean.Algebra.MatrixReindexGap
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLowerRemainder
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

/-!
# Upper and lower norm comparisons from an auxiliary pair

The norm comparisons of Proposition 8.1 for a finite product system. A unit ground
vector of a positive gapped Hamiltonian, a physical target `X` and a typical Schmidt
set of `X` determine one sequence of common auxiliary labels. The projected vectors
`pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k}` are nonzero, symmetric, of norm at most one,
exact mean-energy eigenvectors, and carry the same label on both auxiliary systems.
For every finite collection of nested status partitions, every weight `0 < a ≤ a₀`
and every mean tree, the inverse-power norm of the band product satisfies the rough
and sharp upper and lower comparisons, with remainders uniform in the tree, its
terminal probabilities and the symmetric coordinates. The entropy identity and the
nonnegativity of the pre-comparison entropy expression hold exactly.

The rough upper bound uses the nested prefix data; the rough lower bound uses neither
the prefix data nor the marginal moment data; both sharp bounds use the marginal moment
data and `a ≤ c / √𝓑`, and the sharp upper bound uses no prefix data. The rough
constant is universal, the sharp constant depends only on `C₀`, and the threshold `c`
depends only on `c₀`. The lower comparisons hold for every symmetric vector of norm at
most one carrying the common label on both auxiliary systems, in particular for
`pre_k`, with one remainder for all of them.

The physical sites carry arbitrary finite local spaces. The proof assembles the
general comparisons of QICLean for the actual band product; the band factorization of
the mean-tree root is the commuting-band factorization of the leaves.

## Main definitions

* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsTypicalSchmidtSet`: `comparator:typical-set`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsStatusFamily`: status partitions obeying
  `comparator:nesting`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsPrefixData`: `comparator:prefix-data`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.IsMarginalMomentData`: `comparator:mgf-data`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.prevector`: the vector `pre_k`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.bandMetric`: the leaf factor `A_{j,g}`.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.meanRoot`: the mean-tree root `𝓜` with
  leaves `A_j = ∏_g A_{j,g}` on the symmetric space.
* `TNLean.PEPS.AreaLaw.Scan.Comparators.ComparatorsStatement`: Proposition 8.1.
* `Matrix.MeanTree.labels`, `Matrix.MeanTree.restrict`: the leaf labels of a mean tree and
  the same tree read on them, over which `g_max` is taken.

## Main result

* `TNLean.PEPS.AreaLaw.Scan.Comparators.comparatorsStatement`: Proposition 8.1 holds.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 125–214, with the
standing data of lines 13–123. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are written from the
manuscript; no Lean declaration of the accompanying development is reused.
-/

noncomputable section

open Filter Topology Matrix TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  symmDiff

namespace Matrix.MeanTree

variable {ι : Type*} [DecidableEq ι]

/-- The labels occurring at the leaves of a mean tree. -/
def labels : MeanTree ι → Finset ι
  | leaf j => {j}
  | node _ l r => l.labels ∪ r.labels

theorem labels_nonempty : (T : MeanTree ι) → T.labels.Nonempty
  | leaf j => Finset.singleton_nonempty j
  | node _ l _ => (labels_nonempty l).mono Finset.subset_union_left

/-- The same tree with its leaf labels read in a finite set containing all of them. -/
def restrict (s : Finset ι) : (T : MeanTree ι) → T.labels ⊆ s → MeanTree s
  | leaf j, h => leaf ⟨j, h (Finset.mem_singleton_self j)⟩
  | node p l r, h => node p (l.restrict s (Finset.subset_union_left.trans h))
      (r.restrict s (Finset.subset_union_right.trans h))

theorem eval_restrict {n : Type*} [Fintype n] [DecidableEq n] (A : ι → Matrix n n ℂ)
    (s : Finset ι) : (T : MeanTree ι) → (h : T.labels ⊆ s) →
    (T.restrict s h).eval (fun j ↦ A j.val) = T.eval A
  | leaf _, _ => rfl
  | node p l r, h => by
    simp only [restrict, eval_node, eval_restrict A s l, eval_restrict A s r]

theorem weight_restrict (s : Finset ι) : (T : MeanTree ι) → (h : T.labels ⊆ s) →
    ∀ j : s, (T.restrict s h).weight j = T.weight j.val
  | leaf j, h, i => by
    by_cases hij : i.val = j
    · have hi : i = ⟨j, h (Finset.mem_singleton_self j)⟩ := Subtype.ext hij
      subst hi
      simp [restrict]
    · have hi : i ≠ ⟨j, h (Finset.mem_singleton_self j)⟩ := fun hi ↦ hij (by simp [hi])
      simp [restrict, hi, hij]
  | node p l r, h, i => by
    simp only [restrict, weight_node, weight_restrict s l, weight_restrict s r]

theorem weight_eq_zero_of_notMem : (T : MeanTree ι) → ∀ j, j ∉ T.labels → T.weight j = 0
  | leaf i, j, hj => by
    have : j ≠ i := fun h ↦ hj (by simp [labels, h])
    simp [this]
  | node p l r, j, hj => by
    simp only [labels, Finset.mem_union, not_or] at hj
    rw [weight_node, weight_eq_zero_of_notMem l j hj.1, weight_eq_zero_of_notMem r j hj.2]
    ring

/-- A weighted sum over the leaf labels of a restricted tree is the weighted sum over all
labels. -/
theorem sum_weight_restrict_mul [Fintype ι] (T : MeanTree ι) (f : ι → ℝ) :
    ∑ j : T.labels, (T.restrict T.labels subset_rfl).weight j * f j.val =
      ∑ j, T.weight j * f j := by
  simp only [weight_restrict]
  rw [Finset.sum_coe_sort T.labels (fun j ↦ T.weight j * f j)]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ by
    rw [weight_eq_zero_of_notMem T j hj, zero_mul]

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

open Classical in
/-- The rough lower comparison `comparator:rough-lower` (`07-comparators.tex`,
lines 162–169 and 585–651) for the band product of a status family, with coefficient four
and one remainder for every tree, isometric coordinates and symmetric vector of norm at
most one carrying the label `λ_k` on both auxiliary systems. Neither prefix nor moment
data are used. -/
theorem exists_rough_lower [∀ v, Nonempty (β v)]
    (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ) (Ω : EuclideanSpace ℂ ((v : ι) → β v))
    (E₀ gap : ℝ) (hgap : (H - (E₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ω.ofLp (star Ω.ofLp))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hgap_pos : 0 < gap) {d : ℕ} [NeZero d]
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (hSent : 0 ≤ Sent)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent) (fun k : ℕ ↦ (k : ℝ)))
    {St : Type} [Finite St] {K : ℕ} (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
      ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ (T : MeanTree St) (ξ : EuclideanSpace ℂ (Config k (siteSpace β d))),
        ξ ≠ 0 → ‖ξ‖ ≤ 1 →
        symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {some none}) (ell k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {none}) (ell k) *ᵥ ξ = ξ →
        let w := toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ ξ)
        let N := ‖w‖
        let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
        let Edef := ((star v ⬝ᵥ
          (globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k *ᵥ v)).re - E₀) / gap
        0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
          2 * (1 / 4) * (a * K) * (2 * Sent - 4 * (τ * Real.log d + Real.binEntropy τ / a) -
              4 * (Edef / τ) * Sent) -
            ρ k ≤ -Real.log (N ^ 2) / k := by
  classical
  have := Fintype.ofFinite St
  obtain ⟨c, Cf, hc, hCf, hlow⟩ :=
    exists_replicaMetric_symProj_bandProduct_rough_lower_norm β (Fin d) (Fin d)
      (t := a / 2) (by positivity) (by linarith)
  refine ⟨Scan.roughLowerRemainderAtWeight K a c Cf ell Sent,
    Scan.tendsto_roughLowerRemainderAtWeight_of_label_dimension ell Sent hdim K a c Cf, ?_⟩
  intro k hk n Z hZ hZZ T ξ hξ hξn hsym hC hR
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ U j l ∪ Y j l)ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l]) (fun _ _ ↦ rfl)
  rw [hroot]
  intro w N v Edef
  have hΩ' : ‖WithLp.toLp 2 Ω.ofLp‖ = 1 := by simpa using hΩ
  obtain ⟨hw, -, hδ, hτb⟩ := hlow k n hk H Ω.ofLp E₀ gap hgap hΩ' hgap_pos Z hZ hZZ St K
    (fun j l ↦ X ∪ U j l) Y hfam.disjoint_inner_middle hfam.nesting T (ell k) (ell k) Sent
    (Scan.roughLowerLabelDefect ell Sent k) (1 / 4)
    (Scan.roughLowerLabelDefect_label_bound ell Sent k).2 (by norm_num)
    ξ hξ hξn hsym hC hR
  refine ⟨norm_pos_iff.mpr hw, fun τ hτ hτ1 ↦ ?_⟩
  have h1 := hτb τ hτ hτ1.le
  simp only [Fintype.card_fin] at h1
  have hb : |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| =
      Cf * Real.log ((k : ℝ) + 2) + Real.log 2 := by
    have hlog : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_rpow (by positivity),
      abs_of_nonpos (by nlinarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)])]
    ring
  rw [hb] at h1
  have hrem : Scan.roughLowerRemainderAtWeight K a c Cf ell Sent k =
      (K / 2 * (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * (a / 2) * Scan.roughLowerLabelDefect ell Sent k| +
        (Cf * Real.log ((k : ℝ) + 2) + Real.log 2) + Real.log 2 + Real.log (3 / 2))) / k := by
    rw [Scan.roughLowerRemainderAtWeight, show 2 * (a / 2) = a by ring]
    ring
  rw [hrem]
  exact rough_lower_scalar K a k Sent (Real.log d) (Real.binEntropy τ) Edef τ _ _
    (Nat.cast_nonneg K) ha (by linarith) (Nat.cast_pos.mpr hk) hSent
    (Real.log_natCast_nonneg d) (Real.binEntropy_nonneg hτ.le (by linarith)) hδ hτ h1

open Classical in
/-- The rough upper comparison `comparator:rough-upper` (`07-comparators.tex`,
lines 154–161 and 332–381) for `pre_k` under the prefix data, with a remainder uniform in the
tree and the isometric coordinates. -/
theorem exists_rough_upper (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (hΩ : ‖Ω‖ = 1)
    [∀ v, Nonempty (β v)] (X : Finset ι) (E : Finset (FiniteProduct.Configuration β X))
    [NeZero E.card]
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass
      E)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hmass :
      let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
      let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
        compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
      ∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
              (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2)
    {St : Type} [Finite St] {K : ℕ}
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (a : ℝ) (ha : 0 < a) (R : Finset (Finset ι)) (Bsh Bexc : ℝ)
    (hpre : IsPrefixData β Ω X U Y R Bsh Bexc) :
    let d := E.card
    let z := ∑ i ∈ E, (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues i
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ T : MeanTree St,
        let N := ‖toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
        0 < N ∧ -Real.log (N ^ 2) / k ≤
          2 * Real.log d - Real.log z + 2 * (1 / 4) * (a * K) * (2 * Bsh / z + 2 * Bexc) +
            ρ k := by
  intro d z
  have hu := FiniteProduct.eventually_suppliedReplicaPrevector_rough_upper (S := St) β Ω X E
    hΩ hz R.toList
    (List.pairwise_of_forall_mem_list fun B hB B' hB' ↦
      hpre.nested B (Finset.mem_toList.mp hB) B' (Finset.mem_toList.mp hB'))
    (fun B hB ↦ hpre.disjoint B (Finset.mem_toList.mp hB)) ell (t := a / 2) (half_pos ha)
    (hmass.mono fun k hk ↦ by
      simpa only [Nat.cast_pow, one_div,
        TensorPower.norm_sq_labelProj_compressedTypicalSite_prod β X k Ω E (ell k)] using! hk)
  obtain ⟨c, hc, hu⟩ := hu
  refine ⟨Real.bellOverlapRemainder d c K, Real.tendsto_bellOverlapRemainder d c K,
    hu.mono fun k hk n Z hZ hZZ T ↦ ?_⟩
  have hY : ∀ j l, Y j l \ X = Y j l := fun j l ↦
    Finset.sdiff_eq_self_of_disjoint (hfam.disjoint_XY j l).symm
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l \ X).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l, Finset.union_assoc]) (fun j l ↦ by rw [hY j l])
  intro N
  obtain ⟨hpos, hle⟩ := hk n Z hZ hZZ K U Y hfam.disjoint_UY hfam.union_subset_later
    (fun j l ↦ Finset.disjoint_union_right.mpr ⟨hfam.disjoint_XU j l, hfam.disjoint_XY j l⟩)
    T Bsh Bexc (fun B hB ↦ hpre.entropy_le B (Finset.mem_toList.mp hB))
    (fun j l Q hQ ↦ by
      obtain ⟨B, hB, hBQ⟩ := hpre.matched j l Q hQ
      exact ⟨B, Finset.mem_toList.mpr hB, hBQ⟩)
    (1 / 4) (by norm_num)
  have hN : N ^ 2 = ‖toEuclideanLin ((List.ofFn fun l ↦ T.eval fun j ↦ Zᴴ *
      ((replicaMetric (siteSpace β d) (a / 2) k
        (insert (some none) ((X ∪ U j l).image fun x ↦ some (some x))))⁻¹ *
        (replicaMetric (siteSpace β d) (a / 2) k
          (insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x))))⁻¹ *
        replicaMetric (siteSpace β d) (a / 2) k ((Y j l \ X).image fun x ↦ some (some x))) ^ 2 *
        Z).prod ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖ ^ 2 := by
    simp only [N, hroot]
  refine ⟨?_, ?_⟩
  · have hsq : 0 < N ^ 2 := hN ▸ hpos
    have hN0 : 0 ≤ N := norm_nonneg _
    exact lt_of_le_of_ne hN0 fun h ↦ by rw [← h] at hsq; simp at hsq
  · rw [hN]
    have hcoef : 8 * (1 / 4 : ℝ) * (a / 2) * (K : ℝ) * (Bsh / z + Bexc) =
        2 * (1 / 4) * (a * K) * (2 * Bsh / z + 2 * Bexc) := by ring
    rw [← hcoef]
    exact hle

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

open Classical in
/-- The sharp upper comparison `comparator:sharp-upper` (`07-comparators.tex`,
lines 171–188 and 383–418) for `pre_k` under the moment data, without prefix data, with a
remainder uniform in the tree and the isometric coordinates. -/
theorem exists_sharp_upper (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (hΩ : ‖Ω‖ = 1)
    [∀ v, Nonempty (β v)] (X : Finset ι) (E : Finset (FiniteProduct.Configuration β X))
    [NeZero E.card]
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass
      E)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hmass :
      let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
      let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
        compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
      ∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
              (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2)
    {St : Type} [Fintype St] [DecidableEq St] {K : ℕ}
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (C₀ c₀ B C' : ℝ) (hC' : 12 * C₀ ≤ C') (hC'1 : 1 ≤ C')
    (hmom : IsMarginalMomentData β Ω X U Y V C₀ c₀ B)
    (a : ℝ) (ha : 0 < a) (har : 6 * a ≤ c₀ / Real.sqrt B) (ha1 : 6 * a ≤ 1) :
    let d := E.card
    let z := ∑ i ∈ E, (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues i
    let S := FiniteProduct.entropy β Ω
    let gpost := fun j l ↦ S (U j l) + S (U j l ∪ Y j l) - S (Y j l)
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ T : MeanTree St,
        let N := ‖toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
        0 < N ∧ -Real.log (N ^ 2) / k ≤
          2 * Real.log d - Real.log z +
            2 * (1 / 4) * (a * K) * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpost j l +
              C' * (a * B + |Real.log z| / a)) + ρ k := by
  intro d z S gpost
  obtain ⟨c, hc, hlim, hu⟩ := FiniteProduct.eventually_suppliedReplicaPrevector_sharp_upper β Ω X E
    hΩ hz (K := C₀ * B) (r := c₀ / Real.sqrt B) ha har ha1 ell hmass
  refine ⟨Real.bellOverlapRemainder d c K, hlim K, hu.mono fun k hk n Z hZ hZZ T ↦ ?_⟩
  have hY : ∀ j l, Y j l \ X = Y j l := fun j l ↦
    Finset.sdiff_eq_self_of_disjoint (hfam.disjoint_XY j l).symm
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l \ X).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l, Finset.union_assoc]) (fun j l ↦ by rw [hY j l])
  intro N
  obtain ⟨hpos, hle⟩ := hk n Z hZ hZZ K U Y hfam.disjoint_XU hfam.disjoint_XY
    hfam.disjoint_UY hfam.union_subset_later
    (fun j l Q hQ u hu ↦ hmom.surprisalMoment_le β j l Q (by tauto) u hu)
    T (1 / 4) (by norm_num)
  have hN : N ^ 2 = ‖toEuclideanLin ((List.ofFn fun l ↦ T.eval fun j ↦ Zᴴ *
      ((replicaMetric (siteSpace β d) (a / 2) k
        (insert (some none) ((X ∪ U j l).image fun x ↦ some (some x))))⁻¹ *
        (replicaMetric (siteSpace β d) (a / 2) k
          (insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x))))⁻¹ *
        replicaMetric (siteSpace β d) (a / 2) k ((Y j l \ X).image fun x ↦ some (some x))) ^ 2 *
        Z).prod ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖ ^ 2 := by
    simp only [N, hroot]
  refine ⟨?_, ?_⟩
  · have hsq : 0 < N ^ 2 := hN ▸ hpos
    have hN0 : 0 ≤ N := norm_nonneg _
    exact lt_of_le_of_ne hN0 fun h ↦ by rw [← h] at hsq; simp at hsq
  · rw [hN]
    refine le_trans (b := 2 * Real.log d - Real.log z +
      2 * (1 / 4) * a * (∑ l, ∑ j, T.weight j * gpost j l) +
        24 * (1 / 4) * K * (C₀ * B) * a ^ 2 - 2 * (1 / 4) * K * Real.log z +
          Real.bellOverlapRemainder d c K k) hle ?_
    have havg := mul_avg_eq a T gpost
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hB0 : 0 ≤ B := zero_le_one.trans hmom.one_le
    have h1 : 24 * (1 / 4 : ℝ) * K * (C₀ * B) * a ^ 2 ≤
        2 * (1 / 4) * (a * K) * (C' * (a * B)) := by
      have : 0 ≤ (K : ℝ) * B * a ^ 2 := by positivity
      nlinarith
    have h2 : -(2 * (1 / 4 : ℝ) * K * Real.log z) ≤
        2 * (1 / 4) * (a * K) * (C' * (|Real.log z| / a)) := by
      have heq : 2 * (1 / 4) * (a * K) * (C' * (|Real.log z| / a)) =
          (1 / 2) * K * (C' * |Real.log z|) := by field_simp; ring
      rw [heq]
      have h3 := mul_nonneg (mul_nonneg hK0 (abs_nonneg (Real.log z))) (sub_nonneg.mpr hC'1)
      have h4 := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log z)) hK0
      nlinarith
    have hsplit : 2 * (1 / 4) * (a * K) * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpost j l +
        C' * (a * B + |Real.log z| / a)) = 2 * (1 / 4) * a * (∑ l, ∑ j, T.weight j * gpost j l) +
          2 * (1 / 4) * (a * K) * (C' * (a * B)) +
          2 * (1 / 4) * (a * K) * (C' * (|Real.log z| / a)) := by
      have : 2 * (1 / 4) * (a * K) * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpost j l) =
          2 * (1 / 4) * a * (∑ l, ∑ j, T.weight j * gpost j l) := by
        rw [mul_assoc (2 * (1 / 4 : ℝ)), havg]
        ring
      rw [mul_add, this, mul_add]
      ring
    rw [hsplit]
    linarith

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

open Classical in
/-- The sharp lower comparison `comparator:sharp-lower` (`07-comparators.tex`,
lines 171–196 and 550–651) under the moment data, with one remainder for every tree,
isometric coordinates and symmetric vector of norm at most one carrying the label `λ_k` on
both auxiliary systems. The maximum `g_max` runs over the leaf labels of the tree. -/
theorem exists_sharp_lower [∀ v, Nonempty (β v)]
    (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ) (Ω : EuclideanSpace ℂ ((v : ι) → β v))
    (E₀ gap : ℝ) (hgap : (H - (E₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ω.ofLp (star Ω.ofLp))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hgap_pos : 0 < gap) {d : ℕ} [NeZero d]
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (hSent : 0 ≤ Sent)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent) (fun k : ℕ ↦ (k : ℝ)))
    {St : Type} [Fintype St] [DecidableEq St] {K : ℕ} (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (C₀ c₀ B C' : ℝ) (hC₀ : 0 ≤ C₀) (hC'4 : 4 ≤ C') (hC'0 : 25 * C₀ ≤ C')
    (hmom : IsMarginalMomentData β Ω X U Y V C₀ c₀ B)
    (a : ℝ) (ha : 0 < a) (har : 10 * a ≤ c₀ / Real.sqrt B) (ha1 : 10 * a ≤ 1) :
    let S := FiniteProduct.entropy β Ω
    let gpre := fun j l ↦ S (X ∪ U j l) + S (V j l) - S (Y j l)
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
      ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ (T : MeanTree St) (ξ : EuclideanSpace ℂ (Config k (siteSpace β d))),
        ξ ≠ 0 → ‖ξ‖ ≤ 1 →
        symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {some none}) (ell k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {none}) (ell k) *ᵥ ξ = ξ →
        let gmax := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels × Fin K)).image
          fun x ↦ gpre x.1.val x.2)).max' (Finset.insert_nonempty _ _)
        let w := toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ ξ)
        let N := ‖w‖
        let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
        let Edef := ((star v ⬝ᵥ
          (globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k *ᵥ v)).re - E₀) / gap
        0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
          2 * (1 / 4) * (a * K) * (2 * Sent + (1 - τ) *
              ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpre j l) -
              C' * (τ * Real.log d + Real.binEntropy τ / a + a * B) -
              C' * (Edef / τ) * (Sent + gmax)) - ρ k ≤ -Real.log (N ^ 2) / k := by
  intro S gpre
  obtain ⟨c, Cf, hc, hCf, hlow⟩ :=
    exists_replicaMetric_symProj_bandProduct_sharp_lower_norm β (Fin d) (Fin d)
      (t := a / 2) (half_pos ha)
  refine ⟨Scan.roughLowerRemainderAtWeight K a c Cf ell Sent,
    Scan.tendsto_roughLowerRemainderAtWeight_of_label_dimension ell Sent hdim K a c Cf, ?_⟩
  intro k hk n Z hZ hZZ T ξ hξ hξn hsym hC hR
  let T' := T.restrict T.labels subset_rfl
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ U j l ∪ Y j l)ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l]) (fun _ _ ↦ rfl)
  simp only [← MeanTree.eval_restrict _ T.labels T subset_rfl] at hroot
  rw [hroot]
  intro gmax w N v Edef
  have hΩ' : ‖WithLp.toLp 2 Ω.ofLp‖ = 1 := by simpa using hΩ
  have hmomQ : ∀ (j : T.labels) (l : Fin K) (b : Fin 3) (u : ℝ), |u| ≤ c₀ / Real.sqrt B →
      let Q := FiniteProduct.regionalPhysicalRegion (X ∪ U j.val l) (Y j.val l) b
      Real.log (Entropy.surprisalMoment (FiniteProduct.reducedPure_posSemidef β
        (WithLp.toLp 2 Ω.ofLp) Q).isHermitian.eigenvalues u) ≤
          u * FiniteProduct.entropy β (WithLp.toLp 2 Ω.ofLp) Q + C₀ * B * u ^ 2 := by
    intro j l b u hu Q
    have hQ : Q = X ∪ U j.val l ∨ Q = V j.val l ∨ Q = Y j.val l ∨ Q = U j.val l ∨
        Q = U j.val l ∪ Y j.val l := by
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl (hfam.far_eq_compl j.val l).symm)
    exact hmom.surprisalMoment_le β j.val l Q hQ u hu
  obtain ⟨hw, -, hδ, hτb⟩ := hlow k n hk H Ω.ofLp E₀ gap hgap hΩ' hgap_pos Z hZ hZZ
    T.labels K (fun j l ↦ X ∪ U j.val l) (fun j l ↦ Y j.val l)
    (fun j l ↦ hfam.disjoint_inner_middle j.val l)
    (fun j j' l l' hll ↦ hfam.nesting j.val j'.val l l' hll)
    (C₀ * B) (c₀ / Real.sqrt B) hmomQ (by linarith) (by linarith)
    (mul_nonneg hC₀ (zero_le_one.trans hmom.one_le)) T' (ell k) (ell k) Sent
    (Scan.roughLowerLabelDefect ell Sent k) (1 / 4)
    (Scan.roughLowerLabelDefect_label_bound ell Sent k).2 (by norm_num)
    ξ hξ hξn hsym hC hR
  refine ⟨norm_pos_iff.mpr hw, fun τ hτ hτ1 ↦ ?_⟩
  have h1 := hτb τ hτ hτ1.le
  let gmax' := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels × Fin K)).image
    fun x ↦ S (X ∪ U x.1.val x.2) + S ((X ∪ U x.1.val x.2 ∪ Y x.1.val x.2)ᶜ) -
      S (Y x.1.val x.2))).max' (Finset.insert_nonempty _ _)
  have h1' : 2 * (1 / 4) * ∑ l : Fin K, (2 * (a / 2) * k * ((2 * Sent + (1 - τ) *
      (∑ j : T.labels, T'.weight j * (S (X ∪ U j.val l) + S ((X ∪ U j.val l ∪ Y j.val l)ᶜ) -
        S (Y j.val l))) - τ * (Real.log (Fintype.card (Fin d)) +
          Real.log (Fintype.card (Fin d))) - (3 + 1 / (2 * (a / 2))) * Real.binEntropy τ -
          50 * (C₀ * B) * (a / 2)) - Edef / τ * max 0 (2 * Sent + gmax')) -
      (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * (a / 2) * Scan.roughLowerLabelDefect ell Sent k| +
        |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| + Real.log 2 + Real.log (3 / 2))) ≤
      -Real.log (N ^ 2) := h1
  have hsum : ∀ l : Fin K, ∑ j : T.labels, T'.weight j * (S (X ∪ U j.val l) +
      S ((X ∪ U j.val l ∪ Y j.val l)ᶜ) - S (Y j.val l)) = ∑ j, T.weight j * gpre j l :=
    fun l ↦ (MeanTree.sum_weight_restrict_mul T (fun j ↦ S (X ∪ U j l) +
      S ((X ∪ U j l ∪ Y j l)ᶜ) - S (Y j l))).trans
        (Finset.sum_congr rfl fun j _ ↦ by simp only [gpre, hfam.far_eq_compl])
  have hgm : gmax' = gmax := by simp only [gmax', gmax, gpre, hfam.far_eq_compl]
  have hb : |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| =
      Cf * Real.log ((k : ℝ) + 2) + Real.log 2 := by
    have hlog : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_rpow (by positivity),
      abs_of_nonpos (by nlinarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)])]
    ring
  simp only [hsum, hgm, hb, Fintype.card_fin] at h1'
  have hrem : Scan.roughLowerRemainderAtWeight K a c Cf ell Sent k =
      (K / 2 * (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * (a / 2) * Scan.roughLowerLabelDefect ell Sent k| +
        (Cf * Real.log ((k : ℝ) + 2) + Real.log 2) + Real.log 2 + Real.log (3 / 2))) / k := by
    rw [Scan.roughLowerRemainderAtWeight, show 2 * (a / 2) = a by ring]
    ring
  have hgm0 : 0 ≤ gmax := Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
  rw [hrem]
  exact sharp_lower_scalar a k Sent (Real.log d) τ (Real.binEntropy τ) Edef gmax C₀ B C' _ _
    (fun l ↦ ∑ j, T.weight j * gpre j l) ha (by linarith) (Nat.cast_pos.mpr hk) hSent
    (Real.log_natCast_nonneg d) (Real.binEntropy_nonneg hτ.le (by linarith)) hδ hτ hgm0
    (zero_le_one.trans hmom.one_le) hC'4 hC'0 h1'

open Classical in
/-- **Proposition 8.1** (`prop:comparators`, `07-comparators.tex`, lines 125–214).

There are an absolute `a₀ > 0` and a universal rough constant `C`, and for all `C₀, c₀ > 0`
a sharp constant `C'` and a threshold `c > 0`, with the following property. Let `Ω` be the
unit ground vector, with energy `E₀` and gap `g > 0`, of a positive Hamiltonian `H` on a
finite product system (lines 15–19), let `X` be a physical target and `E` a typical Schmidt
set of width `w` (`comparator:typical-set`). Put `d_* = |E|`, `z = ∑_{i ∈ E} p_i` and
`S' = -∑_{i ∈ E} p'_i log p'_i`. There are common auxiliary labels `λ_k` such that
`pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k} ∈ 𝒮_k` is nonzero, has norm at most one, is a
physical mean-energy eigenvector of eigenvalue `E₀` and has label `λ_k` on both `C` and `R`
(`comparator:prevector`, lines 131–142). The labels precede the statuses and the weight.

The entropy identity `comparator:entropy-identity` holds for every physical partition
(lines 198–202). For every finite status family obeying `comparator:nesting`,
`g^pre_{j,g} ≥ 0` (line 181), and for every `0 < a ≤ a₀`, with `t = a/2`, `s = 1/4` and
`W = aK` (lines 99–100), every mean tree with metrics `comparator:metrics`, `N = ‖𝓜^{-s} ξ‖`
and `E_def = (⟨v, H̄ v⟩ - E₀)/g` for `v = 𝓜^{-s} ξ / N` (lines 143–153):

* the rough upper bound `comparator:rough-upper` for `ξ = pre_k` holds under the prefix
  data (lines 154–161);
* the rough lower bound `comparator:rough-lower` holds for every `0 < τ < 1/2`, without
  the prefix or moment data (lines 162–169);
* under the moment data and `a ≤ c/√𝓑`, the sharp upper bound `comparator:sharp-upper` for
  `ξ = pre_k` holds without the prefix data, and the sharp lower bound
  `comparator:sharp-lower` holds for every `0 < τ < 1/2` (lines 171–197).

Every remainder `o_k(1)` is one sequence tending to zero, chosen with the physical system,
the auxiliary dimensions, the status family, `a` and the respective data fixed, and uniform
over the tree, its terminal probabilities, the isometric coordinates `Z` of the symmetric
space and, for the lower bounds, over every symmetric vector `ξ` of norm at most one with
label `λ_k` on both `C` and `R`, which includes `pre_k` (lines 205–213). The maximum
`g_max` is taken over the bands and the labels occurring at the leaves of the tree; since
`g^pre ≥ 0`, inserting `0` changes it only for `K = 0`. -/
def ComparatorsStatement : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 < C ∧
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → Type) [∀ v, Fintype (β v)]
    [∀ v, DecidableEq (β v)] (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ)
    (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (E₀ gap : ℝ),
    H.PosSemidef → IsGappedGroundState H E₀ Ω gap → 0 < gap →
  ∀ (X : Finset ι) (E : Finset (FiniteProduct.Configuration β X)) (w : ℝ),
    IsTypicalSchmidtSet β Ω X E w →
    let p := (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.eigenvalues
    let S := FiniteProduct.entropy β Ω
    let z := ∑ i ∈ E, p i
    let d := E.card
    let S' := ∑ i ∈ E, Real.negMulLog (p i / z)
    let Hbar := fun k : ℕ ↦ globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k
    let Psym := fun k : ℕ ↦ symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k)
    let LC := fun (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) ↦
      labelProj (subsystemPerm k (siteSpace β d) {some none}) l
    let LR := fun (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) ↦
      labelProj (subsystemPerm k (siteSpace β d) {none}) l
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let pre := prevector β Ω d ell k
        pre ≠ 0 ∧ ‖pre‖ ≤ 1 ∧ Psym k *ᵥ pre = pre ∧ Hbar k *ᵥ pre = (E₀ : ℂ) • pre.ofLp ∧
          LC k (ell k) *ᵥ pre = pre ∧ LR k (ell k) *ᵥ pre = pre) ∧
      (∀ U Y V : Finset ι, Disjoint X U → Disjoint X Y → Disjoint X V → Disjoint U Y →
        Disjoint U V → Disjoint Y V → X ∪ U ∪ Y ∪ V = Finset.univ →
        2 * S X + (S (X ∪ U) + S V - S Y) - (S U + S (U ∪ Y) - S Y) =
          FiniteProduct.mutualInformation β Ω X V +
            FiniteProduct.mutualInformation β Ω X (Y ∪ V)) ∧
      ∀ (St : Type) [Fintype St] [DecidableEq St] (K : ℕ) (U Y V : St → Fin K → Finset ι),
        IsStatusFamily X U Y V →
        let gpre := fun j l ↦ S (X ∪ U j l) + S (V j l) - S (Y j l)
        let gpost := fun j l ↦ S (U j l) + S (U j l ∪ Y j l) - S (Y j l)
        (∀ j l, 0 ≤ gpre j l) ∧
        ∀ a : ℝ, 0 < a → a ≤ a₀ →
        let s : ℝ := 1 / 4
        let t := a / 2
        let W := a * K
        let avg := fun (T : MeanTree St) (f : St → Fin K → ℝ) ↦
          (1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * f j l
        (∀ (R : Finset (Finset ι)) (Bsh Bexc : ℝ), IsPrefixData β Ω X U Y R Bsh Bexc →
          ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
            ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ T : MeanTree St,
              let N := ‖toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
              0 < N ∧ -Real.log (N ^ 2) / k ≤
                2 * Real.log d - Real.log z + 2 * s * W * (2 * Bsh / z + 2 * Bexc) + ρ k) ∧
        (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
          ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
            Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ (T : MeanTree St)
            (ξ : EuclideanSpace ℂ (Config k (siteSpace β d))), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
            Psym k *ᵥ ξ = ξ → LC k (ell k) *ᵥ ξ = ξ → LR k (ell k) *ᵥ ξ = ξ →
            let w := toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
              (toEuclideanLin Zᴴ ξ)
            let N := ‖w‖
            let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
            let Edef := ((star v ⬝ᵥ (Hbar k *ᵥ v)).re - E₀) / gap
            0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
              2 * s * W * (2 * S' - C * (τ * Real.log d + Real.binEntropy τ / a) -
                  C * (Edef / τ) * S') - ρ k ≤ -Real.log (N ^ 2) / k) ∧
        (∀ B : ℝ, IsMarginalMomentData β Ω X U Y V C₀ c₀ B → a ≤ c / Real.sqrt B →
          (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
            ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ T : MeanTree St,
              let N := ‖toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
              0 < N ∧ -Real.log (N ^ 2) / k ≤
                2 * Real.log d - Real.log z +
                  2 * s * W * (avg T gpost + C' * (a * B + |Real.log z| / a)) + ρ k) ∧
          (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
            ∀ (n : ℕ) (Z : Matrix (Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ (T : MeanTree St)
              (ξ : EuclideanSpace ℂ (Config k (siteSpace β d))), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
              Psym k *ᵥ ξ = ξ → LC k (ell k) *ᵥ ξ = ξ → LR k (ell k) *ᵥ ξ = ξ →
              let gmax := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels × Fin K)).image
                fun x ↦ gpre x.1.val x.2)).max' (Finset.insert_nonempty _ _)
              let w := toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ ξ)
              let N := ‖w‖
              let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
              let Edef := ((star v ⬝ᵥ (Hbar k *ᵥ v)).re - E₀) / gap
              0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
                2 * s * W * (2 * S' + (1 - τ) * avg T gpre -
                    C' * (τ * Real.log d + Real.binEntropy τ / a + a * B) -
                    C' * (Edef / τ) * (S' + gmax)) - ρ k ≤ -Real.log (N ^ 2) / k))

/-- **Proposition 8.1** (`prop:comparators`, `07-comparators.tex`, lines 125–214) holds,
with `a₀ = 1/10`, rough constant `4`, sharp constant `4 + 25 C₀` and threshold `c = c₀/10`. -/
theorem comparatorsStatement : ComparatorsStatement := by
  refine ⟨1 / 10, by norm_num, 4, by norm_num, fun C₀ c₀ hC₀ hc₀ ↦
    ⟨c₀ / 10, 4 + 25 * C₀, by positivity, by positivity, ?_⟩⟩
  intro ι _ _ β _ _ H Ω E₀ gap hHpos hgs hgap_pos X E w htyp p S z d S' Hbar Psym LC LR
  obtain ⟨hΩ, hE, hgapM⟩ := isGappedGroundState_iff.mp hgs
  have hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass
      E := htyp.mass_pos
  have : NeZero d := ⟨htyp.nonempty.card_pos.ne'⟩
  have : NeZero E.card := ⟨htyp.nonempty.card_pos.ne'⟩
  have : ∀ v, Nonempty (β v) := fun v ↦ by
    by_contra hv
    rw [not_nonempty_iff] at hv
    have h0 : Ω = 0 := by
      ext x
      exact (hv.false (x v)).elim
    simp [h0] at hΩ
  obtain ⟨ell, hpre, hmass, hdim⟩ := exists_prevector_labels β H Ω E₀ hΩ hE X E hz
  rw [vonNeumannEntropy_compressedTypicalPureState_eq_sum β Ω X E hz] at hdim
  have hS' : 0 ≤ S' := Finset.sum_nonneg fun i hi ↦ Real.negMulLog_nonneg
    (div_nonneg ((FiniteProduct.reducedPure_posSemidef β Ω X).eigenvalues_nonneg i) hz.le)
    ((div_le_one hz).mpr (Finset.single_le_sum (fun j _ ↦
      (FiniteProduct.reducedPure_posSemidef β Ω X).eigenvalues_nonneg j) hi))
  refine ⟨ell, hpre, fun U Y V hXU hXY hXV hUY hUV hYV hc ↦
    FiniteProduct.auxiliaryPair_entropyIdentity β Ω X U Y V hXU hXY hXV hUY hUV hYV hc, ?_⟩
  intro St _ _ K U Y V hfam gpre gpost
  refine ⟨fun j l ↦ FiniteProduct.auxiliaryPair_pre_nonneg β Ω hΩ X (U j l) (Y j l) (V j l)
    (hfam.disjoint_XY j l) (hfam.disjoint_XV j l) (hfam.disjoint_UY j l)
    (hfam.disjoint_UV j l) (hfam.disjoint_YV j l) (hfam.cover j l), ?_⟩
  intro a ha ha₀ s t W avg
  refine ⟨fun R Bsh Bexc hR ↦ exists_rough_upper β Ω hΩ X E hz ell hmass U Y V hfam a ha
      R Bsh Bexc hR,
    exists_rough_lower β H Ω E₀ gap hgapM hΩ hgap_pos ell S' hS' hdim X U Y V hfam a ha
      (by linarith), fun B hmom hac ↦ ?_⟩
  have hB : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hmom.one_le)
  have h10 : 10 * a ≤ c₀ / Real.sqrt B := by
    rw [div_right_comm] at hac
    linarith
  exact ⟨exists_sharp_upper β Ω hΩ X E hz ell hmass U Y V hfam C₀ c₀ B (4 + 25 * C₀)
      (by linarith) (by linarith) hmom a ha (by linarith) (by linarith),
    exists_sharp_lower β H Ω E₀ gap hgapM hΩ hgap_pos ell S' hS' hdim X U Y V hfam
      C₀ c₀ B (4 + 25 * C₀) hC₀.le (by linarith) (by linarith) hmom a ha h10 (by linarith)⟩

end TNLean.PEPS.AreaLaw.Scan.Comparators
