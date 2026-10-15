/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTerminalPartitions
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.Scan.ReceivingRegions
import TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties
import TNLean.PEPS.AreaLaw.TwoFamilies
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Representation.ReplicaPrevectorSharpUpper

/-!
# A sharp upper estimate along the actual fill and charge trees

The supplied physical prevector and its labels are fixed throughout the scan.
A single completed/pre-charge terminal family supplies the physical partitions
for every actual interpolation tree, without changing histories or weights.
The constant and replica threshold precede all times and interpolation parameters.

**Scope restriction (fixed-instance supplied-label estimate):**
`eventually_actualScan_suppliedPrevector_sharp_upper` assumes a positive target
spectral mass, a supplied label sequence with the eventual mass bound, and
common completed/pre-charge marginal moments. Its constant and copy threshold
may depend on the fixed physical instance and supplied labels. The full
Proposition 9.6 lower estimate, telescope and absorption remain separate.
See `docs/paper-gaps/arealaw2d_actual_sharp_upper_scope.tex`.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:sharp-upper`, lines 383–418; `08-scanner.tex`, lines 416–474,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology symmDiff

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open ActualTerminals

local instance sharpUpper_originalConfigDecidableEq
    {V : Type} [Fintype V] [DecidableEq V] (q d k : ℕ) :
    DecidableEq (Config k
      (addedSiteSpace (addedSiteSpace (fun _ : V ↦ Fin q) (Fin d)) (Fin d))) :=
  Fintype.decidablePiFintype

open Classical in
/-- The actual terminal regions are disjoint, ordered by band, and have the
same receiving decomposition. No physical vector or replica parameter enters.
Source: `08-scanner.tex`, lines 83–154 and 400–474, revision adc7f124. -/
private theorem actualTerminal_sharpUpper_geometry
    {I : Type} [Fintype I] [LinearOrder I]
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) ∧
    (∀ j j' g g', g < g' → U j g ∪ Y j g ⊆ U j' g') ∧
    (∀ j g, Disjoint (U j g) (Y j g)) ∧
    (∀ j g, Disjoint X (U j g ∪ Y j g)) ∧
    (∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ) := by
  classical
  intro X σ U Y
  have hdepthX : ∀ x ∈ X, S.depth x ≤ 0 := fun x hx ↦ by
    simpa only [hdepth, Nat.cast_zero] using
      (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
        ((ambientDilation_zero T).symm ▸ (Finset.mem_filter.mp hx).2)
  have hmiddle : ∀ j g x, σ j g x = none → 0 < S.depth x := fun
    | Sum.inl ⟨r, h⟩, g, x, hx =>
      lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
        (Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hx)).1
    | Sum.inr ⟨r, h⟩, g, x, hx =>
      lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
        (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hx)).1
  have hUYeq : ∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g) :=
    fun j g ↦ by
      simp only [U, Y, positiveNear, positiveNearMiddle, Finset.filter_union,
        (Finset.filter_eq_self (s := middle (σ j g))
          (p := fun x ↦ 0 < S.depth x)).mpr
          (fun x hx ↦ hmiddle j g x (Finset.mem_filter.mp hx).2)]
  have hnest₀ : ∀ j j' g g', g < g' →
      receiving (σ j g) false ∪ middle (σ j g) ⊆ receiving (σ j' g') false := fun
    | Sum.inl ⟨_, h⟩, Sum.inl ⟨_, h'⟩, g, g', hgg' =>
      S.state_near_middle_subset_later_near h h' g g' hgg'
    | Sum.inl ⟨_, h⟩, Sum.inr ⟨_, h'⟩, g, g', hgg' =>
      S.state_near_middle_subset_later_old_near h h' g g' hgg'
    | Sum.inr ⟨_, h⟩, Sum.inl ⟨_, h'⟩, g, g', hgg' =>
      S.old_near_middle_subset_later_state_near h h' g g' hgg'
    | Sum.inr ⟨_, h⟩, Sum.inr ⟨_, h'⟩, g, g', hgg' =>
      S.oldChargeState_near_middle_subset_later_near h h' g g' hgg'
  have hnest : ∀ j j' g g', g < g' → U j g ∪ Y j g ⊆ U j' g' :=
    fun j j' g g' hgg' ↦ by
      exact (hUYeq j g).symm ▸
        Finset.filter_subset_filter (p := fun x ↦ 0 < S.depth x) (hnest₀ j j' g g' hgg')
  have hUY : ∀ j g, Disjoint (U j g) (Y j g) := fun j g ↦ by
    simpa only [U, Y,
      middle_eq_positiveNearMiddle_sdiff_positiveNear S.depth (σ j g) (hmiddle j g)] using
      (disjoint_sdiff_self_right : Disjoint (positiveNear S.depth (σ j g))
        (positiveNearMiddle S.depth (σ j g) \ positiveNear S.depth (σ j g)))
  have hXY : ∀ j g, Disjoint X (U j g ∪ Y j g) :=
    fun j g ↦ Finset.disjoint_left.mpr fun x hx hxy ↦
      (not_lt_of_ge (hdepthX x hx))
        (Finset.mem_filter.mp
          (show x ∈ positiveNearMiddle S.depth (σ j g) from (hUYeq j g) ▸ hxy)).2
  have hregions : ∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ := fun
    | Sum.inl ⟨_, h⟩, g => state_receiving_regions hT S hdepth h g
    | Sum.inr ⟨_, h⟩, g => oldChargeState_receiving_regions hT S hdepth h g
  exact ⟨hUYeq, hnest, hUY, hXY, hregions⟩

open Classical in
/-- The regional moment inequality uses the same reduced matrix and entropy
in finite-product coordinates. Source: `07-comparators.tex`, lines 70–85,
revision adc7f124. -/
private theorem sharpUpper_marginalMoment_finiteProduct
    {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (Q : Finset (Site Λ)) (Kmom u : ℝ)
    (h : Real.log (Entropy.surprisalMoment
      (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
        u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) :
    Real.log (Entropy.surprisalMoment
      (FiniteProduct.reducedPure_posSemidef
        (fun _ : Site Λ ↦ Fin q) Ωt Q).isHermitian.eigenvalues u) ≤
      u * vonNeumannEntropy (FiniteProduct.reducedPure (fun _ : Site Λ ↦ Fin q) Ωt Q)
        (FiniteProduct.reducedPure_posSemidef
          (fun _ : Site Λ ↦ Fin q) Ωt Q).isHermitian + Kmom * u ^ 2 := by
  classical
  let β := fun _ : Site Λ ↦ Fin q
  have hEigen := congrArg (fun A : {A : Matrix (FiniteProduct.Configuration β Q)
      (FiniteProduct.Configuration β Q) ℂ // A.IsHermitian} ↦ A.2.eigenvalues)
    (Subtype.ext
      (a1 := ⟨reducedState Λ q Ωt Q, reducedState_isHermitian Λ q Ωt Q⟩)
      (a2 := ⟨FiniteProduct.reducedPure β Ωt Q,
        (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian⟩)
      (reducedState_eq_finiteProduct Λ q Ωt Q))
  change Real.log (Entropy.surprisalMoment
    (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian.eigenvalues u) ≤
      u * FiniteProduct.entropy β Ωt Q + Kmom * u ^ 2
  rw [← hEigen, ← regionalEntropy_eq_finiteProduct Λ q Ωt Q]
  exact h

open Classical in
/-- The original completed and pre-charge moment inputs supply precisely the
three positive terminal marginals used in the sharp comparison.
Source: `07-comparators.tex`, lines 70–85; `08-scanner.tex`, lines 400–414,
revision adc7f124. -/
private theorem actualTerminal_sharpUpper_moments
    {q : ℕ} {I : Type} [Fintype I] [LinearOrder I]
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I) (Kmom r : ℝ)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q))
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ r →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2)) :
    let β := fun _ : Site Λ ↦ Fin q
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) →
    ∀ j g (Q : Finset (Site Λ)),
      Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
      ∀ u : ℝ, |u| ≤ r →
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian.eigenvalues u) ≤
          u * vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
            (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian + Kmom * u ^ 2 := by
  classical
  intro β σ U Y hUYeq
  have hmomStatus : ∀ j g (Q : Finset (Site Λ)),
      Q ∈ statusMarginalRegions S.depth (σ j g) →
      ∀ u : ℝ, |u| ≤ r →
        Real.log (Entropy.surprisalMoment
          (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
          u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2 := fun
    | Sum.inl ⟨s, hist⟩, g, Q, hQ, u, hu =>
      (hmom s.val hist g).1 (Nat.le_of_lt_succ s.isLt) Q hQ u hu
    | Sum.inr ⟨s, hist⟩, g, Q, hQ, u, hu =>
      (hmom s.val hist g).2 (Nat.succ_le_of_lt s.isLt) Q hQ u hu
  intro j g Q hQ u hu
  have hmem : Q ∈ statusMarginalRegions S.depth (σ j g) := by
    simp only [statusMarginalRegions, Finset.mem_insert, Finset.mem_singleton]
    rcases hQ with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hUYeq j g))))
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact sharpUpper_marginalMoment_finiteProduct Ωt Q Kmom u
    (hmomStatus j g Q hmem u hu)

open Classical in
/-- Reindexing the supplied symmetric range isometry preserves both its
orthonormal columns and its exact symmetric range projection.
Source: `07-comparators.tex`, lines 80–110 and 383–418, revision adc7f124. -/
private theorem sharpUpper_augmented_symmetricCoordinates
    {V : Type} [Fintype V] [DecidableEq V] (q d k N : ℕ)
    (ZS : Matrix (Config k (fun v ↦ Fin (augmentedDimensions (V := V) q
      (fun _ ↦ d) v))) (Fin N) ℂ)
    (hZS : ZSᴴ * ZS = 1)
    (hZSZS : ZS * ZSᴴ = symProj (copyPerm ((v : V ⊕ Bool) →
      Fin (augmentedDimensions (V := V) q (fun _ ↦ d) v)) k)) :
    let β := fun _ : V ↦ Fin q
    let e := augmentedReplicaConfigurationEquiv (V := V) q d k
    let ZO := ZS.submatrix e (id : Fin N → Fin N)
    ZOᴴ * ZO = 1 ∧
      ZO * ZOᴴ = symProj (copyPerm ((o : Option (Option V)) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) := by
  classical
  intro β e ZO
  let n := augmentedDimensions (V := V) q (fun _ ↦ d)
  have hZO : ZOᴴ * ZO = 1 :=
    Matrix.IsIsometry.reindex ZS hZS e.symm (Equiv.refl (Fin N))
  have hSymm :
      symProj (copyPerm ((o : Option (Option (V))) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) =
      (symProj (copyPerm ((v : V ⊕ Bool) → Fin (n v)) k)).submatrix e e := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      (symProj_of_intertwine e.symm
        (φ := copyPerm ((v : V ⊕ Bool) → Fin (n v)) k)
        (ψ := copyPerm ((o : Option (Option (V))) →
          addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k)
        (fun σ x ↦ funext fun j ↦ rfl))
  have hZOZO : ZO * ZOᴴ =
      symProj (copyPerm ((o : Option (Option (V))) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) := by
    simpa only [ZO, Matrix.conjTranspose_submatrix, Equiv.coe_refl] using
      ((Matrix.submatrix_mul_equiv ZS ZSᴴ e (Equiv.refl (Fin N)) e).trans
        (congrArg (fun P : Matrix (Config k (fun v ↦ Fin (n v)))
          (Config k (fun v ↦ Fin (n v))) ℂ ↦ P.submatrix e e) hZSZS)).trans hSymm.symm
  exact ⟨hZO, hZOZO⟩

open Classical in
/-- Identify the actual filtered norm with the compressed quarter-power norm.
This matrix identity retains the root, supplied prevector and terminal tree;
no entropy estimate or scalar rate bound enters.
Source: `06-transport.tex`, lines 251–286 and 388–392;
`07-comparators.tex`, lines 383–418; `08-scanner.tex`, lines 416–474,
revision adc7f124. -/
private theorem actualRoot_sharpUpper_normSq
    {q d : ℕ} [NeZero q] [NeZero d] {I : Type} [Fintype I] [LinearOrder I]
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (X : Finset (Site Λ)) (a : ℝ) (ha : 0 < a)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q))
    (k : ℕ) (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (N : ℕ)
    (ZS : Matrix (Config k (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q
      (fun _ ↦ d) v))) (Fin N) ℂ)
    (hZS : ZSᴴ * ZS = 1)
    (hZSZS : ZS * ZSᴴ = symProj (copyPerm ((v : Site Λ ⊕ Bool) →
      Fin (augmentedDimensions (V := Site Λ) q (fun _ ↦ d) v)) k)) :
    let β := fun _ : Site Λ ↦ Fin q
    let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
    let pre := replicaPrevector Ωt d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
    let ZO := ZS.submatrix e (id : Fin N → Fin N)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) →
    (∀ j g, Disjoint X (U j g ∪ Y j g)) →
    (∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ) →
    ∀ {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ h, DecidableEq (Choice h)]
      (D : ReplicaTransport.TransportData (Site Λ ⊕ Bool) S.K Hist Choice)
      (_ : D.IsAdmissible) (_ : D.CrossBandCommute n (a / 2) k)
      (f : (Σ h, Option (Choice h)) → terminalFamily S.K S.m S.M (S.n * S.m))
      (_ : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g)) (p : ℝ),
      let tree := (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map f
      let v : EuclideanSpace ℂ (Config k
        (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) := WithLp.toLp 2
          (replicaPrevector Ωt d k ell ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      let W := replicaMetric (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)) (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun x ↦ some (some x))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
      let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun x ↦ some (some x)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ tree.eval (fun j ↦ ZOᴴ * A j g * ZO)).prod
      Transport.filteredNormSq (D.rootPath n (a / 2) k p) pre =
        ‖toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin ZOᴴ v)‖ ^ 2 := by
  classical
  intro β n pre σ U Y e ZO hUYeq hXY hregions
    Hist instHist Choice instChoice D hD hcomm f hparts p tree v W Q F ext A M
  have hsym : symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre = pre :=
    symProj_mulVec_augmentedReplicaPrevector q d k Ωt ell
  have hpre : pre ∘ e = replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, e, Equiv.symm_comp_self, Function.comp_id, β]
  have hroot := (rootPath_augmented_compressed_bandProduct q d D hD
    (div_pos ha zero_lt_two).le k N hcomm ZS hZS hZSZS pre hsym p).2.2.2.1
  have hP (j : Σ h, Option (Choice h)) (g : Fin S.K) :
      (D.leafPart j g).P.image augmentedSiteEquiv.symm =
        insert (some none) ((X ∪ U (f j) g).image (fun x ↦ some (some x))) := by
    rw [hparts, augmentedPartition_eq_images]
    simp only [Finset.image_insert, Finset.image_image]
    change insert (some none)
      ((receiving (σ (f j) g) false).image (fun x ↦ some (some x))) = _
    rw [(hregions (f j) g).1]
  have hF (j : Σ h, Option (Choice h)) (g : Fin S.K) :
      (D.leafPart j g).F.image augmentedSiteEquiv.symm =
        insert none (((X ∪ (U (f j) g ∪ Y (f j) g))ᶜ).image
          (fun x ↦ some (some x))) := by
    rw [hparts, augmentedPartition_eq_images]
    simp only [Finset.image_insert, Finset.image_image]
    change insert none
      ((receiving (σ (f j) g) true).image (fun x ↦ some (some x))) = _
    rw [(hregions (f j) g).2.2, ← hUYeq (f j) g]
  have hY (j : Σ h, Option (Choice h)) (g : Fin S.K) :
      (D.leafPart j g).Y.image augmentedSiteEquiv.symm =
        ((Y (f j) g \ X).image (fun x ↦ some (some x))) := by
    rw [hparts, augmentedPartition_eq_images]
    simp only [Finset.image_image]
    change (middle (σ (f j) g)).image (fun x ↦ some (some x)) = _
    rw [Finset.sdiff_eq_self_of_disjoint
      (Finset.disjoint_union_right.mp (hXY (f j) g)).2.symm]
  simp only [e] at hpre
  simpa only [M, tree, Matrix.MeanTree.eval_map, A, W, Q, F, ext, v,
    hP, hF, hY, hpre, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, ZO, e, β] using! hroot

open Classical in
/-- Transport a quarter-power compressed sharp comparison to the same actual
root, preserving its terminal weights, prevector and interpolation parameter.
Source: `06-transport.tex`, lines 251–286 and 388–392;
`07-comparators.tex`, lines 383–418; `08-scanner.tex`, lines 416–474,
revision adc7f124. -/
private theorem actualRoot_sharpUpper_of_compressed
    {q d : ℕ} [NeZero q] [NeZero d] {I : Type} [Fintype I] [LinearOrder I]
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (X : Finset (Site Λ)) (a Kmom z c : ℝ) (ha : 0 < a)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q))
    (k : ℕ) (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (N : ℕ)
    (ZS : Matrix (Config k (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q
      (fun _ ↦ d) v))) (Fin N) ℂ)
    (hZS : ZSᴴ * ZS = 1)
    (hZSZS : ZS * ZSᴴ = symProj (copyPerm ((v : Site Λ ⊕ Bool) →
      Fin (augmentedDimensions (V := Site Λ) q (fun _ ↦ d) v)) k)) :
    let β := fun _ : Site Λ ↦ Fin q
    let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
    let pre := replicaPrevector Ωt d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
    let ZO := ZS.submatrix e (id : Fin N → Fin N)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) →
    (∀ j g, Disjoint X (U j g ∪ Y j g)) →
    (∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ) →
    (∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
      let v : EuclideanSpace ℂ (Config k
        (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) := WithLp.toLp 2
          (replicaPrevector Ωt d k ell ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      let W := replicaMetric (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)) (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun x ↦ some (some x))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
      let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun x ↦ some (some x)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ tree.eval (fun j ↦ ZOᴴ * A j g * ZO)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin ZOᴴ v)‖ ^ 2
      let entropy := fun Q : Finset (Site Λ) ↦ vonNeumannEntropy
        (FiniteProduct.reducedPure β Ωt Q) (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (d : ℝ) - Real.log z +
          2 * (1 / 4) * a * (∑ g, ∑ j, tree.weight j *
            (entropy (U j g) + entropy (U j g ∪ Y j g) - entropy (Y j g))) +
          24 * (1 / 4) * S.K * Kmom * a ^ 2 - 2 * (1 / 4) * S.K * Real.log z +
            Real.bellOverlapRemainder d c S.K k) →
    ∀ {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ h, DecidableEq (Choice h)]
      (D : ReplicaTransport.TransportData (Site Λ ⊕ Bool) S.K Hist Choice)
      (_ : D.IsAdmissible) (_ : D.CrossBandCommute n (a / 2) k)
      (f : (Σ h, Option (Choice h)) → terminalFamily S.K S.m S.M (S.n * S.m))
      (_ : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g)) (p : ℝ),
      let Nsq := Transport.filteredNormSq (D.rootPath n (a / 2) k p) pre
      let tree := (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map f
      let gpost := fun j g ↦ regionalEntropy Λ q Ωt (U j g) +
        regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
          regionalEntropy Λ q Ωt (Y j g)
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (d : ℝ) - Real.log z +
          (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
            6 * (S.K : ℝ) * Kmom * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
              Real.bellOverlapRemainder d c S.K k := by
  classical
  intro β n pre σ U Y e ZO hUYeq hXY hregions hupper
    Hist instHist Choice instChoice D hD hcomm f hparts p Nsq tree gpost
  have hnorm := actualRoot_sharpUpper_normSq (q := q) (d := d) S X a ha Ωt
    k ell N ZS hZS hZSZS hUYeq hXY hregions D hD hcomm f hparts p
  have hcoef : 2 * (1 / 4 : ℝ) * a = a / 2 := by ring
  have hquad : 24 * (1 / 4 : ℝ) * (S.K : ℝ) * Kmom * a ^ 2 =
      6 * (S.K : ℝ) * Kmom * a ^ 2 := by ring
  have hmasscoef : 2 * (1 / 4 : ℝ) * (S.K : ℝ) = (S.K : ℝ) / 2 := by ring
  refine Eq.mp (congrArg (fun u : ℝ ↦ 0 < u ∧ -Real.log u / (k : ℝ) ≤
    2 * Real.log (d : ℝ) - Real.log z +
      (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
        6 * (S.K : ℝ) * Kmom * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
          Real.bellOverlapRemainder d c S.K k) hnorm.symm) ?_
  have hestimate := hupper ((D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map f)
  refine ⟨hestimate.1, hestimate.2.trans_eq ?_⟩
  have hentropy (Q : Finset (Site Λ)) :
      vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
        (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian =
          regionalEntropy Λ q Ωt Q :=
    (regionalEntropy_eq_finiteProduct Λ q Ωt Q).symm
  have hunion (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K) :
      regionalEntropy Λ q Ωt (U j g ∪ Y j g) =
        regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) :=
    congrArg (regionalEntropy Λ q Ωt) (hUYeq j g)
  simp only [hcoef, hquad, hmasscoef, gpost, tree, hentropy, hunion]

open Classical in
/-- Apply one uniform compressed estimate at a fixed replica number to the
actual fill and charge roots. Symmetric-coordinate selection changes neither
the supplied label nor the physical prevector or terminal weights.
Source: `06-transport.tex`, lines 251–286 and 388–392;
`07-comparators.tex`, lines 383–418; `08-scanner.tex`, lines 416–474,
revision adc7f124. -/
private theorem actualScan_sharpUpper_of_compressed
    {q d : ℕ} [NeZero q] [NeZero d] {I : Type} [Fintype I] [LinearOrder I]
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hm : 0 < S.m) (hM : 0 < S.M)
    (X : Finset (Site Λ)) (a Kmom z c : ℝ) (ha : 0 < a)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q))
    (k : ℕ) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let β := fun _ : Site Λ ↦ Fin q
    let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
    let pre := replicaPrevector Ωt d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) →
    (∀ j g, Disjoint X (U j g ∪ Y j g)) →
    (∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ) →
    (∀ (N : ℕ) (ZO : Matrix (Config k
      (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) (Fin N) ℂ),
      ZOᴴ * ZO = 1 →
      ZO * ZOᴴ = symProj (copyPerm ((o : Option (Option (Site Λ))) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) →
      ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
      let v : EuclideanSpace ℂ (Config k
        (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) := WithLp.toLp 2
          (replicaPrevector Ωt d k ell ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      let W := replicaMetric (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)) (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun x ↦ some (some x))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
      let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun x ↦ some (some x)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ tree.eval (fun j ↦ ZOᴴ * A j g * ZO)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin ZOᴴ v)‖ ^ 2
      let entropy := fun Q : Finset (Site Λ) ↦ vonNeumannEntropy
        (FiniteProduct.reducedPure β Ωt Q) (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (d : ℝ) - Real.log z +
          2 * (1 / 4) * a * (∑ g, ∑ j, tree.weight j *
            (entropy (U j g) + entropy (U j g ∪ Y j g) - entropy (Y j g))) +
          24 * (1 / 4) * S.K * Kmom * a ^ 2 - 2 * (1 / 4) * S.K * Real.log z +
            Real.bellOverlapRemainder d c S.K k) →
    ∀ (s : ℕ) (hs : s + 1 ≤ S.n * S.m) (p : ℝ),
      let p₀ := Set.projIcc (0 : ℝ) 1 zero_le_one p
      let gpost := fun j g ↦ regionalEntropy Λ q Ωt (U j g) +
        regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
          regionalEntropy Λ q Ωt (Y j g)
      let bound := fun (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) ↦
        2 * Real.log (d : ℝ) - Real.log z +
          (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
            6 * (S.K : ℝ) * Kmom * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
              Real.bellOverlapRemainder d c S.K k
      let step : Fin (S.n * S.m) := ⟨s, Nat.lt_of_succ_le hs⟩
      let Nfill := Matrix.Transport.filteredNormSq
        ((S.actualFillData hm hM s).rootPath n (a / 2) k p) pre
      let Ncharge := Matrix.Transport.filteredNormSq
        ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) pre
      (0 < Nfill ∧ -Real.log Nfill / (k : ℝ) ≤
        bound (((S.actualFillData hm hM s).tree p₀).map
          (fillTerminalIndex S.K S.m S.M (S.n * S.m) step))) ∧
      (0 < Ncharge ∧ -Real.log Ncharge / (k : ℝ) ≤
        bound (((S.actualChargeData hm hM s).tree p₀).map
          (chargeTerminalIndex S.K S.m S.M (S.n * S.m) step))) := by
  classical
  intro β n pre σ U Y hUYeq hXY hregions hupper s hs p p₀ gpost bound
    step Nfill Ncharge
  obtain ⟨N, ZS, hZS, hZSZS⟩ :=
    (isStarProjection_symProj
      (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)).exists_matrix_range_isometry
  let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
  let ZO := ZS.submatrix e (id : Fin N → Fin N)
  obtain ⟨hZO, hZOZO⟩ :=
    sharpUpper_augmented_symmetricCoordinates q d k N ZS hZS hZSZS
  have hu (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) :=
    hupper N ZO hZO hZOZO tree
  have hbound {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ h, DecidableEq (Choice h)]
      (D : ReplicaTransport.TransportData (Site Λ ⊕ Bool) S.K Hist Choice)
      (hD : D.IsAdmissible) (hcomm : D.CrossBandCommute n (a / 2) k)
      (f : (Σ h, Option (Choice h)) → terminalFamily S.K S.m S.M (S.n * S.m))
      (hparts : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g)) :
      let Nsq := Transport.filteredNormSq (D.rootPath n (a / 2) k p) pre
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤ bound ((D.tree p₀).map f) := by
    exact actualRoot_sharpUpper_of_compressed (q := q) (d := d) S X a Kmom z c ha Ωt
      k ell N ZS hZS hZSZS hUYeq hXY hregions hu D hD hcomm f hparts p
  exact
    let r : Fin (S.n * S.m) := ⟨s, Nat.lt_of_succ_le hs⟩
    ⟨hbound (S.actualFillData hm hM s)
        (S.actualFillData_isAdmissible hm hM s)
        (S.fillTransportData_crossBandCommute
          (historyMeanTree S.K S.m S.M hm hM s) n (div_pos ha zero_lt_two).le k)
        (fillTerminalIndex S.K S.m S.M (S.n * S.m) r)
        (fun j g ↦ actualFillData_leafPart_terminalPartition S hm hM (S.n * S.m) r j g),
      hbound (S.actualChargeData hm hM s)
        (S.actualChargeData_isAdmissible hm hM s)
        (S.chargeTransportData_crossBandCommute
          (historyMeanTree S.K S.m S.M hm hM s)
          (fun _ ↦ chargeChoiceTree S.K S.M hM) n (div_pos ha zero_lt_two).le k)
        (chargeTerminalIndex S.K S.m S.M (S.n * S.m) r)
        (fun j g ↦ actualChargeData_leafPart_terminalPartition S hm hM (S.n * S.m) r j g)⟩

open Classical in
/-- The fixed-copy QIC comparison, still uniform in coordinates, bands,
terminal labels, regions, weighted trees, and comparison powers.
Source: `07-comparators.tex`, lines 383–418, revision adc7f124. -/
private def sharpUpper_uniformCompressedAt
    {q : ℕ} [NeZero q] {Λ : Finset (ℤ × ℤ)}
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (X : Finset (Site Λ))
    (d : ℕ) (z a Kmom r c : ℝ) (k : ℕ)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  let β := fun _ : Site Λ ↦ Fin q
  ∀ (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) (Fin n) ℂ),
  Zᴴ * Z = 1 →
  Z * Zᴴ = symProj (copyPerm ((o : Option (Option (Site Λ))) →
    addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) →
  ∀ (G : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (U Y : ι → Fin G → Finset (Site Λ)),
  (∀ j g, Disjoint X (U j g)) → (∀ j g, Disjoint X (Y j g)) →
  (∀ j g, Disjoint (U j g) (Y j g)) →
  (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
  (∀ j g (Q : Finset (Site Λ)), Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
    ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment
        (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
          (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian + Kmom * v ^ 2) →
  ∀ (T : MeanTree ι) (s : ℝ), 2 * s ∈ Set.Icc (0 : ℝ) 1 →
  let v : EuclideanSpace ℂ (Config k
    (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) := WithLp.toLp 2
    (replicaPrevector Ωt d k ell ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
  let W := replicaMetric (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)) (a / 2) k
  let Q := fun j g ↦ insert (some none)
    ((X ∪ U j g).image fun v ↦ some (some v))
  let F := fun j g ↦ insert none
    (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
  let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun v ↦ some (some v)
  let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
  let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * A j g * Z)).prod
  let Nsq := ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ ^ 2
  let S := fun Q : Finset (Site Λ) ↦ vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
    (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian
  0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
    2 * Real.log (d : ℝ) - Real.log z +
      2 * s * a * (∑ g, ∑ j, T.weight j *
        (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))) +
      24 * s * G * Kmom * a ^ 2 - 2 * s * G * Real.log z +
        Real.bellOverlapRemainder d c G k

open Classical in
/-- Name one fixed-copy QIC conclusion only after all uniform arguments have
been introduced. The native spectral mass is kept throughout this conversion.
Source: `07-comparators.tex`, lines 383–418, revision adc7f124. -/
private theorem sharpUpper_uniformCompressedAt_of_qic
    {q : ℕ} [NeZero q] {Λ : Finset (ℤ × ℤ)}
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (X : Finset (Site Λ))
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) X))
    (a Kmom r c : ℝ) (k : ℕ) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let β := fun _ : Site Λ ↦ Fin q
    let zQ := (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E
    (∀ (n : ℕ) (Z : Matrix (Config k
        (addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card))) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((o : Option (Option (Site Λ))) →
        addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card) o) k) →
      ∀ (G : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
        (U Y : ι → Fin G → Finset (Site Λ)),
      (∀ j g, Disjoint X (U j g)) → (∀ j g, Disjoint X (Y j g)) →
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      (∀ j g (Q : Finset (Site Λ)), Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
        ∀ v : ℝ, |v| ≤ r →
          Real.log (Entropy.surprisalMoment
            (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian.eigenvalues v) ≤
            v * vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
              (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian + Kmom * v ^ 2) →
      ∀ (T : MeanTree ι) (s : ℝ), 2 * s ∈ Set.Icc (0 : ℝ) 1 →
      let v : EuclideanSpace ℂ (Config k
        (addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card))) := WithLp.toLp 2
        (replicaPrevector Ωt E.card k ell ∘
          globalReplicaCopiesEquiv β (Fin E.card) (Fin E.card) k)
      let W := replicaMetric
        (addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)) (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun v ↦ some (some v))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
      let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun v ↦ some (some v)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * A j g * Z)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ ^ 2
      let S := fun Q : Finset (Site Λ) ↦ vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
        (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (E.card : ℝ) - Real.log zQ +
          2 * s * a * (∑ g, ∑ j, T.weight j *
            (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))) +
          24 * s * G * Kmom * a ^ 2 - 2 * s * G * Real.log zQ +
            Real.bellOverlapRemainder E.card c G k) →
    sharpUpper_uniformCompressedAt Ωt X E.card zQ a Kmom r c k ell := by
  classical
  intro β zQ h
  intro N Z hZ hZZ G ι instF instD U Y hXU hXY hUY hnest hmom tree s hs
    v W Q F ext A M Nsq entropy
  exact h N Z hZ hZZ G U Y hXU hXY hUY hnest hmom tree s hs

open Classical in
/-- Obtain the uniform QIC witness before specializing to the scan family.
The selected state, spectral set, mass bound, and supplied labels are unchanged.
Source: `07-comparators.tex`, lines 383–418, revision adc7f124. -/
private theorem eventually_sharpUpper_uniformCompressed
    {q : ℕ} [NeZero q] {Λ : Finset (ℤ × ℤ)} (X : Finset (Site Λ))
    (a Kmom r : ℝ) (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) X))
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let β := fun _ : Site Λ ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (FiniteProduct.splitEquiv β X) Ωt
    let z := Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
    0 < z →
    let d := E.card
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    (∀ᶠ k : ℕ in atTop,
      (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
        ‖WithLp.toLp 2
          (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
            (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
            (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
              (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ G : ℕ, Tendsto (Real.bellOverlapRemainder d c G) atTop (𝓝 0)) ∧
      ∀ᶠ k : ℕ in atTop,
        sharpUpper_uniformCompressedAt Ωt X d z a Kmom r c k (ell k) := by
  classical
  intro β ΩX z hz d ψ hmass
  have hzQ :
      0 < (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E :=
    hz
  have hzEq :
      (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E = z :=
    rfl
  have hqic := FiniteProduct.eventually_suppliedReplicaPrevector_sharp_upper
    (K := Kmom) β Ωt X E hΩt hzQ ha har ha1 ell
  obtain ⟨c, hc, hlim, hu⟩ := hqic hmass
  refine ⟨c, hc, hlim, hu.mono ?_⟩
  intro k hk
  have hfixed := sharpUpper_uniformCompressedAt_of_qic Ωt X E a Kmom r c k (ell k) hk
  exact Eq.mp (congrArg (fun mass : ℝ ↦
    sharpUpper_uniformCompressedAt Ωt X E.card mass a Kmom r c k (ell k)) hzEq) hfixed

open Classical in
/-- Specialize one fixed-copy uniform comparison to the supplied terminal
family, using already typed geometric and marginal-moment hypotheses.
Source: `07-comparators.tex`, lines 383–418; `08-scanner.tex`, lines 400–474,
revision adc7f124. -/
private theorem actualTerminal_sharpUpper_of_uniformCompressed
    {q : ℕ} [NeZero q] {I : Type} [LinearOrder I]
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I) (X : Finset (Site Λ))
    (a Kmom r z c : ℝ) (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (d k : ℕ)
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (U Y : terminalFamily S.K S.m S.M (S.n * S.m) → Fin S.K → Finset (Site Λ))
    (hXU : ∀ j g, Disjoint X (U j g))
    (hXY : ∀ j g, Disjoint X (Y j g))
    (hUY : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g g', g < g' → U j g ∪ Y j g ⊆ U j' g')
    (hmomQ : ∀ j g (Q : Finset (Site Λ)),
      Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
      ∀ u : ℝ, |u| ≤ r →
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef
            (fun _ : Site Λ ↦ Fin q) Ωt Q).isHermitian.eigenvalues u) ≤
          u * vonNeumannEntropy (FiniteProduct.reducedPure (fun _ : Site Λ ↦ Fin q) Ωt Q)
            (FiniteProduct.reducedPure_posSemidef (fun _ : Site Λ ↦ Fin q) Ωt Q).isHermitian +
              Kmom * u ^ 2)
    (hk : sharpUpper_uniformCompressedAt Ωt X d z a Kmom r c k ell) :
    let β := fun _ : Site Λ ↦ Fin q
    ∀ (N : ℕ) (ZO : Matrix (Config k
      (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) (Fin N) ℂ),
      ZOᴴ * ZO = 1 →
      ZO * ZOᴴ = symProj (copyPerm ((o : Option (Option (Site Λ))) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) →
      ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
      let v : EuclideanSpace ℂ (Config k
        (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) := WithLp.toLp 2
          (replicaPrevector Ωt d k ell ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      let W := replicaMetric (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)) (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun x ↦ some (some x))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
      let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun x ↦ some (some x)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ tree.eval (fun j ↦ ZOᴴ * A j g * ZO)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin ZOᴴ v)‖ ^ 2
      let entropy := fun Q : Finset (Site Λ) ↦ vonNeumannEntropy
        (FiniteProduct.reducedPure β Ωt Q)
        (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (d : ℝ) - Real.log z +
          2 * (1 / 4) * a * (∑ g, ∑ j, tree.weight j *
            (entropy (U j g) + entropy (U j g ∪ Y j g) - entropy (Y j g))) +
          24 * (1 / 4) * S.K * Kmom * a ^ 2 - 2 * (1 / 4) * S.K * Real.log z +
            Real.bellOverlapRemainder d c S.K k := by
  classical
  intro β N ZO hZO hZOZO tree
  exact hk N ZO hZO hZOZO S.K
    (ι := terminalFamily S.K S.m S.M (S.n * S.m)) U Y
    hXU hXY hUY hnest hmomQ tree (1 / 4) (by norm_num)

open Classical in
/-- Specialize the uniform QIC sharp estimate to the actual terminal regions.
The constant and replica threshold precede every symmetric coordinate and
terminal tree, and the original supplied label sequence is retained.
Source: `07-comparators.tex`, lines 383–418; `08-scanner.tex`, lines 400–474,
revision adc7f124. -/
private theorem eventually_actualTerminal_compressed_sharp_upper
    {q : ℕ} [NeZero q] {I : Type} [Fintype I] [LinearOrder I]
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I) (X : Finset (Site Λ))
    (a Kmom r : ℝ) (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q) X))
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ r →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2)) :
    let β := fun _ : Site Λ ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (FiniteProduct.splitEquiv β X) Ωt
    let z := Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
    0 < z →
    let d := E.card
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    (∀ᶠ k : ℕ in atTop,
      (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
        ‖WithLp.toLp 2
          (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
            (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
            (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
              (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) →
    (∀ j j' g g', g < g' → U j g ∪ Y j g ⊆ U j' g') →
    (∀ j g, Disjoint (U j g) (Y j g)) →
    (∀ j g, Disjoint X (U j g ∪ Y j g)) →
    ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (Real.bellOverlapRemainder d c S.K) atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop,
      ∀ (N : ℕ) (ZO : Matrix (Config k
        (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) (Fin N) ℂ),
        ZOᴴ * ZO = 1 →
        ZO * ZOᴴ = symProj (copyPerm ((o : Option (Option (Site Λ))) →
          addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) →
        ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
        let v : EuclideanSpace ℂ (Config k
          (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d))) := WithLp.toLp 2
            (replicaPrevector Ωt d k (ell k) ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
        let W := replicaMetric (addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)) (a / 2) k
        let Q := fun j g ↦ insert (some none)
          ((X ∪ U j g).image fun x ↦ some (some x))
        let F := fun j g ↦ insert none
          (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
        let ext := fun B : Finset (Site Λ) ↦ (B \ X).image fun x ↦ some (some x)
        let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
        let M := (List.ofFn fun g ↦ tree.eval (fun j ↦ ZOᴴ * A j g * ZO)).prod
        let Nsq := ‖toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin ZOᴴ v)‖ ^ 2
        let entropy := fun Q : Finset (Site Λ) ↦ vonNeumannEntropy
          (FiniteProduct.reducedPure β Ωt Q)
          (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian
        0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
          2 * Real.log (d : ℝ) - Real.log z +
            2 * (1 / 4) * a * (∑ g, ∑ j, tree.weight j *
              (entropy (U j g) + entropy (U j g ∪ Y j g) - entropy (Y j g))) +
            24 * (1 / 4) * S.K * Kmom * a ^ 2 - 2 * (1 / 4) * S.K * Real.log z +
              Real.bellOverlapRemainder d c S.K k := by
  classical
  intro β ΩX z hz d ψ hmass σ U Y hUYeq hnest hUY hXY
  have hXU : ∀ (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K),
      Disjoint X (U j g) :=
    fun j g ↦ (Finset.disjoint_union_right.mp (hXY j g)).1
  have hXY' : ∀ (j : terminalFamily S.K S.m S.M (S.n * S.m)) (g : Fin S.K),
      Disjoint X (Y j g) :=
    fun j g ↦ (Finset.disjoint_union_right.mp (hXY j g)).2
  have hmomQ := actualTerminal_sharpUpper_moments S Kmom r Ωt hmom hUYeq
  obtain ⟨c, hc, hlim, hu⟩ :=
    eventually_sharpUpper_uniformCompressed X a Kmom r ha har ha1 Ωt hΩt E ell hz hmass
  refine ⟨c, hc, hlim S.K, hu.mono ?_⟩
  intro k hk
  exact actualTerminal_sharpUpper_of_uniformCompressed S X a Kmom r z c Ωt d k (ell k)
    U Y hXU hXY' hUY hnest hmomQ hk

open Classical in
/-- The supplied-label sharp upper estimate at every actual fill and charge
root. The entropy contribution uses the actual terminal-tree weights, and the
quadratic moment cost is retained. The per-band weight is `a`, the metric
parameter is `a / 2`, and the comparison power is one quarter.
Source: `07-comparators.tex`, `comparator:sharp-upper`, lines 383–418;
`08-scanner.tex`, lines 416–474, revision adc7f124. -/
theorem eventually_actualScan_suppliedPrevector_sharp_upper
    {q : ℕ} [NeZero q] {I : Type} [Fintype I] [LinearOrder I]
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hm : 0 < S.m) (hM : 0 < S.M)
    (a Kmom r : ℝ) (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T)))
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (g : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist g),
        ∀ u : ℝ, |u| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist g),
          ∀ u : ℝ, |u| ≤ r →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + Kmom * u ^ 2)) :
    let X := S.A.filter fun x ↦ x.val ∈ T
    let β := fun _ : Site Λ ↦ Fin q
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (FiniteProduct.splitEquiv β X) Ωt
    let z := Matrix.IsHermitian.spectralRestrictionMass
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E
    0 < z →
    let d := E.card
    let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
    let pre : (k : ℕ) → Config k (fun v ↦ Fin (n v)) → ℂ := fun k ↦
      replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    (∀ᶠ k : ℕ in atTop,
      (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
        ‖WithLp.toLp 2
          (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
            (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
            (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
              (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
    ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (Real.bellOverlapRemainder d c S.K) atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (s : ℕ) (hs : s + 1 ≤ S.n * S.m) (p : ℝ),
        let σ := terminalPartition S (S.n * S.m)
        let gpost := fun j g ↦
          regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
            regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
              regionalEntropy Λ q Ωt (middle (σ j g))
        let p₀ := Set.projIcc (0 : ℝ) 1 zero_le_one p
        let bound := fun (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) ↦
          2 * Real.log (d : ℝ) - Real.log z +
            (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
              6 * (S.K : ℝ) * Kmom * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
                Real.bellOverlapRemainder d c S.K k
        let step : Fin (S.n * S.m) := ⟨s, Nat.lt_of_succ_le hs⟩
        let Nfill := Matrix.Transport.filteredNormSq
          ((S.actualFillData hm hM s).rootPath n (a / 2) k p) (pre k)
        let Ncharge := Matrix.Transport.filteredNormSq
          ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) (pre k)
        (0 < Nfill ∧ -Real.log Nfill / (k : ℝ) ≤
          bound (((S.actualFillData hm hM s).tree p₀).map
            (fillTerminalIndex S.K S.m S.M (S.n * S.m) step))) ∧
        (0 < Ncharge ∧ -Real.log Ncharge / (k : ℝ) ≤
          bound (((S.actualChargeData hm hM s).tree p₀).map
            (chargeTerminalIndex S.K S.m S.M (S.n * S.m) step))) := by
  classical
  intro X β ΩX z hz d n pre ψ hmass
  obtain ⟨hUYeq, hnest, hUY, hXY, hregions⟩ :=
    actualTerminal_sharpUpper_geometry hT S hdepth L hL
  have hzQ :
      0 < (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E :=
    hz
  have hd : 0 < d := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr fun hE ↦ by
      simp [hE, Matrix.IsHermitian.spectralRestrictionMass] at hzQ)
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨c, hc, hlim, hu⟩ := eventually_actualTerminal_compressed_sharp_upper
    S X a Kmom r ha har ha1 Ωt hΩt E ell hmom hz hmass hUYeq hnest hUY hXY
  refine ⟨c, hc, hlim, hu.mono fun k hk s hs p ↦ ?_⟩
  intro σ gpost p₀ bound step Nfill Ncharge
  exact actualScan_sharpUpper_of_compressed (q := q) (d := d) S hm hM X a Kmom z c ha Ωt
    k (ell k) hUYeq hXY hregions hk s hs p

end TNLean.PEPS.AreaLaw.Scan.CollarScan
