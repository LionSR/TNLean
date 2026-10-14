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

open Classical in
/-- The fixed terminal family has the common ordered regions and marginal
moments used in the sharp upper comparison. This preparation precedes the
replica count and the actual interpolation tree.
Source: `07-comparators.tex`, lines 70–85 and 383–418;
`08-scanner.tex`, lines 83–154 and 400–474, revision adc7f124. -/
private theorem actualTerminal_sharpUpper_data
    {q : ℕ} [NeZero q] {I : Type} [Fintype I] [LinearOrder I]
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (Kmom r : ℝ) (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
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
    let X := S.A.filter fun x ↦ x.val ∈ T
    let σ := terminalPartition S (S.n * S.m)
    let U := fun j g ↦ positiveNear S.depth (σ j g)
    let Y := fun j g ↦ middle (σ j g)
    (∀ j g, U j g ∪ Y j g = positiveNearMiddle S.depth (σ j g)) ∧
    (∀ j j' g g', g < g' → U j g ∪ Y j g ⊆ U j' g') ∧
    (∀ j g, Disjoint (U j g) (Y j g)) ∧
    (∀ j g, Disjoint X (U j g ∪ Y j g)) ∧
    (∀ j g (Q : Finset (Site Λ)),
      Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
      ∀ u : ℝ, |u| ≤ r →
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian.eigenvalues u) ≤
          u * vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
            (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian + Kmom * u ^ 2) ∧
    (∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ) := by
  classical
  intro β X σ U Y
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
  have hmomQ : ∀ j g (Q : Finset (Site Λ)),
      Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
      ∀ u : ℝ, |u| ≤ r →
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian.eigenvalues u) ≤
          u * vonNeumannEntropy (FiniteProduct.reducedPure β Ωt Q)
            (FiniteProduct.reducedPure_posSemidef β Ωt Q).isHermitian + Kmom * u ^ 2 := by
    intro j g Q hQ u hu
    have hmem : Q ∈ statusMarginalRegions S.depth (σ j g) := by
      rcases hQ with rfl | rfl | rfl
      · simp [statusMarginalRegions, U]
      · simp [statusMarginalRegions, hUYeq]
      · simp [statusMarginalRegions, Y]
    simpa only [regionalEntropy_eq_finiteProduct, FiniteProduct.entropy,
      reducedState_eq_finiteProduct, β] using! hmomStatus j g Q hmem u hu
  have hregions : ∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ := fun
    | Sum.inl ⟨_, h⟩, g => state_receiving_regions hT S hdepth h g
    | Sum.inr ⟨_, h⟩, g => oldChargeState_receiving_regions hT S hdepth h g
  exact ⟨hUYeq, hnest, hUY, hXY, hmomQ, hregions⟩

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
  have hzQ :
      0 < (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E :=
    hz
  obtain ⟨c, hc, hlim, hu⟩ :=
    FiniteProduct.eventually_suppliedReplicaPrevector_sharp_upper
      (K := Kmom) β Ωt X E hΩt hzQ ha har ha1 ell hmass
  refine ⟨c, hc, hlim S.K, hu.mono fun k hk s hs p ↦ ?_⟩
  intro σ gpost p₀ bound step Nfill Ncharge
  let U := fun j g ↦ positiveNear S.depth (σ j g)
  let Y := fun j g ↦ middle (σ j g)
  obtain ⟨hUYeq, hnest, hUY, hXY, hmomQ, hregions⟩ :=
    actualTerminal_sharpUpper_data hT S hdepth Kmom r L hL Ωt hmom
  have hd : 0 < d := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr fun hE ↦ by
      simp [hE, Matrix.IsHermitian.spectralRestrictionMass] at hzQ)
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨N, ZS, hZS, hZSZS⟩ :=
    (isStarProjection_symProj
      (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)).exists_matrix_range_isometry
  let e := augmentedReplicaConfigurationEquiv (V := Site Λ) q d k
  let ZO := ZS.submatrix e (id : Fin N → Fin N)
  have hZO : ZOᴴ * ZO = 1 :=
    Matrix.IsIsometry.reindex ZS hZS e.symm (Equiv.refl (Fin N))
  have hSymm :
      symProj (copyPerm ((o : Option (Option (Site Λ))) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) =
      (symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)).submatrix e e := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      (symProj_of_intertwine e.symm
        (φ := copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k)
        (ψ := copyPerm ((o : Option (Option (Site Λ))) →
          addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k)
        (fun σ x ↦ funext fun j ↦ rfl))
  have hZOZO : ZO * ZOᴴ =
      symProj (copyPerm ((o : Option (Option (Site Λ))) →
        addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d) o) k) := by
    simpa only [ZO, Matrix.conjTranspose_submatrix, Equiv.coe_refl] using
      ((Matrix.submatrix_mul_equiv ZS ZSᴴ e (Equiv.refl (Fin N)) e).trans
        (congrArg (fun P : Matrix (Config k (fun v ↦ Fin (n v)))
          (Config k (fun v ↦ Fin (n v))) ℂ ↦ P.submatrix e e) hZSZS)).trans hSymm.symm
  have hsym : symProj (copyPerm ((v : Site Λ ⊕ Bool) → Fin (n v)) k) *ᵥ pre k = pre k :=
    symProj_mulVec_augmentedReplicaPrevector q d k Ωt (ell k)
  have hpre : pre k ∘ e = replicaPrevector Ωt d k (ell k) ∘
      globalReplicaCopiesEquiv β (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, e, Equiv.symm_comp_self, Function.comp_id, β]
  have hupper (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) :=
    hk N ZO hZO hZOZO S.K U Y
      (fun j g ↦ (Finset.disjoint_union_right.mp (hXY j g)).1)
      (fun j g ↦ (Finset.disjoint_union_right.mp (hXY j g)).2)
      hUY hnest hmomQ tree (1 / 4) (by norm_num)
  have hbound {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ h, DecidableEq (Choice h)]
      (D : ReplicaTransport.TransportData (Site Λ ⊕ Bool) S.K Hist Choice)
      (hD : D.IsAdmissible) (hcomm : D.CrossBandCommute n (a / 2) k)
      (f : (Σ h, Option (Choice h)) → terminalFamily S.K S.m S.M (S.n * S.m))
      (hparts : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g)) :
      let Nsq := Transport.filteredNormSq (D.rootPath n (a / 2) k p) (pre k)
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤ bound ((D.tree p₀).map f) := by
    have hroot := (rootPath_augmented_compressed_bandProduct q d D hD
      (div_pos ha zero_lt_two).le k N hcomm ZS hZS hZSZS (pre k) hsym p).2.2.2.1
    have hestimate := hupper ((D.tree p₀).map f)
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
    have hcoef : 2 * (1 / 4 : ℝ) * a = a / 2 := by ring
    have hquad : 24 * (1 / 4 : ℝ) * (S.K : ℝ) * Kmom * a ^ 2 =
        6 * (S.K : ℝ) * Kmom * a ^ 2 := by ring
    have hmasscoef : 2 * (1 / 4 : ℝ) * (S.K : ℝ) = (S.K : ℝ) / 2 := by ring
    rw [hroot]
    simp only [Matrix.MeanTree.eval_map] at hestimate
    simp only [e] at hpre
    simpa only [hP, hF, hY, hpre, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, hcoef, hquad, hmasscoef, ZO, e, β, d, bound, gpost,
      regionalEntropy_eq_finiteProduct, FiniteProduct.entropy, U, Y, p₀, hUYeq] using! hestimate
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

end TNLean.PEPS.AreaLaw.Scan.CollarScan
