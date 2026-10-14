/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FillTransport
import TNLean.PEPS.AreaLaw.Scan.ActualChargeData
import TNLean.PEPS.AreaLaw.Scan.FrontPrefixFamily
import TNLean.PEPS.AreaLaw.Scan.StatusCutBounds
import TNLean.PEPS.AreaLaw.Scan.ReceivingRegions
import TNLean.PEPS.AreaLaw.Scan.AugmentedRootCompression
import TNLean.PEPS.AreaLaw.Scan.AugmentedReplicaPrevectorProperties
import QICLean.Algebra.ProjectionRangeIsometry
import QICLean.Representation.ReplicaPrevectorRoughUpper

/-!
# A uniform rough upper bound along the actual scanner

The actual fill and charge interpolations obey one upper bound, with the
same supplied replica prevector and label sequence at every time. The
constant and replica threshold are chosen before the scan time and the
interpolation parameter. The finite family of terminal partitions retains
the original history trees, conditional choices, and band order.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:rough-upper`, lines 332–381;
`08-scanner.tex`, lines 457–474 and 755–769, revision `adc7f124`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- Completed times range through the horizon, whereas pre-charge times are
strictly smaller. Source: `08-scanner.tex`, lines 83–154, adc7f124. -/
private abbrev terminalFamily (K m M H : ℕ) :=
  (Σ s : Fin (H + 1), History K m M s.val) ⊕
    (Σ s : Fin H, History K m M s.val)

/-- The family keeps the literal completed or pre-charge physical status.
Source: `08-scanner.tex`, lines 83–154, adc7f124. -/
private def terminalPartition (S : CollarScan V I) (H : ℕ) :
    terminalFamily S.K S.m S.M H → Fin S.K → PhysicalPartition V :=
  fun j g ↦ match j with
    | Sum.inl ⟨_, h⟩ => S.state h g
    | Sum.inr ⟨_, h⟩ => S.oldChargeState h g

/-- A charge appends its actual choice to the completed history.
Source: `08-scanner.tex`, lines 145–154 and 416–451, adc7f124. -/
private def chargeTerminalIndex (K m M H : ℕ) (s : Fin H) :
    (Σ _h : History K m M s.val, Option (ChargeChoices K M)) →
      terminalFamily K m M H :=
  fun j ↦ match j with
    | ⟨h, none⟩ => Sum.inr ⟨s, h⟩
    | ⟨h, some c⟩ => Sum.inl ⟨s.succ, extendHistory h c⟩

/-- Charge terminals retain their actual physical partitions under the
finite-family indexing. Source: `08-scanner.tex`, lines 145–154 and 416–451,
adc7f124. -/
private theorem actualChargeData_leafPart_terminalPartition
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
    (H : ℕ) (s : Fin H)
    (j : Σ _h : History S.K S.m S.M s.val, Option (ChargeChoices S.K S.M))
    (g : Fin S.K) :
    (S.actualChargeData hm hM s.val).leafPart j g =
      augmentedPartition
        (terminalPartition S H (chargeTerminalIndex S.K S.m S.M H s j) g) := by
  rcases j with ⟨h, c⟩
  cases c
  case some c => exact S.chargeTransportData_new _ _ h c g
  rfl


/-- A fill retains its completed history or its following pre-charge status.
Source: `08-scanner.tex`, lines 83–154 and 416–451, adc7f124. -/
private def fillTerminalIndex (K m M H : ℕ) (s : Fin H) :
    (Σ _h : History K m M s.val, Option Unit) → terminalFamily K m M H :=
  fun j ↦ match j with
    | ⟨h, none⟩ => Sum.inl ⟨s.castSucc, h⟩
    | ⟨h, some _⟩ => Sum.inr ⟨s, h⟩

/-- Fill terminals retain their actual physical partitions under the
finite-family indexing. Source: `08-scanner.tex`, lines 83–154 and 416–451,
adc7f124. -/
private theorem actualFillData_leafPart_terminalPartition
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
    (H : ℕ) (s : Fin H)
    (j : Σ _h : History S.K S.m S.M s.val, Option Unit)
    (g : Fin S.K) :
    (S.actualFillData hm hM s.val).leafPart j g =
      augmentedPartition
        (terminalPartition S H (fillTerminalIndex S.K S.m S.M H s j) g) := by
  rcases j with ⟨h, _ | c⟩
  case some h c => exact S.fillTransportData_new _ h c g
  rfl


end TNLean.PEPS.AreaLaw.Scan.CollarScan

open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology symmDiff

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open Classical in
/-- The rough upper estimate for every actual fill and charge interpolation
through the fixed fill horizon. The same selected labels and physical
prevector occur at every time. The constant and replica threshold precede
the scan time and interpolation parameter. The per-band weight is any
positive a, the metric parameter is a/2, and the total weight is aK.
Source: area-law manuscript, `07-comparators.tex`, `comparator:rough-upper`,
lines 332–381; `08-scanner.tex`, lines 457–474 and 755–769,
revision adc7f124. -/
theorem eventually_actualScan_suppliedPrevector_rough_upper
    {q : ℕ} [NeZero q] {I : Type} [Fintype I] [LinearOrder I]
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    (hm : 0 < S.m) (hM : 0 < S.M)
    (a : ℝ) (ha : 0 < a)
    (hn : 0 < S.n) (hr : S.r₀ ≤ S.D)
    (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m)
    (L : ℕ) (hL : 8 * S.K * S.m ≤ L)
    (hrows : ∀ j : ℕ, 1 ≤ j → j ≤ L →
      (ambientDilation T j \ ambientDilation T (j - 1)).card ≤ S.n)
    (Ωt : EuclideanSpace ℂ (Site Λ → Fin q)) (hΩt : ‖Ωt‖ = 1)
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ ↦ Fin q)
      (S.A.filter fun x ↦ x.val ∈ T)))
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Bsh : ℝ)
    (hsh : ∀ j : Fin (L + 1),
      FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ωt
        (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤ Bsh) :
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
      ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, s + 1 ≤ S.n * S.m → ∀ p : ℝ,
        let Nfill := Matrix.Transport.filteredNormSq
          ((S.actualFillData hm hM s).rootPath n (a / 2) k p) (pre k)
        let Ncharge := Matrix.Transport.filteredNormSq
          ((S.actualChargeData hm hM s).rootPath n (a / 2) k p) (pre k)
        let B := 2 * Real.log (d : ℝ) - Real.log z +
          (a * (S.K : ℝ)) * (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ))) +
            Real.bellOverlapRemainder d c S.K k
        (0 < Nfill ∧ -Real.log Nfill / (k : ℝ) ≤ B) ∧
        (0 < Ncharge ∧ -Real.log Ncharge / (k : ℝ) ≤ B) := by
  classical
  intro X β ΩX z hz d n pre ψ hmass
  let regions := List.ofFn fun j : Fin (L + 1) ↦
    positiveDepthPrefix S.A S.depth (j.val : ℤ)
  have hnested : regions.Pairwise (fun D D' ↦ D ⊆ D' ∨ D' ⊆ D) :=
    List.pairwise_ofFn.mpr (fun {i j} hij ↦ Or.inl
      (positiveDepthPrefix_mono S.A S.depth (by exact_mod_cast (Nat.le_of_lt hij))))
  have hzQ :
      0 < (FiniteProduct.reducedPure_posSemidef β Ωt X).isHermitian.spectralRestrictionMass E :=
    hz
  have hu :=
    FiniteProduct.eventually_suppliedReplicaPrevector_rough_upper
      (S := terminalFamily S.K S.m S.M (S.n * S.m)) β Ωt X E hΩt hzQ
  specialize hu regions
  have hdepthX : ∀ x ∈ X, S.depth x ≤ 0 := fun x hx ↦ by
    simpa only [hdepth, Nat.cast_zero] using
      (ambientDepth_le_iff_mem_dilation T hT x.val 0).mpr
        ((ambientDilation_zero T).symm ▸ (Finset.mem_filter.mp hx).2)
  have hdisjoint : ∀ D ∈ regions, Disjoint X D :=
    List.forall_mem_ofFn_iff.mpr fun j ↦ Finset.disjoint_left.mpr fun x hx hx' ↦
      (not_lt_of_ge (hdepthX x hx)) (Finset.mem_filter.mp hx').2.1
  specialize hu hnested hdisjoint ell (t := a / 2) (div_pos ha zero_lt_two)
  obtain ⟨c, hc, hu⟩ := hu (hmass.mono fun k hk ↦ by
    simpa only [Nat.cast_pow, one_div,
      TensorPower.norm_sq_labelProj_compressedTypicalSite_prod β X k Ωt E (ell k)] using! hk)
  refine ⟨c, hc, Real.tendsto_bellOverlapRemainder d c S.K,
    hu.mono fun k hk s hs p ↦ ?_⟩
  let σ : terminalFamily S.K S.m S.M (S.n * S.m) → Fin S.K →
      PhysicalPartition (Site Λ) := terminalPartition S (S.n * S.m)
  have hmiddle : ∀ j g x, σ j g x = none → 0 < S.depth x := fun
    | Sum.inl ⟨r, h⟩, g, x, hx =>
      lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
        (Finset.mem_Icc.mp (S.state_depth_bounds h g hL x hx)).1
    | Sum.inr ⟨r, h⟩, g, x, hx =>
      lt_of_lt_of_le (by decide : (0 : ℤ) < 1)
        (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hx)).1
  let U := fun j g ↦ positiveNear S.depth (σ j g)
  let Y := fun j g ↦ middle (σ j g)
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
  have hd : 0 < d := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr fun hE ↦ by
      simp [hE, Matrix.IsHermitian.spectralRestrictionMass] at hzQ)
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hlogCard (B : Finset (Site Λ)) (hB : B.card ≤ 3 * S.n * S.D) :
      1 + Real.log (Fintype.card (FiniteProduct.Configuration β B)) ≤
        1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ) := by
    simpa only [β, FiniteProduct.Configuration, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_coe, Nat.cast_pow, Real.log_pow,
      Nat.cast_mul, Nat.cast_ofNat] using
      add_le_add (le_refl (1 : ℝ))
        (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr hB : (B.card : ℝ) ≤ ((3 * S.n * S.D : ℕ) : ℝ))
          (Real.log_natCast_nonneg q))
  have hpref : ∀ j g, ∃ Dnear ∈ regions, ∃ Dfar ∈ regions,
      Dnear ⊆ positiveNear S.depth (σ j g) ∧
      positiveNearMiddle S.depth (σ j g) ⊆ Dfar ∧
      (positiveNear S.depth (σ j g) ∆ Dnear).card ≤ 3 * S.n * S.D ∧
      (positiveNearMiddle S.depth (σ j g) ∆ Dfar).card ≤ 3 * S.n * S.D := fun
    | Sum.inl ⟨r, h⟩, g => by
      obtain ⟨hnear, hfar, _, _, hnearCard, hfarCard⟩ :=
        S.state_prefix_approximation_domainGraph hT hgraph hdepth h g hn
          (Nat.le_of_lt_succ r.isLt) hr hDpos hD hL hrows
      have hmem := S.front_positiveDepthPrefix_mem_fixed_family hn hL g (h.1 g) r.val
        (Nat.le_of_lt_succ r.isLt)
      exact ⟨_, (List.mem_ofFn' _ _).mpr hmem.1, _, (List.mem_ofFn' _ _).mpr hmem.2,
        hnear, hfar, hnearCard, hfarCard⟩
    | Sum.inr ⟨r, h⟩, g => by
      obtain ⟨hnear, hfar, _, _, hnearCard, hfarCard⟩ :=
        S.oldChargeState_prefix_approximation_domainGraph hT hgraph hdepth h g hn
          (Nat.succ_le_of_lt r.isLt) hr hDpos hD hL hrows
      have hmem := S.front_positiveDepthPrefix_mem_fixed_family hn hL g (h.1 g) (r.val + 1)
        (Nat.succ_le_of_lt r.isLt)
      exact ⟨_, (List.mem_ofFn' _ _).mpr hmem.1, _, (List.mem_ofFn' _ _).mpr hmem.2,
        hnear, hfar, hnearCard, hfarCard⟩
  have hmatch : ∀ j g (Q : Finset (Site Λ)),
      Q = U j g ∨ Q = U j g ∪ Y j g →
      ∃ D ∈ regions, (D ⊆ Q ∨ Q ⊆ D) ∧
        1 + Real.log (Fintype.card (FiniteProduct.Configuration β (D ∆ Q))) ≤
          1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ) := fun j g Q hQ => by
    obtain ⟨Dnear, hDnear, Dfar, hDfar, hnear, hfar, hnearCard, hfarCard⟩ := hpref j g
    rcases hQ with rfl | rfl
    · exact ⟨Dnear, hDnear, Or.inl hnear,
        hlogCard _ (by simpa only [U, symmDiff_comm] using hnearCard)⟩
    · exact ⟨Dfar, hDfar, Or.inr (by simpa only [hUYeq] using hfar),
        hlogCard _ (by simpa only [hUYeq, symmDiff_comm] using hfarCard)⟩
  have hsh' : ∀ D ∈ regions, FiniteProduct.entropy β Ωt D ≤ Bsh :=
    List.forall_mem_ofFn_iff.mpr hsh
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
  have hupper (T' : Matrix.MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) :=
    hk N ZO hZO hZOZO S.K U Y hUY hnest hXY T' Bsh
      (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ)) hsh' hmatch
      (1 / 4) (by norm_num)
  have hregions : ∀ j g,
      receiving (σ j g) false = X ∪ positiveNear S.depth (σ j g) ∧
      receiving (σ j g) false ∪ middle (σ j g) =
        X ∪ positiveNearMiddle S.depth (σ j g) ∧
      receiving (σ j g) true = (X ∪ positiveNearMiddle S.depth (σ j g))ᶜ := fun
    | Sum.inl ⟨_, h⟩, g => state_receiving_regions hT S hdepth h g
    | Sum.inr ⟨_, h⟩, g => oldChargeState_receiving_regions hT S hdepth h g
  have hbound {Hist : Type} [DecidableEq Hist] {Choice : Hist → Type}
      [∀ h, DecidableEq (Choice h)]
      (D : ReplicaTransport.TransportData (Site Λ ⊕ Bool) S.K Hist Choice)
      (hD : D.IsAdmissible) (hcomm : D.CrossBandCommute n (a / 2) k)
      (f : (Σ h, Option (Choice h)) → terminalFamily S.K S.m S.M (S.n * S.m))
      (hparts : ∀ j g, D.leafPart j g = augmentedPartition (σ (f j) g)) :
      let Nsq := Transport.filteredNormSq (D.rootPath n (a / 2) k p) (pre k)
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (d : ℝ) - Real.log z +
          a * (S.K : ℝ) *
            (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ))) +
          Real.bellOverlapRemainder d c S.K k := by
    have hroot := (rootPath_augmented_compressed_bandProduct q d D hD
      (div_pos ha zero_lt_two).le k N hcomm ZS hZS hZSZS (pre k) hsym p).2.2.2.1
    have hestimate := hupper ((D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map f)
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
    have hcoef : 8 * (1 / 4) * (a / 2) * (S.K : ℝ) = a * (S.K : ℝ) := by
      ring
    rw [hroot]
    simp only [Matrix.MeanTree.eval_map] at hestimate
    simp only [e] at hpre
    simpa only [hP, hF, hY, hpre, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, hcoef, ZO, e, β, d] using! hestimate
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
