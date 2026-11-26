/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.ReindexSandwich
import QICLean.Circuit.Party.Compression.SourceSampling.Approximation
import TNLean.Network.IncidentFactor.OriginalGateSamplePhysicalSum
import TNLean.Network.DistributedContraction.SourceSampleIndices
import TNLean.Network.DistributedContraction.UnivDensityPairContraction

/-!
# Sampled distributed approximation from local gate expansions

The original gate operators are approximated by the recorded local monomial
lists at the prescribed accuracy. The sampling estimate for their rescaled
contraction circuit supplies normalized Schmidt data and a Gaussian sample
array. The exact distributed contraction represents its sampled physical
operator with the same total error bound.

The local tensors read the output of every party through its own readout: the
physical index and the discarded and auxiliary outputs of the party, on the
blocks of all parties, with one configuration at the exterior block. Read
together, these readouts are the readout of the physical density up to a
reordering of the configurations.

The statement concerns monomial lists supplied at this prescribed accuracy
and the physical error of their actual sampled contraction.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19,
137–175, 199–229, 342–381, 565–588 and 590–600.

It also contains the following results.

*
  `QuantumCircuit.Party.SourceCircuit.physicalSourceReplacedDensity_pure_sampled_eq_exterior_smul_contractedOperator`:
  the exact distributed contraction of the sampled physical density.
-/

section ActualSampledDistributedContraction

/-! # The exact distributed contraction of the sampled physical density

At every original nonempty gate occurrence, choose one of its participants
as the root of the shared ordered ket and bra label. The common pair samples
remain attached to their original source occurrences. The physical matrix
at a party is constructed directly from its incident labels and samples.
Each gate's averaging powers appear once in its root coefficient. The squared
modulus of the original empty-gate scalar remains outside the contraction,
and the partial trace of the readout of the exterior block stands beside it
as a separate tensor factor.

This is an exact representation of the sampled circuit. It asserts neither
an approximation error nor a polynomial bound on the virtual dimensions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker ComplexConjugate
open TNLean.Network

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] [Fintype P] {X Y : P → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
  {Phys Env : Option {_p : P // true = true} → Type} [∀ q, Fintype (Env q)]

open Classical in
/-- The actual sampled physical density is the distributed ordered ket and
bra contraction, with gate-owned averaging weights and the exterior scalar
retained multiplicatively, beside the partial trace of the exterior readout.
The root is derived from each gate's recorded participant set; no ambient
nonemptiness or factorization premise is added.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem physicalSourceReplacedDensity_pure_sampled_eq_exterior_smul_contractedOperator
    (K : ∀ q, Matrix (Phys q × Env q) (blockSystem (affectedOwner fun _ ↦ true) Y q) ℂ)
    (w : SourceCircuit X Y) (φ : ∀ s, EuclideanSpace ℂ (X s)) (k : ℕ)
    (lam : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Fin (min (w.sourceDims e).1 (w.sourceDims e).2) → ℝ)
    (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
    (ω : SourceGaussianSamples w k) :
    let e := Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true}) Phys Env
    let b := blockConfigEquiv (affectedOwner fun _ ↦ true) Y
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let T := fun (p : P) (η θ : OriginalGateLabelsAt w p)
      (j : DistributedOperatorContraction.SampleAt
        (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1) p → Fin k) ↦
      incidentSampledPhysicalFactor K w φ k lam E F p η θ ω (j ∘ partialSlotSampleEquiv w p)
    physicalSourceReplacedDensity w (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω)
        ((piKronecker K).submatrix e.symm b.symm) (euclideanOuterProduct ψ ψ) =
      (w.emptyGateScalar * conj w.emptyGateScalar) •
        reindex (exteriorConfigEquiv Phys).symm (exteriorConfigEquiv Phys).symm
          (partialTraceRight (K none * (K none)ᴴ) ⊗ₖ
            DistributedOperatorContraction.contractedOperator
              (Finset.univ : Finset w.nonemptyGateLocations) (fun g ↦ w.participants g.1)
              (sourceGateRoot w) (fun g _ ↦ sourceGateRoot_mem w g)
              (fun g ↦ w.branchLabels g.1 × w.branchLabels g.1) k
              (DistributedOperatorContraction.densityPairCoefficient
                (Gate := w.nonemptyGateLocations)
                (fun g ↦ w.branchLabels g.1) (fun g ↦ w.branchLabels g.1)
                (fun g ↦ w.branchCoefficient g.1) (fun g ↦ w.branchCoefficient g.1)
                (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card))
              (fun p ξζ j ↦ T p (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) j)) := by
  intro e b ψ T
  -- The network identity is stated with the classical equality test on the parties.
  obtain rfl : ‹DecidableEq P› = fun a b ↦ Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  have hActual := physicalSourceReplacedDensity_pure_sampled_eq_scalar_smul_originalGateSampleSum
    K w φ k lam E F ω
  dsimp only at hActual
  have hNetwork := DistributedOperatorContraction.contractedOperator_densityPair_univ_eq_double_sum
    (fun g : w.nonemptyGateLocations ↦ w.participants g.1)
    (sourceGateRoot w) (fun g _ ↦ sourceGateRoot_mem w g) k
    (fun g ↦ w.branchCoefficient g.1) (fun g ↦ w.branchCoefficient g.1)
    (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (w.participants g.1)).card) 1 T
  rw [one_smul, mul_one, ← inv_sampleSize_pow_allSourceSlots_eq_prod w k] at hNetwork
  rw [hActual, hNetwork, kronecker_smul, reindex_apply, reindex_apply, submatrix_smul, mul_smul,
    smul_comm]
  rfl

end QuantumCircuit.Party.SourceCircuit

end

end ActualSampledDistributedContraction

section ApproximateSampledNetworkApproximation

noncomputable section

open Matrix ManyBody QICLean.ComplexGaussian
open scoped Kronecker ComplexConjugate NNReal Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P] [Fintype P]

namespace SourceCircuit

/-- The physical basis at a block of all parties: one configuration at the exterior block and
`Fin (d p)` at the block of the party `p`. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–434 and 565–579. -/
abbrev blockPhys (d : P → ℕ) (q : Option {_p : P // true = true}) : Type :=
  Option.rec (motive := fun _ ↦ Type) PUnit (fun p ↦ Fin (d p.1)) q

/-- The traced-out basis at a block of all parties: one configuration at the exterior block and
`G p` at the block of the party `p`. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–434 and 565–579. -/
abbrev blockEnv (G : P → Type) (q : Option {_p : P // true = true}) : Type :=
  Option.rec (motive := fun _ ↦ Type) PUnit (fun p ↦ G p.1) q

instance instFintypeBlockPhys (d : P → ℕ) : ∀ q, Fintype (blockPhys d q)
  | none => inferInstanceAs (Fintype PUnit)
  | some p => inferInstanceAs (Fintype (Fin (d p.1)))

instance instDecidableEqBlockPhys (d : P → ℕ) : ∀ q, DecidableEq (blockPhys d q)
  | none => inferInstanceAs (DecidableEq PUnit)
  | some p => inferInstanceAs (DecidableEq (Fin (d p.1)))

instance instFintypeBlockEnv (G : P → Type) [∀ p, Fintype (G p)] :
    ∀ q, Fintype (blockEnv G q)
  | none => inferInstanceAs (Fintype PUnit)
  | some p => inferInstanceAs (Fintype (G p.1))

instance instDecidableEqBlockEnv (G : P → Type) [∀ p, DecidableEq (G p)] :
    ∀ q, DecidableEq (blockEnv G q)
  | none => inferInstanceAs (DecidableEq PUnit)
  | some p => inferInstanceAs (DecidableEq (G p.1))

omit [DecidableEq P] [Fintype P] in
/-- Every party is the only party of its own block. -/
theorem affectedOwner_all_eq_some_iff (p : {_p : P // true = true}) (u : P) :
    affectedOwner (fun _ ↦ true) u = some p ↔ u = p.1 := by
  simp only [affectedOwner, dite_true, Option.some.injEq]
  exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

/-- The readout at the blocks of all parties of a system split sitewise by `e p : Y p ≃
Fin (d p) × G p`: at the block of `p`, the configuration of `p` split by `e p`; at the exterior
block, which has one configuration, the only matrix entry. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–434 and 565–579. -/
noncomputable def blockReadout {Y : P → Type} [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    {d : P → ℕ} {G : P → Type} [∀ p, DecidableEq (G p)]
    (e : ∀ p, Y p ≃ Fin (d p) × G p) :
    ∀ q, Matrix (blockPhys d q × blockEnv G q)
      (blockSystem (affectedOwner fun _ ↦ true) Y q) ℂ
  | none => of fun _ _ ↦ 1
  | some p => of fun r z ↦
    if (blockFiberEquiv (affectedOwner fun _ ↦ true) (affectedOwner_all_eq_some_iff p) Y).trans
      (e p.1) z = r then 1 else 0

/-- The physical configurations at the blocks of all parties are the physical configurations of
the parties. -/
def blockPhysEquiv (d : P → ℕ) : (∀ q, blockPhys d q) ≃ ∀ p, Fin (d p) :=
  (exteriorConfigEquiv (blockPhys d)).trans (Equiv.punitProd _)

/-- The exterior partial trace of the exterior readout is one. -/
theorem partialTraceRight_blockReadout_none {Y : P → Type} [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] {d : P → ℕ} {G : P → Type} [∀ p, DecidableEq (G p)]
    (e : ∀ p, Y p ≃ Fin (d p) × G p) :
    partialTraceRight (blockReadout e none * (blockReadout e none)ᴴ) = 1 := by
  let _ := uniqueBlockSystemNone Y
  ext a b
  obtain rfl : a = b := Subsingleton.elim (α := PUnit) a b
  rw [partialTraceRight_apply]
  change ∑ _k : PUnit, ∑ _z : blockSystem (affectedOwner fun _ ↦ true) Y none,
    (1 : ℂ) * star (1 : ℂ) = 1
  simp

end SourceCircuit

namespace EffectCircuit

open TNLean.Network SourceCircuit

variable {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The readout of the replacement at the blocks of all parties is its readout through the
physical readout, up to a reordering of the rows. -/
private theorem piKronecker_blockReadout_eq {A : P → Type} [∀ p, Fintype (A p)]
    [∀ p, DecidableEq (A p)] (d : P → ℕ) (V : P → Type) [∀ p, Fintype (V p)]
    [∀ p, DecidableEq (V p)] :
    let e : ∀ p, A p × (Fin (d p) × V p) ≃ Fin (d p) × (A p × V p) :=
      fun _ ↦ Equiv.prodLeftComm _ _ _
    let σ₂ : (∀ q, blockEnv (fun p ↦ A p × V p) q) ≃ Config V × Config A :=
      (exteriorConfigEquiv (blockEnv fun p ↦ A p × V p)).trans ((Equiv.punitProd _).trans
        ((Equiv.arrowProdEquivProdArrow P A V).trans (Equiv.prodComm _ _)))
    (piKronecker (blockReadout e)).submatrix
        (Equiv.arrowProdEquivProdArrow _ (blockPhys d) (blockEnv fun p ↦ A p × V p)).symm
        (blockConfigEquiv (affectedOwner fun _ ↦ true) (fun p ↦ A p × physicalSystem d V p)).symm =
      reindex ((blockPhysEquiv d).prodCongr σ₂).symm (Equiv.refl _)
        (extendedReadout (A := A) (physicalReadout d V)) := by
  intro e σ₂
  ext ⟨ph, en⟩ y
  rw [submatrix_apply, piKronecker_apply, Fintype.prod_option]
  simp only [blockReadout, Matrix.of_apply, one_mul]
  rw [Finset.prod_boole]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.refl_symm,
    Equiv.coe_refl, id_eq, extendedReadout, physicalReadout, kronecker_apply,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.prodAssoc_symm_apply, Equiv.trans_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.arrowProdEquivProdArrow_apply,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, one_apply,
    ite_zero_mul_ite_zero]
  simp only [Finset.mem_univ, Equiv.trans_apply, blockFiberEquiv_apply,
    blockConfigEquiv_symm_apply, Subtype.forall, mul_one, σ₂, e, blockPhysEquiv,
    exteriorConfigEquiv, Equiv.coe_fn_mk, Equiv.punitProd_apply, Equiv.prodLeftComm_apply,
    Equiv.arrowProdEquivProdArrow_symm_apply, funext_iff, Prod.ext_iff, Equiv.prodComm_apply,
    Prod.fst_swap, Prod.snd_swap, Equiv.arrowProdEquivProdArrow_apply, forall_const]
  by_cases H : ∀ a : P, (y a).2.1 = ph (some ⟨a, rfl⟩) ∧ (y a).1 = (en (some ⟨a, rfl⟩)).1 ∧
      (y a).2.2 = (en (some ⟨a, rfl⟩)).2
  · rw [ite_eq_left fun a _ ↦ H a,
      ite_eq_left ⟨fun x ↦ ⟨(H x).1.symm, (H x).2.2.symm⟩, fun x ↦ (H x).2.1.symm⟩]
  · rw [ite_eq_right fun h ↦ H fun a ↦ h a trivial, ite_eq_right]
    rintro ⟨h1, h2⟩
    exact H fun a ↦ ⟨(h1 a).1.symm, (h2 a).symm, (h1 a).2.symm⟩

open Classical in
/-- **Local gate expansions at the prescribed approximation budget give an actual sampled
distributed contraction within physical trace-norm error `ε` of the original gate operators.**
The original local approximation hypothesis is retained. The local tensors read the output of
each party through its own readout (`blockReadout`). Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 17–19, 137–175, 199–229, 342–381, 565–588 and 590–600. -/
theorem exists_sampled_contractedOperator_approximate_error_le
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1) (d : P → ℕ) (V : P → Type)
    [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)] (w : EffectCircuit X (physicalSystem d V))
    (G : w.GateMaps) {r M lifetime : ℕ} (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hb : w.IsExpansionBounded r (B : ℝ)) (hcount : w.numGates ≤ M)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime) (hphysical : ∀ p, (d p : ℝ≥0) ≤ D)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (happrox : w.IsGateApproximation (sourceGateBudget (ε / 2) M) G) :
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) M).le G happrox
    let R := W.replacement (sourceGateBudget_pos hε M)
      (w.isExpansionBounded_rescaledOriginal (sourceGateBudget_pos (half_pos hε) M).le G
        happrox hb)
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := binomialSampleCount (max 1 (Fintype.card R.sourceLocations)) Q ε
    ∃ (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
      (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (R.leftBasis s) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
      (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (R.rightBasis s) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (R.sourceVectorAt s ξ).ofLp) ∧
      ∃ ω : SourceCircuit.SourceGaussianSamples R k,
        let T : (p : P) → SourceCircuit.OriginalGateLabelsAt R p →
            SourceCircuit.OriginalGateLabelsAt R p →
            (DistributedOperatorContraction.SampleAt
              (Finset.univ : Finset R.nonemptyGateLocations)
              (fun g ↦ R.participants g.1) p → Fin k) → Matrix (Fin (d p)) (Fin (d p)) ℂ :=
          fun p η θ j ↦ SourceCircuit.incidentSampledPhysicalFactor
            (blockReadout fun _ ↦ Equiv.prodLeftComm _ _ _) R φ k lam E F p η θ ω
            (j ∘ SourceCircuit.partialSlotSampleEquiv R p)
        rectangularTraceNorm
          ((R.emptyGateScalar * conj R.emptyGateScalar) •
              DistributedOperatorContraction.contractedOperator
                (Finset.univ : Finset R.nonemptyGateLocations) (fun g ↦ R.participants g.1)
                (SourceCircuit.sourceGateRoot R) (fun g _ ↦ SourceCircuit.sourceGateRoot_mem R g)
                (fun g ↦ R.branchLabels g.1 × R.branchLabels g.1) k
                (DistributedOperatorContraction.densityPairCoefficient
                  (Gate := R.nonemptyGateLocations)
                  (fun g ↦ R.branchLabels g.1) (fun g ↦ R.branchLabels g.1)
                  (fun g ↦ R.branchCoefficient g.1) (fun g ↦ R.branchCoefficient g.1)
                  (fun g ↦ (k : ℂ)⁻¹ ^ (pairSampleLabels (R.participants g.1)).card))
                (fun p ξζ j ↦ T p (fun g ↦ (ξζ g).1) (fun g ↦ (ξζ g).2) j) -
            w.physicalDensityWithGateMaps G (physicalReadout d V) ψ) ≤ ε := by
  classical
  intro ψ W R Q k
  obtain ⟨lam, E, F, hframes, ω, hω⟩ := w.exists_sourceSample_approximate_error_le φ hφ d V G
    B D hB hD hb hcount hlifetime hphysical ε hε hεone happrox
  refine ⟨lam, E, F, hframes, ω, ?_⟩
  intro T
  have hN := physicalSourceReplacedDensity_pure_sampled_eq_exterior_smul_contractedOperator
    (blockReadout fun _ ↦ Equiv.prodLeftComm _ _ _) R φ k lam E F ω
  dsimp only at hN hω
  have hσ : ∀ {α α' β β' : Type} (e₁ : α ≃ α') (e₂ : β ≃ β'),
      e₁.prodCongr e₂ = (e₁.symm.prodCongr e₂.symm).symm := fun _ _ ↦ by
    rw [Equiv.prodCongr_symm, Equiv.symm_symm, Equiv.symm_symm]
  have hD := piKronecker_blockReadout_eq (A := EffectCircuit.auxiliary
    (stackLength r (B : ℝ) (sourceGateBudget ε M)) W.toEffectCircuit) d V
  dsimp only at hD
  rw [hD, physicalSourceReplacedDensity, reindex_mul_mul_conjTranspose, Equiv.refl_symm,
    reindex_refl_refl, reindex_apply, Equiv.symm_symm, hσ, partialTraceRight_submatrix_prod_equiv,
    Equiv.symm_symm, ← physicalSourceReplacedDensity, partialTraceRight_blockReadout_none] at hN
  have hext := congrArg (fun A ↦ A.submatrix (blockPhysEquiv d).symm (blockPhysEquiv d).symm) hN
  simp only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at hext
  rw [hext] at hω
  convert hω using 3
  ext x y
  simp only [blockPhysEquiv, submatrix_apply, Matrix.smul_apply, reindex_apply, Equiv.symm_symm,
    Equiv.symm_trans_apply, Equiv.apply_symm_apply, Equiv.punitProd_symm_apply,
    kroneckerMap_apply, one_apply_eq, one_mul, T]

end EffectCircuit

end QuantumCircuit.Party

end

end ApproximateSampledNetworkApproximation
