/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteSetTruncationGap
import TNLean.PEPS.AreaLaw.MarginalTails
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling
import QICLean.Representation.ReplicaTransport.Setup

/-!
# Actual truncated Hamiltonian terms for replica transport

Each labelled term is the positive normalized absolute value of the centered
spectral filter of the corresponding local interaction, truncated at the
scanner's variable radius. It acts as the identity on both auxiliary factors,
whose dimensions may differ. Its designated support contains physical sites only.

The positivity, contraction and support hypotheses of energy transport are
proved from the local interaction and its admissible supports. The construction
does not require a ground-state equation, does not shift individual terms by a
global ground energy, and makes no kernel claim about the truncated terms.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`03-quasilocal.tex`, lines 417–426, and `06-transport.tex`, lines 335–358,
at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open Entropy TensorPower TensorPower.ReplicaTransport SpectralFilter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Physical dimension `q` and the independently specified dimensions of C and R.
Source: `06-transport.tex`, the augmented tensor factors. -/
abbrev augmentedDimensions (q : ℕ) (aux : Bool → ℕ) : V ⊕ Bool → ℕ :=
  Sum.elim (fun _ => q) aux

instance {q : ℕ} {aux : Bool → ℕ} [NeZero q] [∀ b, NeZero (aux b)]
    (v : V ⊕ Bool) : NeZero (augmentedDimensions q aux v) := by
  cases v <;> dsimp [augmentedDimensions] <;> infer_instance

/-- A designated physical support, with neither auxiliary factor adjoined.
Source: `06-transport.tex`, lines 335–337. -/
def physicalRegion (D : Finset V) : Finset (V ⊕ Bool) :=
  D.map ⟨Sum.inl, Sum.inl_injective⟩

/-- Extend a physical operator by the identity on the joint C and R factor.
The product is indexed by the two independent auxiliary dimensions.
Source: `06-transport.tex`, lines 335–337. -/
def augmentOperator (q : ℕ) (aux : Bool → ℕ)
    (h : Matrix (V → Fin q) (V → Fin q) ℂ) :
    Matrix (SiteConfig (augmentedDimensions (V := V) q aux))
      (SiteConfig (augmentedDimensions (V := V) q aux)) ℂ :=
  let e : SiteConfig (augmentedDimensions (V := V) q aux) ≃
      (V → Fin q) × ((b : Bool) → Fin (aux b)) :=
    Equiv.sumPiEquivProdPi (fun v => Fin (augmentedDimensions q aux v))
  (h ⊗ₖ (1 : Matrix ((b : Bool) → Fin (aux b))
    ((b : Bool) → Fin (aux b)) ℂ)).submatrix e e

omit [DecidableEq V] in
/-- Identity extension preserves the identity on the whole augmented space. -/
theorem augmentOperator_one (q : ℕ) (aux : Bool → ℕ) :
    augmentOperator (V := V) q aux 1 = 1 := by
  dsimp only [augmentOperator]
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv
    (Equiv.sumPiEquivProdPi (fun v => Fin (augmentedDimensions q aux v)))

omit [Fintype V] [DecidableEq V] in
/-- Identity extension preserves subtraction. -/
theorem augmentOperator_sub (q : ℕ) (aux : Bool → ℕ)
    (h k : Matrix (V → Fin q) (V → Fin q) ℂ) :
    augmentOperator q aux (h - k) = augmentOperator q aux h - augmentOperator q aux k := by
  ext σ τ
  simp only [augmentOperator, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.sub_apply, sub_mul]

omit [Fintype V] [DecidableEq V] in
/-- Identity extension preserves every labelled finite sum. -/
theorem augmentOperator_sum (q : ℕ) (aux : Bool → ℕ) {I : Type*} (s : Finset I)
    (h : I → Matrix (V → Fin q) (V → Fin q) ℂ) :
    augmentOperator q aux (∑ i ∈ s, h i) = ∑ i ∈ s, augmentOperator q aux (h i) := by
  ext σ τ
  simp only [augmentOperator, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Finset.sum_mul]

omit [DecidableEq V] in
/-- Extending by both auxiliary identities preserves positive contractions. -/
theorem augmentOperator_mem_Icc (q : ℕ) (aux : Bool → ℕ)
    {h : Matrix (V → Fin q) (V → Fin q) ℂ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ augmentOperator q aux h ∧ augmentOperator q aux h ≤ 1 := by
  have hpos : ∀ {A : Matrix (V → Fin q) (V → Fin q) ℂ}, 0 ≤ A →
      0 ≤ augmentOperator q aux A := by
    intro A hA
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hK := (Matrix.nonneg_iff_posSemidef.mp hA).kronecker
      (Matrix.PosSemidef.one :
        (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ).PosSemidef)
    exact hK.submatrix
      (Equiv.sumPiEquivProdPi (fun v => Fin (augmentedDimensions q aux v)))
  refine ⟨hpos h0, ?_⟩
  have hdiff := hpos (sub_nonneg.mpr h1)
  rw [augmentOperator_sub, augmentOperator_one] at hdiff
  exact sub_nonneg.mp hdiff

omit [Fintype V] [DecidableEq V] in
/-- Identity extension has the embedded physical support, even when C and R
have unequal dimensions. The designated support need not be minimal. -/
theorem augmentOperator_isSupportedOn (q : ℕ) (aux : Bool → ℕ)
    {h : Matrix (V → Fin q) (V → Fin q) ℂ} {D : Finset V}
    (hh : IsSupportedOn (n := fun _ => q) h D) :
    IsSupportedOn (augmentOperator q aux h) (physicalRegion D) := by
  classical
  refine ⟨?_, ?_⟩
  · intro σ τ hex
    obtain ⟨v, hv, hne⟩ := hex
    change h (fun x => σ (.inl x)) (fun x => τ (.inl x)) *
      (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
        (fun b => σ (.inr b)) (fun b => τ (.inr b)) = 0
    cases v with
    | inl x =>
      have hx : x ∉ D := by simpa [physicalRegion] using hv
      exact mul_eq_zero_of_left
        (hh.1 (fun x => σ (.inl x)) (fun x => τ (.inl x)) ⟨x, hx, hne⟩) _
    | inr b =>
      have haux : (fun b => σ (.inr b)) ≠ (fun b => τ (.inr b)) :=
        fun he => hne (congrFun he b)
      have hz : (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
          (fun b => σ (.inr b)) (fun b => τ (.inr b)) = 0 := Matrix.one_apply_ne haux
      exact mul_eq_zero_of_right (h (fun x => σ (.inl x)) (fun x => τ (.inl x))) hz
  · intro σ τ σ' τ' h1 h2 h3 h4
    have ha : (fun b => σ (.inr b)) = (fun b => τ (.inr b)) :=
      funext fun b => h3 (.inr b) (by simp [physicalRegion])
    have hb : (fun b => σ' (.inr b)) = (fun b => τ' (.inr b)) :=
      funext fun b => h4 (.inr b) (by simp [physicalRegion])
    change h (fun x => σ (.inl x)) (fun x => τ (.inl x)) *
      (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
        (fun b => σ (.inr b)) (fun b => τ (.inr b)) =
      h (fun x => σ' (.inl x)) (fun x => τ' (.inl x)) *
        (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
          (fun b => σ' (.inr b)) (fun b => τ' (.inr b))
    have hphys : h (fun x => σ (.inl x)) (fun x => τ (.inl x)) =
        h (fun x => σ' (.inl x)) (fun x => τ' (.inl x)) := hh.2 _ _ _ _
      (fun x hx => h1 (.inl x) (by simpa [physicalRegion] using hx))
      (fun x hx => h2 (.inl x) (by simpa [physicalRegion] using hx))
      (fun x hx => h3 (.inl x) (by simpa [physicalRegion] using hx))
      (fun x hx => h4 (.inl x) (by simpa [physicalRegion] using hx))
    have haux : (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
        (fun b => σ (.inr b)) (fun b => τ (.inr b)) = 1 :=
      Matrix.one_apply.trans (ite_eq_left ha)
    have haux' : (1 : Matrix ((b : Bool) → Fin (aux b)) ((b : Bool) → Fin (aux b)) ℂ)
        (fun b => σ' (.inr b)) (fun b => τ' (.inr b)) = 1 :=
      Matrix.one_apply.trans (ite_eq_left hb)
    exact congrArg₂ (fun z w : ℂ => z * w) hphys (haux.trans haux'.symm)

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}

/-- The source positive constraint of the actual labelled interaction.
Source: `03-quasilocal.tex`, lines 250–266. -/
def _root_.TNLean.PEPS.AreaLaw.LocalHamiltonian.positiveTerm
    (h : LocalHamiltonian Λ q R J) (Δ : ℝ) (Ω : StateSpace Λ q)
    (i : AdmissibleSupport Λ R) : Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  positiveConstraint (positiveNormalization 1 (Δ / 2) J)
    (centeredFilter 1 (Δ / 2) h.operator Ω (h.term i))

namespace CollarScan

variable (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)

/-- The actual constraint truncated near the scanner's compact set at its base radius.
Source: `03-quasilocal.tex`, lines 417–426. -/
def truncatedEnergyTerm (Δ : ℝ) (L : ℕ) (i : AdmissibleSupport Λ R) :
    Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  truncatedConstraint q S.graph (S.truncationSet L) S.r₀ (S.anchor i) (h.positiveTerm Δ Ω i)

/-- Actual energy terms, with the original support labels retained and with both
auxiliary identities. Only the term and designated-support fields are bundled.
Source: `06-transport.tex`, lines 335–358. -/
def actualEnergyTerms (Δ : ℝ) (L : ℕ) (aux : Bool → ℕ) :
    EnergyTerms (Site Λ ⊕ Bool) (augmentedDimensions q aux) (AdmissibleSupport Λ R) where
  term i := augmentOperator q aux (S.truncatedEnergyTerm h Ω Δ L i)
  support i := physicalRegion (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i))

/-- The actual truncated terms are positive contractions, derived from the norm
bound on each local interaction and the accepted centered-filter estimate. -/
theorem truncatedEnergyTerm_mem_Icc [NeZero q] (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1)
    (L : ℕ) (i : AdmissibleSupport Λ R) :
    0 ≤ S.truncatedEnergyTerm h Ω Δ L i ∧ S.truncatedEnergyTerm h Ω Δ L i ≤ 1 := by
  have hc := positiveNormalization_pos 1 (Δ / 2) J
  apply truncatedConstraint_mem_Icc
  · exact positiveConstraint_nonneg hc.le _
  · apply positiveConstraint_le_one hc
    refine (norm_centeredFilter_le (le_refl 1) (half_pos hΔ)
      h.operator_isHermitian hΩ (h.term i)).trans ?_
    exact (mul_le_mul_of_nonneg_right (h.norm_le i)
      (add_nonneg (filterL1_nonneg _ _) zero_le_one)).trans (le_max_right _ _)

/-- The support certificate follows from actual admissibility: every interaction
support has induced-graph diameter at most `R`, including in disconnected domains. -/
theorem truncatedEnergyTerm_isSupportedOn [NeZero q]
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (L : ℕ) (i : AdmissibleSupport Λ R) :
    IsSupportedOn (n := fun _ => q) (S.truncatedEnergyTerm h Ω Δ L i)
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)) := by
  apply QuantumCircuit.isSupportedOn_of_mem_supportedOperators
  apply truncatedConstraint_mem_supportedOperators
  apply positiveConstraint_mem_supportedOperators_component (le_refl 1) (half_pos hΔ)
    S.graph (fun i : AdmissibleSupport Λ R => i.val) S.anchor hanchor h.term
    h.hermitian h.supported R
  intro j x hx y hy
  rw [hgraph]
  exact (exists_walk_length_le_iff_edist_le Λ R x y).mp (j.property.2 x hx y hy)

/-- All three operator hypotheses of energy transport hold for the actual
labelled augmented terms; no positivity or support certificate is assumed. -/
theorem actualEnergyTerms_spec [NeZero q]
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) (aux : Bool → ℕ) :
    (∀ i, 0 ≤ (S.actualEnergyTerms h Ω Δ L aux).term i) ∧
    (∀ i, (S.actualEnergyTerms h Ω Δ L aux).term i ≤ 1) ∧
    (∀ i, IsSupportedOn ((S.actualEnergyTerms h Ω Δ L aux).term i)
      ((S.actualEnergyTerms h Ω Δ L aux).support i)) := by
  have hc := fun i => S.truncatedEnergyTerm_mem_Icc h Ω hΔ hΩ L i
  have ha := fun i => augmentOperator_mem_Icc q aux (hc i).1 (hc i).2
  exact ⟨fun i => (ha i).1, fun i => (ha i).2, fun i =>
    augmentOperator_isSupportedOn q aux
      (S.truncatedEnergyTerm_isSupportedOn h Ω hgraph hanchor hΔ L i)⟩

/-- The labelled augmented sum is exactly the identity extension of the actual
truncated physical Hamiltonian. No term labels are merged or discarded. -/
theorem sum_actualEnergyTerms (Δ : ℝ) (L : ℕ) (aux : Bool → ℕ) :
    ∑ i, (S.actualEnergyTerms h Ω Δ L aux).term i =
      augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i) :=
  (augmentOperator_sum q aux Finset.univ _).symm

/-- The replica energy is the copy mean of the actual augmented truncated sum,
with the source copy normalization retained also at zero replicas. -/
theorem replicaEnergy_actualEnergyTerms (Δ : ℝ) (L : ℕ) (aux : Bool → ℕ) (k : ℕ) :
    (S.actualEnergyTerms h Ω Δ L aux).replicaEnergy k =
      copyMean (augmentedDimensions q aux) k
        (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i)) := by
  rw [← S.sum_actualEnergyTerms h Ω Δ L aux]
  simp only [EnergyTerms.replicaEnergy, copyMean, siteOp_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

end CollarScan
end TNLean.PEPS.AreaLaw.Scan
