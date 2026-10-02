/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoSiteChargeCommutation
import TNLean.PEPS.RegularChargeCompleteMeasurement

/-!
# Original-spin charge measurement for two regular isometric sites

The product of two original physical site maps has a positive multiple of the
product local averaging projector as its Gram matrix, derived from the local
G-isometry assumptions. The shared charge projector commutes with that average,
so it induces a positive Hermitian physical projection. Its complement completes
a binary measurement. The actual regular charge labels also yield a complete
measurement, chosen before every internal parameter and boundary label.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.
**Scope restriction (auxiliary finite-leg measurement):** The binary theorem uses
an explicit selected unitary irreducible representation. The complete-family
result derives all labels from the actual regular representation. Specializing
to the prescribed lattice geometry remains separate. No nonzero
column assertion is made when there is no remaining boundary leg, and no
six-spin creation or parent-Hamiltonian conclusion is asserted. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι κ A B : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [Fintype A] [Fintype B]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The actual two-site physical column obtained by contracting a character-weighted
shared regular bond. Source: SCP10, charge detection, lines 2464–2486. -/
def regularTwoSitePhysicalChargeColumn (i : ι) (j : κ)
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ) (χ : G → ℂ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) (s : A × B) : ℂ :=
  ∑ k : G, χ (p * k) * a ((Equiv.funSplitAt i G).symm (k, θ.1)) s.1 *
    b ((Equiv.funSplitAt j G).symm (k, θ.2)) s.2

private theorem local_site_matrix_data
    (a : (ι → G) → A → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a)) :
    ∃ c : ℝ, 0 < c ∧
      (Matrix.of fun s η => a η s).conjTranspose * (Matrix.of fun s η => a η s) =
        (c : ℂ) • regularLegProjector ι ∧
      (Matrix.of fun s η => a η s) * regularLegProjector ι =
        (Matrix.of fun s η => a η s) := by
  classical
  obtain ⟨c, hc, hg⟩ := ha.exists_regularSiteGram
  refine ⟨c, hc, ?_, ?_⟩
  · ext η θ
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      regularLegProjector_apply, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_assoc] using hg η θ
  · ext s η
    simpa only [Matrix.mul_apply, Matrix.of_apply] using
      ha.toIsGInjective.regularSiteMap_projector_coefficients s η

/-- The actual physical contraction is the product of the original site maps applied
 to the canonical charge column. Source: SCP10, lines 2464–2486. -/
theorem regularTwoSitePhysicalChargeColumn_eq_image (i : ι) (j : κ)
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGIsometric (regularLegRepresentation κ) (regularSiteMap b))
    (χ : G → ℂ) (p : G)
    (θ : ({e : ι // e ≠ i} → G) × ({e : κ // e ≠ j} → G)) :
    ((Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)) *ᵥ
      regularTwoSiteChargeColumn i j χ p θ =
        regularTwoSitePhysicalChargeColumn i j a b χ p θ := by
  obtain ⟨_, _, _, hA⟩ := local_site_matrix_data a ha
  obtain ⟨_, _, _, hB⟩ := local_site_matrix_data b hb
  rw [regularTwoSiteChargeColumn_eq_projector, Matrix.kronecker, Matrix.mulVec_mulVec,
    ← Matrix.mul_kronecker_mul, hA, hB, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  funext s
  simp [regularTwoSitePhysicalChargeColumn, Matrix.kroneckerMap, mul_assoc]

private theorem transported_projection {H K : Type*} [Fintype H] [Fintype K]
    (T : Matrix H K ℂ) (P D : Matrix K K ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P)
    (hTP : T * P = T) (hcomm : D * P = P * D)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    let Q := (c : ℂ)⁻¹ • (T * D * T.conjTranspose)
    Q.IsHermitian ∧ Q.PosSemidef ∧ Q * Q = Q ∧ Q * T = T * D := by
  let Q := (c : ℂ)⁻¹ • (T * D * T.conjTranspose)
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hQT : Q * T = T * D := by
    change (c : ℂ)⁻¹ • (T * D * T.conjTranspose) * T = _
    rw [Matrix.smul_mul, Matrix.mul_assoc, hGram, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hc', one_smul, Matrix.mul_assoc, hcomm,
      ← Matrix.mul_assoc, hTP]
  have hQh : Q.IsHermitian :=
    (Matrix.isHermitian_mul_mul_conjTranspose T hDh).smul (by simp [IsSelfAdjoint])
  have hQI : Q * Q = Q := by
    change Q * ((c : ℂ)⁻¹ • (T * D * T.conjTranspose)) = Q
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQT,
      Matrix.mul_assoc T D D, hDI]
  refine ⟨hQh, ?_, hQI, hQT⟩
  simpa only [hQh.eq, hQI] using Matrix.posSemidef_self_mul_conjTranspose Q

omit [Group G] [Fintype G] [DecidableEq G] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ] [Fintype A] [Fintype B] in
/-- A complete commuting virtual projection family induces a complete physical
measurement through a supported scaled isometry. The extra outcome is the
orthogonal complement of the physical image. Source: the local physical
isometry argument in SCP10, lines 2464–2486; auxiliary finite-dimensional form. -/
theorem exists_physicalProjectionFamily {H K L : Type*}
    [Fintype H] [Fintype K] [Fintype L]
    [DecidableEq H] [DecidableEq K] [DecidableEq L]
    (T : Matrix H K ℂ) (P : Matrix K K ℂ) (D : L → Matrix K K ℂ)
    (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P) (hTP : T * P = T)
    (hDh : ∀ l, (D l).IsHermitian)
    (hDD : ∀ l m, D l * D m = if l = m then D l else 0)
    (hDP : ∀ l, Commute (D l) P) (hDsum : ∑ l, D l = 1) :
    ∃ Q : Option L → Matrix H H ℂ,
      (∀ l, (Q l).IsHermitian ∧ (Q l).PosSemidef) ∧
      (∀ l m, Q l * Q m = if l = m then Q l else 0) ∧
      (∑ l, Q l = 1) ∧ (Q none*T = 0) ∧
      ∀ l, Q (some l)*T = T*D l := by
  classical
  let F : L → Matrix H H ℂ := fun l => (c : ℂ)⁻¹ • (T*D l*T.conjTranspose)
  have hF (l : L) : (F l).IsHermitian ∧ (F l).PosSemidef ∧
      F l*F l = F l ∧ F l*T = T*D l :=
    transported_projection T P (D l) c hc hGram hTP (hDP l).eq
      (hDh l) (by simpa using hDD l l)
  have hFF (l m : L) : F l*F m = if l=m then F l else 0 := by
    change F l*((c : ℂ)⁻¹ • (T*D m*T.conjTranspose)) = _
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (hF l).2.2.2,
      Matrix.mul_assoc T (D l) (D m), hDD]
    split_ifs <;> simp [F]
  let S : Matrix H H ℂ := ∑ l, F l
  have hSh : S.IsHermitian := by
    change (∑ l, F l).conjTranspose = ∑ l, F l
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun l _ => (hF l).1.eq
  have hFS (l : L) : F l*S = F l := by
    simp only [S, Matrix.mul_sum, hFF]
    simp
  have hSF (l : L) : S*F l = F l := by
    simp only [S, Matrix.sum_mul, hFF]
    simp
  have hSI : S*S = S := by
    simp only [S, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun l _ => hFS l
  have hST : S*T = T := by
    simp only [S, Matrix.sum_mul]
    simp_rw [(hF _).2.2.2]
    rw [← Matrix.mul_sum, hDsum, Matrix.mul_one]
  let C : Matrix H H ℂ := 1-S
  have hCh : C.IsHermitian := Matrix.isHermitian_one.sub hSh
  have hCI : C*C=C := by
    simp only [C, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      hSI, sub_self, sub_zero]
  have hCp : C.PosSemidef := by
    simpa only [hCh.eq, hCI] using Matrix.posSemidef_self_mul_conjTranspose C
  let Q : Option L → Matrix H H ℂ := fun l => l.elim C F
  refine ⟨Q, ?_, ?_, ?_, ?_, fun l => (hF l).2.2.2⟩
  · rintro (_ | l)
    · exact ⟨hCh, hCp⟩
    · exact ⟨(hF l).1, (hF l).2.1⟩
  · rintro (_ | l) (_ | m)
    · exact hCI
    · simp [Q, C, Matrix.sub_mul, hSF]
    · simp [Q, C, Matrix.mul_sub, hFS]
    · simpa [Q] using hFF l m
  · simp [Q, C, S]
  · simp [Q, C, Matrix.sub_mul, hST]

private theorem two_site_matrix_data
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGIsometric (regularLegRepresentation κ) (regularSiteMap b)) :
    let T := (Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)
    let P := (regularLegProjector (G := G) ι) ⊗ₖ regularLegProjector (G := G) κ
    ∃ c : ℝ, 0 < c ∧ T.conjTranspose * T = (c : ℂ) • P ∧ T * P = T := by
  obtain ⟨cA, hcA, hGA, hAP⟩ := local_site_matrix_data a ha
  obtain ⟨cB, hcB, hGB, hBP⟩ := local_site_matrix_data b hb
  let T := (Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)
  let P : Matrix ((ι → G) × (κ → G)) ((ι → G) × (κ → G)) ℂ :=
    (regularLegProjector (G := G) ι) ⊗ₖ regularLegProjector (G := G) κ
  have hGram : T.conjTranspose * T = ((cA * cB : ℝ) : ℂ) • P := by
    dsimp only [T, P]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hGA, hGB,
      Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, Complex.ofReal_mul]
  have hTP : T * P = T := by
    dsimp only [T, P]
    rw [← Matrix.mul_kronecker_mul, hAP, hBP]
  exact ⟨cA*cB, mul_pos hcA hcB, hGram, hTP⟩

/-- A charge projector on the original two physical spins is derived from local
regular G-isometry, uniformly before every internal and boundary label.
Source: SCP10, charge detection, lines 2464–2486; auxiliary finite-leg statement. -/
theorem exists_regularTwoSitePhysicalChargeProjector (i : ι) (j : κ)
    (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGIsometric (regularLegRepresentation κ) (regularSiteMap b)) (χ : G → ℂ) :
    ∃ Q : Matrix (A × B) (A × B) ℂ,
      Q.IsHermitian ∧ Q.PosSemidef ∧ Q * Q = Q ∧
      Q * ((Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)) =
        ((Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)) *
          regularTwoSiteChargeDetector i j χ ∧
      ∀ p θ, Q *ᵥ regularTwoSitePhysicalChargeColumn i j a b χ p θ =
        regularTwoSitePhysicalChargeColumn i j a b χ p θ := by
  classical
  let T := (Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)
  let P := (regularLegProjector (G := G) ι) ⊗ₖ regularLegProjector (G := G) κ
  obtain ⟨c, hc, hGram, hTP⟩ := two_site_matrix_data a b ha hb
  let Q := (c : ℂ)⁻¹ •
    (T * regularTwoSiteChargeDetector i j χ * T.conjTranspose)
  obtain ⟨hh, hp, hi, hQT⟩ := transported_projection T P
    (regularTwoSiteChargeDetector i j χ) c hc hGram hTP
      (regularTwoSiteChargeDetector_commute_projector i j χ).eq
      (regularTwoSiteChargeDetector_properties i j χ).1
      (regularTwoSiteChargeDetector_properties i j χ).2.2
  refine ⟨Q, hh, hp, hi, hQT, ?_⟩
  intro p θ
  rw [← regularTwoSitePhysicalChargeColumn_eq_image i j a b ha hb,
    Matrix.mulVec_mulVec, hQT, ← Matrix.mulVec_mulVec,
    regularTwoSiteChargeDetector_column]

omit [DecidableEq G] in
open Classical in
/-- A complete binary measurement distinguishes a selected irreducible charge from
all inequivalent irreducible charges in the literal two-site contraction. The two
local physical maps need only regular G-isometry. Source: SCP10, charge detection,
lines 2464–2486; auxiliary finite-leg statement. -/
theorem exists_regularTwoSitePhysicalChargeMeasurement
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (i : ι) (j : κ) (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGIsometric (regularLegRepresentation κ) (regularSiteMap b)) :
    ∃ Q : Bool → Matrix (A × B) (A × B) ℂ,
      (∀ r, (Q r).IsHermitian ∧ (Q r).PosSemidef) ∧
      (∀ r s, Q r * Q s = if r = s then Q r else 0) ∧
      (∑ r, Q r = 1) ∧
      (∀ p θ, Q true *ᵥ regularTwoSitePhysicalChargeColumn i j a b σ.character p θ =
        regularTwoSitePhysicalChargeColumn i j a b σ.character p θ) ∧
      (∀ (τ : Representation ℂ G F), τ.IsIrreducible → σ.character ≠ τ.character →
        ∀ p θ, Q true *ᵥ regularTwoSitePhysicalChargeColumn i j a b τ.character p θ = 0) := by
  classical
  obtain ⟨D, hh, hp, hi, hDT, hselected⟩ :=
    exists_regularTwoSitePhysicalChargeProjector i j a b ha hb σ.character
  let C : Matrix (A × B) (A × B) ℂ := 1-D
  let Q : Bool → Matrix (A × B) (A × B) ℂ := fun r => if r then D else C
  have hCh : C.IsHermitian := Matrix.isHermitian_one.sub hh
  have hCI : C*C = C := by
    dsimp only [C]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      hi, sub_self, sub_zero]
  have hCp : C.PosSemidef := by
    simpa only [hCh.eq, hCI] using Matrix.posSemidef_self_mul_conjTranspose C
  refine ⟨Q, ?_, ?_, ?_, hselected, ?_⟩
  · intro r
    cases r with
    | false => exact ⟨hCh, hCp⟩
    | true => exact ⟨hh, hp⟩
  · intro r s
    cases r <;> cases s <;>
      simp [Q, C, Matrix.mul_sub, Matrix.sub_mul, hi]
  · simp [Q, C]
  · intro τ hτ hne p θ
    let := hτ
    change D *ᵥ regularTwoSitePhysicalChargeColumn i j a b τ.character p θ = 0
    rw [← regularTwoSitePhysicalChargeColumn_eq_image i j a b ha hb,
      Matrix.mulVec_mulVec, hDT, ← Matrix.mulVec_mulVec,
      regularTwoSiteChargeDetector_other_column σ τ hσ hne, Matrix.mulVec_zero]

/-- All actual regular charge detectors remain complete after extending them to the
remaining half-edge coordinates. Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularTwoSiteChargeDetector_complete (i : ι) (j : κ) :
    (∀ χ ψ : regularChargeLabels (G := G),
      regularTwoSiteChargeDetector i j χ.val * regularTwoSiteChargeDetector i j ψ.val =
        if χ = ψ then regularTwoSiteChargeDetector i j χ.val else 0) ∧
    (∑ χ : regularChargeLabels (G := G), regularTwoSiteChargeDetector i j χ.val = 1) := by
  classical
  obtain ⟨hDD, hsum⟩ := regularChargeDetectorMatrix_complete (G := G)
  constructor
  · intro χ ψ
    by_cases h : χ = ψ
    · subst ψ
      simpa using (regularTwoSiteChargeDetector_properties i j χ.val).2.2
    · have hval : χ.val ≠ ψ.val := fun hval => h (Subtype.ext hval)
      rw [ite_eq_right h, regularTwoSiteChargeDetector, regularTwoSiteChargeDetector,
        Matrix.submatrix_mul_equiv, Matrix.kronecker, ← Matrix.mul_kronecker_mul,
        hDD χ χ.property ψ ψ.property, ite_eq_right hval,
        Matrix.zero_kronecker]
      rfl
  · let E := regularSharedLegEquiv (G := G) i j
    have hs : ∑ χ : regularChargeLabels (G := G), regularChargeDetectorMatrix χ.val = 1 := by
      rw [Finset.sum_coe_sort]
      exact hsum
    have h : (∑ χ : regularChargeLabels (G := G),
        regularTwoSiteChargeDetector i j χ.val) =
        ((∑ χ : regularChargeLabels (G := G), regularChargeDetectorMatrix χ.val).kronecker
          (1 : Matrix _ _ ℂ)).submatrix E E := by
      ext α β
      simp only [regularTwoSiteChargeDetector, Matrix.sum_apply, Matrix.submatrix_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
      rfl
    rw [h, hs, Matrix.kronecker, Matrix.one_kronecker_one]
    exact Matrix.submatrix_one_equiv E

open Classical in
/-- A single complete measurement on the two original physical spins distinguishes
all actual regular charge labels. It is chosen before every internal parameter
and boundary configuration. Its additional outcome is the complement of the
physical image and annihilates all charged columns.
Source: SCP10, charge detection, lines 2464–2486; auxiliary finite-leg form. -/
theorem exists_regularTwoSitePhysicalAllChargeMeasurement
    (i : ι) (j : κ) (a : (ι → G) → A → ℂ) (b : (κ → G) → B → ℂ)
    (ha : IsGIsometric (regularLegRepresentation ι) (regularSiteMap a))
    (hb : IsGIsometric (regularLegRepresentation κ) (regularSiteMap b)) :
    ∃ Q : Option (regularChargeLabels (G := G)) → Matrix (A × B) (A × B) ℂ,
      (∀ r, (Q r).IsHermitian ∧ (Q r).PosSemidef) ∧
      (∀ r s, Q r * Q s = if r = s then Q r else 0) ∧
      (∑ r, Q r = 1) ∧
      ∀ (χ : regularChargeLabels (G := G)) r p θ,
        Q r *ᵥ regularTwoSitePhysicalChargeColumn i j a b χ.val p θ =
          if r = some χ then regularTwoSitePhysicalChargeColumn i j a b χ.val p θ else 0 := by
  classical
  let T := (Matrix.of fun s η => a η s) ⊗ₖ (Matrix.of fun s η => b η s)
  let P := (regularLegProjector (G := G) ι) ⊗ₖ regularLegProjector (G := G) κ
  obtain ⟨c, hc, hGram, hTP⟩ := two_site_matrix_data a b ha hb
  obtain ⟨hDD, hsum⟩ := regularTwoSiteChargeDetector_complete (G := G) i j
  obtain ⟨Q, hQh, hQQ, hQsum, hQnone, hQT⟩ := exists_physicalProjectionFamily T P
    (fun χ : regularChargeLabels (G := G) => regularTwoSiteChargeDetector i j χ.val)
    c hc hGram hTP
    (fun χ => (regularTwoSiteChargeDetector_properties i j χ.val).1) hDD
    (fun χ => regularTwoSiteChargeDetector_commute_projector i j χ.val) hsum
  refine ⟨Q, hQh, hQQ, hQsum, ?_⟩
  intro χ r p θ
  rw [← regularTwoSitePhysicalChargeColumn_eq_image i j a b ha hb,
    Matrix.mulVec_mulVec]
  cases r with
  | none =>
    change (Q none * T) *ᵥ regularTwoSiteChargeColumn i j χ.val p θ = 0
    rw [hQnone, Matrix.zero_mulVec]
  | some ψ =>
    rw [hQT, ← Matrix.mulVec_mulVec]
    by_cases h : ψ = χ
    · subst ψ
      rw [regularTwoSiteChargeDetector_column, ite_eq_left rfl]
    · have hval : ψ.val ≠ χ.val := fun hval => h (Subtype.ext hval)
      obtain ⟨S, hS, hψ, hunit⟩ :=
        exists_unitary_irreducible_regularChargeLabel ψ.val ψ.property
      obtain ⟨U, hU, hχ, _⟩ :=
        exists_unitary_irreducible_regularChargeLabel χ.val χ.property
      let := hS
      let := hU
      have hne : S.toRepresentation.character ≠ U.toRepresentation.character := by
        simpa only [← hψ, ← hχ] using hval
      have hzero := regularTwoSiteChargeDetector_other_column
        S.toRepresentation U.toRepresentation hunit hne i j p θ
      rw [← hψ, ← hχ] at hzero
      rw [hzero, Matrix.mulVec_zero]
      simp [h]

end TNLean.PEPS
