/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalColumns
import TNLean.MPS.MPU.MinimalCutEndpointMetrics

/-!
# Exact physical columns at the root interval

The full interval contains every logical site, so its outside configuration
is unique. Its two endpoint cut spaces have dimension one, and their bond
registers have width zero. The full input and output encodings therefore
coincide with the physical configuration followed by initialized logical
auxiliaries.

Endpoint normalization identifies the weighted full interval with the given
unitary, including its complex phase. The actual interval column invariant
then yields the exact physical columns of the logical operator. Composing
these columns with a full logical clean-workspace implementation gives the
same physical unitary while returning all logical auxiliaries and the shared
scratch pool to zero.

These are algebraic consequences of the interval invariant and clean
implementation, used after the recursive circuit construction. See
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation
open scoped Kronecker Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The full interval packet contains every logical site.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacketSites_full_range (d D N : ℕ) :
    Set.range (intervalPacketSites d D N 0 N) = Set.univ := by
  rw [intervalPacketSites_range, intervalConsecutiveSupport, intervalLogicalSupport_full,
    Set.image_univ, Equiv.range_eq_univ]

/-- The full interval has a unique configuration on the empty set of outside sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem outsidePlacedConfig_full_subsingleton (d D N : ℕ) :
    Subsingleton (OutsidePlacedConfig d (intervalPacketSites d D N 0 N)) := by
  refine ⟨fun x y ↦ funext fun s ↦ ?_⟩
  exact False.elim (s.2 (by simp only [intervalPacketSites_full_range, Set.mem_univ]))

private theorem intervalPhysicalZeroConfig_full {d D N : ℕ} [NeZero d]
    (x : Cfg d N) (s : LogicalSite d D N) :
    intervalPhysicalZeroConfig (D := D) 0 N (fullCutIntervalConfigEquiv d N x) s =
      zeroWorkspaceEmbedding (d := d) (n := N) (a := auxiliarySiteCount d D N) x
        (logicalSiteEquivFin d D N s) := by
  rcases s with s | s
  · change _ = Fin.append x 0 (Fin.castAdd (auxiliarySiteCount d D N) s)
    simp [intervalPhysicalZeroConfig, fullCutIntervalConfigEquiv, s.isLt]
  · change _ = Fin.append x 0 (Fin.natAdd N (auxiliarySiteEquivFin d D N s))
    simp [intervalPhysicalZeroConfig]

private theorem placedBasisEmbedding_eq_of_restriction {d a n : ℕ} {α : Type*}
    (e : Fin a ↪ Fin n) [Subsingleton (OutsidePlacedConfig d e)]
    (g : α ↪ Cfg d a) (x : α) (z : OutsidePlacedConfig d e) (y : Cfg d n)
    (hg : g x = y ∘ e) :
    placedBasisEmbedding e g (Function.Embedding.refl _) (x, z) = y := by
  apply (placedConfigEquiv d e).injective
  change (placedConfigEquiv d e) ((placedConfigEquiv d e).symm (g x, z)) = _
  rw [Equiv.apply_symm_apply]
  exact Prod.ext hg (Subsingleton.elim _ _)

/-- The root input encoding initializes every logical auxiliary and retains the physical input.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalInputEmbedding_full_apply {d D N : ℕ} [NeZero d]
    (x : Cfg d N) (z : OutsidePlacedConfig d (intervalPacketSites d D N 0 N)) :
    minimalIntervalInputEmbedding (D := D) 0 N (fullCutIntervalConfigEquiv d N x, z) =
      zeroWorkspaceEmbedding (d := d) (n := N) (a := auxiliarySiteCount d D N) x := by
  let := outsidePlacedConfig_full_subsingleton d D N
  apply placedBasisEmbedding_eq_of_restriction
  funext i
  exact intervalPhysicalZeroConfig_full x (intervalPacketLogicalSite d D N 0 N i)

private theorem intervalBoundaryConfig_full {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N (Fin.last N)))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N 0))
    (x : CutIntervalConfig d N 0 N × (ρ × σ)) :
    intervalBoundaryConfig 0 (Fin.last N) eρ eσ x = intervalPhysicalZeroConfig 0 N x.1 := by
  funext s
  unfold intervalBoundaryConfig
  rw [Function.extend_apply' _ _ _ (by
    rintro ⟨q, _⟩
    have hq := cutBondRegisterWidth_internal q
    simp only [Fin.val_last] at hq
    omega), Function.extend_apply' _ _ _ (by
    rintro ⟨q, _⟩
    have hq := cutBondRegisterWidth_internal q
    simp only [Fin.val_zero] at hq
    omega)]
  simp only [Fin.val_zero, Fin.val_last]

/-- The root output encoding retains only the physical output. Both endpoint bond registers have
width zero, and every logical auxiliary is initialized.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalOutputEmbedding_full_apply {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (x : Cfg d N)
    (α : Fin (cutRank (operatorCoefficientTensor U) 0))
    (β : Fin (cutRank (operatorCoefficientTensor U) N))
    (z : OutsidePlacedConfig d (intervalPacketSites d D N 0 N)) :
    minimalIntervalOutputEmbedding hd U hU hbound 0 (Fin.last N)
      ((fullCutIntervalConfigEquiv d N x, (β, α)), z) =
      zeroWorkspaceEmbedding (d := d) (n := N) (a := auxiliarySiteCount d D N) x := by
  let := outsidePlacedConfig_full_subsingleton d D N
  simp only [minimalIntervalOutputEmbedding, Fin.val_zero, Fin.val_last]
  apply placedBasisEmbedding_eq_of_restriction
  funext i
  change intervalBoundaryConfig 0 (Fin.last N) _ _
    (fullCutIntervalConfigEquiv d N x, (β, α))
    (intervalPacketLogicalSite d D N 0 N i) = _
  exact (congrFun (intervalBoundaryConfig_full
    (minimalCutBondRegisterEncoding hd U hU hbound (Fin.last N))
    (minimalCutBondRegisterEncoding hd U hU hbound 0)
    (fullCutIntervalConfigEquiv d N x, (β, α)))
    (intervalPacketLogicalSite d D N 0 N i)).trans
      (intervalPhysicalZeroConfig_full x (intervalPacketLogicalSite d D N 0 N i))

open scoped Classical in
/-- Include the physical chain by initializing all logical auxiliary sites to zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def physicalLogicalConfigEmbedding {d D N : ℕ} [NeZero d] :
    Cfg d N ↪ Cfg d (logicalSiteCount d D N) :=
  zeroWorkspaceEmbedding (d := d) (n := N) (a := auxiliarySiteCount d D N)

open scoped Classical in
/-- The actual root interval invariant yields the exact physical columns when the weighted full
interval has been identified with the given operator. The following theorem derives that
identification from the normalized endpoint bases and their actual Gram hulls.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalRootColumns_eq_physical_of_fullInterval {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) j.val))
      (Fin (cutRank (operatorCoefficientTensor U) j.val)) ℂ)
    (hfull : ∀ (α : Fin (cutRank (operatorCoefficientTensor U) 0))
        (β : Fin (cutRank (operatorCoefficientTensor U) N)),
      (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
        (CFC.sqrt (P 0)) (CFC.sqrt (dualGramMetric (P (Fin.last N))))).submatrix
        (fun x ↦ (fullCutIntervalConfigEquiv d N x, (β, α)))
        (fullCutIntervalConfigEquiv d N) = U)
    (X : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (hX : IsMinimalIntervalColumnImplementation hd U hU hbound B P 0 (Fin.last N)
      (by simp) X) :
    X * initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) =
      initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) * U := by
  classical
  let := outsidePlacedConfig_full_subsingleton d D N
  let : Unique (OutsidePlacedConfig d (intervalPacketSites d D N 0 N)) :=
    { default := 0, uniq := fun _ ↦ Subsingleton.elim _ _ }
  have hψ := operatorCoefficientTensor_ne_zero (by omega : 0 < d) U hU
  let : Unique (Fin (cutRank (operatorCoefficientTensor U) 0)) :=
    Equiv.unique (finCongr (cutRank_zero _ hψ))
  let : Unique (Fin (cutRank (operatorCoefficientTensor U) N)) :=
    Equiv.unique (finCongr (cutRank_last _ hψ))
  let : Unique (Fin (cutRank (operatorCoefficientTensor U) N) ×
      Fin (cutRank (operatorCoefficientTensor U) 0)) :=
    { default := (default, default), uniq := fun _ ↦ Prod.ext
        (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
  let ei : Cfg d N ≃ CutIntervalConfig d N 0 N ×
      OutsidePlacedConfig d (intervalPacketSites d D N 0 N) :=
    (fullCutIntervalConfigEquiv d N).trans (Equiv.prodUnique _ _).symm
  let eo : Cfg d N ≃ (CutIntervalConfig d N 0 N ×
      (Fin (cutRank (operatorCoefficientTensor U) N) ×
        Fin (cutRank (operatorCoefficientTensor U) 0))) ×
      OutsidePlacedConfig d (intervalPacketSites d D N 0 N) :=
    ((fullCutIntervalConfigEquiv d N).trans (Equiv.prodUnique _ _).symm).trans
      (Equiv.prodUnique _ _).symm
  have hinput : (initializedBasisMatrix
        (minimalIntervalInputEmbedding (d := d) (D := D) (N := N) 0 N)).submatrix id ei =
      initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) := by
    ext z x
    change (1 : Matrix (Cfg d (logicalSiteCount d D N))
      (Cfg d (logicalSiteCount d D N)) ℂ) z (minimalIntervalInputEmbedding 0 N (ei x)) =
        (1 : Matrix (Cfg d (logicalSiteCount d D N))
          (Cfg d (logicalSiteCount d D N)) ℂ) z (physicalLogicalConfigEmbedding x)
    apply congrArg ((1 : Matrix (Cfg d (logicalSiteCount d D N))
      (Cfg d (logicalSiteCount d D N)) ℂ) z)
    exact minimalIntervalInputEmbedding_full_apply x default
  have houtput : (initializedBasisMatrix
        (minimalIntervalOutputEmbedding hd U hU hbound 0 (Fin.last N))).submatrix id eo =
      initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) := by
    ext z x
    change (1 : Matrix (Cfg d (logicalSiteCount d D N))
      (Cfg d (logicalSiteCount d D N)) ℂ) z
        (minimalIntervalOutputEmbedding hd U hU hbound 0 (Fin.last N) (eo x)) =
      (1 : Matrix (Cfg d (logicalSiteCount d D N))
        (Cfg d (logicalSiteCount d D N)) ℂ) z (physicalLogicalConfigEmbedding x)
    apply congrArg ((1 : Matrix (Cfg d (logicalSiteCount d D N))
      (Cfg d (logicalSiteCount d D N)) ℂ) z)
    exact minimalIntervalOutputEmbedding_full_apply hd U hU hbound x default default default
  have hweighted :
      ((vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.zero_le N))
        (CFC.sqrt (P 0)) (CFC.sqrt (dualGramMetric (P (Fin.last N))))) ⊗ₖ
        (1 : Matrix (OutsidePlacedConfig d (intervalPacketSites d D N 0 N))
          (OutsidePlacedConfig d (intervalPacketSites d D N 0 N)) ℂ)).submatrix eo ei = U := by
    ext x y
    simp only [Matrix.submatrix_apply, eo, ei, Equiv.trans_apply,
      Equiv.prodUnique_symm_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      ite_true, mul_one]
    exact congrArg (fun M ↦ M x y) (hfull default default)
  unfold IsMinimalIntervalColumnImplementation at hX
  simp only [Fin.val_zero, Fin.val_last] at hX
  have hh := congrArg (fun M ↦ M.submatrix id ei) hX
  erw [← Matrix.submatrix_mul_equiv X _ id (Equiv.refl _) ei,
    ← Matrix.submatrix_mul_equiv _ _ id eo ei] at hh
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at hh
  erw [hinput, houtput, hweighted] at hh
  exact hh

open scoped Classical in
/-- Endpoint-normalized minimal factors and their actual Gram hulls identify the root columns
with the original unitary, with its complex phase retained. No physical column identity is
supplied: it follows from the actual root interval invariant.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalRootColumns_eq_physical {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    (hBN : ∀ q, (B N q).val = fullCutVector (operatorCoefficientTensor U))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) j.val))
      (Fin (cutRank (operatorCoefficientTensor U) j.val)) ℂ)
    (hP0 : P 0 ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q))
    (hPN : P (Fin.last N) ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q))
    (X : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (hX : IsMinimalIntervalColumnImplementation hd U hU hbound B P 0 (Fin.last N)
      (by simp) X) :
    X * initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) =
      initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) * U := by
  apply minimalIntervalRootColumns_eq_physical_of_fullInterval hd U hU hbound B P _ X hX
  intro α β
  exact weightedMinimalOperatorInterval_full_submatrix (by omega) U hU B hB0 hBN hP0 hPN α β

/-- Include the entire logical register by initializing the common scratch pool to zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def logicalGlobalConfigEmbedding {d D N : ℕ} [NeZero d] :
    Cfg d (logicalSiteCount d D N) ↪ Cfg d (globalSiteCount d D N) :=
  zeroWorkspaceEmbedding (d := d) (n := logicalSiteCount d D N)
    (a := auxiliarySiteCount d D N)

/-- Include the physical chain with all logical auxiliary and shared scratch sites initialized
to zero, in the fixed global register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def physicalGlobalConfigEmbedding {d D N : ℕ} [NeZero d] :
    Cfg d N ↪ Cfg d (globalSiteCount d D N) :=
  (physicalLogicalConfigEmbedding (d := d) (D := D) (N := N)).trans
    (logicalGlobalConfigEmbedding (d := d) (D := D) (N := N))

/-- The initialized global configuration appends zeros first on the logical auxiliaries and then
on the shared scratch pool.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem physicalGlobalConfigEmbedding_apply {d D N : ℕ} [NeZero d] (x : Cfg d N) :
    physicalGlobalConfigEmbedding (D := D) x = Fin.append (Fin.append x 0) 0 := rfl

private theorem initializedBasisMatrix_trans {α β γ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq γ] (e : α ↪ β) (f : β ↪ γ) :
    initializedBasisMatrix (e.trans f) = initializedBasisMatrix f * initializedBasisMatrix e := by
  exact (Matrix.mul_submatrix_one (Equiv.refl β) e (initializedBasisMatrix f)).symm

/-- The physical basis inclusion factors through the logical register and its initialized
scratch pool.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem initializedBasisMatrix_physicalGlobalConfigEmbedding {d D N : ℕ} [NeZero d] :
    initializedBasisMatrix (physicalGlobalConfigEmbedding (d := d) (D := D) (N := N)) =
      initializedBasisMatrix (logicalGlobalConfigEmbedding (d := d) (D := D) (N := N)) *
        initializedBasisMatrix (physicalLogicalConfigEmbedding (d := d) (D := D) (N := N)) :=
  initializedBasisMatrix_trans _ _

/-- Exact physical columns of the logical operator and full logical workspace cleanup imply
exact physical columns on the global register, with every auxiliary returned to zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem physicalGlobalColumns_of_clean_logicalColumns {d D N : ℕ} [NeZero d]
    {U : Matrix (Cfg d N) (Cfg d N) ℂ}
    {X : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ}
    {W : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ}
    (hX : X * initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) =
      initializedBasisMatrix (physicalLogicalConfigEmbedding (D := D)) * U)
    (hW : IsCleanImplementation
      (initializedBasisMatrix (logicalGlobalConfigEmbedding (D := D))) W X) :
    W * initializedBasisMatrix (physicalGlobalConfigEmbedding (D := D)) =
      initializedBasisMatrix (physicalGlobalConfigEmbedding (D := D)) * U := by
  change W * initializedBasisMatrix (logicalGlobalConfigEmbedding (D := D)) =
    initializedBasisMatrix (logicalGlobalConfigEmbedding (D := D)) * X at hW
  rw [initializedBasisMatrix_physicalGlobalConfigEmbedding, ← Matrix.mul_assoc, hW,
    Matrix.mul_assoc, hX, ← Matrix.mul_assoc]

open scoped Classical in
/-- The actual root interval invariant, its endpoint-normalized minimal factors, and the full
logical clean implementation yield the original physical unitary with all logical auxiliary
and scratch sites returned to zero. The physical output identity and its complex phase are
derived from the given unitary and endpoint Gram hulls.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalRootColumns_eq_physical_global {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (hB0 : ∀ q, (B 0 q).val = 1)
    (hBN : ∀ q, (B N q).val = fullCutVector (operatorCoefficientTensor U))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) j.val))
      (Fin (cutRank (operatorCoefficientTensor U) j.val)) ℂ)
    (hP0 : P 0 ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B 0 aa bb q))
    (hPN : P (Fin.last N) ∈ prefixGramAffineHull
      (fun aa bb (_ : Unit) q ↦ minimalOperatorPrefixFactor U B N aa bb q))
    (X : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (hX : IsMinimalIntervalColumnImplementation hd U hU hbound B P 0 (Fin.last N)
      (by simp) X)
    (W : Matrix (Cfg d (globalSiteCount d D N)) (Cfg d (globalSiteCount d D N)) ℂ)
    (hW : IsCleanImplementation
      (initializedBasisMatrix (logicalGlobalConfigEmbedding (D := D))) W X) :
    W * initializedBasisMatrix (physicalGlobalConfigEmbedding (D := D)) =
      initializedBasisMatrix (physicalGlobalConfigEmbedding (D := D)) * U :=
  physicalGlobalColumns_of_clean_logicalColumns
    (minimalIntervalRootColumns_eq_physical hd U hU hbound B hB0 hBN P hP0 hPN X hX) hW

end MPUCircuit
