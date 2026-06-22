/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Fundamental

/-!
# BNT equal-MPV global-gauge witness

This module states the equal-MPV theorem `ft_sector_bnt_equal_global_gauge`
in the form of the equal-MPV corollary labelled II_cor2 in CPSV16 §II.C:
the main-text statement is at lines 354–361, the appendix restatement is at
lines 1172–1179, the copy-weight comparison is at line 1188, and the
global-gauge construction is at lines 1189–1192 of the Appendix MPV proof.

The bundled-witness theorem `ft_sector_bnt_equal_mps_gaugeEquiv_witnessesPos`
exposes, for any two BNT sector decompositions $P$ and $Q$ satisfying
`IsBNTCanonicalForm` and generating the same MPV family:

* the basis bijection $β : \{1,\dots,g_Q\} \simeq \{1,\dots,g_P\}$ between
  corresponding BNT sectors;
* per-block bond-dimension equalities $D_P^{(βk)} = D_Q^{(k)}$;
* matched copy multiplicities $r_{βk}^P = r_k^Q$;
* matched copy permutations $τ_k$;
* per-block unit-modulus gauge phases $ζ_k$;
* per-block gauge matrices $X_k \in \mathrm{GL}(D_Q^{(k)},\mathbb{C})$;
* the equality of total bond dimensions $\sum_k r_k D_k$;
* the explicit global gauge $X \in \mathrm{GL}(\sum_s D^{(s)},\mathbb{C})$;

together with the three CPSV16 conjugation identities from the Appendix MPV
proof:

* $B_k = ζ_k\,X_k\,A_{βk}\,X_k^{-1}$ (per basis block, lines 1182–1183);
* $ν_{k,q} = ζ_k^{-1}\,μ_{βk,\,τ_k q}$ (per copy weight, line 1188);
* $V_Q = X\,V_P\,X^{-1}$ at every site (global gauge equation, in matched
  flattened-copy coordinates, lines 1189–1192).

The global equation is stated in the matched coordinates of $Q$'s flattened
copy index; this is the direct-sum gauge construction of CPSV16 Appendix MPV
proof, lines 1189–1192.
Converting the right-hand side from the matched-coordinate `toTensorFromBlocks`
into a literal `cast`-of-`P.toTensor` requires assembling a sector-permutation
matrix from `sectorFlatEquiv` and conjugating; the present module records the
witness bundle that matches the CPSV16 equal-MPV corollary form, while
the permutation-matrix conjugation is left for a follow-up module.

Paper anchors:

* CPSV16 §II.C lines 354–361 and Appendix MPV proof lines 1172–1179:
  statement of the equal-MPV corollary labelled II_cor2.
* CPSV16 Appendix MPV proof, lines 1182–1183: per-basis-block gauge-phase
  matching from the proportional theorem.
* CPSV16 Appendix MPV proof, line 1188: copy multiplicity and copy-weight
  identification from finite power-sum comparison.
* CPSV16 Appendix MPV proof, lines 1189–1192: explicit global gauge
  $X = \bigoplus_k (𝟙_{r_k} \otimes X_k)$ and the global conjugation equation.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **BNT equal-MPV global-gauge witness.**

If two BNT sector decompositions satisfying `IsBNTCanonicalForm` generate the
same MPV family, then there exist:

* a basis bijection $β : \{1,\dots,g_Q\} \simeq \{1,\dots,g_P\}$,
* per-block bond-dimension equalities $D_P^{(βk)} = D_Q^{(k)}$,
* matched copy multiplicities $r_{βk}^P = r_k^Q$,
* per-block copy permutations $τ_k$,
* per-block unit-modulus gauge phases $ζ_k$,
* per-block gauge matrices $X_k \in \mathrm{GL}(D_Q^{(k)},\mathbb{C})$,
* a total bond-dimension equality $\sum_k r_k D_k = \sum_k r_k' D_k'$, and
* an explicit global gauge $X \in \mathrm{GL}\bigl(\sum_s D^{(s)},
  \mathbb{C}\bigr)$ of the form $X = \bigoplus_k (𝟙_{r_k}\otimes X_k)$,

such that the three CPSV16 Appendix MPV proof identities

* $B_k = ζ_k\,X_k\,A_{βk}\,X_k^{-1}$ (per basis block, lines 1182–1183),
* $ν_{k,q} = ζ_k^{-1}\,μ_{βk,\,τ_k q}$ (per copy weight, line 1188),
* $V_Q^i = X\,V_P^i\,X^{-1}$ at every physical site $i$ (global gauge,
  lines 1189–1192),

hold simultaneously.  The final global identity is exposed here in the
matched flattened-copy coordinates of $Q$: writing the $P$-side block tensors
through the matched bijections gives the
`toTensorFromBlocks`-tensor that conjugates to $Q.toTensor$ under $X$.

CPSV16 §II.C lines 354–361 and Appendix MPV proof lines 1172–1179 state the
equal-MPV corollary; Appendix MPV proof lines 1182–1192 supply the block
matching, copy-weight comparison, and global-gauge construction used here. -/
theorem ft_sector_bnt_equal_mps_gaugeEquiv_witnessesPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (_hCopies : ∀ k : Fin Q.basisCount, P.copies (β k) = Q.copies k)
      (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
      (ζ : Fin Q.basisCount → ℂ)
      (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ)
      (_hTotal : P.totalDim = Q.totalDim)
      (X : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Xblock k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Xblock k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) ∧
      (∀ (k : Fin Q.basisCount) (q : Fin (Q.copies k)),
        Q.weight k q = (ζ k)⁻¹ * P.weight (β k) (τ k q)) ∧
      (∀ i : Fin d,
        Q.toTensor i =
          (X : Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                      (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) *
            toTensorFromBlocks (d := d)
              (μ := matched_p_weight (P := P) (Q := Q) β τ)
              (matched_p_basis (P := P) (Q := Q) β hDim) i *
            (((X)⁻¹ : GL (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ) :
              Matrix (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s))
                     (Fin (∑ s : Fin Q.totalCopies, Q.flatDim s)) ℂ)) := by
  classical
  obtain ⟨β, hDim, hCopies, τ, ζ, Xblock, hζ_norm, hConj, hWeight, X, _hXdef, hGauge⟩ :=
    ft_sector_bnt_equal_global_gaugePos hP hQ hEqual
  -- `P.totalDim = Q.totalDim` follows from `sectorFlatEquiv` plus matched dims
  have hTotal : P.totalDim = Q.totalDim :=
    SectorDecomposition.totalDim_eq_of_match (P := P) (Q := Q) β hDim τ
  -- the bond-dimension index `Q.totalDim` and `∑ s, Q.flatDim s` agree definitionally
  refine ⟨β, hDim, hCopies, τ, ζ, Xblock, hTotal, X, hζ_norm, hConj, hWeight, ?_⟩
  intro i
  exact hGauge i

/-! ## Coordinate identification between matched and literal blocks

The matched-coordinate `toTensorFromBlocks` and the literal `P.toTensor`
differ only by a $\Sigma$-level permutation of flattened sector indices
along `sectorFlatSigmaEquiv`; equivalently a permutation of
`Fin Q.totalDim` (after the bond-dimension equality) by
`sectorFlatDimEquiv`.  This lets us upgrade the matched-coordinate gauge
equation of `ft_sector_bnt_equal_mps_gaugeEquiv_witnessesPos` into the literal
form `ft_sector_bnt_equal_mps_gaugeEquiv_literalPos`, the equal-MPV corollary
form (CPSV16 §II.C lines 354–361). -/

/-- Cast of an `MPSTensor` along a bond-dimension equality, evaluated at one
physical site and two bond indices, equals the underlying tensor evaluated at
the inversely-cast indices. -/
private lemma mpsTensor_cast_apply {n m : ℕ} (h : n = m) (A : MPSTensor d n)
    (i : Fin d) (j₁ j₂ : Fin m) :
    (cast (congr_arg (MPSTensor d) h) A) i j₁ j₂ =
      A i (finCongr h.symm j₁) (finCongr h.symm j₂) := by
  subst h
  simp [finCongr]

/-- Coordinate identification of `matched_p_basis` with a cast of `P.flatBasis`
at the matched flat sector. -/
private lemma matched_p_basis_eq_cast_flatBasis
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
    (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
    (s : Fin Q.totalCopies) :
    matched_p_basis (P := P) (Q := Q) β hDim s =
      cast (congr_arg (MPSTensor d)
        (SectorDecomposition.flatDim_sectorFlatEquiv
          (P := P) (Q := Q) β hDim τ s))
        (P.flatBasis (SectorDecomposition.sectorFlatEquiv
          (P := P) (Q := Q) β τ s)) := by
  classical
  set k : Fin Q.basisCount := (Q.flatIndexEquiv.symm s).1 with hk_def
  -- `matched_p_basis β hDim s` reduces to `cast (hDim k) (P.basis (β k))`.
  have hMatched :
      matched_p_basis (P := P) (Q := Q) β hDim s =
        cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k)) := rfl
  -- `P.flatBasis (sectorFlatEquiv β τ s)` reduces to `P.basis (...).1`, where
  -- `(...).1 = β k` via `hsym`.
  have hsym :
      P.flatIndexEquiv.symm
          (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s) =
        ⟨β k, τ k (Q.flatIndexEquiv.symm s).2⟩ := by
    rw [SectorDecomposition.sectorFlatEquiv_apply, Equiv.symm_apply_apply]
  -- The dependent index `(P.flatIndexEquiv.symm (sectorFlatEquiv β τ s)).1` equals `β k`.
  have hk1 :
      (P.flatIndexEquiv.symm
          (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s)).1 =
        β k := congrArg Sigma.fst hsym
  rw [hMatched]
  -- Use HEq-elimination: both sides are casts of `P.basis (...)` at indices
  -- that equal `β k`.  We prove the underlying terms HEq, then transport.
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  refine HEq.trans ?_ (HEq.symm (cast_heq _ _))
  -- Goal: HEq (P.basis (β k)) (P.flatBasis (sectorFlatEquiv β τ s))
  -- which unfolds to HEq (P.basis (β k)) (P.basis ((P.flatIndexEquiv.symm _).1))
  change HEq (P.basis (β k))
    (P.basis (P.flatIndexEquiv.symm
      (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s)).1)
  -- Generalize the dependent index so we can perform `subst`.
  set k' : Fin P.basisCount :=
    (P.flatIndexEquiv.symm
      (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s)).1
    with hk'_def
  have hk1' : k' = β k := hk1
  clear_value k'
  subst hk1'
  rfl

/-- Pointwise identity: the matched-coordinate basis tensor at flattened sector
`s` equals the `P`-basis at the matched flattened sector, after reindexing the
inner bond-dimension `Fin`s by `flatDim_sectorFlatEquiv`. -/
private lemma matched_p_basis_apply
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
    (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
    (s : Fin Q.totalCopies) (i : Fin d) (m m' : Fin (Q.flatDim s)) :
    matched_p_basis (P := P) (Q := Q) β hDim s i m m' =
      P.flatBasis (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s) i
        (finCongr (SectorDecomposition.flatDim_sectorFlatEquiv
            (P := P) (Q := Q) β hDim τ s).symm m)
        (finCongr (SectorDecomposition.flatDim_sectorFlatEquiv
            (P := P) (Q := Q) β hDim τ s).symm m') := by
  rw [matched_p_basis_eq_cast_flatBasis (P := P) (Q := Q) β hDim τ s,
      mpsTensor_cast_apply
        (SectorDecomposition.flatDim_sectorFlatEquiv (P := P) (Q := Q) β hDim τ s)
        (P.flatBasis (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s))
        i m m']

/-- `matched_p_weight β τ s = P.flatWeight (sectorFlatEquiv β τ s)`. -/
private lemma matched_p_weight_eq_flatWeight
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
    (s : Fin Q.totalCopies) :
    matched_p_weight (P := P) (Q := Q) β τ s =
      P.flatWeight (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s) := by
  set k : Fin Q.basisCount := (Q.flatIndexEquiv.symm s).1
  have hsym :
      P.flatIndexEquiv.symm
          (SectorDecomposition.sectorFlatEquiv (P := P) (Q := Q) β τ s) =
        ⟨β k, τ k (Q.flatIndexEquiv.symm s).2⟩ := by
    rw [SectorDecomposition.sectorFlatEquiv_apply, Equiv.symm_apply_apply]
  change P.weight (β k) (τ k _) = P.weight _ _
  rw [hsym]

/-- The matched-coordinate tensor equals the submatrix of `P.toTensor` along
`sectorFlatDimEquiv` (the sector permutation between flat bond-dim indices). -/
private lemma matched_toTensor_eq_submatrix
    {P Q : SectorDecomposition d}
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
    (τ : (k : Fin Q.basisCount) → Fin (Q.copies k) ≃ Fin (P.copies (β k)))
    (i : Fin d) :
    toTensorFromBlocks (d := d)
        (μ := matched_p_weight (P := P) (Q := Q) β τ)
        (matched_p_basis (P := P) (Q := Q) β hDim) i =
      (P.toTensor i).submatrix
        (SectorDecomposition.sectorFlatDimEquiv (P := P) (Q := Q) β hDim τ)
        (SectorDecomposition.sectorFlatDimEquiv (P := P) (Q := Q) β hDim τ) := by
  classical
  -- Unfold both sides to `reindex finSigmaFinEquiv` applied to `blockDiagonal'`.
  -- Then identify the underlying blockDiagonal matrices via a Σ-level submatrix.
  ext j₁ j₂
  -- Decompose j₁, j₂ as flat-Q Σ-indices.
  obtain ⟨s, m⟩ : (s : Fin Q.totalCopies) × Fin (Q.flatDim s) :=
    finSigmaFinEquiv.symm j₁
  obtain ⟨s', m'⟩ : (s' : Fin Q.totalCopies) × Fin (Q.flatDim s') :=
    finSigmaFinEquiv.symm j₂
  -- LHS: matched-block-diagonal at (⟨s,m⟩, ⟨s',m'⟩).
  -- RHS: P-block-diagonal at (σ_Sigma ⟨s,m⟩, σ_Sigma ⟨s',m'⟩) where σ_Sigma is
  -- the sigma-level equiv induced by sectorFlatDimEquiv.
  -- Compute both:
  have hLHS :
      toTensorFromBlocks (d := d)
          (μ := matched_p_weight (P := P) (Q := Q) β τ)
          (matched_p_basis (P := P) (Q := Q) β hDim) i j₁ j₂ =
        Matrix.blockDiagonal' (fun s : Fin Q.totalCopies =>
          matched_p_weight (P := P) (Q := Q) β τ s •
            matched_p_basis (P := P) (Q := Q) β hDim s i)
          (finSigmaFinEquiv.symm j₁) (finSigmaFinEquiv.symm j₂) := by
    simp [toTensorFromBlocks, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hRHS :
      ((P.toTensor i).submatrix
            (SectorDecomposition.sectorFlatDimEquiv (P := P) (Q := Q) β hDim τ)
            (SectorDecomposition.sectorFlatDimEquiv (P := P) (Q := Q) β hDim τ))
          j₁ j₂ =
        Matrix.blockDiagonal' (fun k : Fin P.totalCopies =>
          P.flatWeight k • P.flatBasis k i)
          (SectorDecomposition.sectorFlatSigmaEquiv (P := P) (Q := Q) β hDim τ
            (finSigmaFinEquiv.symm j₁))
          (SectorDecomposition.sectorFlatSigmaEquiv (P := P) (Q := Q) β hDim τ
            (finSigmaFinEquiv.symm j₂)) := by
    simp [Matrix.submatrix_apply,
      SectorDecomposition.sectorFlatDimEquiv_apply,
      SectorDecomposition.toTensor, toTensorFromBlocks,
      Matrix.reindex_apply, Equiv.symm_apply_apply]
  rw [hLHS, hRHS]
  -- Now compare two blockDiagonal' entries.  Case split on whether the
  -- Σ-base indices agree.
  -- finSigmaFinEquiv.symm j₁ = ⟨a, b⟩ for some a, b; we keep the let-binding
  -- abstract and split on the .fst components.
  set xs : (s : Fin Q.totalCopies) × Fin (Q.flatDim s) := finSigmaFinEquiv.symm j₁
  set xs' : (s : Fin Q.totalCopies) × Fin (Q.flatDim s) := finSigmaFinEquiv.symm j₂
  by_cases hss : xs.1 = xs'.1
  · -- Diagonal case: identify the matched data with the P-data at the matched sector.
    rcases xs with ⟨s₀, m₀⟩
    rcases xs' with ⟨s₀', m₀'⟩
    simp only at hss
    subst hss
    rw [Matrix.blockDiagonal'_apply_eq, SectorDecomposition.sectorFlatSigmaEquiv_apply,
      SectorDecomposition.sectorFlatSigmaEquiv_apply, Matrix.blockDiagonal'_apply_eq,
      Matrix.smul_apply, Matrix.smul_apply,
      matched_p_basis_apply (P := P) (Q := Q) β hDim τ s₀ i m₀ m₀',
      matched_p_weight_eq_flatWeight (P := P) (Q := Q) β τ s₀]
  · -- Off-diagonal case: both sides are zero.
    rcases xs with ⟨s₀, m₀⟩
    rcases xs' with ⟨s₀', m₀'⟩
    simp only at hss
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hss,
      SectorDecomposition.sectorFlatSigmaEquiv_apply,
      SectorDecomposition.sectorFlatSigmaEquiv_apply,
      Matrix.blockDiagonal'_apply_ne _ _ _ (fun h => hss
        ((SectorDecomposition.sectorFlatEquiv
          (P := P) (Q := Q) β τ).injective h))]

/-- The general linear group element associated with a permutation of a finite
type: realized as the unit whose underlying matrix is `Equiv.Perm.permMatrix σ`
and whose inverse is `Equiv.Perm.permMatrix σ.symm`. -/
noncomputable def permGL {n : Type*} [DecidableEq n] [Fintype n]
    (σ : Equiv.Perm n) : GL n ℂ :=
  ⟨Equiv.Perm.permMatrix ℂ σ, Equiv.Perm.permMatrix ℂ σ.symm,
    by
      have hmul : Equiv.Perm.permMatrix ℂ σ * Equiv.Perm.permMatrix ℂ σ.symm =
          Equiv.Perm.permMatrix ℂ (σ.symm * σ) :=
        (Matrix.permMatrix_mul (σ := σ.symm) (τ := σ)).symm
      rw [hmul]
      change Equiv.Perm.permMatrix ℂ (σ⁻¹ * σ) = 1
      rw [inv_mul_cancel]
      exact Matrix.permMatrix_one,
    by
      have hmul : Equiv.Perm.permMatrix ℂ σ.symm * Equiv.Perm.permMatrix ℂ σ =
          Equiv.Perm.permMatrix ℂ (σ * σ.symm) :=
        (Matrix.permMatrix_mul (σ := σ) (τ := σ.symm)).symm
      rw [hmul]
      change Equiv.Perm.permMatrix ℂ (σ * σ⁻¹) = 1
      rw [mul_inv_cancel]
      exact Matrix.permMatrix_one⟩

@[simp]
theorem permGL_val {n : Type*} [DecidableEq n] [Fintype n] (σ : Equiv.Perm n) :
    (permGL σ : Matrix n n ℂ) = Equiv.Perm.permMatrix ℂ σ := rfl

@[simp]
theorem permGL_inv_val {n : Type*} [DecidableEq n] [Fintype n] (σ : Equiv.Perm n) :
    (((permGL σ)⁻¹ : GL n ℂ) : Matrix n n ℂ) = Equiv.Perm.permMatrix ℂ σ.symm := rfl

/-- Entrywise expansion of `Equiv.Perm.permMatrix`. -/
private lemma permMatrix_apply' {n : Type*} [DecidableEq n] (σ : Equiv.Perm n)
    (i j : n) :
    Equiv.Perm.permMatrix ℂ σ i j = if j = σ i then (1 : ℂ) else 0 := by
  rw [Equiv.Perm.permMatrix]
  by_cases h : j = σ i
  · subst h
    rw [if_pos rfl, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp
  · rw [if_neg h, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_def, Option.some.injEq, ite_eq_right_iff,
      one_ne_zero, imp_false]
    exact fun heq => h heq.symm

/-- Multiplying a matrix on the left by `permMatrix σ` reindexes its rows by `σ`. -/
private lemma permMatrix_mul_eq_submatrix {n : Type*}
    [DecidableEq n] [Fintype n] (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M = M.submatrix σ id := by
  ext i j
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id]
  simp_rw [permMatrix_apply', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (σ i)]
  simp

/-- Multiplying a matrix on the right by `permMatrix σ` reindexes its columns by
`σ.symm`. -/
private lemma mul_permMatrix_eq_submatrix {n : Type*}
    [DecidableEq n] [Fintype n] (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    M * Equiv.Perm.permMatrix ℂ σ = M.submatrix id σ.symm := by
  ext i j
  rw [Matrix.mul_apply, Matrix.submatrix_apply, id]
  simp_rw [permMatrix_apply', mul_ite, mul_one, mul_zero]
  -- Rewrite the condition `j = σ x` to `σ.symm j = x` so `sum_ite_eq` applies.
  have hcond : ∀ x : n, (j = σ x) ↔ (σ.symm j = x) := by
    intro x
    constructor
    · intro h; rw [h]; exact σ.symm_apply_apply x
    · intro h; rw [← h]; exact (σ.apply_symm_apply j).symm
  simp_rw [hcond]
  rw [Finset.sum_ite_eq Finset.univ (σ.symm j)]
  simp

/-- Conjugating a square matrix by a permutation matrix gives a `submatrix` of
the original by the permutation index map. -/
private lemma permMatrix_conj_eq_submatrix {n : Type*}
    [DecidableEq n] [Fintype n] (σ : Equiv.Perm n) (M : Matrix n n ℂ) :
    Equiv.Perm.permMatrix ℂ σ * M * Equiv.Perm.permMatrix ℂ σ.symm =
      M.submatrix σ σ := by
  rw [permMatrix_mul_eq_submatrix, mul_permMatrix_eq_submatrix,
    Matrix.submatrix_submatrix]
  simp

/-- **BNT equal-MPV literal global-gauge form.**

If two BNT sector decompositions satisfying `IsBNTCanonicalForm` generate the
same MPV family, then their total bond dimensions agree, and there exists an
explicit
$Y \in \mathrm{GL}(Q.\mathrm{totalDim},\mathbb{C})$ realizing the global gauge
equation
$$V_Q^i \;=\; Y \,\bigl(\mathrm{cast}\;V_P^i\bigr)\, Y^{-1}$$
at every physical site $i$, where the inner factor is the bond-dim cast of the
literal $P$-tensor along the total-dimension equality.

This reformulates the matched-coordinate gauge equation
`ft_sector_bnt_equal_mps_gaugeEquiv_witnessesPos` (CPSV16 Appendix MPV proof,
lines 1189–1192) into the equal-MPV corollary labelled II_cor2 in CPSV16
§II.C lines 354–361 by composing the matched-coordinate global gauge with the
sector permutation.

CPSV16 §II.C lines 354–361. -/
theorem ft_sector_bnt_equal_mps_gaugeEquiv_literalPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (hTotal : P.totalDim = Q.totalDim) (Y : GL (Fin Q.totalDim) ℂ),
      ∀ i : Fin d,
        Q.toTensor i =
          (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
            cast (by rw [hTotal] :
                Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
                Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
              (P.toTensor i) *
            (((Y)⁻¹ : GL (Fin Q.totalDim) ℂ) :
              Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) := by
  classical
  obtain ⟨β, hDim, _hCopies, τ, _ζ, _Xblock, _hTotal, X, _, _, _, hGauge⟩ :=
    ft_sector_bnt_equal_mps_gaugeEquiv_witnessesPos hP hQ hEqual
  -- Total bond dimensions agree.
  have hTotal : P.totalDim = Q.totalDim :=
    SectorDecomposition.totalDim_eq_of_match (P := P) (Q := Q) β hDim τ
  refine ⟨hTotal, ?_⟩
  -- Sector-permutation `ρ := sectorFlatDimEquiv ∘ finCongr hTotal` on
  -- `Fin Q.totalDim`.
  set ρ : Equiv.Perm (Fin Q.totalDim) :=
    (SectorDecomposition.sectorFlatDimEquiv (P := P) (Q := Q) β hDim τ).trans
      (finCongr hTotal) with hρ_def
  -- The witness `X` has type `GL (Fin (∑ s, Q.flatDim s)) ℂ`, which is
  -- definitionally equal to `GL (Fin Q.totalDim) ℂ` since `totalDim` is a
  -- reducible def.  Bind `X'` to the same value at the `Q.totalDim` form via
  -- `let` so that `X' = X` definitionally.
  let X' : GL (Fin Q.totalDim) ℂ := X
  refine ⟨X' * permGL ρ, ?_⟩
  intro i
  -- (i) `matched_tensor i = (P.toTensor i).submatrix sectorFlatDimEquiv ...`
  have hsubm := matched_toTensor_eq_submatrix (P := P) (Q := Q) β hDim τ i
  -- (ii) cast of `P.toTensor i` equals submatrix along `finCongr hTotal.symm`.
  have hCast :
      cast (by rw [hTotal] :
          Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
        (P.toTensor i) =
        (P.toTensor i).submatrix (finCongr hTotal.symm) (finCongr hTotal.symm) := by
    -- The cast of a `Matrix (Fin n) (Fin n) ℂ` along a bond-dim equality
    -- equals the `submatrix` by `finCongr` of the inverse.
    have hgen : ∀ (n m : ℕ) (h : n = m) (M : Matrix (Fin n) (Fin n) ℂ),
        cast (by rw [h] :
            Matrix (Fin n) (Fin n) ℂ = Matrix (Fin m) (Fin m) ℂ) M =
          M.submatrix (finCongr h.symm) (finCongr h.symm) := by
      intro n m h M
      subst h
      simp [finCongr]
    exact hgen P.totalDim Q.totalDim hTotal (P.toTensor i)
  -- (iii) connect `matched_tensor` to cast via `permMatrix ρ` conjugation.
  have hPerm :
      (permGL ρ : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
          cast (by rw [hTotal] :
              Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
              Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
            (P.toTensor i) *
          (((permGL ρ)⁻¹ : GL (Fin Q.totalDim) ℂ) :
            Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) =
        toTensorFromBlocks (d := d)
            (μ := matched_p_weight (P := P) (Q := Q) β τ)
            (matched_p_basis (P := P) (Q := Q) β hDim) i := by
    rw [permGL_val, permGL_inv_val, hCast,
      permMatrix_conj_eq_submatrix ρ
        ((P.toTensor i).submatrix (finCongr hTotal.symm) (finCongr hTotal.symm)),
      Matrix.submatrix_submatrix, hsubm]
    -- The composition `(finCongr hTotal.symm) ∘ ρ` reduces to
    -- `sectorFlatDimEquiv`; both sides of the equation are then identical
    -- submatrices of `P.toTensor i`.
    rfl
  -- (iv) combine the matched-coord gauge with the sector permutation.
  -- We have: Q.toTensor i = X * matched * X⁻¹ from hGauge.  Substituting in the
  -- conjugation `hPerm` gives the desired equation.  Use that `X'` (resp.
  -- `X'⁻¹`) coerces to the same matrix as `X` (resp. `X⁻¹`).
  rw [hGauge i, ← hPerm]
  have hY_inv :
      (((X' * permGL ρ)⁻¹ : GL (Fin Q.totalDim) ℂ) :
        Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) =
        (((permGL ρ)⁻¹ : GL (Fin Q.totalDim) ℂ) :
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
        ((X'⁻¹ : GL (Fin Q.totalDim) ℂ) :
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) := by
    rw [mul_inv_rev]; rfl
  rw [hY_inv]
  -- `X` and `X'` are definitionally equal (`X' := X` via `let`); reformulate
  -- the goal entirely in terms of `X'` before invoking matrix associativity.
  change (X' : Matrix _ _ ℂ) *
      ((permGL ρ : Matrix _ _ ℂ) *
        cast (by rw [hTotal] :
            Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
            Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) (P.toTensor i) *
        (((permGL ρ)⁻¹ : GL (Fin Q.totalDim) ℂ) :
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)) *
      ((X'⁻¹ : GL (Fin Q.totalDim) ℂ) :
        Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) =
    ((X' : Matrix _ _ ℂ) * (permGL ρ : Matrix _ _ ℂ)) *
      cast (by rw [hTotal] :
          Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) (P.toTensor i) *
      ((((permGL ρ)⁻¹ : GL (Fin Q.totalDim) ℂ) :
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
        ((X'⁻¹ : GL (Fin Q.totalDim) ℂ) :
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ))
  simp only [Matrix.mul_assoc]

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem ft_sector_bnt_equal_mps_gaugeEquiv_literal
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (hTotal : P.totalDim = Q.totalDim) (Y : GL (Fin Q.totalDim) ℂ),
      ∀ i : Fin d,
        Q.toTensor i =
          (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
            cast (by rw [hTotal] :
                Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
                Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
              (P.toTensor i) *
            (((Y)⁻¹ : GL (Fin Q.totalDim) ℂ) :
              Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) :=
  ft_sector_bnt_equal_mps_gaugeEquiv_literalPos
    (P := P) (Q := Q) hP hQ hEqual.toSameMPV₂Pos

/-- **Fundamental Theorem of MPS, equal case (CPSV16 Corollary II.2).**

Two BNT canonical forms generating the same MPV family at every length are
globally conjugate: their total bond dimensions agree, and a single invertible
gauge `Y` carries one total tensor to the other.  This is the literal
equal-case source statement on the basis-of-normal-tensors canonical-form
surface — no per-sector unit-modulus restriction and no one-site injectivity
assumption (arXiv:1606.00608, Corollary II.2; Appendix MPV proof,
lines 1189–1192). -/
theorem fundamentalTheorem_equal_canonicalForm
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ (hTotal : P.totalDim = Q.totalDim) (Y : GL (Fin Q.totalDim) ℂ),
      ∀ i : Fin d,
        Q.toTensor i =
          (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
            cast (by rw [hTotal] :
                Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
                Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
              (P.toTensor i) *
            (((Y)⁻¹ : GL (Fin Q.totalDim) ℂ) :
              Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) :=
  ft_sector_bnt_equal_mps_gaugeEquiv_literal hP hQ hEqual

/-- **Fundamental Theorem of MPS, proportional multi-block case (CPSV16
Theorem II.1) on the BNT canonical-form surface.**

Eventual projective proportionality of the generated MPV families matches the
normal-tensor sectors bijectively.  For each `Q`-sector `k`, the matched
`P`-sector `β k` has the same bond dimension (`g_a = g_b` via the bijection
`β`) and `Q.basis k` is obtained from `P.basis (β k)` by a per-normal-tensor
unit phase and gauge conjugation. -/
theorem fundamentalTheorem_proportional_canonicalForm
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor) :
    ∃ (β : Fin Q.basisCount ≃ Fin P.basisCount)
      (hDim : ∀ k : Fin Q.basisCount, P.basisDim (β k) = Q.basisDim k)
      (ζ : Fin Q.basisCount → ℂ)
      (Y : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ),
      (∀ k : Fin Q.basisCount, ‖ζ k‖ = 1) ∧
      (∀ (k : Fin Q.basisCount) (i : Fin d),
        Q.basis k i =
          ζ k • ((Y k : Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ) *
            (cast (congr_arg (MPSTensor d) (hDim k)) (P.basis (β k))) i *
            (((Y k)⁻¹ : GL (Fin (Q.basisDim k)) ℂ) :
              Matrix (Fin (Q.basisDim k)) (Fin (Q.basisDim k)) ℂ))) := by
  classical
  obtain ⟨β, hDim, ζ, Y, hζ_norm, hConj, _hMpv⟩ :=
    ft_sector_bnt_proportional_sector_match_witnesses
      (P := P) (Q := Q) hP hQ hProp
  exact ⟨β, hDim, ζ, Y, hζ_norm, hConj⟩

end MPSTensor
