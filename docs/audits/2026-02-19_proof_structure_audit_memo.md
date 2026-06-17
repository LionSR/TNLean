---
modifiedBy: chat
executionId: 9cf3f20c5c10
modifiedAt: 2026-02-19T08:23:43.761Z
---
# MPS Lean Formalization — Proof Structure Audit
## Written: 2026-02-19

---

## I. Executive Overview

The project formalizes the **Fundamental Theorem of Matrix Product States (FT-MPS)** in Lean 4 /
Mathlib. The theorem states that two MPS tensors A, B are gauge equivalent (B_i = X A_i X⁻¹) if
and only if they generate the same Matrix Product Vector (MPV) family — the complete invariant
classifying MPS under local unitary equivalence.

**Sorry status**: 9 of the 10 audited files are **completely sorry-free**. The 10th
(`SpectralGap.lean`) contains 7 occurrences of the word "sorry" — but every single one is in a
*comment* describing the proof strategy. There is no `sorry` tactic anywhere in the 10 audited
files. Only `TNLean/PiAlgebra/BlockSeparationProof.lean` (not in the 10 audited files) and
`TNLean/Scratch/KerInvariance.lean` contain actual sorry tactics, both intentionally gated behind
`TNLean/Experimental.lean`.

---

## II. Per-File Technical Summary

### 1. `TNLean/MPS/FundamentalTheorem.lean` — Single-block FT

**Lines**: ~63

**Main theorem**:
```
fundamentalTheorem_singleBlock :
  IsInjective A → SameMPV A B → GaugeEquiv A B
```
In mathematics: If A is injective (span{A^i} = M_D(ℂ)) and ∀N,σ: mpv(A,σ) = mpv(B,σ),
then ∃ X ∈ GL(D,ℂ) such that B_i = X A_i X⁻¹ for all i.

**Sorry**: None.

**Key proof technique**: Three-step algebraic argument:
1. **Linear extension** (`LinearExtension.lean`): Unique linear map T with T(A_i) = B_i;
   multiplicativity T(A·B) = T(A)·T(B) from SameMPV + injectivity.
2. **Simplicity** (`SkolemNoether.lean`): A nonzero multiplicative endomorphism of M_D(ℂ)
   (a simple algebra) is automatically bijective → T is an algebra automorphism.
3. **Skolem–Noether** (`SkolemNoether.lean`): Every automorphism of M_n(ℂ) is inner,
   i.e., of the form Ad_X for some X ∈ GL_n(ℂ).

**Connection to literature**: Theorem 1 of Pérez-García, Verstraete, Wolf, Cirac 2007
(quant-ph/0608197). The Lean proof follows the Skolem–Noether route used in Wolf 2012.

---

### 2. `TNLean/PiAlgebra/CanonicalFormSep.lean` — Block separation core

**Lines**: ~1094

**Main theorems**:

```
IsCanonicalForm (structure) :
  block_injective : ∀ k, IsInjective (A k)
  ds_gauge        : ∀ k, ∑ i, (A k i)ᴴ * (A k i) = 1
  mu_strict_anti  : StrictAnti (λ k => ‖μ k‖)   -- |μ₀| > |μ₁| > … > |μ_{r-1}|
  mu_ne_zero      : ∀ k, μ k ≠ 0
  overlap_tendsto_one : ∀ k, mpvOverlap (A k) (A k) N →_{N→∞} 1
```

```
block_separation_core :
  StrictAnti (‖μ k‖)  →  hμ_ne_zero  →  hA_inj  →  hB_inj  →
  hA_ds  →  hB_ds  →  hA_overlap  →
  (∀ N σ, ∑_k μ_k^N · (mpv(A k,σ) - mpv(B k,σ)) = 0)
  → ∀ k, SameMPV (A k) (B k)
```

```
peeling_exponential_bound :
  0 < r  →  α₀ ≠ 0  →  ‖δ k L‖ ≤ B  →  ∑_k α_k^L · δ_k(L) = 0  →
  ‖α_k‖ ≤ ‖α₀‖ · ρ (k ≠ 0, ρ < 1)
  → ∃ C ≥ 0, ∀ L, ‖δ₀(L)‖ ≤ C · ρ^L
```

```
fundamentalTheorem_canonicalForm :
  IsCanonicalForm μ A  →  hB_inj  →  hB_ds  →
  SameMPV₂ (blockdiag μ A) (blockdiag μ B)
  → (∀ k, GaugeEquiv (A k) (B k)) ∧ GaugeEquiv (blockdiag μ A) (blockdiag μ B)
```

**Sorry**: None.

**Key proof technique**: Mixed-transfer/overlap peeling route by induction on r:
- **r = 0,1**: Direct cancellation by μ₀^N ≠ 0.
- **r ≥ 2 (inductive step)**:
  1. **Overlap identity**: Take star + sum against mpv(A₀,·) to derive
     ∑_k (star μ_k)^N · (Ov(A₀,A_k,N) - Ov(A₀,B_k,N)) = 0.
  2. **Peeling**: Apply `peeling_exponential_bound` to get
     |Ov(A₀,A₀,N) - Ov(A₀,B₀,N)| ≤ C · ρ^N → 0.
  3. **Limit argument**: Combined with hA_overlap (self-overlap → 1):
     Ov(A₀,B₀,N) → 1.
  4. **Dichotomy via spectral gap**: If ¬GaugePhaseEquiv(A₀,B₀), then
     `mpvOverlap_tendsto_zero` gives Ov(A₀,B₀,N) → 0 ≠ 1, contradiction.
  5. **Phase cancellation**: GaugePhaseEquiv → ∃ X,ζ: B₀ i = ζ·X A₀ i X⁻¹;
     the ratio Ov(A₀,B₀,N)/Ov(A₀,A₀,N) = (star ζ)^N → 1, forcing ζ = 1.
     Thus GaugeEquiv(A₀,B₀) and SameMPV(A₀,B₀).
  6. **Induction**: Subtract the k=0 term from the sum; IH applies to the r-block tail.

**Connection to literature**: Pérez-García et al. 2007 (Appendix E, Thm. 1 for multi-block).
Cirac, Pérez-García et al. 2021 (arXiv:2011.12127, Thm. IV.3).

---

### 3. `TNLean/Spectral/SpectralGap.lean` — Spectral gap

**Lines**: ~1214

**Main theorems**:

```
eigenvalue_norm_le_one [NeZero D] :
  ∑ i, (A i)ᴴ * A i = 1  →  ∑ i, (B i)ᴴ * B i = 1  →
  HasEigenvalue (mixedTransferMap A B) μ  →  ‖μ‖ ≤ 1
```

```
spectralRadius_mixedTransfer_le_one :
  ∑ i, (A i)ᴴ * A i = 1  →  ∑ i, (B i)ᴴ * B i = 1
  → ρ(F_{AB}) ≤ 1    (ρ = spectral radius)
```

```
eigenvector_gives_gauge [NeZero D] :
  IsInjective A  →  IsInjective B  →  normalized  →
  F_{AB}(X) = μ·X  →  ‖μ‖ = 1  →  X ≠ 0
  → GaugePhaseEquiv A B
```

```
modulus_one_eigenvalue_implies_gauge :
  ρ(F_{AB}) ≥ 1  →  GaugePhaseEquiv A B
```

```
spectralRadius_mixedTransfer_lt_one :
  IsInjective A  →  IsInjective B  →  normalized  →  ¬GaugePhaseEquiv A B
  →  ρ(F_{AB}) < 1
```

```
mixedTransfer_pow_tendsto_zero :
  ¬GaugePhaseEquiv A B  →  ∀ X, F_{AB}^n(X) →_{n→∞} 0
```

**Sorry**: None (all occurrences are in comments).

**Key proof techniques**:

*Upper bound* (|μ| ≤ 1): From the HS contraction bound
  ‖F_{AB}^n(X)‖_F² ≤ D² · ‖X‖_F²,
eigenvectors satisfy ‖μ‖^{2n} ≤ D²; taking n → ∞ forces ‖μ‖ ≤ 1.
The HS contraction uses Cauchy-Schwarz on word sums + the iterated TP identity
∑_σ evalWord(A,σ)† evalWord(A,σ) = I.

*Eigenvector → gauge* (the algebraic core):
1. DS-gauge both tensors via QPF fixed point: A' = S_A⁻¹ A S_A, B' = S_B⁻¹ B S_B.
2. Let X' = S_A⁻¹ X (S_B†)⁻¹ (gauged eigenvector), X' ≠ 0.
3. Embed in block unital Kraus map K_i = diag(A'_i, B'_i).
4. Apply KS equality (`Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint`
   from Channel/Schwarz) to get M * K_i† = K_i† * (μ·M), giving intertwining
   X' (B'_i)† = μ·(A'_i)† X' and A'_i X' = μ·X' B'_i.
5. Kernel invariance: X' *ᵥ v = 0 → X' *ᵥ ((B'_k)† *ᵥ v) = 0
   → by injectivity of B' (inherited from B via conjugation), ker(X') = {0}
   → det(X') ≠ 0 via `det_ne_zero_of_ker_all`.
6. From A'_i X' = μ·X' B'_i and det(X') ≠ 0: B'_i = μ⁻¹·X'⁻¹ A'_i X'.
7. Gauge back: Y = S_B X'⁻¹ S_A⁻¹ ∈ GL → B_i = μ⁻¹·Y A_i Y⁻¹.

*Power convergence*: Spectral radius < 1 → powers tend to zero in CL(V) →
  apply evaluation functional.

**Connection to literature**: Evans-Hanche-Olsen 1978; Pérez-García et al. 2007 Lemma 5;
Wolf 2012 §6.2 (multiplicative domain characterization).

---

### 4. `TNLean/Spectral/MixedTransferRect.lean` — Rectangular mixed transfer

**Lines**: ~92

**Main theorems**:

```
mixedTransferMap₂ (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
  Matrix (Fin D₁) (Fin D₂) ℂ →ₗ[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ
  defined by X ↦ ∑_i A_i · X · (B_i)†
```

```
mixedTransferMap₂_apply : mixedTransferMap₂ A B X = ∑ i, A_i * X * (B_i)†
```

```
mixedTransferMap₂_pow_apply :
  (F_{AB})^N(X) = ∑_{σ: Fin N → Fin d} evalWord(A,σ) · X · (evalWord(B,σ))†
```

**Sorry**: None.

**Key proof technique**: Induction on N; `sum_fin_succ_eq` for head+tail reindexing of
word-length-N+1 paths; relies on `Mathlib.Data.Matrix.Bilinear` for rectangular matrix
multiplication linear maps (`mulLeftLinearMap`, `mulRightLinearMap`).

**Connection to literature**: Heterogeneous-bond-dimension generalization needed for the
multi-block FT where blocks may have different bond dimensions D₁ ≠ D₂. Used as
infrastructure for `MPVOverlapTraceRect`.

---

### 5. `TNLean/Spectral/MPVOverlapDecay.lean` — Overlap decay

**Lines**: ~145

**Main theorems**:

```
mpvOverlap_tendsto_zero [NeZero D] :
  IsInjective A  →  IsInjective B  →  normalized A  →  normalized B  →
  ¬GaugePhaseEquiv A B
  →  mpvOverlap (A, B, N) →_{N→∞} 0

mpvInner_tendsto_zero [NeZero D] :
  (same hypotheses)  →  mpvInner (A, B, N) →_{N→∞} 0
```

where `mpvOverlap A B N = ∑_{σ: Fin N → Fin d} mpv(A,σ) · star(mpv(B,σ))`.

**Sorry**: None.

**Key proof technique**:
1. Use `trace_mixedTransferMap_pow_eq_mpvOverlap` to write mpvOverlap(A,B,N) = Tr(F_{AB}^N).
2. Expand Tr(T) = ∑_{p,q} (T e_{pq})_{pq} via `linearMap_trace_eq_sum_apply_single`.
3. For each (p,q): entry functional is continuous → entry of F_{AB}^N(e_{pq}) → 0 by
   `mixedTransfer_pow_tendsto_zero`.
4. Finite sum of convergent sequences → 0.
5. `mpvInner_tendsto_zero` follows from `mpvOverlap_eq_star_mpvInner` + continuity of star.

**Connection to literature**: Standard "equal-or-orthogonal" dichotomy: distinct primitive
blocks have exponentially decaying cross-overlaps. Key ingredient for the block separation
inductive step.

---

### 6. `TNLean/Spectral/MPVOverlapTraceRect.lean` — Overlap trace identity (rectangular)

**Lines**: ~180

**Main theorems**:

```
linearMap_trace_eq_sum_apply_single₂ [NeZero D₁] [NeZero D₂] :
  Tr(T) = ∑_{p: Fin D₁} ∑_{q: Fin D₂} (T(e_{pq}))_{pq}
  where e_{pq} = Matrix.single p q 1

entry_mul_single_mul₂ :
  (M · e_{pq} · N)_{pq} = M_{pp} · N_{qq}

trace_mixedTransferMap₂_pow_eq_mpvOverlap [NeZero D₁] [NeZero D₂] :
  Tr((F_{AB})^N) = ∑_{σ: Fin N → Fin d} mpv(A,σ) · star(mpv(B,σ))
  = mpvOverlap(A, B, N)
```

**Sorry**: None.

**Key proof technique**:
- Trace expansion: use `Matrix.stdBasis` as the basis for rectangular matrices;
  `LinearMap.trace_eq_matrix_trace` converts operator trace to matrix trace;
  diagonal entry read-off gives the double sum formula.
- Entry identity: `Matrix.mul_single_apply_same/of_ne` isolate the single nonzero column.
- Overlap assembly: reorder ∑_{p,q,σ} to ∑_σ ∑_p ∑_q; factorize as
  (∑_p A_{pp})(∑_q (B†)_{qq}) = Tr(evalWord A) · Tr(evalWord B)† = mpv(A,σ)·star(mpv(B,σ)).

**Connection to literature**: Bridge identity connecting the operator-algebraic spectral
gap (spectral radius of F_{AB}) with the combinatorial MPV overlap sum; fundamental to the
"overlap decay ↔ spectral gap" equivalence used in block separation.

---

### 7. `TNLean/PiAlgebra/NewtonGirard.lean` — Newton-Girard identities

**Lines**: ~316

**Main theorems**:

```
newton_girard_charpolyRev_coeff (M : Matrix n n R) (m : ℕ) :
  (m+1) · p_{m+1} = -∑_{j=0}^{m} p_j · tr(M^{m+1-j})
  where p_k = (charpolyRev M).coeff k,  charpolyRev M = det(I - X·M)
```

```
charpolyRev_eq_of_forall_trace_pow_eq [CharZero R] [IsDomain R] :
  (∀ k ≥ 1, tr(A^k) = tr(B^k))  →  charpolyRev A = charpolyRev B
```

```
charpoly_eq_of_forall_trace_pow_eq [CharZero R] [IsDomain R] :
  (∀ k ≥ 1, tr(A^k) = tr(B^k))  →  charpoly A = charpoly B
```

**Sorry**: None.

**Key proof technique**:
- **Jacobi's formula**: differentiate P(X) = det(I - X·M); use adjugate identity
  adj(F)·F = det(F)·I and column-expansion det_updateCol.
- **T_trace recursion**: T(l,X) = Tr((M.map C)^l · adj(I - X·M)) satisfies
  T(l,X) - X·T(l+1,X) = P(X)·C(tr(M^l)).
- **Coefficient extraction** by induction on m: T_trace_coeff.
- **Equality of charpolys**: strong induction on m; use Newton-Girard recursion;
  equality of RHS sums by IH + trace hypothesis; cancel (m+1) via CharZero + IsDomain.
- **charpoly vs charpolyRev**: `reverse_charpoly` + `reflect_reflect` involution.

**Connection to literature**: Newton's identities (power sums → elementary symmetric
polynomials → characteristic polynomial). Classical algebraic result formalized from
scratch using the Jacobi formula route rather than the combinatorial multiset route.
Key algebraic ingredient used (implicitly) in the older block separation strategy via
`sameMPV₂_repeated_word` + power-trace comparison; the current proof route in
`CanonicalFormSep.lean` uses spectral gap instead, but NewtonGirard remains available
as an alternative algebraic path.

---

### 8. `TNLean/Algebra/GramMatrixLI.lean` — Gram matrix linear independence

**Lines**: ~73

**Main theorem**:

```
eventually_linearIndependent_of_gram_tendsto_id :
  (∀ i j, ⟪v_i(N), v_j(N)⟫_ℂ →_{N→∞} δ_{ij})
  →  ∀ᶠ N in atTop, LinearIndependent ℂ (λ i => v_i(N))
```

**Sorry**: None.

**Key proof technique**:
1. Form Gram matrix G(N)_{ij} = ⟪v_i(N), v_j(N)⟫.
2. G(N) → I by `tendsto_pi_nhds`.
3. det(G(N)) → det(I) = 1 by continuity of det.
4. Eventually det(G(N)) ≠ 0 via `Tendsto.eventually_ne`.
5. det ≠ 0 → G(N) is nondegenerate → {v_i(N)} are linearly independent by
   `Matrix.eq_zero_of_mulVec_eq_zero`.

**Connection to literature**: Lem1 from MPDO papers arXiv:1606.00608 and arXiv:1708.00029
(Cirac, Pérez-García, Schuch et al.): eventual linear independence of MPV states from
distinct blocks, needed to establish the isomorphism underlying the block structure.

---

### 9. `TNLean/PiAlgebra/FundamentalTheoremComplete.lean` — Multi-block assembly

**Lines**: ~214

**Main theorems**:

```
fundamentalTheorem_multiBlock_full :
  (∀ k, IsInjective (A k))  →  (∀ k, SameMPV (A k) (B k))
  →  (∀ k, GaugeEquiv (A k) (B k)) ∧ GaugeEquiv (blockdiag μ A) (blockdiag μ B)

fundamentalTheorem_multiBlock_explicit :
  (∀ k, IsInjective (A k))  →  (∀ k, SameMPV (A k) (B k))
  →  ∃ (X_k : ∀ k, GL(dim k)), ∀ k i, B k i = X_k · A k i · X_k⁻¹

fundamentalTheorem_multiBlock_decomposition :
  ∃ σ : Fin r ≃ Fin r, ∃ hDeq, ∃ X_i, ∀ i M,
    reindex(componentMap(piAlgEquiv A B) σ i M) = X_i · M · X_i⁻¹
```

```
sameMPV₂_single_block (μ₀ ≠ 0) :
  SameMPV₂ (blockdiag(μ₀) A₀) (blockdiag(μ₀) B₀)  →  SameMPV A₀ B₀

fundamentalTheorem_singleBlock_fromMPV₂ :
  (μ₀ ≠ 0)  →  IsInjective A₀  →  SameMPV₂(...)  →  GaugeEquiv A₀ B₀

fundamentalTheorem_multiBlock_fromSameMPV₂ :
  SameMPV₂(blockdiag A, blockdiag B)  →  (separation hyp: ∀ k, SameMPV(A k, B k))
  →  (∀ k, GaugeEquiv(A k, B k)) ∧ global GaugeEquiv ∧ block-permutation decomposition

perBlock_sameMPV_iff_gaugeEquiv :
  (∀ k, IsInjective (A k))
  →  (∀ k, SameMPV (A k) (B k)) ↔ (∀ k, GaugeEquiv (A k) (B k))
```

**Sorry**: None.

**Key proof technique**: Thin assembly layer using `fundamentalTheorem_singleBlock`
applied blockwise; `piAlgEquiv_decomposition` for the block-permutation structure;
single-block shortcut via μ₀^N cancellation.

**Connection to literature**: The "block-permutation + gauge" structure of the FT for
multi-block (non-injective) MPS; corresponds to Theorem IV.2 of Cirac et al. 2021.

---

### 10. `TNLean/MPS/FundamentalTheoremMulti.lean` — Multi-block theorem

**Lines**: ~214

**Main theorems**:

```
toTensorFromBlocks μ A : MPSTensor d (∑_k dim k)
  := fun i => reindex(blockDiag'(λ k => μ k • A k i))

blockDiagonalGL (X_k : ∀ k, GL(dim k)) : GL((k × Fin(dim k)))
  := ⟨blockDiag'(X_k), blockDiag'(X_k⁻¹), ⋯⟩

gaugeEquiv_toTensorFromBlocks_of_blockConj :
  (∀ k i, B k i = X_k · A k i · X_k⁻¹)
  →  GaugeEquiv (blockdiag μ A) (blockdiag μ B)

fundamentalTheorem_multiBlock_global :
  (∀ k, IsInjective (A k))  →  (∀ k, SameMPV (A k) (B k))
  →  GaugeEquiv (blockdiag μ A) (blockdiag μ B)

mpv_toTensorFromBlocks_eq_sum :
  mpv(blockdiag μ A, σ) = ∑_k μ_k^N · mpv(A k, σ)

sameMPV_toTensorFromBlocks_of_blockSameMPV :
  (∀ k, SameMPV (A k) (B k))  →  SameMPV (blockdiag μ A) (blockdiag μ B)
```

**Sorry**: None.

**Key proof technique**:
- `finSigmaFinEquiv` reindexing: the block-diagonal index `(k : Fin r) × Fin(dim k)`
  is equipped with a canonical bijection to `Fin(∑_k dim k)`.
- Block-diagonal GL: blockDiag'(X_k) · blockDiag'(X_k⁻¹) = I by `blockDiagonal'_mul`.
- Trace of block diagonal = sum of block traces (used in `mpv_toTensorFromBlocks_eq_sum`).
- Assembly: per-block gauge conjugation assembles into global conjugation by the
  block-diagonal GL element via `gaugeEquiv_toTensorFromBlocks_of_blockConj`.

**Connection to literature**: The "block-diagonal gauge transform" part of the multi-block
FT; constructive assembly showing that blockwise gauge transforms (X_k ∈ GL(D_k)) lift to
a global gauge transform (blockDiag(X_k) ∈ GL(∑_k D_k)).

---

## III. End-to-End Mathematical Narrative

The project proves the following complete theorem chain (all sorry-free in the core):

### Step 0: MPV overlap is an operator trace
`mpvOverlap(A,B,N) = ∑_σ mpv(A,σ)·star(mpv(B,σ)) = Tr(F_{AB}^N)`

Proved in `MPVOverlapTraceRect.lean` via the identity Tr(T) = ∑_{p,q}(T e_{pq})_{pq}
applied to the rectangular mixed transfer operator F_{AB}^N.

### Step 1: Spectral gap for distinct blocks
If A,B injective + normalized + ¬GaugePhaseEquiv(A,B), then ρ(F_{AB}) < 1, hence
F_{AB}^N(X) → 0 for all X, hence mpvOverlap(A,B,N) → 0.

Key: HS contraction bound (Cauchy-Schwarz on word sums + TP identity) forces |μ| ≤ 1
for all eigenvalues; the reverse direction (|μ|=1 → GaugePhaseEquiv) uses QPF fixed
points + KS equality from Channel/Schwarz (proved fully in `SpectralGap.lean`).

### Step 2: Block separation (single-block reduction)
Under canonical form (strict ordering |μ₀| > … > |μ_{r-1}|, all blocks primitive),
the summed identity ∑_k μ_k^N · Δmpv_k(σ) = 0 is reduced by induction on r:
- Peeling: self-overlap → 1 + exponential decay → cross-overlap → 1 → GaugePhaseEquiv;
  phase uniqueness argument → GaugeEquiv(A₀, B₀) → SameMPV(A₀, B₀).
- Tail: Subtract k=0 term; IH closes the (r-1)-block tail.

Result: `∀ k, SameMPV(A_k, B_k)`.

Proved fully in `CanonicalFormSep.lean`.

### Step 3: Single-block FT
`IsInjective A + SameMPV(A,B) → GaugeEquiv(A,B)` via linear extension + simplicity
+ Skolem–Noether. Proved in `FundamentalTheorem.lean`.

### Step 4: Multi-block assembly
Per-block GaugeEquiv(A_k, B_k) → blockDiag(X_k) gives global gauge on the
block-diagonal tensor. The block-permutation structure is extracted from the
Pi-algebra automorphism. Proved in `FundamentalTheoremMulti.lean` and
`FundamentalTheoremComplete.lean`.

### Supporting infrastructure (all sorry-free):
- **Newton-Girard** (`NewtonGirard.lean`): tr(A^k) = tr(B^k) ∀k ⟹ same charpoly
  (alternative algebraic path, not used in the main spectral-gap proof route).
- **GramMatrixLI** (`GramMatrixLI.lean`): Gram matrix → I ⟹ eventual linear independence.
- **MixedTransferRect** (`MixedTransferRect.lean`): Rectangular F_{AB} for D₁ ≠ D₂.

---

## IV. Sorry Inventory (Core Files)

| File | Sorry (tactic) | Notes |
|------|----------------|-------|
| FundamentalTheorem.lean | 0 | ✅ Complete |
| CanonicalFormSep.lean | 0 | ✅ Complete |
| SpectralGap.lean | 0 | ✅ All 7 occurrences are in comments |
| MixedTransferRect.lean | 0 | ✅ Complete |
| MPVOverlapDecay.lean | 0 | ✅ Complete |
| MPVOverlapTraceRect.lean | 0 | ✅ Complete |
| NewtonGirard.lean | 0 | ✅ Complete |
| GramMatrixLI.lean | 0 | ✅ Complete |
| FundamentalTheoremComplete.lean | 0 | ✅ Complete |
| FundamentalTheoremMulti.lean | 0 | ✅ Complete |

**NOT in the audited 10 (gated behind Experimental.lean)**:
- `BlockSeparationProof.lean`: 1 sorry — `per_block_trace_eq_of_summed_blocks` (false as stated, counterexample known)
- `Scratch/KerInvariance.lean`: 3 sorry — scratch file, not imported by core

---

## V. Key Definitions

| Lean name | Mathematical object |
|-----------|-------------------|
| `MPSTensor d D` | Fin d → Matrix (Fin D) (Fin D) ℂ |
| `IsInjective A` | span{A i} = M_D(ℂ) as ℂ-algebra |
| `mpv A σ` | tr(A(σ₀)·A(σ₁)···A(σ_{N-1})) ∈ ℂ |
| `SameMPV A B` | ∀ N σ, mpv A σ = mpv B σ |
| `GaugeEquiv A B` | ∃ X ∈ GL(D), ∀ i, B i = X A i X⁻¹ |
| `GaugePhaseEquiv A B` | ∃ X ∈ GL(D), ∃ ζ ∈ U(1), ∀ i, B i = ζ·X A i X⁻¹ |
| `SameMPV₂ A B` | ∀ N σ, mpv A σ = mpv B σ (global block-diagonal) |
| `toTensorFromBlocks μ A` | blockDiag(μ_k · A_k) reindexed |
| `mixedTransferMap A B` | F_{AB}: X ↦ ∑_i A_i X (B_i)† (square) |
| `mixedTransferMap₂ A B` | Same, rectangular (D₁ × D₂) |
| `mpvOverlap A B N` | ∑_{σ: Fin N → Fin d} mpv(A,σ)·star(mpv(B,σ)) |
| `IsCanonicalForm μ A` | Injective blocks + DS gauge + strict |μ_k| ordering + primitivity |
