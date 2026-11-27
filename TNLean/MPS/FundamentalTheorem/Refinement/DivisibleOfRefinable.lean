/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking
import TNLean.MPS.FundamentalTheorem.Refinement.PhysicalSymmetry
import TNLean.MPS.Tensor.DirectSum.BlockAssembly
import TNLean.MPS.CanonicalForm.Periodic.SectorNormalization
import TNLean.MPS.CanonicalForm.Periodic.Blocking.IrreducibleFormBlocking
import TNLean.MPS.FundamentalTheorem.Periodic.PhaseClassGrouping
import TNLean.MPS.FundamentalTheorem.Refinement.RefinableOfDivisible
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.FundamentalTheorem.Periodic.EqualCaseGlobal
import TNLean.MPS.CanonicalForm.Periodic.Blocking.SectorPhaseWord

/-!
# Refinability implies divisibility for a block form with unit weights

Let `B = ⊕_k μ_k B_k` be a direct sum of left-canonical periodic blocks with
`|μ_k| = 1`. If the vectors of `B` can be `p`-refined, then the transfer
channel of `B` is the `p`-th power of a channel. This is the forward
implication of arXiv:1708.00029, Theorem 4.1, lines 735--810.

The proof follows the source. A refinement supplies a tensor `A` whose
`p`-blocked vectors are those of the physically rotated tensor
`⊕_k μ_k C_k`, where every `C_k` is again periodic. The periodic blocks of
`A` are normalized and split into step orbits under blocking
(`lem:blocking-arbitrary`, lines 432--456). The equal-case fundamental theorem
(`thm:bdequal`) matches the orbit blocks with the `C_k` up to roots of unity
(`eq:ZPA-is-cPA`). These phases are redistributed among the cyclic sectors
(`eq:Aprime-is-cPA`), and a final unitary conjugation gives a trace-preserving
tensor `R` with `R^{[p]} = ⊕_k μ_k C_k` exactly (lines 807--810). Hence
`𝔼_B = 𝔼_{⊕ μ C} = 𝔼_R^p`.

**Local fix (trace preservation):** the printed forward implication omits
the trace preservation of `𝔼_B` that the definition of `p`-divisibility at
lines 717--718 presupposes. Here the multiplicities have modulus one, which
makes `𝔼_B` trace preserving. Documented in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.

## Main declarations

* `MPSTensor.exists_unitary_stepOrbit_decomposition_toTensorFromBlocks`: the
  step-orbit decomposition of a blocked unit-weight block sum, with phase lifts.
* `MPSTensor.exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks`: a
  trace-preserving root with exactly prescribed blocking.
* `MPSTensor.isPDivisibleChannel_of_isPRefinable_toTensorFromBlocks`: the
  corrected forward implication of Theorem 4.1.
* `MPSTensor.weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos`,
  `MPSTensor.exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos`: normalizing a tensor
  from a unit-weight blocked comparison.
* `MPSTensor.refinementScalarCounterexample`, `MPSTensor.refinement_normalization_counterexample`: a
  scalar counterexample to the printed refinement implication.
* `MPSTensor.IsPeriodic.exists_unitary_stepOrbit_decomposition`: unitary orbit coordinates and
  phase-weighted blocked roots.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029,
  `lem:blocking-arbitrary`, lines 432--456; `thm:bdequal`, lines 643--693;
  Theorem 4.1, lines 715--810.
-/

open MPTensor

section Normalization

/-!
## Normalizing a tensor from a unit-weight blocked comparison

Start with the positive-weight periodic decomposition of an arbitrary tensor.
If a positive blocking has the same positive-length MPVs as a periodic sector
decomposition with unit-modulus multiplicities, the original block weights have
modulus one. The multiplicity-bearing equal-case fundamental theorem also
recovers the exact total bond dimension.

Absorbing the original weight phases into the blocks gives a unit-weight periodic
presentation without assuming an initial canonical form or empty-word equality.
This is the normalization step in arXiv:1708.00029, Theorem 4.1, lines 750–756.
The subsequent orbit-phase matching and root construction are separate steps.

**Scope restriction (positive lengths):**
`exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos` asserts equality
of MPVs only at positive lengths, since discarding zero blocks may lower the bond
dimension. The convention is inherited from `exists_periodic_blockDecomposition`
and recorded in `docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`.

**Scope restriction (unit-modulus target weights):** both blocked-comparison
theorems assume the target multiplicities have modulus one (`hQweight`). This is
the trace-preservation correction to the forward direction of Theorem 4.1, which
is false as printed without it; see
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators ComplexOrder
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}

section Blocked

variable {r : ℕ} {dim : Fin r → ℕ}

private theorem sum_dim_eq_of_sameMPV₂Pos (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (A k))
    (Q : SectorDecomposition d) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (toTensorFromBlocks μ A) Q.toTensor) :
    (∑ k, dim k) = Q.totalDim := by
  let classes := mpvPhaseClassData A
  obtain ⟨ξ, hξ, hdim, hP, hNonRepP, _, hgroup, _⟩ :=
    classes.exists_unitary_sectorDecomposition μ hμ period hper
  let P := classes.toSectorDecomposition μ ξ hμ hξ
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor := hgroup.symm.trans hSame
  obtain ⟨_, _, _, _, _, _, _, _, _, Y, Y', hYY', hY'Y, _⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition P Q
      (fun j ↦ period (classes.repr j)) periodQ hP hPerQ hNonRepP hNonRepQ hPQ
  exact hdim.symm.trans (by simpa using Matrix.square_of_invertible Y Y' hYY' hY'Y)

/-- A blocked comparison with unit-modulus multiplicities forces every original
periodic-block weight to have modulus one and recovers the target bond dimension.
Source: arXiv:1708.00029, Theorem 4.1, lines 750–756, using `lem:blocking-arbitrary`
and the multiplicity matching in `thm:bdequal`. The unit-modulus target condition
is the trace-preservation correction recorded in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ) (hper : ∀ k, IsPeriodic (period k) (A k))
    {p : ℕ} (hp : 0 < p)
    (Q : SectorDecomposition (blockPhysDim d p)) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (blockTensor (toTensorFromBlocks μ A) p) Q.toTensor)
    (hQweight : ∀ j q, ‖Q.weight j q‖ = 1) :
    (∀ k, ‖μ k‖ = 1) ∧ (∑ k, dim k) = Q.totalDim := by
  classical
  let n : Fin r → ℕ := fun k ↦ (period k).gcd p
  have hex (k : Fin r) :
      ∃ (sd : Fin (n k) → ℕ)
        (B : (a : Fin (n k)) → MPSTensor (blockPhysDim d p) (sd a)),
        (∑ a, sd a) = dim k ∧
        (∀ a, IsPeriodic (period k / n k) (B a)) ∧
        SameMPV₂ (blockTensor (A k) p) (toTensorFromBlocks (fun _ ↦ 1) B) := by
    obtain ⟨_, sd, B, _, _, _, _, _, _, hd, _, hSame, _, _, _, hperB⟩ :=
      (hper k).exists_stepOrbit_blockDecomposition p
    exact ⟨sd, B, hd, hperB hp, hSame⟩
  choose sd B hdimB hperB hSameB using hex
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat := sameMPV₂_toTensorFromBlocks_refinement (fun k ↦ μ k ^ p)
    (fun k ↦ blockTensor (A k) p) n sd B hSameB
  have hbase := sameMPV₂_blockTensor_toTensorFromBlocks μ A p
  have hPQ : SameMPV₂Pos
      (toTensorFromBlocks (fun j ↦ μ (e j).1 ^ p) (fun j ↦ B (e j).1 (e j).2))
      Q.toTensor := by
    intro N hN σ
    exact (hflat N σ).symm.trans ((hbase N σ).symm.trans (hSame N hN σ))
  have hw := weight_norm_eq_one_of_block_sum_sameMPV₂Pos
    (fun j ↦ μ (e j).1 ^ p) (fun j ↦ pow_ne_zero _ (hμ _))
    (fun j ↦ period (e j).1 / n (e j).1) (fun j ↦ hperB (e j).1 (e j).2)
    Q periodQ hPerQ hNonRepQ hPQ hQweight
  have hdimFlat := sum_dim_eq_of_sameMPV₂Pos (fun j ↦ μ (e j).1 ^ p)
    (fun j ↦ pow_ne_zero _ (hμ _)) (fun j ↦ B (e j).1 (e j).2)
    (fun j ↦ period (e j).1 / n (e j).1) (fun j ↦ hperB (e j).1 (e j).2)
    Q periodQ hPerQ hNonRepQ hPQ
  constructor
  · intro k
    let a : Fin (n k) := ⟨0, Nat.gcd_pos_of_pos_right _ hp⟩
    have hh := hw (finSigmaFinEquiv ⟨k, a⟩)
    change ‖μ ((finSigmaFinEquiv (n := n)).symm (finSigmaFinEquiv ⟨k, a⟩)).1 ^ p‖ = 1 at hh
    rw [Equiv.symm_apply_apply, norm_pow] at hh
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.ne_of_gt hp)).mp hh
  · have hdimSum : (∑ j, sd (e j).1 (e j).2) = ∑ k, dim k := by
      rw [Equiv.sum_comp e (fun ka ↦ sd ka.1 ka.2), Fintype.sum_sigma]
      simp only [hdimB]
    exact hdimSum.symm.trans hdimFlat

end Blocked

/-- Normalize an arbitrary tensor whose positive blocking matches a periodic
sector decomposition with unit-modulus weights. The resulting unit-weight blocks
have total dimension exactly that of the target. Source: arXiv:1708.00029,
Theorem 4.1, lines 750–756. This is a positive-length presentation, not a claimed
unitary similarity of the original arbitrary tensor; the corrected forward proof
continues with the presented blocks. -/
theorem exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos
    (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (Q : SectorDecomposition (blockPhysDim d p)) (periodQ : Fin Q.basisCount → ℕ)
    (hPerQ : ∀ j, IsPeriodic (periodQ j) (Q.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos (blockTensor A p) Q.toTensor)
    (hQweight : ∀ j q, ‖Q.weight j q‖ = 1) :
    ∃ (r : ℕ) (dim : Fin r → ℕ)
      (B : (k : Fin r) → MPSTensor d (dim k)) (period : Fin r → ℕ),
      (∀ k, IsPeriodic (period k) (B k)) ∧
      (∑ k, dim k) = Q.totalDim ∧ (∑ k, dim k) ≤ D ∧
      SameMPV₂Pos A (toTensorFromBlocks (fun _ ↦ 1) B) := by
  obtain ⟨r, dim, μ, B, period, hper, hμpos, _, hAB, hbound⟩ :=
    exists_periodic_blockDecomposition A
  have hμ (k : Fin r) : μ k ≠ 0 := (hμpos k).ne'
  have hBlock := sameMPV₂Pos_blockTensor A (toTensorFromBlocks μ B) hAB p hp
  obtain ⟨hw, hdim⟩ := weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos
    μ hμ B period hper hp Q periodQ hPerQ hNonRepQ
    (hBlock.symm.trans hSame) hQweight
  refine ⟨r, dim, (fun k i ↦ μ k • B k i), period,
    (fun k ↦ isPeriodic_smul_of_norm_one (hw k) (B k) (hper k)), hdim, hbound, ?_⟩
  have he : toTensorFromBlocks (fun _ ↦ 1) (fun k i ↦ μ k • B k i) =
      toTensorFromBlocks μ B := by
    unfold toTensorFromBlocks
    simp only [one_smul]
  rw [he]
  exact hAB

end MPSTensor

end Normalization

section OrbitUnitary

/-!
## Unitary orbit coordinates and phase-weighted blocked roots

The isometries of the prescribed periodic decomposition assemble into a unitary
on the original bond space. Its columns keep the original step-orbit labels,
so the diagonal multiplicity phases can be transported to those orbit supports.
The cyclic phase construction then gives a left-canonical tensor whose blocking
is the phase-weighted direct sum in these same coordinates.

This supplies the bond-coordinate and phase-transport steps of
arXiv:1708.00029, Theorem 4.1. It does not yet identify the phases supplied by the
global equal-case theorem after grouping multiple original periodic blocks.

**Local fix (powered roots):** The period of each orbit block is `m / gcd(m,p)`.
The source's displayed peripheral root set omits the exponent `p`; see
`docs/paper-gaps/dccsp17_blocking_peripheral_roots.tex`.
-/

open scoped Matrix BigOperators
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D m : ℕ} [NeZero m]

private theorem blockScalarMatrix_mul_blockInclusion {r : ℕ} {dim : Fin r → ℕ}
    (c : Fin r → ℂ) (a : Fin r) :
    blockScalarMatrix dim c * blockInclusion dim a = c a • blockInclusion dim a := by
  have h := toTensorFromBlocks_mul_blockInclusion (α := Fin 1) (dim := dim) c
    (fun _ _ ↦ 1) a 0
  change blockScalarMatrix dim c * blockInclusion dim a =
    blockInclusion dim a * (c a • 1) at h
  simpa only [Matrix.mul_smul, Matrix.mul_one] using h

private theorem exists_root_of_orbit_phase (A : MPSTensor d D) (hA : IsLeftCanonical A)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hproj : ∀ u, IsOrthogonalProjection (P u)) (hsum : ∑ u, P u = 1)
    (hshift : ∀ u i, P u * A i = A i * P (u + 1)) (p : ℕ)
    (dim : Fin (m.gcd p) → ℕ)
    (B : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
    (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ)
    (hrange : ∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a)
    (U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ)
    (hiso : Uᴴ * U = 1)
    (hinc : ∀ a, U * blockInclusion dim a = V a)
    (hconj : ∀ i, blockTensor A p i = U * toTensorFromBlocks (fun _ ↦ 1) B i * Uᴴ)
    (c : Fin (m.gcd p) → ℂ) (hc : ∀ a, c a ^ (m / m.gcd p) = 1) :
    ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
      ∀ i, blockTensor A' p i = U * toTensorFromBlocks c B i * Uᴴ := by
  let Z := U * blockScalarMatrix dim c * Uᴴ
  have hZV (a) : Z * V a = c a • V a := by
    rw [← hinc]
    dsimp only [Z]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hiso, Matrix.one_mul, blockScalarMatrix_mul_blockInclusion,
      Matrix.mul_smul]
  have hZ (a i) : Z * (stepOrbitProjection P p a * blockTensor A p i) =
      c a • (stepOrbitProjection P p a * blockTensor A p i) := by
    rw [← hrange]
    simp only [← Matrix.mul_assoc]
    rw [hZV]
    simp only [Matrix.smul_mul]
  have hmul := orthogonalProjection_mul_eq_ite_of_sum_eq_one P hproj hsum
  obtain ⟨A', hA', hblock⟩ := exists_isLeftCanonical_blockTensor_eq_of_orbit_action
    A P hmul (fun u ↦ (hproj u).1.eq) hsum hshift hA p c hc Z hZ
  refine ⟨A', hA', fun i ↦ ?_⟩
  rw [hblock]
  change Z * blockTensor A p i = _
  rw [hconj]
  dsimp only [Z]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hiso, Matrix.one_mul,
    ← Matrix.mul_assoc (blockScalarMatrix dim c), blockScalarMatrix_mul_toTensorFromBlocks]
  simp only [mul_one]

omit [NeZero m] in
/-- The prescribed periodic blocks assemble by one unitary, retaining their orbit
inclusions. Every family of root-of-unity phases on these same blocks lifts to a
left-canonical root with the original physical dimension and bond space.

Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432–456, and
`eq:ZPA-is-cPA` through `eq:Aprime-is-cPA`, lines 778–807. -/
theorem IsPeriodic.exists_unitary_stepOrbit_decomposition
    (A : MPSTensor d D) (hA : IsPeriodic m A) {p : ℕ} (hp : 0 < p) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd p) → ℕ)
      (B : (a : Fin (m.gcd p)) → MPSTensor (blockPhysDim d p) (dim a))
      (V : (a : Fin (m.gcd p)) → Matrix (Fin D) (Fin (dim a)) ℂ)
      (U : Matrix (Fin D) (Fin (∑ a, dim a)) ℂ),
      (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u = 1) ∧
      (∀ u i, P u * A i = A i * P (u + 1)) ∧
      (∑ a, dim a) = D ∧
      (∀ a, IsPeriodic (m / m.gcd p) (B a)) ∧
      (∀ a, V a * (V a)ᴴ = stepOrbitProjection P p a) ∧
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      (∀ a, U * blockInclusion dim a = V a) ∧
      (∀ i, blockTensor A p i = U * toTensorFromBlocks (fun _ ↦ 1) B i * Uᴴ) ∧
      ∀ c : Fin (m.gcd p) → ℂ, (∀ a, c a ^ (m / m.gcd p) = 1) →
        ∃ A' : MPSTensor d D, IsLeftCanonical A' ∧
          ∀ i, blockTensor A' p i = U * toTensorFromBlocks c B i * Uᴴ := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, dim, B, V, hproj, hsum, _, hshift, _, hdim, _, _, hiso, hrange, hB, hper⟩ :=
    hA.exists_stepOrbit_blockDecomposition p
  have hinter (a) (i) : blockTensor A p i * V a = V a * B a i := by
    have hPV : stepOrbitProjection P p a * V a = V a := by
      rw [← hrange, Matrix.mul_assoc, hiso, Matrix.mul_one]
    rw [hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hrange,
      stepOrbitProjection_mul_blockTensor P A hshift, Matrix.mul_assoc, hPV]
  obtain ⟨U, hco, hU, hinc, hconj⟩ :=
    exists_unitary_toTensorFromBlocks_of_resolution (blockTensor A p) B V
      (by simp only [hrange, sum_stepOrbitProjection, hsum]) hdim hinter
  refine ⟨P, dim, B, V, U, hproj, hsum, hshift, hdim, hper hp, hrange,
    hco, hU, hinc, hconj, ?_⟩
  exact fun c hc ↦ exists_root_of_orbit_phase A hA.leftCanonical P hproj hsum hshift p
    dim B V hrange U hU hinc hconj c hc

end MPSTensor

end OrbitUnitary

section DivisibleOfRefinable

open scoped Matrix BigOperators
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

/-- A unit-weight direct sum of trace-preserving tensors is trace preserving.
Source: arXiv:1708.00029, irreducible form II, lines 313--332. -/
theorem isLeftCanonical_toTensorFromBlocks_one {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (hA : ∀ k, IsLeftCanonical (A k)) :
    IsLeftCanonical (toTensorFromBlocks (fun _ ↦ 1) A) := by
  classical
  unfold IsLeftCanonical Kraus.IsTP
  have hres := sum_blockInclusion_mul_conjTranspose dim
  have hcol (k : Fin r) :
      (∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i) *
          blockInclusion dim k = blockInclusion dim k := by
    rw [Matrix.sum_mul]
    have h (i : Fin d) :
        (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i *
            blockInclusion dim k =
          blockInclusion dim k * ((A k i)ᴴ * A k i) := by
      have hl := toTensorFromBlocks_mul_blockInclusion (fun _ ↦ (1 : ℂ)) A k i
      rw [one_smul] at hl
      have hc : (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * blockInclusion dim k =
          blockInclusion dim k * (A k i)ᴴ := by
        have h := congrArg Matrix.conjTranspose
          (blockInclusion_conjTranspose_mul_toTensorFromBlocks (fun _ ↦ (1 : ℂ)) A k i)
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, one_smul]
          using h
      rw [Matrix.mul_assoc, hl, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    simp only [h, ← Matrix.mul_sum]
    have hk := hA k
    unfold IsLeftCanonical Kraus.IsTP at hk
    rw [hk, Matrix.mul_one]
  calc
    ∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i =
        (∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i) *
          ∑ k, blockInclusion dim k * (blockInclusion dim k)ᴴ := by rw [hres, Matrix.mul_one]
    _ = ∑ k, (∑ i, (toTensorFromBlocks (fun _ ↦ 1) A i)ᴴ * toTensorFromBlocks (fun _ ↦ 1) A i) *
          blockInclusion dim k * (blockInclusion dim k)ᴴ := by
      rw [Matrix.mul_sum]
      simp only [Matrix.mul_assoc]
    _ = 1 := by simp only [hcol, hres]

/-- A matrix is determined by its products with the members of a resolution of
the identity. -/
private theorem eq_of_mul_eq_of_resolution {n r : ℕ} {dim : Fin r → ℕ}
    (W : (s : Fin r) → Matrix (Fin n) (Fin (dim s)) ℂ) (hW : ∑ s, W s * (W s)ᴴ = 1)
    {M N : Matrix (Fin n) (Fin n) ℂ} (h : ∀ s, M * W s = N * W s) : M = N := by
  calc
    M = M * ∑ s, W s * (W s)ᴴ := by rw [hW, Matrix.mul_one]
    _ = N * ∑ s, W s * (W s)ᴴ := by simp only [Matrix.mul_sum, ← Matrix.mul_assoc, h]
    _ = N := by rw [hW, Matrix.mul_one]

/-- **Step orbits of a blocked block sum.** Blocking a unit-weight direct sum of
periodic tensors `A_k` of periods `m_k` splits each `A_k` into `gcd(m_k, p)`
periodic blocks of period `m_k / gcd(m_k, p)`. One unitary `Y` identifies the
blocked tensor with the unit-weight direct sum of all these blocks. Every
choice of roots of unity `c_s` of these periods lifts to a trace-preserving
tensor whose blocking is the `c`-weighted direct sum in the same coordinates.

Source: arXiv:1708.00029, `lem:blocking-arbitrary`, lines 432--456, and
`eq:ZPA-is-cPA` through `eq:Aprime-is-cPA`, lines 778--807, applied to every
block of the irreducible form as in the proof of Theorem 4.1, lines 750--765. -/
theorem exists_unitary_stepOrbit_decomposition_toTensorFromBlocks
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k)) {p : ℕ} (hp : 0 < p) :
    ∃ (fdim : Fin (∑ k, (period k).gcd p) → ℕ)
      (C : (s : Fin (∑ k, (period k).gcd p)) → MPSTensor (blockPhysDim d p) (fdim s))
      (Y : Matrix (Fin (∑ k, dim k)) (Fin (∑ s, fdim s)) ℂ),
      (∀ s, IsPeriodic
        (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1 /
          (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1).gcd p)
        (C s)) ∧
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      (∀ i, blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p i =
        Y * toTensorFromBlocks (fun _ ↦ 1) C i * Yᴴ) ∧
      ∀ c : Fin (∑ k, (period k).gcd p) → ℂ,
        (∀ s, c s ^
          (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1 /
            (period ((finSigmaFinEquiv (n := fun k ↦ (period k).gcd p)).symm s).1).gcd p) =
            1) →
        ∃ A' : MPSTensor d (∑ k, dim k), IsLeftCanonical A' ∧
          ∀ i, blockTensor A' p i = Y * toTensorFromBlocks c C i * Yᴴ := by
  classical
  let n : Fin r → ℕ := fun k ↦ (period k).gcd p
  let e := (finSigmaFinEquiv (n := n)).symm
  have hEach (k : Fin r) := IsPeriodic.exists_unitary_stepOrbit_decomposition (A k) (hPer k) hp
  choose P sd B V U hproj hsum _ hdim hperB hrange hUU hU hinc hconj hlift using hEach
  let fdim : Fin (∑ k, n k) → ℕ := fun s ↦ sd (e s).1 (e s).2
  let C : (s : Fin (∑ k, n k)) → MPSTensor (blockPhysDim d p) (fdim s) :=
    fun s ↦ B (e s).1 (e s).2
  let W : (s : Fin (∑ k, n k)) → Matrix (Fin (∑ k, dim k)) (Fin (fdim s)) ℂ :=
    fun s ↦ blockInclusion dim (e s).1 * V (e s).1 (e s).2
  -- each blocked summand intertwines its orbit isometries, also after a phase lift
  have hblockV (k : Fin r) (a : Fin (n k)) (c : Fin (n k) → ℂ)
      (X : MPSTensor (blockPhysDim d p) (dim k))
      (hX : ∀ i, X i = U k * toTensorFromBlocks c (B k) i * (U k)ᴴ) (i) :
      X i * V k a = V k a * (c a • B k a i) := by
    rw [hX, ← hinc k a]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U k)ᴴ, hU k, Matrix.one_mul, toTensorFromBlocks_mul_blockInclusion]
  have hsumV (k : Fin r) : ∑ a, V k a * (V k a)ᴴ = 1 := by
    simp only [hrange, sum_stepOrbitProjection, hsum]
  have hflat (f : ((k : Fin r) × Fin (n k)) → Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ) :
      ∑ s, f (e s) = ∑ k, ∑ a, f ⟨k, a⟩ := by
    rw [Equiv.sum_comp e f, Fintype.sum_sigma]
  have hres : ∑ s, W s * (W s)ᴴ = 1 := by
    refine (hflat fun x ↦
      blockInclusion dim x.1 * V x.1 x.2 * (blockInclusion dim x.1 * V x.1 x.2)ᴴ).trans ?_
    have hk (k : Fin r) :
        ∑ a, blockInclusion dim k * V k a * (blockInclusion dim k * V k a)ᴴ =
          blockInclusion dim k * (blockInclusion dim k)ᴴ := by
      calc
        _ = blockInclusion dim k * (∑ a, V k a * (V k a)ᴴ) * (blockInclusion dim k)ᴴ := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hsumV, Matrix.mul_one]
    exact (Finset.sum_congr rfl fun k _ ↦ hk k).trans (sum_blockInclusion_mul_conjTranspose dim)
  have hdim' : ∑ s, fdim s = ∑ k, dim k := by
    rw [Equiv.sum_comp e (fun x ↦ sd x.1 x.2), Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun k _ ↦ hdim k
  -- the blocked sum intertwines the flattened isometries
  have hblock (X : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k))
      (c : Fin (∑ k, n k) → ℂ)
      (hX : ∀ k a i, X k i * V k a = V k a * (c (finSigmaFinEquiv ⟨k, a⟩) • B k a i))
      (s : Fin (∑ k, n k)) (i : Fin (blockPhysDim d p)) :
      toTensorFromBlocks (fun _ ↦ 1) X i * W s = W s * (c s • C s i) := by
    dsimp only [W, C]
    rw [← Matrix.mul_assoc, toTensorFromBlocks_mul_blockInclusion, one_smul, Matrix.mul_assoc,
      hX, ← Matrix.mul_assoc]
    simp only [e, Sigma.eta, Equiv.apply_symm_apply]
  have hT (i : Fin (blockPhysDim d p)) :
      blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p i =
        toTensorFromBlocks (fun _ ↦ 1) (fun k ↦ blockTensor (A k) p) i := by
    rw [blockTensor_toTensorFromBlocks_apply]
    simp only [one_pow]
  have hinter (s : Fin (∑ k, n k)) (i : Fin (blockPhysDim d p)) :
      blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p i * W s = W s * C s i := by
    rw [hT]
    simpa only [one_smul] using hblock (fun k ↦ blockTensor (A k) p) (fun _ ↦ 1)
      (fun k a i ↦ hblockV k a (fun _ ↦ 1) _ (hconj k) i) s i
  obtain ⟨Y, hYY, hY'Y, hYinc, hYconj⟩ :=
    exists_unitary_toTensorFromBlocks_of_resolution
      (blockTensor (toTensorFromBlocks (fun _ ↦ 1) A) p) C W hres hdim' hinter
  refine ⟨fdim, C, Y, fun s ↦ hperB (e s).1 (e s).2, hYY, hY'Y, hYconj, ?_⟩
  intro c hc
  have hroot (k : Fin r) (a : Fin (n k)) :
      c (finSigmaFinEquiv ⟨k, a⟩) ^ (period k / (period k).gcd p) = 1 := by
    simpa only [e, Equiv.symm_apply_apply] using hc (finSigmaFinEquiv ⟨k, a⟩)
  choose A' hA' hA'block using fun k ↦
    hlift k (fun a ↦ c (finSigmaFinEquiv ⟨k, a⟩)) (hroot k)
  refine ⟨toTensorFromBlocks (fun _ ↦ 1) A', isLeftCanonical_toTensorFromBlocks_one A' hA',
    fun i ↦ ?_⟩
  refine eq_of_mul_eq_of_resolution W hres fun s ↦ ?_
  have hYW : Y * toTensorFromBlocks c C i * Yᴴ * W s = W s * (c s • C s i) := by
    rw [← hYinc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᴴ Y, hY'Y, Matrix.one_mul, toTensorFromBlocks_mul_blockInclusion]
  rw [hYW, blockTensor_toTensorFromBlocks_apply]
  simp only [one_pow]
  exact hblock (fun k ↦ blockTensor (A' k) p) c
    (fun k a i ↦ hblockV k a _ _ (hA'block k) i) s i

/-- **Trace-preserving root with prescribed blocking.** Let `ν_k` have modulus
one and let `B_k` be left-canonical periodic tensors on the blocked physical
alphabet. If the `p`-blocking of some tensor `A` generates the same vectors as
`⊕_k ν_k B_k` at every positive length, then a trace-preserving tensor `R` on
the original alphabet satisfies `R^{[p]} = ⊕_k ν_k B_k` letter by letter.

No normalization of `A` is assumed. Source: arXiv:1708.00029, Theorem 4.1,
lines 750--810: the periodic blocks of `A` are normalized (lines 750--756),
matched with the target by `thm:bdequal` (`eq:ZPA-is-cPA`), and the phases are
absorbed into a trace-preserving tensor (`eq:Aprime-is-cPA`, lines 778--810). -/
theorem exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks
    {d D s p : ℕ} {dim' : Fin s → ℕ} (A : MPSTensor d D) (hp : 0 < p)
    (B : (k : Fin s) → MPSTensor (blockPhysDim d p) (dim' k))
    (ν : Fin s → ℂ) (hν : ∀ k, ‖ν k‖ = 1)
    (period : Fin s → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hSame : SameMPV₂Pos (blockTensor A p) (toTensorFromBlocks ν B)) :
    ∃ R : MPSTensor d (∑ k, dim' k),
      IsLeftCanonical R ∧ blockTensor R p = toTensorFromBlocks ν B := by
  classical
  have hν0 (k : Fin s) : ν k ≠ 0 := Complex.ne_zero_of_norm_eq_one (hν k)
  -- group the target into a basis of periodic tensors with unit-modulus weights
  let classes := mpvPhaseClassData B
  obtain ⟨ξ, hξ, hdimQ, hPerQ, hNonRepQ, hnormQ, hSameQ, _⟩ :=
    classes.exists_unitary_sectorDecomposition ν hν0 period hPer
  -- normalize the periodic blocks of `A`
  obtain ⟨r, dim, A₁, period₁, hPer₁, _, _, hSameA⟩ :=
    exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos A hp
      (classes.toSectorDecomposition ν ξ hν0 hξ) (fun j ↦ period (classes.repr j))
      hPerQ hNonRepQ (hSame.trans hSameQ) fun j q ↦ (hnormQ j q).trans (hν _)
  -- split the blocked normalized blocks into step orbits
  obtain ⟨fdim, C, Y, hPerC, hYY, hY'Y, hYconj, hlift⟩ :=
    exists_unitary_stepOrbit_decomposition_toTensorFromBlocks A₁ period₁ hPer₁ hp
  have hSameC : SameMPV₂Pos (toTensorFromBlocks (fun _ ↦ 1) C) (toTensorFromBlocks ν B) := by
    have hCY : SameMPV₂Pos (blockTensor (toTensorFromBlocks (fun _ ↦ 1) A₁) p)
        (toTensorFromBlocks (fun _ ↦ 1) C) := by
      apply sameMPV₂Pos_of_coisometry_reconstruction _ _ Yᴴ
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hY'Y)
      intro i
      simpa only [Matrix.conjTranspose_conjTranspose] using hYconj i
    exact hCY.symm.trans ((sameMPV₂Pos_blockTensor A _ hSameA p hp).symm.trans hSame)
  -- match the orbit blocks with the target up to roots of unity
  obtain ⟨c, W, hc, hWW, hW'W, hMatch⟩ :=
    exists_unitary_matching_of_periodic_block_families C (fun _ ↦ 1) (fun _ ↦ one_ne_zero)
      B ν hν0 _ period hPerC hPer hSameC
  simp only [mul_one] at hMatch
  obtain ⟨A', hA', hA'block⟩ := hlift c hc
  -- conjugate back to the bond space of the target
  let T := Y * W
  have hTT : T * Tᴴ = 1 := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W, hWW, Matrix.one_mul, hYY]
  have hT'T : Tᴴ * T = 1 := by
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᴴ, hY'Y, Matrix.one_mul, hW'W]
  let R : MPSTensor d (∑ k, dim' k) := fun i ↦ Tᴴ * A' i * T
  refine ⟨R, ?_, ?_⟩
  · have hA'TP := hA'
    unfold IsLeftCanonical Kraus.IsTP at hA'TP ⊢
    calc
      ∑ i, (R i)ᴴ * R i = Tᴴ * (∑ i, (A' i)ᴴ * A' i) * T := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [R, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc T Tᴴ, hTT, Matrix.one_mul]
      _ = 1 := by rw [hA'TP, Matrix.mul_one, hT'T]
  · funext I
    have hw : Kraus.wordOfBlock d p I ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [Kraus.length_wordOfBlock, List.length_nil] at this
      exact hp.ne' this
    have h := evalWord_eq_coisometry_reconstruction_of_ne_nil T hTT
      (A := R) (B := A') (fun _ ↦ rfl) (Kraus.wordOfBlock d p I) hw
    change blockTensor R p I = Tᴴ * blockTensor A' p I * T at h
    rw [h, hA'block, hMatch]
    simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᴴ Y, hY'Y, Matrix.one_mul, ← Matrix.mul_assoc Wᴴ W, hW'W,
      Matrix.one_mul, ← Matrix.mul_assoc Yᴴ Y, hY'Y, Matrix.one_mul, hW'W, Matrix.mul_one]

/-- A `p`-refinable direct sum of left-canonical periodic blocks with
unit-modulus weights has a trace-preserving `p`-th root of its transfer map.
Source: arXiv:1708.00029, Theorem 4.1, lines 735--810. -/
theorem exists_isLeftCanonical_transferMap_eq_pow_of_isPRefinable
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k)) (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) (hRefine : IsPRefinable (toTensorFromBlocks μ B) p) :
    ∃ R : MPSTensor d (∑ k, dim k), IsLeftCanonical R ∧
      Kraus.transferMap (toTensorFromBlocks μ B) = Kraus.transferMap R ^ p := by
  classical
  obtain ⟨A, W, hW, hTransfer, hSame⟩ :=
    pRefinementCanonicalization_pullback (toTensorFromBlocks μ B) p hRefine
  let C : (k : Fin r) → MPSTensor (blockPhysDim d p) (dim k) :=
    fun k τ ↦ ∑ σ, W τ σ • B k σ
  have hLetters : (fun τ ↦ ∑ σ, W τ σ • toTensorFromBlocks μ B σ) = toTensorFromBlocks μ C :=
    funext (toTensorFromBlocks_sum_smul μ B W)
  have hTarget : SameMPV₂Pos (blockTensor A p) (toTensorFromBlocks μ C) := by
    rw [← hLetters]
    exact fun N _ σ ↦ (hSame N σ).symm
  obtain ⟨R, hR, hRoot⟩ := exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks A hp C μ hμ
    period (fun k ↦ isPeriodic_kraus_isometry (B k) W hW (hPer k)) hTarget
  refine ⟨R, hR, ?_⟩
  rw [← Kraus.transferMap_blockTensor, hRoot, ← hLetters, hTransfer]

/-- **Corrected forward implication of Theorem 4.1.** A `p`-refinable direct
sum of left-canonical periodic blocks with unit-modulus weights has a
`p`-divisible transfer channel. Source: arXiv:1708.00029, Theorem 4.1,
lines 735--810, with the trace-preservation correction recorded in the module
docstring. -/
theorem isPDivisibleChannel_of_isPRefinable_toTensorFromBlocks
    {d r p : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → MPSTensor d (dim k)) (μ : Fin r → ℂ) (hμ : ∀ k, ‖μ k‖ = 1)
    (period : Fin r → ℕ) (hPer : ∀ k, IsPeriodic (period k) (B k))
    (hp : 0 < p) (hRefine : IsPRefinable (toTensorFromBlocks μ B) p) :
    IsPDivisibleChannel (Kraus.transferMap (toTensorFromBlocks μ B)) p := by
  obtain ⟨R, hR, hRoot⟩ :=
    exists_isLeftCanonical_transferMap_eq_pow_of_isPRefinable B μ hμ period hPer hp hRefine
  exact ⟨Kraus.transferMap R, Kraus.isChannel_mapLM R hR, hRoot⟩

end MPSTensor

end DivisibleOfRefinable

section NormalizationCounterexample

/-!
## A scalar counterexample to the printed refinement implication

The forward implication of Theorem 4.1 in arXiv:1708.00029, lines 717--731,
requires trace preservation of the target transfer map. The one-dimensional
tensor with sole letter `4` is a literal positive-weight irreducible-form
block and has a two-site refinement with sole root letter `2`. Its transfer
map multiplies by `16`, so it has no channel square root. See
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators
open Kraus (blockTensor)

namespace MPSTensor

private def unitTensor : MPSTensor 1 1 := fun _ => 1

private def rootTensor : MPSTensor 1 1 :=
  fun _ => (2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The one-dimensional target tensor with sole letter four. -/
def refinementScalarCounterexample : MPSTensor 1 1 :=
  fun _ => (4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The normalized one-dimensional block has period one. -/
private theorem unitTensor_periodic : IsPeriodic 1 unitTensor := by
  have hMap : Kraus.transferMap unitTensor = LinearMap.id := by
    ext X i j
    fin_cases i
    fin_cases j
    simp [unitTensor]
  have hNormal := isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    unitTensor hMap
  apply (IsPeriodic.one_iff_primitive unitTensor).2
  refine ⟨hNormal.no_invariant_proj, ?_, hNormal.primitive_transfer⟩
  unfold IsLeftCanonical Kraus.IsTP
  simp [unitTensor]

/-- The target is literally one periodic normalized block with positive weight four. -/
private noncomputable def refinementScalarCounterexample_irreducibleForm :
    IsIrreducibleForm refinementScalarCounterexample := by
  refine {
    r := 1
    dim := fun _ => 1
    blocks := fun _ => unitTensor
    μ := fun _ => 4
    period := fun _ => 1
    periodic := fun _ => unitTensor_periodic
    weight_pos := ?_
    sameMPV := ?_ }
  · intro k
    norm_num
  · intro N σ
    rw [mpv_toTensorFromBlocks_eq_sum]
    change mpv (fun i => (4 : ℂ) • unitTensor i) σ = _
    rw [mpv_smul]
    simp

/-- The target family has a two-site refinement with root letter two. -/
private theorem refinementScalarCounterexample_refinable :
    IsPRefinable refinementScalarCounterexample 2 := by
  apply isPRefinable_of_transferMap_eq_blockTensor refinementScalarCounterexample rootTensor
    (by norm_num)
  have hTensor : refinementScalarCounterexample = blockTensor rootTensor 2 := by
    funext i
    have hw : Kraus.wordOfBlock 1 2 i = List.replicate 2 (0 : Fin 1) := by
      have hdecode : Kraus.decodeBlock 1 2 i = fun _ => (0 : Fin 1) :=
        Subsingleton.elim _ _
      simp only [Kraus.wordOfBlock, hdecode, List.ofFn_const]
    change (4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Kraus.evalWord rootTensor (Kraus.wordOfBlock 1 2 i)
    rw [hw, Kraus.evalWord_replicate]
    ext a b
    fin_cases a
    fin_cases b
    norm_num [rootTensor, pow_two, Matrix.mul_apply]
  exact congrArg Kraus.transferMap hTensor

/-- The target transfer map has no channel square root. -/
private theorem refinementScalarCounterexample_not_divisible :
    ¬ IsPDivisibleChannel (Kraus.transferMap refinementScalarCounterexample) 2 := by
  rintro ⟨E, hE, hpow⟩
  have hChannel : IsChannel (Kraus.transferMap refinementScalarCounterexample) := by
    rw [hpow]
    exact Kraus.isChannel_pow E hE 2
  have hTrace := hChannel.tp (1 : Matrix (Fin 1) (Fin 1) ℂ)
  norm_num [refinementScalarCounterexample, Kraus.transferMap_apply] at hTrace

/-- The positive scalar weight in irreducible form does not force
trace preservation in the printed forward implication of Theorem 4.1.
Source: arXiv:1708.00029, lines 717--731; see
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem refinement_normalization_counterexample :
    Nonempty (IsIrreducibleForm refinementScalarCounterexample) ∧
      (∃ A₀ : MPSTensor 1 1, IsPeriodic 1 A₀ ∧
        ∀ i, refinementScalarCounterexample i = (4 : ℂ) • A₀ i) ∧
      IsPRefinable refinementScalarCounterexample 2 ∧
      ¬ IsPDivisibleChannel (Kraus.transferMap refinementScalarCounterexample) 2 := by
  refine ⟨⟨refinementScalarCounterexample_irreducibleForm⟩,
    ⟨unitTensor, unitTensor_periodic, ?_⟩,
    refinementScalarCounterexample_refinable,
    refinementScalarCounterexample_not_divisible⟩
  intro i
  rfl

end MPSTensor

end NormalizationCounterexample
