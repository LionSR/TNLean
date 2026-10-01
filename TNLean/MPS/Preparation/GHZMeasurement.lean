/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MeasurementCircuit
import TNLean.MPS.Preparation.NonNormalFixedPoint
import TNLean.MPS.Preparation.PermutationGates

/-!
# GHZ-type states in constant depth with measurements

The GHZ-type state `|χ_M⟩ = ∑ᵢ αᵢ |i⟩^{⊗M}` of `M` qudits of dimension `b` has connected
correlations that do not decay with distance, while those of a state prepared by a local
circuit of depth `T` vanish beyond distance `2T`
(`MPSPreparation.expect_mul_eq_of_isPreparedInDepth`); arXiv:2103.13367, Example 1, uses
this to show that the GHZ state needs a depth growing with the system size. With
measurements it is prepared in constant depth: arXiv:2307.01696, paragraph "Long-range MPS using
measurements", states that "the creation of GHZ-like states `|χ_M⟩ = ∑_{i=1}^b αᵢ |i⟩^{⊗M}`
becomes possible in only constant depth", citing among others arXiv:2103.13367, whose
Example 1 gives the preparation for qubits. This file proves it for every dimension `b ≥ 1`
and every nonzero `α`, with depth `2` for every `M`, the depth of that example
(`MPSPreparation.isPreparedWithMeasurementsInDepth_withZeroAncillas_ghzState`).

## The protocol

The system qudit `n` sits at the site `2n` of a ring of `2M` sites and its ancilla at
`2n + 1`, between the system qudits `n` and `n + 1`. The protocol is Example 1 of
arXiv:2103.13367 for qudits, with the differences of neighbouring system values measured
through the ancillas.

* Product state: the first system qudit is in `∑ᵢ αᵢ |i⟩`, the other system qudits in the
  uniform superposition `∑ᵢ |i⟩`, and the ancillas in `|0⟩`.
* Two layers of controlled shifts, `|k⟩|a⟩ ↦ |k⟩|a + k⟩` from the system qudit `n` into
  the ancilla `n`, then `|a⟩|k⟩ ↦ |a - k⟩|k⟩` from the system qudit `n + 1`, write the
  difference `kₙ - k_{n+1}` of neighbouring system values into the ancilla `n`, for
  `n < M - 1`.
* Measuring the ancillas `n < M - 1` in the computational basis gives outcomes `mₙ`, and
  leaves `∑ᵢ αᵢ ⊗ₙ |i - pₙ⟩` on the system qudits with `pₙ = m₀ + ⋯ + m_{n-1}`.
* The single-site shifts `X^{pₙ}` on the system qudit `n` and `X^{-mₙ}` on the ancilla `n`,
  free corrections, give `|χ_M⟩` with every ancilla back in `|0⟩`.

The correction at the system qudit `n` depends on all the outcomes `m₀, …, m_{n-1}`, which is
where the global classical communication of the model is used. Every gate of the circuit
acts inside the pair formed by a system qudit and its ancilla, or between the ancilla of one
system qudit and the next system qudit; in the model of arXiv:2103.13367, where ancillas are
attached to their sites, these are gates between neighbouring sites conjugated by local
unitaries, so the depth `2` counted here bounds the depth of arXiv:2103.13367. Every outcome
has the same probability, and every outcome gives exactly `|χ_M⟩`: no outcome is post-selected.

## Main definitions

* `MPSPreparation.withZeroAncillas` — a state of the system qudits, with every ancilla in
  `|0⟩`, as a state of the ring of `2M` sites.
* `MPSPreparation.ghzProtocol` — the protocol above.

## Main results

* `MPSPreparation.ghzProtocol_output` — every outcome gives `|χ_M⟩`.
* `MPSPreparation.isPreparedWithMeasurementsInDepth_withZeroAncillas_ghzState`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Long-range MPS using
  measurements", and eq. (19) with the paragraph after it.
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 1 ("The GHZ and `W` states").
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {b M : ℕ} [NeZero b]

/-! ### Sites -/

/-- The site of the ring of `2M` sites carrying the system qudit `n` (`r = 0`) or the ancilla
`n` (`r = 1`): the site `2n + r`. -/
def site (n : Fin M) (r : Fin 2) : Fin (M * 2) :=
  finProdFinEquiv (n, r)

private theorem site_val (n : Fin M) (r : Fin 2) : (site n r).val = r.val + 2 * n.val :=
  rfl

private theorem site_injective {n n' : Fin M} {r r' : Fin 2} (h : site n r = site n' r') :
    n = n' ∧ r = r' := by
  simpa [site] using h

/-- The state `ψ` of the `M` system qudits, with every ancilla in `|0⟩`, as a state of the
ring of `2M` sites.

Source: arXiv:2103.13367, paragraph "Quantum circuits and LOCC" (ancillas initialized in a
product state) and Example 1. -/
def withZeroAncillas (ψ : Cfg b M → ℂ) : Cfg b (M * 2) → ℂ := fun x =>
  ψ (fun n => x (site n 0)) * ∏ n, if x (site n 1) = 0 then 1 else 0

section Ring

variable [NeZero M]

private theorem site_zero_add_one (n : Fin M) : site n 0 + 1 = site n 1 := by
  ext
  rw [Fin.val_add_one_of_lt' (by rw [site_val]; omega), site_val, site_val]
  simp only [Fin.val_zero, Fin.val_one]
  omega

private theorem site_one_add_one (n : Fin M) (h : n.val + 1 < M) :
    site n 1 + 1 = site ⟨n.val + 1, h⟩ 0 := by
  ext
  rw [Fin.val_add_one_of_lt' (by rw [site_val]; omega), site_val, site_val]
  simp only [Fin.val_zero, Fin.val_one]
  omega

private theorem add_one_ne_self (k : Fin (M * 2)) : k + 1 ≠ k := by
  intro h
  have h2 : 2 ≤ M * 2 := by have := NeZero.ne M; omega
  have := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M * 2)] at this
  rcases Nat.lt_or_ge (k.val + 1) (M * 2) with hk | hk
  · rw [Nat.mod_eq_of_lt hk] at this; omega
  · have : k.val + 1 = M * 2 := by have := k.isLt; omega
    simp_all

private theorem bond_site_zero (n : Fin M) : bond (site n 0) = {site n 0, site n 1} := by
  rw [bond, site_zero_add_one]

private theorem bond_site_one (n : Fin M) (h : n.val + 1 < M) :
    bond (site n 1) = {site n 1, site ⟨n.val + 1, h⟩ 0} := by
  rw [bond, site_one_add_one n h]

/-! ### The layers -/

/-- The left sites `2n` of the pairs `{2n, 2n + 1}` of the first layer, `n < M - 1`. -/
private def firstBonds : Finset (Fin (M * 2)) :=
  (Finset.univ.filter fun n : Fin M => n.val + 1 < M).image fun n => site n 0

/-- The left sites `2n + 1` of the pairs `{2n + 1, 2n + 2}` of the second layer, `n < M - 1`;
these are also the measured ancillas. -/
private def secondBonds : Finset (Fin (M * 2)) :=
  (Finset.univ.filter fun n : Fin M => n.val + 1 < M).image fun n => site n 1

omit [NeZero b] [NeZero M] in
private theorem mem_firstBonds {k : Fin (M * 2)} :
    k ∈ firstBonds ↔ ∃ n : Fin M, n.val + 1 < M ∧ site n 0 = k := by
  simp [firstBonds]

omit [NeZero b] [NeZero M] in
private theorem mem_secondBonds {k : Fin (M * 2)} :
    k ∈ secondBonds ↔ ∃ n : Fin M, n.val + 1 < M ∧ site n 1 = k := by
  simp [secondBonds]

private theorem firstBonds_pairwiseDisjoint :
    ((firstBonds : Finset (Fin (M * 2))) : Set (Fin (M * 2))).PairwiseDisjoint bond := by
  intro k hk k' hk' hkk'
  obtain ⟨n, -, rfl⟩ := mem_firstBonds.mp hk
  obtain ⟨n', -, rfl⟩ := mem_firstBonds.mp hk'
  have hn : n ≠ n' := fun h => hkk' (h ▸ rfl)
  change Disjoint (bond _) (bond _)
  rw [bond_site_zero, bond_site_zero, Set.disjoint_left]
  rintro i (rfl | rfl) (h | h) <;> exact hn (site_injective h).1

private theorem secondBonds_pairwiseDisjoint :
    ((secondBonds : Finset (Fin (M * 2))) : Set (Fin (M * 2))).PairwiseDisjoint bond := by
  intro k hk k' hk' hkk'
  obtain ⟨n, hn1, rfl⟩ := mem_secondBonds.mp hk
  obtain ⟨n', hn1', rfl⟩ := mem_secondBonds.mp hk'
  have hn : n ≠ n' := fun h => hkk' (h ▸ rfl)
  change Disjoint (bond _) (bond _)
  rw [bond_site_one n hn1, bond_site_one n' hn1', Set.disjoint_left]
  rintro i (rfl | rfl) (h | h)
  · exact hn (site_injective h).1
  · exact absurd (site_injective h).2 (by decide)
  · exact absurd (site_injective h).2 (by decide)
  · exact hn (Fin.ext (by have := congrArg Fin.val (site_injective h).1; simp at this; omega))

omit [NeZero b] in
private theorem firstShift_aux (k : Fin (M * 2)) (x : Cfg b (M * 2)) (c : Fin b) :
    -Function.update x (k + 1) c k = -x k := by
  rw [Function.update_of_ne (add_one_ne_self k).symm]

omit [NeZero b] in
private theorem secondShift_aux (k : Fin (M * 2)) (x : Cfg b (M * 2)) (c : Fin b) :
    Function.update x k c (k + 1) = x (k + 1) := by
  rw [Function.update_of_ne (add_one_ne_self k)]

/-- The gates of the first layer: `|k⟩|a⟩ ↦ |k⟩|a + k⟩` on `{2n, 2n + 1}`, written through its
action `x ↦ x - x_{2n} e_{2n+1}` on configurations. -/
private def firstShift (k : Fin (M * 2)) : Equiv.Perm (Cfg b (M * 2)) :=
  shiftPerm (k + 1) (fun x => -x k) (firstShift_aux k)

/-- The gates of the second layer: `|a⟩|k⟩ ↦ |a - k⟩|k⟩` on `{2n + 1, 2n + 2}`, written through
its action `x ↦ x + x_{2n+2} e_{2n+1}` on configurations. -/
private def secondShift (k : Fin (M * 2)) : Equiv.Perm (Cfg b (M * 2)) :=
  shiftPerm k (fun x => x (k + 1)) (secondShift_aux k)

private theorem isLocalPerm_firstShift (k : Fin (M * 2)) :
    IsLocalPerm (bond k) (firstShift (b := b) k) :=
  isLocalPerm_shiftPerm (Or.inr rfl) _ _ fun x y h => by rw [h k (Or.inl rfl)]

private theorem isLocalPerm_secondShift (k : Fin (M * 2)) :
    IsLocalPerm (bond k) (secondShift (b := b) k) :=
  isLocalPerm_shiftPerm (Or.inl rfl) _ _ fun x y h => by rw [h (k + 1) (Or.inr rfl)]

/-- The first layer of controlled shifts. -/
private noncomputable def firstLayer : Layer b (M * 2) :=
  permLayer firstBonds firstBonds_pairwiseDisjoint firstShift
    fun k _ => isLocalPerm_firstShift k

/-- The second layer of controlled shifts. -/
private noncomputable def secondLayer : Layer b (M * 2) :=
  permLayer secondBonds secondBonds_pairwiseDisjoint secondShift
    fun k _ => isLocalPerm_secondShift k

/-! ### Outcomes and corrections -/

/-- The outcome `mₙ` at the ancilla `n`, and `0` for the last ancilla, which is not
measured. -/
private def ghzOutcome (m : secondBonds (M := M) → Fin b) (n : Fin M) : Fin b :=
  if h : site n 1 ∈ secondBonds then m ⟨site n 1, h⟩ else 0

/-- The prefix sum `pₙ = m₀ + ⋯ + m_{n-1}` of the outcomes. -/
private def ghzPrefix (m : secondBonds (M := M) → Fin b) (n : Fin M) : Fin b :=
  Fin.partialSum (ghzOutcome m) n.castSucc

/-- The correction, as the configuration it adds: `-pₙ` at the system qudit `n` and `mₙ` at
the ancilla `n`. The operator it defines is `X^{pₙ}` on the system qudit `n` and `X^{-mₙ}` on
the ancilla `n`. -/
private def ghzCorrection (m : secondBonds (M := M) → Fin b) : Cfg b (M * 2) :=
  fun j => if (finProdFinEquiv.symm j).2 = 0 then -ghzPrefix m (finProdFinEquiv.symm j).1
    else ghzOutcome m (finProdFinEquiv.symm j).1

omit [NeZero M] in
private theorem ghzCorrection_site_zero (m : secondBonds (M := M) → Fin b)
    (n : Fin M) : ghzCorrection m (site n 0) = -ghzPrefix m n := by
  simp [ghzCorrection, site]

omit [NeZero M] in
private theorem ghzCorrection_site_one (m : secondBonds (M := M) → Fin b)
    (n : Fin M) : ghzCorrection m (site n 1) = ghzOutcome m n := by
  simp [ghzCorrection, site]

/-- The correction at the site `j` for the outcome `m`: the shift `|a⟩ ↦ |a - δⱼ⟩` by the
value `δⱼ` of `ghzCorrection m`, that is `X^{pₙ}` at the system qudit `n` and `X^{-mₙ}` at the
ancilla `n`. -/
private noncomputable def correctionUnitary (m : secondBonds (M := M) → Fin b) (j : Fin (M * 2)) :
    Matrix (Fin b) (Fin b) ℂ :=
  (Equiv.addRight (ghzCorrection m j)).permMatrix ℂ

/-- The product state of the protocol: `∑ᵢ αᵢ |i⟩` at the first system qudit, `∑ᵢ |i⟩` at
the other system qudits, and `|0⟩` at the ancillas. -/
def ghzInitial (α : Fin b → ℂ) : Fin (M * 2) → Fin b → ℂ := fun j =>
  if j = site 0 0 then α
  else if (finProdFinEquiv.symm j).2 = 0 then fun _ => 1 else Pi.single 0 1

/-- The measurement-assisted preparation of the GHZ-type state: two layers of controlled
shifts, the measurement of the ancillas `n < M - 1`, and single-site shifts as corrections.

Source: arXiv:2103.13367, Example 1, for qudits; arXiv:2307.01696, paragraph "Long-range MPS
using measurements". -/
noncomputable def ghzProtocol (α : Fin b → ℂ) : MeasurementProtocol b (M * 2) where
  initial := ghzInitial α
  first := [firstLayer, secondLayer]
  measured := secondBonds
  correction := correctionUnitary
  correction_mem_unitary _ _ := Equiv.Perm.permMatrix_mem_unitaryGroup _

/-! ### The action of the protocol -/

omit [NeZero b] [NeZero M] in
private theorem exists_site (j : Fin (M * 2)) : ∃ n r, site n r = j :=
  ⟨(finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2, finProdFinEquiv.apply_symm_apply j⟩

private theorem exists_firstLayer_op_mulVec : ∃ P : Cfg b (M * 2) → Cfg b (M * 2),
    (∀ v, (firstLayer (b := b) (M := M)).op *ᵥ v = v ∘ P) ∧
    (∀ x (n : Fin M), n.val + 1 < M → P x (site n 1) = x (site n 1) - x (site n 0)) ∧
    (∀ x (n : Fin M), P x (site n 0) = x (site n 0)) ∧
    ∀ x (n : Fin M), n.val + 1 = M → P x (site n 1) = x (site n 1) := by
  obtain ⟨P, hv, h1, h2⟩ := exists_shiftLayer_op_mulVec (d := b) firstBonds
    firstBonds_pairwiseDisjoint (fun k : Fin (M * 2) => k + 1)
    (fun (k : Fin (M * 2)) (x : Cfg b (M * 2)) => -x k) firstShift_aux
    fun k _ => isLocalPerm_firstShift k
  refine ⟨P, hv, fun x n hn => ?_, fun x n => ?_, fun x n hn => ?_⟩
  · have := h1 x (site n 0) (mem_firstBonds.mpr ⟨n, hn, rfl⟩) (Or.inr rfl)
    rwa [site_zero_add_one, ← sub_eq_add_neg] at this
  · refine h2 x _ fun k hk => ?_
    obtain ⟨n', -, rfl⟩ := mem_firstBonds.mp hk
    rw [site_zero_add_one]
    exact fun h => absurd (site_injective h).2 (by decide)
  · refine h2 x _ fun k hk => ?_
    obtain ⟨n', hn', rfl⟩ := mem_firstBonds.mp hk
    rw [site_zero_add_one]
    intro h
    have := (site_injective h).1
    subst this
    omega

private theorem exists_secondLayer_op_mulVec : ∃ P : Cfg b (M * 2) → Cfg b (M * 2),
    (∀ v, (secondLayer (b := b) (M := M)).op *ᵥ v = v ∘ P) ∧
    (∀ x (n : Fin M) (hn : n.val + 1 < M),
      P x (site n 1) = x (site n 1) + x (site ⟨n.val + 1, hn⟩ 0)) ∧
    (∀ x (n : Fin M), P x (site n 0) = x (site n 0)) ∧
    ∀ x (n : Fin M), n.val + 1 = M → P x (site n 1) = x (site n 1) := by
  obtain ⟨P, hv, h1, h2⟩ := exists_shiftLayer_op_mulVec (d := b) secondBonds
    secondBonds_pairwiseDisjoint (fun k : Fin (M * 2) => k)
    (fun (k : Fin (M * 2)) (x : Cfg b (M * 2)) => x (k + 1)) secondShift_aux
    fun k _ => isLocalPerm_secondShift k
  refine ⟨P, hv, fun x n hn => ?_, fun x n => ?_, fun x n hn => ?_⟩
  · have := h1 x (site n 1) (mem_secondBonds.mpr ⟨n, hn, rfl⟩) (Or.inl rfl)
    rwa [site_one_add_one n hn] at this
  · refine h2 x _ fun k hk => ?_
    obtain ⟨n', -, rfl⟩ := mem_secondBonds.mp hk
    exact fun h => absurd (site_injective h).2 (by decide)
  · refine h2 x _ fun k hk => ?_
    obtain ⟨n', hn', rfl⟩ := mem_secondBonds.mp hk
    intro h
    have := (site_injective h).1
    subst this
    omega

private theorem ghzPrefix_zero (m : secondBonds (M := M) → Fin b) :
    ghzPrefix m 0 = 0 := by
  simp [ghzPrefix]

omit [NeZero M] in
private theorem ghzPrefix_succ (m : secondBonds (M := M) → Fin b) (n : Fin M)
    (hn : n.val + 1 < M) : ghzPrefix m ⟨n.val + 1, hn⟩ = ghzPrefix m n + ghzOutcome m n := by
  rw [ghzPrefix, show (⟨n.val + 1, hn⟩ : Fin M).castSucc = n.succ from rfl, Fin.partialSum_succ]
  rfl

omit [NeZero M] in
private theorem ghzOutcome_of_not_lt (m : secondBonds (M := M) → Fin b) (n : Fin M)
    (hn : ¬n.val + 1 < M) : ghzOutcome m n = 0 := by
  refine dite_eq_right fun h => hn ?_
  obtain ⟨n', hn', h'⟩ := mem_secondBonds.mp h
  rw [← (site_injective h').1]
  exact hn'

omit [NeZero M] in
/-- The condition of the outcome `m` on the corrected configuration `x + δ` is that every
measured ancilla of `x` is `0`. -/
private theorem forall_add_ghzCorrection_eq_iff (m : secondBonds (M := M) → Fin b)
    (x : Cfg b (M * 2)) :
    (∀ i : secondBonds (M := M), (x + ghzCorrection m) i = m i) ↔
      ∀ n : Fin M, n.val + 1 < M → x (site n 1) = 0 := by
  constructor
  · intro h n hn
    have hi : site n 1 ∈ secondBonds := mem_secondBonds.mpr ⟨n, hn, rfl⟩
    have := h ⟨_, hi⟩
    rwa [Pi.add_apply, ghzCorrection_site_one, ghzOutcome, dite_eq_left hi, add_eq_right] at this
  · rintro h ⟨i, hi⟩
    obtain ⟨n, hn, rfl⟩ := mem_secondBonds.mp hi
    rw [Pi.add_apply, ghzCorrection_site_one, ghzOutcome, dite_eq_left hi, h n hn, zero_add]

private theorem productVector_ghzInitial (α : Fin b → ℂ) (y : Cfg b (M * 2)) :
    productVector (ghzInitial α) y =
      α (y (site 0 0)) * ∏ n, if y (site n 1) = 0 then 1 else 0 := by
  classical
  have h1 : ∀ n : Fin M, ghzInitial α (site n 1) = Pi.single 0 1 := fun n => by
    rw [ghzInitial, ite_eq_right fun h => absurd (site_injective h).2 (by decide)]
    simp [site]
  have h0 : ∀ n : Fin M, n ≠ 0 → ghzInitial α (site n 0) = fun _ => 1 := fun n hn => by
    rw [ghzInitial, ite_eq_right fun h => hn (site_injective h).1]
    simp [site]
  rw [productVector, ← Fintype.prod_equiv finProdFinEquiv
    (fun q => ghzInitial α (site q.1 q.2) (y (site q.1 q.2))) _ fun _ => rfl,
    Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, h1, Pi.single_apply]
  congr 1
  rw [Finset.prod_eq_single 0 (fun n _ hn => by rw [h0 n hn]) (by simp), ghzInitial,
    ite_eq_left rfl]

omit [NeZero b] in
private theorem forall_succ_eq_iff (s : Fin M → Fin b) :
    (∀ (n : Fin M) (hn : n.val + 1 < M), s ⟨n.val + 1, hn⟩ = s n) ↔ ∀ n, s n = s 0 := by
  constructor
  · intro h n
    obtain ⟨k, hk⟩ := n
    induction k with
    | zero => rfl
    | succ k ih => rw [h ⟨k, by omega⟩ hk, ih]
  · intro h n hn
    rw [h, h n]

private theorem ghzProtocol_output_aux (α : Fin b → ℂ) (m : secondBonds (M := M) → Fin b) :
    (ghzProtocol α).output m = withZeroAncillas (ghzState α) := by
  classical
  obtain ⟨PA, hA, hA1, hA0, hAl⟩ := exists_firstLayer_op_mulVec (b := b) (M := M)
  obtain ⟨PB, hB, hB1, hB0, hBl⟩ := exists_secondLayer_op_mulVec (b := b) (M := M)
  have hout : (ghzProtocol α).output m = fun x =>
      (outcomeProj secondBonds m *ᵥ
        fun z => productVector (ghzInitial α) (PA (PB z)))
        (x + ghzCorrection m) := by
    change finKronecker (fun j => (Equiv.addRight (ghzCorrection m j)).permMatrix ℂ) *ᵥ
      (outcomeProj secondBonds m *ᵥ
        (circuitOp [firstLayer, secondLayer] *ᵥ productVector (ghzInitial α))) = _
    simp only [circuitOp, Matrix.one_mul, ← mulVec_mulVec, hA, hB,
      finKronecker_permMatrix_mulVec]
    rfl
  funext x
  rw [hout]
  dsimp only
  rw [outcomeProj_mulVec_apply]
  simp only [forall_add_ghzCorrection_eq_iff]
  rw [productVector_ghzInitial, withZeroAncillas, MPSTensor.ghzState_apply]
  set s : Fin M → Fin b := fun n => x (site n 0) with hs
  set z := x + ghzCorrection m
  have hz0 : ∀ n, z (site n 0) = s n - ghzPrefix m n := fun n => by
    simp [z, ghzCorrection_site_zero, sub_eq_add_neg, s]
  have hz1 : ∀ n, z (site n 1) = x (site n 1) + ghzOutcome m n := fun n => by
    simp [z, ghzCorrection_site_one]
  have hy0 : PA (PB z) (site 0 0) = s 0 := by
    rw [hA0, hB0, hz0, ghzPrefix_zero, sub_zero]
  rw [hy0]
  by_cases hmeas : ∀ n : Fin M, n.val + 1 < M → x (site n 1) = 0
  · rw [ite_eq_left hmeas]
    have hy : ∀ n, PA (PB z) (site n 1) = 0 ↔
        (∀ hn : n.val + 1 < M, s ⟨n.val + 1, hn⟩ = s n) ∧ x (site n 1) = 0 := fun n => by
      by_cases hn : n.val + 1 < M
      · have hval : PA (PB z) (site n 1) = s ⟨n.val + 1, hn⟩ - s n := by
          rw [hA1 _ n hn, hB1 _ n hn, hB0, hz1, hz0, hz0, ghzPrefix_succ m n hn, hmeas n hn]
          abel
        rw [hval, sub_eq_zero]
        simp [hn, hmeas n hn]
      · rw [hAl _ n (by omega), hBl _ n (by omega), hz1, ghzOutcome_of_not_lt m n hn, add_zero]
        simp [hn]
    simp only [Finset.prod_boole, Finset.mem_univ, true_implies, hy]
    have hiff : (∀ n : Fin M, (∀ hn : n.val + 1 < M, s ⟨n.val + 1, hn⟩ = s n) ∧
        x (site n 1) = 0) ↔
        (∀ n : Fin M, x (site n 0) = x (site 0 0)) ∧ ∀ n : Fin M, x (site n 1) = 0 := by
      rw [forall_and, forall_succ_eq_iff]
    simp only [hiff]
    by_cases hc1 : ∀ n : Fin M, x (site n 0) = x (site 0 0) <;>
      by_cases hc2 : ∀ n : Fin M, x (site n 1) = 0 <;> simp [hc1, hc2, s]
  · rw [ite_eq_right hmeas]
    push Not at hmeas
    obtain ⟨n, -, hn⟩ := hmeas
    rw [Finset.prod_eq_zero (Finset.mem_univ n) (ite_eq_right hn), mul_zero]

/-- **Every outcome gives the GHZ-type state.** For every outcome `m` of the measurement of
the ancillas, the corrected vector of the protocol is `|χ_M⟩ = ∑ᵢ αᵢ |i⟩^{⊗M}` with every
ancilla in `|0⟩`.

Source: arXiv:2103.13367, Example 1 ("Given the output `{k_j}`, we finally apply
`⊗ₙ (σ^x_n)^{∑_{m=2}^n k_m}` to the spins"), for qudits. -/
theorem ghzProtocol_output (α : Fin b → ℂ) (m : (ghzProtocol (M := M) α).measured → Fin b) :
    (ghzProtocol α).output m = withZeroAncillas (ghzState α) :=
  ghzProtocol_output_aux α m

/-- **GHZ-type states in constant depth with measurements.** For every `M ≥ 1`, every
dimension `b ≥ 1` and every nonzero `α`, the GHZ-type state
`|χ_M⟩ = ∑ᵢ αᵢ |i⟩^{⊗M}`, with one ancilla per system qudit left in `|0⟩`, is prepared with
measurements in depth `2` on the ring of `2M` sites.

Source: arXiv:2307.01696, paragraph "Long-range MPS using measurements" ("the creation of
GHZ-like states `|χ_M⟩ = ∑_{i=1}^b αᵢ |i⟩^{⊗M}` becomes possible in only constant depth");
arXiv:2103.13367, Example 1 (`|0⟩ → |GHZ⟩` by `QCcc₂`), for qudits. -/
theorem isPreparedWithMeasurementsInDepth_withZeroAncillas_ghzState (α : Fin b → ℂ)
    (hα : α ≠ 0) :
    IsPreparedWithMeasurementsInDepth 2 (withZeroAncillas (M := M) (ghzState α)) := by
  classical
  refine ⟨ghzProtocol α, le_rfl, ?_, fun m _ => ⟨1, ?_⟩⟩
  swap
  · rw [one_smul]
    exact ghzProtocol_output α m
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hα
  intro h0
  change productVector (ghzInitial α) = 0 at h0
  have := congrFun h0 (fun j => if j = site 0 0 then i else 0)
  rw [productVector_ghzInitial] at this
  have hne : ∀ n : Fin M, site n 1 ≠ site 0 0 := fun n h =>
    absurd (site_injective h).2 (by decide)
  exact hi (by simpa [hne] using this)

end Ring

end MPSPreparation
