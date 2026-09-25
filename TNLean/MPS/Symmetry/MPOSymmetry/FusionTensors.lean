/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Core.ReductionUniqueness
import TNLean.MPS.FundamentalTheorem.Reduction.MPOProduct
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Fusion tensors and action tensors of matrix product operator algebras

Let `O_a` be MPO tensors whose periodic operators obey fusion rules
`O_a O_b = ∑_c N_{ab}^c O_c` at every positive length, with length-independent multiplicities
`N_{ab}^c ∈ ℕ` and normal tensors `O_c` of positive bond dimension
(Garre-Rubio--Lootens--Molnár, arXiv:2203.12563, lines 361--362).  The paper introduces fusion
tensors `W_{ab}^{c,μ}`, `Ŵ_{ab}^{c,μ}`, `μ = 1, …, N_{ab}^c`, that decompose the stacked product
of two MPO tensors into copies of the tensors `T_c`, with orthogonality relations
`W_{ab}^{c,μ} Ŵ_{ab}^{d,ν} = δ_{cd} δ_{μν} 1` (equations `fusiontensors` and `eq:orthoW`).  The
paper derives them from the closedness condition for arbitrary boundary conditions (Appendix
`ap:proofs`, lines 2305--2313), which makes the decomposition exact.

This file derives the periodic-boundary version from the fusion rules alone, through the
multi-block asymmetric compression theorem (Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2,
Proposition 20, and its multi-block form in
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, Theorem 7.7).  The
decomposition then holds up to a nilpotent remainder, as the paper records for periodic
boundaries at lines 1028 and 1131 (the tails of the off-diagonal blocks vanish after a finite
number of sites).  Each copy `(c, μ)` of the fusion channel `c` is a separate block of the
compression, indexed by the sigma type `Σ c, Fin (N_{ab}^c)`.

The same argument gives the action tensors `V_{ax}^{y,i}` of an MPO on a family of matrix
product states (arXiv:2203.12563, equation `fusiontensors2`, lines 459--480), from the
periodic-boundary relation `O_a ψ_{A_x} = ∑_y M_{a,x}^y ψ_{A_y}` (lines 567--568).

## Main results

* `MPSTensor.exists_multiBlockCompression_sigma_of_isNormal`: a tensor whose periodic vectors
  are `∑_c N_c` times those of normal tensors compresses onto `N_c` copies of each of them.
* `MPSTensor.exists_multiplicityReductions_of_isNormal`: the per-copy reductions, their
  biorthogonality, and the nilpotency of the remainder beyond the bond dimension.
* `MPOTensor.exists_fusionTensors_of_mpo_mul_eq_sum`: fusion tensors with multiplicity.
* `MPOTensor.IsMPOFusionAlgebra.exists_fusionTensors`: the same for a matrix product operator
  fusion algebra.
* `MPOTensor.exists_actionTensors_of_mpo_mulVec_eq_sum`: action tensors with multiplicity.
* `MPOTensor.exists_boundary_dressed_proportional_of_mpo_mul_eq`: the gauge freedom of the
  fusion tensors of a multiplicity-free single fusion channel is one nonzero scalar, after
  sufficiently long words.
-/

open scoped Matrix

namespace MPSTensor

variable {d DB : ℕ} {L : Type*} [Fintype L] [DecidableEq L] {D : L → ℕ}

omit [DecidableEq L] in
/-- A sum weighted by natural-number multiplicities is the sum over the copies. -/
theorem sum_natCast_mul_eq_sum_sigma (N : L → ℕ) (f : L → ℂ) :
    ∑ c, (N c : ℂ) * f c = ∑ s : Σ c, Fin (N c), f s.1 := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

/-- **Compression onto blocks with multiplicity** (P5 note, Theorem 7.7, with the multiplicity
index made explicit).  If the periodic vectors of `B` are `V_n(B) = ∑_c N_c V_n(C_c)` at every
positive length, with normal tensors `C_c` of positive bond dimension and multiplicities
`N_c ∈ ℕ`, then `B` admits a multi-block compression onto the family indexed by the copies
`(c, μ)`, `μ < N_c`, whose block at `(c, μ)` is `C_c`.

This is `MPSTensor.exists_multiBlockCompression_of_isNormal` applied to the sigma type of copies;
no hypothesis relating distinct `C_c` is needed. -/
theorem exists_multiBlockCompression_sigma_of_isNormal (B : MPSTensor d DB)
    (C : ∀ c, MPSTensor d (D c)) (N : L → ℕ) (hC : ∀ c, Kraus.IsNormal (C c))
    (hD : ∀ c, 0 < D c)
    (hmpv : ∀ n : ℕ, 0 < n → ∀ σ : Fin n → Fin d,
      mpv B σ = ∑ c, (N c : ℂ) * mpv (C c) σ) :
    Nonempty (MultiBlockCompression (D := fun s : Σ c, Fin (N c) => D s.1) B Finset.univ
      fun s => C s.1) := by
  refine exists_multiBlockCompression_of_isNormal (D := fun s : Σ c, Fin (N c) => D s.1)
    Finset.univ (fun s => C s.1) (fun s _ => hC s.1) (fun s _ => hD s.1) B fun w hw => ?_
  have h := hmpv w.length (List.length_pos_of_ne_nil hw) w.get
  simp only [mpv, coeff, List.ofFn_get] at h
  rw [h, sum_natCast_mul_eq_sum_sigma N fun c => (Kraus.evalWord (C c) w).trace]

omit [DecidableEq L] in
/-- **Reductions onto blocks with multiplicity**.  Under the hypotheses of
`MPSTensor.exists_multiBlockCompression_sigma_of_isNormal`, there are, for every copy
`s = (c, μ)`, rectangular matrices `V s` and `W s` such that

* `(V s, W s)` is a reduction of `B` onto `C_c`: `V s W s = 1` and `V s B^w W s = C_c^w` for
  every word `w`;
* distinct copies are biorthogonal: `V s W t = 0` for `s ≠ t`;
* the remainder `B^i - ∑_s W s C_{s.1}^i V s` is nilpotent: its words of length at least the
  bond dimension of `B` vanish.

These are the relations `W_{ab}^{c,μ} Ŵ_{ab}^{d,ν} = δ_{cd} δ_{μν} 1` of arXiv:2203.12563,
equation `eq:orthoW`, together with the periodic-boundary form of the decomposition, whose
off-diagonal tails vanish after finitely many sites (lines 1028 and 1131). -/
theorem exists_multiplicityReductions_of_isNormal (B : MPSTensor d DB)
    (C : ∀ c, MPSTensor d (D c)) (N : L → ℕ) (hC : ∀ c, Kraus.IsNormal (C c))
    (hD : ∀ c, 0 < D c)
    (hmpv : ∀ n : ℕ, 0 < n → ∀ σ : Fin n → Fin d,
      mpv B σ = ∑ c, (N c : ℂ) * mpv (C c) σ) :
    ∃ (V : ∀ s : Σ c, Fin (N c), Matrix (Fin (D s.1)) (Fin DB) ℂ)
      (W : ∀ s : Σ c, Fin (N c), Matrix (Fin DB) (Fin (D s.1)) ℂ),
      (∀ s, IsReduction B (C s.1) (V s) (W s)) ∧
        (∀ s t, s ≠ t → V s * W t = 0) ∧
        ∀ w : List (Fin d), DB ≤ w.length →
          Kraus.evalWord (fun i => B i - ∑ s, W s * C s.1 i * V s) w = 0 := by
  classical
  obtain ⟨P⟩ := exists_multiBlockCompression_sigma_of_isNormal B C N hC hD hmpv
  refine ⟨fun s => P.left ⟨s, Finset.mem_univ s⟩, fun s => P.right ⟨s, Finset.mem_univ s⟩,
    fun s => P.isReduction ⟨s, Finset.mem_univ s⟩, fun s t hst => P.left_mul_right_of_ne
      fun h => hst (congrArg Subtype.val h), fun w hw => ?_⟩
  have hrem : (fun i => B i - ∑ s, P.right ⟨s, Finset.mem_univ s⟩ * C s.1 i *
      P.left ⟨s, Finset.mem_univ s⟩) = P.remainder := by
    funext i
    rw [MultiBlockCompression.remainder]
    congr 1
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv Finset.mem_univ) _ _ fun _ => rfl).symm
  rw [hrem]
  refine P.evalWord_remainder_eq_zero w (le_trans ?_ hw)
  have hdim := P.dim_eq
  have hcard : (Finset.univ : Finset (Σ c, Fin (N c))).card ≤
      ∑ s ∈ (Finset.univ : Finset (Σ c, Fin (N c))), D s.1 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun s _ => hD s.1
  omega

namespace IsReduction

variable {DA : ℕ} {B : MPSTensor d DB} {A : MPSTensor d DA}
  {V V' : Matrix (Fin DA) (Fin DB) ℂ} {W W' : Matrix (Fin DB) (Fin DA) ℂ}

/-- A residual nilpotency statement for all words of length at least `K` gives the
exact-length bound of MGSC18, Definition 8, at `K`. -/
theorem isReductionResidualNilpotencyBound_of_forall_le {K : ℕ}
    (h : ∀ w : List (Fin d), K ≤ w.length →
      Kraus.evalWord (fun i => B i - W * A i * V) w = 0) :
    IsReductionResidualNilpotencyBound B A V W K :=
  fun w hw => h w hw.ge

/-- **Uniqueness of a single reduction with a nilpotent remainder**, in the form produced by
the compression theorems: two reductions of `B` onto the same normal tensor `A`, whose
remainders `B^i - W A^i V` both have vanishing words of every length at least `K`, agree up
to one nonzero scalar on every word longer than `2K`, after dressing with the source word.

Source: Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Theorem 22, `cornerproblem.tex` lines
3156--3162 and 4007--4035 (via `MPSTensor.IsReduction.exists_boundary_dressed_proportional`). -/
theorem exists_boundary_dressed_proportional_of_forall_le (h : IsReduction B A V W)
    (h' : IsReduction B A V' W') (hA : Kraus.IsNormal A) {K : ℕ}
    (hK : ∀ w : List (Fin d), K ≤ w.length →
      Kraus.evalWord (fun i => B i - W * A i * V) w = 0)
    (hK' : ∀ w : List (Fin d), K ≤ w.length →
      Kraus.evalWord (fun i => B i - W' * A i * V') w = 0) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ w : List (Fin d), 2 * K < w.length →
      V * Kraus.evalWord B w = z • (V' * Kraus.evalWord B w) ∧
        Kraus.evalWord B w * W = z⁻¹ • (Kraus.evalWord B w * W') :=
  h.exists_boundary_dressed_proportional h' hA
    (isReductionResidualNilpotencyBound_of_forall_le hK)
    (isReductionResidualNilpotencyBound_of_forall_le hK')

end IsReduction

end MPSTensor

namespace MPOTensor

variable {d : ℕ} {L : Type*} [Fintype L]

/-- **Fusion tensors with multiplicity** (Garre-Rubio--Lootens--Molnár, arXiv:2203.12563,
equations `fusiontensors` and `eq:orthoW`, lines 361--389).  Let the periodic operators of the
MPO tensors `O_c` obey the fusion rule `O_a O_b = ∑_c N_{ab}^c O_c` at every positive length,
with `N_{ab}^c ∈ ℕ` and every `O_c` normal (as a tensor on the pair alphabet) of positive bond
dimension.  Then there are fusion tensors `V s`, `W s` for every copy `s = (c, μ)`,
`μ < N_{ab}^c`, of every fusion channel such that

* `(V s, W s)` reduces the stacked product `mulTensor (O a) (O b)` onto `O_c`;
* `V s W t = 0` for distinct copies, so that with `V s W s = 1` these are the paper's
  orthogonality relations `W_{ab}^{c,μ} Ŵ_{ab}^{d,ν} = δ_{cd} δ_{μν} 1`;
* the remainder `B^{ij} - ∑_s W s O_{s.1}^{ij} V s` of the paper's decomposition
  `∑_m T_a^{lm} T_b^{mp} = ∑_{c,μ} Ŵ_{ab}^{c,μ} T_c^{lp} W_{ab}^{c,μ}` is nilpotent: its words
  of length at least `χ_a χ_b` vanish.

The paper proves the exact decomposition from the closedness condition for arbitrary boundary
conditions (Appendix `ap:proofs`, lines 2305--2313).  Here only the periodic fusion rules are
assumed, and the decomposition holds up to the nilpotent remainder, the off-diagonal tails
that the paper describes for periodic boundaries at lines 1028 and 1131. -/
theorem exists_fusionTensors_of_mpo_mul_eq_sum {χ : L → ℕ} (O : ∀ c, MPOTensor d (χ c))
    (N : L → L → L → ℕ) (hO : ∀ c, Kraus.IsNormal (O c).toMPSTensor) (hχ : ∀ c, 0 < χ c)
    (a b : L)
    (hfus : ∀ n : ℕ, 0 < n → mpo (O a) n * mpo (O b) n = ∑ c, (N a b c : ℂ) • mpo (O c) n) :
    ∃ (V : ∀ s : Σ c, Fin (N a b c), Matrix (Fin (χ s.1)) (Fin (χ a * χ b)) ℂ)
      (W : ∀ s : Σ c, Fin (N a b c), Matrix (Fin (χ a * χ b)) (Fin (χ s.1)) ℂ),
      (∀ s, MPSTensor.IsReduction (mulTensor (O a) (O b)).toMPSTensor (O s.1).toMPSTensor
          (V s) (W s)) ∧
        (∀ s t, s ≠ t → V s * W t = 0) ∧
        ∀ w : List (Fin (d * d)), χ a * χ b ≤ w.length →
          Kraus.evalWord (fun i => (mulTensor (O a) (O b)).toMPSTensor i -
            ∑ s, W s * (O s.1).toMPSTensor i * V s) w = 0 := by
  classical
  refine MPSTensor.exists_multiplicityReductions_of_isNormal _ (fun c => (O c).toMPSTensor)
    (N a b) hO hχ fun n hn ρ => ?_
  have h := congrFun (congrFun (hfus n hn) fun k => (ρ k).divNat) fun k => (ρ k).modNat
  rw [← mpo_mulTensor] at h
  rw [mpv_toMPSTensor, h, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun c _ => by rw [Matrix.smul_apply, smul_eq_mul, mpv_toMPSTensor]

/-- **Fusion tensors of a matrix product operator fusion algebra** (arXiv:2203.12563, lines
361--389): `MPOTensor.exists_fusionTensors_of_mpo_mul_eq_sum` for every pair of labels of an
algebra whose tensors are normal of positive bond dimension. -/
theorem IsMPOFusionAlgebra.exists_fusionTensors {χ : L → ℕ} {O : ∀ c, MPOTensor d (χ c)}
    {N : L → L → L → ℕ} (hF : IsMPOFusionAlgebra O N)
    (hO : ∀ c, Kraus.IsNormal (O c).toMPSTensor) (hχ : ∀ c, 0 < χ c) (a b : L) :
    ∃ (V : ∀ s : Σ c, Fin (N a b c), Matrix (Fin (χ s.1)) (Fin (χ a * χ b)) ℂ)
      (W : ∀ s : Σ c, Fin (N a b c), Matrix (Fin (χ a * χ b)) (Fin (χ s.1)) ℂ),
      (∀ s, MPSTensor.IsReduction (mulTensor (O a) (O b)).toMPSTensor (O s.1).toMPSTensor
          (V s) (W s)) ∧
        (∀ s t, s ≠ t → V s * W t = 0) ∧
        ∀ w : List (Fin (d * d)), χ a * χ b ≤ w.length →
          Kraus.evalWord (fun i => (mulTensor (O a) (O b)).toMPSTensor i -
            ∑ s, W s * (O s.1).toMPSTensor i * V s) w = 0 :=
  exists_fusionTensors_of_mpo_mul_eq_sum O N hO hχ a b (hF a b)

/-- **Action tensors with multiplicity** (Garre-Rubio--Lootens--Molnár, arXiv:2203.12563,
equation `fusiontensors2`, lines 459--480).  Let the periodic operator of the MPO tensor `T`
act on the periodic vector of `A_x` as `O_T ψ_{A_x} = ∑_y M_y ψ_{A_y}` at every positive
length (the periodic-boundary form of lines 567--568), with multiplicities `M_y ∈ ℕ` and
normal tensors `A_y` of positive bond dimension.  Then there are action tensors `V s`, `W s`
for every copy `s = (y, i)`, `i < M_y`, such that `(V s, W s)` reduces the action tensor
`T · A_x` onto `A_y`, distinct copies are biorthogonal, and the remainder of the decomposition
`∑_l T^{ml} A_x^l = ∑_{y,i} V̂_{ax}^{y,i} A_y^m V_{ax}^{y,i}` has vanishing words of length at
least the bond dimension of `T · A_x`. -/
theorem exists_actionTensors_of_mpo_mulVec_eq_sum {κ : Type*} [Fintype κ]
    {χ Dx : ℕ} {D : κ → ℕ} (T : MPOTensor d χ) (Ax : MPSTensor d Dx)
    (A : ∀ y, MPSTensor d (D y)) (M : κ → ℕ) (hA : ∀ y, Kraus.IsNormal (A y))
    (hD : ∀ y, 0 < D y)
    (hact : ∀ n : ℕ, 0 < n →
      mpo T n *ᵥ (fun τ : Fin n → Fin d => MPSTensor.mpv Ax τ) =
        fun σ : Fin n → Fin d => ∑ y, (M y : ℂ) * MPSTensor.mpv (A y) σ) :
    ∃ (V : ∀ s : Σ y, Fin (M y), Matrix (Fin (D s.1)) (Fin (χ * Dx)) ℂ)
      (W : ∀ s : Σ y, Fin (M y), Matrix (Fin (χ * Dx)) (Fin (D s.1)) ℂ),
      (∀ s, MPSTensor.IsReduction (actTensor T Ax) (A s.1) (V s) (W s)) ∧
        (∀ s t, s ≠ t → V s * W t = 0) ∧
        ∀ w : List (Fin d), χ * Dx ≤ w.length →
          Kraus.evalWord (fun i => actTensor T Ax i - ∑ s, W s * A s.1 i * V s) w = 0 := by
  classical
  exact MPSTensor.exists_multiplicityReductions_of_isNormal _ A M hA hD fun n hn σ =>
    congrFun ((mpo_mulVec_mpv T Ax n).symm.trans (hact n hn)) σ

/-- **Gauge freedom of a multiplicity-free fusion channel** (arXiv:2203.12563, line 361: the
fusion tensors are unique up to a gauge; line 416 describes the gauge for exact
decompositions).  Let `(V, W)` and `(V', W')` be two reductions of the stacked product
`B = mulTensor (O_a) (O_b)` onto the same normal tensor `O_c`, each with a remainder
`B^i - W O_c^i V` whose words of every length at least `K` vanish.  Then they agree up to one
nonzero scalar `z` once dressed with a word of the stacked product longer than `2K`:
`V B^w = z V' B^w` and `B^w W = z⁻¹ B^w W'`.

Such pairs are exactly the fusion tensors of a single multiplicity-free channel: when
`O_a O_b = O_c` at every positive length, `MPOTensor.exists_fusionTensors_of_mpo_mul_eq_sum`
with `N_{ab}^{c'} = δ_{c c'}` produces one with `K = χ_a χ_b`.  With several channels the
single-copy remainder is not nilpotent, and the dressed proportionality fails in general
(two compressions of `A ⊕ A'` may differ by an off-diagonal shear on the `A'` block).

This is the boundary-dressed uniqueness theorem of Molnár--Ge--Schuch--Cirac,
arXiv:1706.07329v2, Theorem 22 (`cornerproblem.tex` lines 3156--3162), on the pair alphabet.
The source's gauge `W ↦ y W`, `Ŵ ↦ y⁻¹ Ŵ` is recovered only after dressing, because in the
periodic setting the fusion tensors are not determined off the support of long words. -/
theorem exists_boundary_dressed_proportional_of_mpo_mul_eq {χa χb χc : ℕ}
    {Oa : MPOTensor d χa} {Ob : MPOTensor d χb} {Oc : MPOTensor d χc}
    (hOc : Kraus.IsNormal Oc.toMPSTensor)
    {V V' : Matrix (Fin χc) (Fin (χa * χb)) ℂ} {W W' : Matrix (Fin (χa * χb)) (Fin χc) ℂ}
    (h : MPSTensor.IsReduction (mulTensor Oa Ob).toMPSTensor Oc.toMPSTensor V W)
    (h' : MPSTensor.IsReduction (mulTensor Oa Ob).toMPSTensor Oc.toMPSTensor V' W') {K : ℕ}
    (hK : ∀ w : List (Fin (d * d)), K ≤ w.length →
      Kraus.evalWord (fun i => (mulTensor Oa Ob).toMPSTensor i - W * Oc.toMPSTensor i * V) w =
        0)
    (hK' : ∀ w : List (Fin (d * d)), K ≤ w.length →
      Kraus.evalWord (fun i => (mulTensor Oa Ob).toMPSTensor i - W' * Oc.toMPSTensor i * V') w =
        0) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ w : List (Fin (d * d)), 2 * K < w.length →
      V * Kraus.evalWord (mulTensor Oa Ob).toMPSTensor w =
          z • (V' * Kraus.evalWord (mulTensor Oa Ob).toMPSTensor w) ∧
        Kraus.evalWord (mulTensor Oa Ob).toMPSTensor w * W =
          z⁻¹ • (Kraus.evalWord (mulTensor Oa Ob).toMPSTensor w * W') :=
  h.exists_boundary_dressed_proportional_of_forall_le h' hOc hK hK'

end MPOTensor
