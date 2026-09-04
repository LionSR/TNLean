/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import TNLean.MPS.ParentHamiltonian.Martingale.NachtergaeleFullRangeEstimate

/-!
# The lower endpoint in Nachtergaele's Theorem 2.1(i)

Conditions C1, C2, and C3 of Nachtergaele, arXiv:cond-mat/9410110, at lines
1030--1041, 1043--1058, and 1083--1094, carry lower endpoints: C1 sums from
the window length, and C2 and C3 are imposed only from an index \(n_l\)
onwards. Theorem 2.1(i) at lines 1119--1130 nevertheless concludes
\[
\langle\psi\mid H_{\Lambda_N}\psi\rangle
\geq\frac{\gamma_{l+1}}{d_{l+1}}
  \left(1-\epsilon_l\sqrt{l+1}\right)^2\lVert\psi\rVert^2
\]
for every \(N\) and every \(\psi\) orthogonal to the ground space, and its
proof at lines 1195--1259 resolves \(\psi\) over the whole range
\(0\leq n<N\) and estimates every martingale difference \(E_n\psi\).

This file shows that the printed conclusion does not follow from the printed
hypotheses. `FrustrationFree.UnrestrictedNachtergaeleEstimate` transcribes
Theorem 2.1(i) with each condition imposed exactly on the source range it
carries -- C1 on \(l\leq n<N\) after the reindexing of its window sum, at the
volumes \(\Lambda_{n_0}\) and \(\Lambda_N\) at which the source asserts it,
and C2 and C3 on \(n_0\leq n<N\) -- together with the source's ordering
\(l\leq n_0\) of the onset, the nontriviality of every ground space that C2
requires, and the conclusion on \(\lVert\psi\rVert^2\); then
`FrustrationFree.not_unrestrictedNachtergaeleEstimate` refutes it in every
dimension \(k+2\).

The refuting data is the restriction of a genuine spin chain to an invariant
subspace. Take one-site interactions \(h_x=\lvert1\rangle\langle1\rvert_x\)
for \(x\geq2\) and \(h_1=\frac12\lvert1\rangle\langle1\rvert_1\), with
\(\Lambda_n=[1,n]\), so that \(\mathcal G_{\Lambda_n}\) is spanned by
\(\lvert0^n\rangle\) and \(G_{\Lambda_n}=\prod_{x\leq n}P_x\) with
\(P_x=\lvert0\rangle\langle0\rvert_x\). Conditions C1, C2, and C3 hold with
\(d_q=q\), \(\gamma_q=1\), \(\epsilon_l=0\), and \(n_l=l+1\), the last
because the weakened bond at the left end is inside
\(\Lambda_n\setminus\Lambda_{n-l}\) exactly when \(n\leq l\). The vector
\(\psi=\lvert10\cdots0\rangle\) is orthogonal to \(\mathcal G_{\Lambda_N}\)
and satisfies \(\langle\psi\mid H_{\Lambda_N}\psi\rangle=\frac12
\lVert\psi\rVert^2\), which is below the printed bound
\(\frac{\gamma_1}{d_1}\lVert\psi\rVert^2=\lVert\psi\rVert^2\).

The span of the vacuum \(\lvert0^N\rangle\) together with the single
excitations \(\lvert0^m10^{N-m-1}\rangle\) is invariant under every operator
involved, and restricting to it produces the coordinate model below on a space
of dimension \(N+1\). Keeping the vacuum coordinate keeps every ground space
\(\mathcal G_{\Lambda_n}=\ker H_{\Lambda_n}\) of the chain nontrivial, as C2
requires, and in particular \(\mathcal G_{\Lambda_N}\) is the line it spans.

**Local fix (lower endpoint of Theorem 2.1(i)):** The printed statement is
repaired by requiring the martingale differences below the C2--C3 onset to
annihilate \(\psi\). The repaired theorem is
`energy_lower_bound_of_nachtergaele_c1_c3_of_martingaleDifference_below_eq_zero`
in `TNLean.MPS.ParentHamiltonian.Martingale.NachtergaeleFullRangeEstimate`.
The source defect and the repair are recorded in
`docs/paper-gaps/nachtergaele96_theorem_2_1_lower_endpoint.tex`.
-/

open scoped BigOperators InnerProductSpace

namespace FrustrationFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Theorem 2.1(i) of Nachtergaele, arXiv:cond-mat/9410110, lines 1119--1130,
transcribed in the finite-filtration notation of its proof at lines
1195--1259, with each of C1, C2, and C3 imposed exactly on the source index
range it carries and the conclusion on \(\lVert v\rVert^2\).

Condition C1 at lines 1030--1035 sums from the window length, so at window
\(l+1\) and volume \(\Lambda_M\) it reads
\(0\leq\sum_{n=l+1}^{M}H_{\Lambda_n\setminus\Lambda_{n-l-1}}
\leq d_{l+1}H_{\Lambda_M}\); reindexing to the summand
\(H_{\Lambda_{n+1}\setminus\Lambda_{n-l}}\) puts it on \(l\leq n<M\). It is
assumed here at the two volumes the source makes available and the printed
proof uses, namely \(M=N\) in full and \(M=n_0\) in its nonnegativity clause.
Conditions C2 and C3 at lines 1043--1058 and 1083--1094 are imposed from the
onset index \(n_0=\max\{l,n_l,n_{l+1}-1\}\) onwards, hence on \(n_0\leq n<N\),
and that onset is at least \(l\). Condition C2 also asks that each ground
space \(\mathcal G_\Lambda=\ker H_\Lambda\) be nontrivial, which is the
nonvanishing of the corresponding projection.

This is the hypothesis list of
`NestedGroundProjections.energy_lower_bound_of_nachtergaele_c1_c3_threshold`,
with C1 restated on its own source range and the nontriviality clause of C2
adjoined, together with the printed conclusion in place of the estimate on the
martingale mass above the threshold. It is refuted by
`not_unrestrictedNachtergaeleEstimate`. -/
def UnrestrictedNachtergaeleEstimate (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : Prop :=
  ∀ (G : NestedGroundProjections (E := E)) (Q localHamiltonian : ℕ → E →ₗ[ℂ] E)
    (H : E →ₗ[ℂ] E) (N n₀ l : ℕ) (v : E) (γ d ε : ℝ),
    l ≤ n₀ → n₀ ≤ N →
    G.projection 0 = LinearMap.id →
    (∀ n ≤ N, G.projection n ≠ 0) →
    (∀ n ∈ Finset.Ico n₀ N, Q n ≠ 0) →
    v ∈ (LinearMap.range (G.projection N))ᗮ →
    0 < γ → 0 < d → 0 ≤ ε → ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) →
    (∀ n ∈ Finset.Ico n₀ N, (Q n).IsSymmetricProjection) →
    (∀ n ∈ Finset.Ico n₀ N, ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp (Q n) =
        (Q n).comp (G.martingaleDifference m)) →
    (∀ x,
      0 ≤ ∑ n ∈ Finset.Ico l N, (⟪localHamiltonian n x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.Ico l N, (⟪localHamiltonian n x, x⟫_ℂ).re) ≤
        d * (⟪H x, x⟫_ℂ).re) →
    (∀ x, 0 ≤ ∑ n ∈ Finset.Ico l n₀, (⟪localHamiltonian n x, x⟫_ℂ).re) →
    (∀ n ∈ Finset.Ico n₀ N, ∀ x,
      γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) x‖ ^ 2 ≤
        (⟪localHamiltonian n x, x⟫_ℂ).re) →
    (∀ n ∈ Finset.Ico n₀ N,
      ‖(Q n).toContinuousLinearMap.comp
          (G.martingaleDifference n).toContinuousLinearMap‖ ≤ ε) →
    (γ / d) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ^ 2 ≤
      (⟪H v, v⟫_ℂ).re

namespace NachtergaeleLowerEndpoint

/-! ### Coordinate operators

Every operator of the refuting model is multiplication by a real weight in the
fixed orthonormal basis, so the whole verification reduces to finite sums of
weights. -/

/-- Multiplication by a real weight in each coordinate. -/
private noncomputable def diagonal (k : ℕ) (f : Fin k → ℝ) :
    EuclideanSpace ℂ (Fin k) →ₗ[ℂ] EuclideanSpace ℂ (Fin k) where
  toFun x := WithLp.toLp 2 fun i ↦ (f i : ℂ) * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp; ring

@[simp]
private theorem diagonal_apply (k : ℕ) (f : Fin k → ℝ)
    (x : EuclideanSpace ℂ (Fin k)) (i : Fin k) :
    diagonal k f x i = (f i : ℂ) * x i := rfl

private theorem diagonal_congr (k : ℕ) {f g : Fin k → ℝ} (h : ∀ i, f i = g i) :
    diagonal k f = diagonal k g := by
  ext x i
  simp [h i]

private theorem diagonal_comp (k : ℕ) (f g : Fin k → ℝ) :
    (diagonal k f).comp (diagonal k g) = diagonal k fun i ↦ f i * g i := by
  ext x i
  simp [mul_assoc]

private theorem diagonal_sub (k : ℕ) (f g : Fin k → ℝ) :
    diagonal k f - diagonal k g = diagonal k fun i ↦ f i - g i := by
  ext x i
  simp [sub_mul]

private theorem diagonal_one (k : ℕ) :
    diagonal k (fun _ ↦ (1 : ℝ)) = LinearMap.id := by
  ext x i
  simp

private theorem diagonal_zero (k : ℕ) :
    diagonal k (fun _ ↦ (0 : ℝ)) = 0 := by
  ext x i
  simp

private theorem diagonal_ne_zero (k : ℕ) (f : Fin k → ℝ) (i : Fin k)
    (hf : f i ≠ 0) : diagonal k f ≠ 0 := by
  intro hzero
  refine hf ?_
  have hi : diagonal k f (EuclideanSpace.single i (1 : ℂ)) i = 0 := by
    rw [hzero]
    simp
  simpa using hi

private theorem diagonal_isSymmetric (k : ℕ) (f : Fin k → ℝ) :
    (diagonal k f).IsSymmetric := by
  intro x y
  simp [PiLp.inner_apply, mul_assoc, mul_left_comm]

private theorem diagonal_isSymmetricProjection (k : ℕ) (f : Fin k → ℝ)
    (hf : ∀ i, f i * f i = f i) : (diagonal k f).IsSymmetricProjection where
  isIdempotentElem := by
    change diagonal k f * diagonal k f = diagonal k f
    rw [Module.End.mul_eq_comp, diagonal_comp]
    exact diagonal_congr k hf
  isSymmetric := diagonal_isSymmetric k f

private theorem inner_diagonal_re (k : ℕ) (f : Fin k → ℝ)
    (x : EuclideanSpace ℂ (Fin k)) :
    (⟪diagonal k f x, x⟫_ℂ).re = ∑ i, f i * ‖x i‖ ^ 2 := by
  rw [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc : (starRingEnd ℂ) (x i) * x i = ((‖x i‖ : ℝ) : ℂ) ^ 2 :=
    RCLike.conj_mul _
  have h : ⟪diagonal k f x i, x i⟫_ℂ =
      ((f i : ℝ) : ℂ) * ((‖x i‖ : ℝ) : ℂ) ^ 2 := by
    rw [RCLike.inner_apply, diagonal_apply, map_mul, Complex.conj_ofReal, ← hc]
    ring
  rw [h, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem norm_sq_diagonal (k : ℕ) (f : Fin k → ℝ)
    (x : EuclideanSpace ℂ (Fin k)) :
    ‖diagonal k f x‖ ^ 2 = ∑ i, f i ^ 2 * ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [mul_pow]

/-! ### The refuting model

The weights below are the restrictions of the spin-chain operators of the
module docstring to the span of the vacuum and the single-excitation vectors,
for the chain of \(N=k+1\) sites. Coordinate \(i<k+1\) carries the excitation
at site \(i+1\), and the last coordinate \(k+1\) carries the vacuum
\(\lvert0^N\rangle\); the weakened left bond appears as the coefficient
\(1/2\) at coordinate \(0\). -/

/-- The ground-space weight of \(G_{\Lambda_n}\): a coordinate survives
exactly when its excitation sits outside \(\Lambda_n\), and the vacuum
coordinate survives at every level \(n\leq k+1\). -/
private noncomputable def groundWeight (k n : ℕ) : Fin (k + 2) → ℝ :=
  fun i ↦ if n ≤ (i : ℕ) then 1 else 0

/-- The one-site energy: \(1/2\) at the weakened left bond, \(1\) at the
remaining excitations, and \(0\) at the vacuum coordinate. -/
private noncomputable def siteWeight (k : ℕ) : Fin (k + 2) → ℝ :=
  fun i ↦ if (i : ℕ) = 0 then 1 / 2 else if (i : ℕ) = k + 1 then 0 else 1

/-- The weight of the local Hamiltonian
\(H_{\Lambda_{n+1}\setminus\Lambda_n}\). -/
private noncomputable def localWeight (k n : ℕ) : Fin (k + 2) → ℝ :=
  fun i ↦ if (i : ℕ) = n then siteWeight k i else 0

/-- The weight of \(G_{\Lambda_{n+1}\setminus\Lambda_n}\). -/
private noncomputable def excitationWeight (k n : ℕ) : Fin (k + 2) → ℝ :=
  fun i ↦ if (i : ℕ) = n then 0 else 1

/-- The weight of the martingale difference \(E_n\). -/
private noncomputable def differenceWeight (k n : ℕ) : Fin (k + 2) → ℝ :=
  fun i ↦ if (i : ℕ) = n then 1 else 0

private theorem siteWeight_nonneg (k : ℕ) (i : Fin (k + 2)) :
    0 ≤ siteWeight k i := by
  simp only [siteWeight]
  split_ifs <;> norm_num

private theorem localWeight_nonneg (k n : ℕ) (i : Fin (k + 2)) :
    0 ≤ localWeight k n i := by
  simp only [localWeight]
  split_ifs with h
  · exact siteWeight_nonneg k i
  · exact le_rfl

private theorem inner_localWeight_nonneg (k n : ℕ)
    (x : EuclideanSpace ℂ (Fin (k + 2))) :
    0 ≤ (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re := by
  rw [inner_diagonal_re]
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (localWeight_nonneg k n i) (sq_nonneg _)

private theorem groundWeight_mul_self (k n : ℕ) (i : Fin (k + 2)) :
    groundWeight k n i * groundWeight k n i = groundWeight k n i := by
  simp only [groundWeight]
  split_ifs <;> norm_num

private theorem excitationWeight_mul_self (k n : ℕ) (i : Fin (k + 2)) :
    excitationWeight k n i * excitationWeight k n i = excitationWeight k n i := by
  simp only [excitationWeight]
  split_ifs <;> norm_num

/-- The nested ground-space projections of the refuting model. -/
private noncomputable def chain (k : ℕ) :
    NestedGroundProjections (E := EuclideanSpace ℂ (Fin (k + 2))) where
  projection n := diagonal (k + 2) (groundWeight k n)
  isSymmetricProjection n :=
    diagonal_isSymmetricProjection _ _ (groundWeight_mul_self k n)
  antitone_range := by
    intro m n hmn
    have hcomp :
        (diagonal (k + 2) (groundWeight k m)).comp
            (diagonal (k + 2) (groundWeight k n)) =
          diagonal (k + 2) (groundWeight k n) := by
      rw [diagonal_comp]
      refine diagonal_congr _ fun i ↦ ?_
      simp only [groundWeight]
      split_ifs <;> first | (exfalso; omega) | norm_num
    calc
      LinearMap.range (diagonal (k + 2) (groundWeight k n)) =
          LinearMap.range ((diagonal (k + 2) (groundWeight k m)).comp
            (diagonal (k + 2) (groundWeight k n))) := by rw [hcomp]
      _ ≤ LinearMap.range (diagonal (k + 2) (groundWeight k m)) :=
        LinearMap.range_comp_le_range _ _

private theorem chain_projection (k n : ℕ) :
    (chain k).projection n = diagonal (k + 2) (groundWeight k n) := rfl

private theorem chain_martingaleDifference (k n : ℕ) :
    (chain k).martingaleDifference n = diagonal (k + 2) (differenceWeight k n) := by
  rw [NestedGroundProjections.martingaleDifference, chain_projection,
    chain_projection, diagonal_sub]
  refine diagonal_congr _ fun i ↦ ?_
  simp only [groundWeight, differenceWeight]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The excited vector \(\lvert10\cdots0\rangle\) of the module docstring. -/
private noncomputable def defect (k : ℕ) : EuclideanSpace ℂ (Fin (k + 2)) :=
  EuclideanSpace.single (0 : Fin (k + 2)) (1 : ℂ)

private theorem norm_sq_defect (k : ℕ) : ‖defect k‖ ^ 2 = 1 := by
  simp [defect]

private theorem inner_defect (k : ℕ) :
    (⟪diagonal (k + 2) (siteWeight k) (defect k), defect k⟫_ℂ).re = 1 / 2 := by
  rw [inner_diagonal_re]
  rw [Finset.sum_eq_single (0 : Fin (k + 2))]
  · simp [defect, siteWeight]
  · intro i _ hi
    simp [defect, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

end NachtergaeleLowerEndpoint

open NachtergaeleLowerEndpoint in
/-- Theorem 2.1(i) of Nachtergaele, arXiv:cond-mat/9410110, lines 1119--1130,
is false as printed: with each of C1, C2, and C3 imposed on the source range
it carries at lines 1030--1094, the printed conclusion fails in every
dimension \(k+2\).

The witness is described in the module docstring: the chain of \(N=k+1\)
one-site interactions whose leftmost term is halved, restricted to the span of
its vacuum and its single excitations. All three conditions hold with
\(l=0\), \(n_0=1\), \(\gamma_1=1\), \(d_1=1\), and \(\epsilon_0=0\), so the
printed bound would read
\(\langle\psi\mid H_{\Lambda_N}\psi\rangle\geq\lVert\psi\rVert^2\), while the
single-excitation vector at the weakened bond has energy
\(\frac12\lVert\psi\rVert^2\). Condition C1 is supplied on its own range
\(0\leq n<N\), where the local terms sum to \(H_{\Lambda_N}\) exactly, and at
the volume \(\Lambda_{n_0}\) as well; every ground space is the nonzero span
of the vacuum, so the nontriviality clause of C2 holds too. The index \(n=0\)
is excluded only from C2 and C3, and the printed proof estimates its
martingale difference all the same. -/
theorem not_unrestrictedNachtergaeleEstimate (k : ℕ) :
    ¬ UnrestrictedNachtergaeleEstimate (EuclideanSpace ℂ (Fin (k + 2))) := by
  intro hsource
  have hsqrt : Real.sqrt (((0 : ℕ) + 1 : ℕ) : ℝ) = 1 := by
    norm_num
  have hzero : (chain k).projection 0 = LinearMap.id := by
    rw [chain_projection, ← diagonal_one (k + 2)]
    refine diagonal_congr _ fun i ↦ ?_
    simp [groundWeight]
  have hgroundne : ∀ n ≤ k + 1, (chain k).projection n ≠ 0 := by
    intro n hn
    rw [chain_projection]
    refine diagonal_ne_zero _ _ (⟨k + 1, by omega⟩ : Fin (k + 2)) ?_
    simp [groundWeight, hn]
  have hQne : ∀ n ∈ Finset.Ico 1 (k + 1),
      diagonal (k + 2) (excitationWeight k n) ≠ 0 := by
    intro n hn
    have hn2 : n < k + 1 := (Finset.mem_Ico.mp hn).2
    have hne : (k + 1 : ℕ) ≠ n := by omega
    exact diagonal_ne_zero _ _ (⟨k + 1, by omega⟩ : Fin (k + 2))
      (by simp [excitationWeight, hne])
  have hv : defect k ∈ (LinearMap.range ((chain k).projection (k + 1)))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hu
    have hw : groundWeight k (k + 1) (0 : Fin (k + 2)) = 0 := by
      simp [groundWeight]
    simp [defect, chain_projection, EuclideanSpace.inner_single_right, hw]
  have hQ : ∀ n ∈ Finset.Ico 1 (k + 1),
      (diagonal (k + 2) (excitationWeight k n)).IsSymmetricProjection :=
    fun n _ ↦ diagonal_isSymmetricProjection _ _ (excitationWeight_mul_self k n)
  have hcomm : ∀ n ∈ Finset.Ico 1 (k + 1), ∀ m, m < n - 0 ∨ n < m →
      ((chain k).martingaleDifference m).comp
          (diagonal (k + 2) (excitationWeight k n)) =
        (diagonal (k + 2) (excitationWeight k n)).comp
          ((chain k).martingaleDifference m) := by
    intro n _ m _
    rw [chain_martingaleDifference, diagonal_comp, diagonal_comp]
    exact diagonal_congr _ fun i ↦ mul_comm _ _
  have hlocal : ∀ (x : EuclideanSpace ℂ (Fin (k + 2))),
      ∑ n ∈ Finset.Ico 0 (k + 1),
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re =
        (⟪diagonal (k + 2) (siteWeight k) x, x⟫_ℂ).re := by
    intro x
    have hswap :
        ∑ n ∈ Finset.Ico 0 (k + 1), ∑ i, localWeight k n i * ‖x i‖ ^ 2 =
          ∑ i, ∑ n ∈ Finset.Ico 0 (k + 1), localWeight k n i * ‖x i‖ ^ 2 :=
      Finset.sum_comm
    calc
      ∑ n ∈ Finset.Ico 0 (k + 1),
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re =
          ∑ n ∈ Finset.Ico 0 (k + 1), ∑ i, localWeight k n i * ‖x i‖ ^ 2 :=
        Finset.sum_congr rfl fun n _ ↦ inner_diagonal_re _ _ x
      _ = ∑ i, ∑ n ∈ Finset.Ico 0 (k + 1), localWeight k n i * ‖x i‖ ^ 2 := hswap
      _ = ∑ i : Fin (k + 2), siteWeight k i * ‖x i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_mul]
        congr 1
        rw [← Finset.range_eq_Ico]
        have hi : (i : ℕ) < k + 2 := i.isLt
        simp only [localWeight, Finset.sum_ite_eq, Finset.mem_range, siteWeight]
        split_ifs <;> first | rfl | (exfalso; omega)
      _ = (⟪diagonal (k + 2) (siteWeight k) x, x⟫_ℂ).re :=
        (inner_diagonal_re _ _ x).symm
  have hC1 : ∀ (x : EuclideanSpace ℂ (Fin (k + 2))),
      0 ≤ ∑ n ∈ Finset.Ico 0 (k + 1),
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.Ico 0 (k + 1),
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re) ≤
        1 * (⟪diagonal (k + 2) (siteWeight k) x, x⟫_ℂ).re := by
    intro x
    refine ⟨Finset.sum_nonneg fun n _ ↦ inner_localWeight_nonneg k n x, ?_⟩
    exact le_of_eq (by rw [hlocal x, one_mul])
  have hC1below : ∀ (x : EuclideanSpace ℂ (Fin (k + 2))),
      0 ≤ ∑ n ∈ Finset.Ico 0 1,
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re :=
    fun x ↦ Finset.sum_nonneg fun n _ ↦ inner_localWeight_nonneg k n x
  have hC2 : ∀ n ∈ Finset.Ico 1 (k + 1), ∀ x : EuclideanSpace ℂ (Fin (k + 2)),
      (1 : ℝ) * ‖((LinearMap.id :
            EuclideanSpace ℂ (Fin (k + 2)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (k + 2))) -
          diagonal (k + 2) (excitationWeight k n)) x‖ ^ 2 ≤
        (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re := by
    intro n hn x
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hn2 : n < k + 1 := (Finset.mem_Ico.mp hn).2
    have hid :
        (LinearMap.id : EuclideanSpace ℂ (Fin (k + 2)) →ₗ[ℂ]
              EuclideanSpace ℂ (Fin (k + 2))) -
            diagonal (k + 2) (excitationWeight k n) =
          diagonal (k + 2) (differenceWeight k n) := by
      rw [← diagonal_one (k + 2), diagonal_sub]
      refine diagonal_congr _ fun i ↦ ?_
      simp only [excitationWeight, differenceWeight]
      split_ifs <;> norm_num
    rw [hid, one_mul, norm_sq_diagonal, inner_diagonal_re]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simp only [differenceWeight, localWeight, siteWeight]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have hC3 : ∀ n ∈ Finset.Ico 1 (k + 1),
      ‖(diagonal (k + 2) (excitationWeight k n)).toContinuousLinearMap.comp
          ((chain k).martingaleDifference n).toContinuousLinearMap‖ ≤ 0 := by
    intro n _
    have hcompzero :
        (diagonal (k + 2) (excitationWeight k n)).comp
            ((chain k).martingaleDifference n) = 0 := by
      rw [chain_martingaleDifference, diagonal_comp, ← diagonal_zero (k + 2)]
      refine diagonal_congr _ fun i ↦ ?_
      simp only [excitationWeight, differenceWeight]
      split_ifs <;> norm_num
    have hCLM :
        (diagonal (k + 2) (excitationWeight k n)).toContinuousLinearMap.comp
            ((chain k).martingaleDifference n).toContinuousLinearMap = 0 := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have hx : (diagonal (k + 2) (excitationWeight k n))
          ((chain k).martingaleDifference n x) = 0 := by
        rw [← LinearMap.comp_apply, hcompzero, LinearMap.zero_apply]
      simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', zero_apply] using hx
    rw [hCLM, norm_zero]
  have hmain := hsource (chain k)
    (fun n ↦ diagonal (k + 2) (excitationWeight k n))
    (fun n ↦ diagonal (k + 2) (localWeight k n))
    (diagonal (k + 2) (siteWeight k)) (k + 1) 1 0 (defect k) 1 1 0
    (by omega) (by omega) hzero hgroundne hQne hv one_pos one_pos le_rfl
    (by rw [hsqrt]; norm_num) hQ hcomm hC1 hC1below hC2 hC3
  rw [hsqrt, norm_sq_defect, inner_defect] at hmain
  norm_num at hmain

end FrustrationFree
