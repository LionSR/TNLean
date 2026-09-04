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
carries -- C1 on \(l\leq n<M\) after the reindexing of its window sum, with
one constant at every volume \(\Lambda_M\), and C2 and C3 on \(n_0\leq n<N\)
-- together with the source's ordering \(l\leq n_0\) of the onset, the
identification of every ground space with the kernel of its Hamiltonian and
its nontriviality that C2 requires, the conventions
\(G_{\Lambda_0}=\mathbf 1\) and \(G_{\Lambda_{N+1}}=0\), and the conclusion on
\(\lVert\psi\rVert^2\); then
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
\(H_{\Lambda_{n+1}\setminus\Lambda_{n-l}}\) puts it on \(l\leq n<M\). The
source supplies a single constant \(d_{l+1}\) serving every volume, so the
condition is imposed here at every \(M\), against the corresponding member
\(H_{\Lambda_M}\) of the family of Hamiltonians. Conditions C2 and C3 at lines
1043--1058 and 1083--1094 are imposed from the onset index
\(n_0=\max\{l,n_l,n_{l+1}-1\}\) onwards, hence on \(n_0\leq n<N\), and that
onset is at least \(l\). Condition C2 at lines 1044--1049 also identifies each
ground space with the kernel of its Hamiltonian and asks that it be
nontrivial; both clauses are imposed, for the volumes \(\Lambda_M\) with
\(M\leq N\) and for the windows \(\Lambda_{n+1}\setminus\Lambda_{n-l}\) on the
C2--C3 range. The conventions \(G_{\Lambda_0}=\mathbf 1\) and
\(G_{\Lambda_{N+1}}=0\) at lines 1060--1061 are imposed as well.

All of this is read at the volume \(\Lambda_N\) that the conclusion is about.
The source ranges of C2 and C3 extend upwards without bound, but at an index
\(n\geq N\) the window \(\Lambda_{n+1}\setminus\Lambda_{n-l}\) reaches outside
\(\Lambda_N\), so neither its Hamiltonian nor its ground projection acts on
that space; correspondingly the printed proof sums its per-index estimate over
\(0\leq n<N\), reading C2 at window index at most \(N\) and C3 at index at
most \(N-1\). Condition C1 is different, because its right-hand side names the
Hamiltonian of the volume, which is why it is imposed at every \(M\).

This is the hypothesis list of
`NestedGroundProjections.energy_lower_bound_of_nachtergaele_c1_c3_threshold`,
with C1 restated on its own source range at every volume and the remaining
clauses of C2 and the two conventions adjoined, together with the printed
conclusion in place of the estimate on the martingale mass above the
threshold. It is refuted by `not_unrestrictedNachtergaeleEstimate`. -/
def UnrestrictedNachtergaeleEstimate (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : Prop :=
  ∀ (G : NestedGroundProjections (E := E))
    (Q localHamiltonian H : ℕ → E →ₗ[ℂ] E) (N n₀ l : ℕ) (v : E) (γ d ε : ℝ),
    l ≤ n₀ → n₀ ≤ N →
    G.projection 0 = LinearMap.id →
    G.projection (N + 1) = 0 →
    (∀ M ≤ N, LinearMap.ker (H M) = LinearMap.range (G.projection M)) →
    (∀ n ≤ N, G.projection n ≠ 0) →
    (∀ n ∈ Finset.Ico n₀ N,
      LinearMap.ker (localHamiltonian n) = LinearMap.range (Q n)) →
    (∀ n ∈ Finset.Ico n₀ N, Q n ≠ 0) →
    v ∈ (LinearMap.range (G.projection N))ᗮ →
    0 < γ → 0 < d → 0 ≤ ε → ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) →
    (∀ n ∈ Finset.Ico n₀ N, (Q n).IsSymmetricProjection) →
    (∀ n ∈ Finset.Ico n₀ N, ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp (Q n) =
        (Q n).comp (G.martingaleDifference m)) →
    (∀ M, ∀ x,
      0 ≤ ∑ n ∈ Finset.Ico l M, (⟪localHamiltonian n x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.Ico l M, (⟪localHamiltonian n x, x⟫_ℂ).re) ≤
        d * (⟪H M x, x⟫_ℂ).re) →
    (∀ n ∈ Finset.Ico n₀ N, ∀ x,
      γ * ‖((LinearMap.id : E →ₗ[ℂ] E) - Q n) x‖ ^ 2 ≤
        (⟪localHamiltonian n x, x⟫_ℂ).re) →
    (∀ n ∈ Finset.Ico n₀ N,
      ‖(Q n).toContinuousLinearMap.comp
          (G.martingaleDifference n).toContinuousLinearMap‖ ≤ ε) →
    (γ / d) * (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ^ 2 ≤
      (⟪H N v, v⟫_ℂ).re

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

/-- The kernel of a diagonal operator is the range of the diagonal projection
onto the coordinates that the operator annihilates. -/
private theorem ker_diagonal_eq_range_diagonal (k : ℕ) (f g : Fin k → ℝ)
    (hg : ∀ i, g i = 0 ∨ g i = 1) (hfg : ∀ i, f i = 0 ↔ g i = 1) :
    LinearMap.ker (diagonal k f) = LinearMap.range (diagonal k g) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    refine ⟨x, ?_⟩
    ext i
    have hxi : (f i : ℂ) * x i = 0 := by
      rw [← diagonal_apply k f x i, hx]
      simp
    rcases hg i with h | h
    · have hne : (f i : ℂ) ≠ 0 := by
        have : f i ≠ 0 := fun hf ↦ by rw [(hfg i).mp hf] at h; norm_num at h
        exact_mod_cast this
      have hxz : x i = 0 := (mul_eq_zero.mp hxi).resolve_left hne
      simp [h, hxz]
    · simp [h]
  · rintro ⟨y, rfl⟩
    have hcomp : (diagonal k f).comp (diagonal k g) = 0 := by
      rw [diagonal_comp, ← diagonal_zero k]
      refine diagonal_congr _ fun i ↦ ?_
      rcases hg i with h | h
      · simp [h]
      · simp [(hfg i).mpr h]
    have hy := congrArg (fun T : EuclideanSpace ℂ (Fin k) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin k) ↦ T y) hcomp
    simpa using hy

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

/-- The weight of the Hamiltonian \(H_{\Lambda_M}\): the excitations inside
the volume carry their one-site energy and every other coordinate carries
none. -/
private noncomputable def hamiltonianWeight (k M : ℕ) : Fin (k + 2) → ℝ :=
  fun i ↦ if (i : ℕ) < M then siteWeight k i else 0

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

private theorem siteWeight_ne_zero (k : ℕ) (i : Fin (k + 2))
    (hi : (i : ℕ) ≠ k + 1) : siteWeight k i ≠ 0 := by
  simp only [siteWeight]
  split_ifs with h₁
  · norm_num
  · norm_num

private theorem localWeight_nonneg (k n : ℕ) (i : Fin (k + 2)) :
    0 ≤ localWeight k n i := by
  simp only [localWeight]
  split_ifs with h
  · exact siteWeight_nonneg k i
  · exact le_rfl

private theorem sum_localWeight (k M : ℕ) (i : Fin (k + 2)) :
    ∑ n ∈ Finset.Ico 0 M, localWeight k n i = hamiltonianWeight k M i := by
  rw [← Finset.range_eq_Ico]
  simp only [localWeight, hamiltonianWeight, Finset.sum_ite_eq,
    Finset.mem_range]

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
    (⟪diagonal (k + 2) (hamiltonianWeight k (k + 1)) (defect k),
      defect k⟫_ℂ).re = 1 / 2 := by
  rw [inner_diagonal_re]
  rw [Finset.sum_eq_single (0 : Fin (k + 2))]
  · simp [defect, hamiltonianWeight, siteWeight]
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
\(0\leq n<M\) at every volume \(\Lambda_M\) with the one constant \(d_1=1\),
because the local terms below \(M\) sum to \(H_{\Lambda_M}\) exactly. Every
ground space is the kernel of its own Hamiltonian, spanned by the vacuum
together with the excitations outside its volume, so it contains the vacuum
and is nonzero and both clauses of C2 hold; the conventions
\(G_{\Lambda_0}=\mathbf 1\) and \(G_{\Lambda_{N+1}}=0\) hold as well, the
first because the empty volume constrains no coordinate and the second
because every coordinate lies below \(N+1\). At the chain length the ground
space is the line the vacuum spans, and the witness vector is orthogonal to
it. The index \(n=0\) is
excluded only from C2 and C3, and the printed proof estimates its martingale
difference all the same. The refutation is asserted separately in each
dimension; from \(k=1\) onwards the C2--C3 range \(n_0\leq n<N\) is nonempty,
so both conditions carry content at the witness. -/
theorem not_unrestrictedNachtergaeleEstimate (k : ℕ) :
    ¬ UnrestrictedNachtergaeleEstimate (EuclideanSpace ℂ (Fin (k + 2))) := by
  intro hsource
  have hsqrt : Real.sqrt (((0 : ℕ) + 1 : ℕ) : ℝ) = 1 := by
    norm_num
  have hzero : (chain k).projection 0 = LinearMap.id := by
    rw [chain_projection, ← diagonal_one (k + 2)]
    refine diagonal_congr _ fun i ↦ ?_
    simp [groundWeight]
  have hfinal : (chain k).projection (k + 1 + 1) = 0 := by
    rw [chain_projection, ← diagonal_zero (k + 2)]
    refine diagonal_congr _ fun i ↦ ?_
    have hi : (i : ℕ) < k + 2 := i.isLt
    simp only [groundWeight]
    split_ifs with h
    · exact absurd h (Nat.not_le.mpr (by omega))
    · rfl
  have hkerH : ∀ M ≤ k + 1,
      LinearMap.ker (diagonal (k + 2) (hamiltonianWeight k M)) =
        LinearMap.range ((chain k).projection M) := by
    intro M hM
    rw [chain_projection]
    refine ker_diagonal_eq_range_diagonal _ _ _ (fun i ↦ ?_) fun i ↦ ?_
    · simp only [groundWeight]
      split_ifs <;> simp
    · have hi : (i : ℕ) < k + 2 := i.isLt
      simp only [hamiltonianWeight, groundWeight]
      split_ifs with h1 h2 h3
      · exact absurd h2 (Nat.not_le.mpr h1)
      · constructor
        · intro h
          exact absurd h (siteWeight_ne_zero k i (by omega))
        · intro h
          norm_num at h
      · simp
      · exact absurd (Nat.not_lt.mp h1) h3
  have hkerQ : ∀ n ∈ Finset.Ico 1 (k + 1),
      LinearMap.ker (diagonal (k + 2) (localWeight k n)) =
        LinearMap.range (diagonal (k + 2) (excitationWeight k n)) := by
    intro n hn
    have hn2 : n < k + 1 := (Finset.mem_Ico.mp hn).2
    refine ker_diagonal_eq_range_diagonal _ _ _ (fun i ↦ ?_) fun i ↦ ?_
    · simp only [excitationWeight]
      split_ifs <;> simp
    · simp only [localWeight, excitationWeight]
      split_ifs with hin
      · constructor
        · intro h
          exact absurd h (siteWeight_ne_zero k i (by omega))
        · intro h
          norm_num at h
      · simp
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
  have hlocal : ∀ (M : ℕ) (x : EuclideanSpace ℂ (Fin (k + 2))),
      ∑ n ∈ Finset.Ico 0 M,
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re =
        (⟪diagonal (k + 2) (hamiltonianWeight k M) x, x⟫_ℂ).re := by
    intro M x
    have hswap :
        ∑ n ∈ Finset.Ico 0 M, ∑ i, localWeight k n i * ‖x i‖ ^ 2 =
          ∑ i, ∑ n ∈ Finset.Ico 0 M, localWeight k n i * ‖x i‖ ^ 2 :=
      Finset.sum_comm
    calc
      ∑ n ∈ Finset.Ico 0 M,
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re =
          ∑ n ∈ Finset.Ico 0 M, ∑ i, localWeight k n i * ‖x i‖ ^ 2 :=
        Finset.sum_congr rfl fun n _ ↦ inner_diagonal_re _ _ x
      _ = ∑ i, ∑ n ∈ Finset.Ico 0 M, localWeight k n i * ‖x i‖ ^ 2 := hswap
      _ = ∑ i : Fin (k + 2), hamiltonianWeight k M i * ‖x i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_mul, sum_localWeight]
      _ = (⟪diagonal (k + 2) (hamiltonianWeight k M) x, x⟫_ℂ).re :=
        (inner_diagonal_re _ _ x).symm
  have hC1 : ∀ (M : ℕ) (x : EuclideanSpace ℂ (Fin (k + 2))),
      0 ≤ ∑ n ∈ Finset.Ico 0 M,
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.Ico 0 M,
          (⟪diagonal (k + 2) (localWeight k n) x, x⟫_ℂ).re) ≤
        1 * (⟪diagonal (k + 2) (hamiltonianWeight k M) x, x⟫_ℂ).re := by
    intro M x
    refine ⟨Finset.sum_nonneg fun n _ ↦ inner_localWeight_nonneg k n x, ?_⟩
    exact le_of_eq (by rw [hlocal M x, one_mul])
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
    (fun M ↦ diagonal (k + 2) (hamiltonianWeight k M)) (k + 1) 1 0 (defect k)
    1 1 0
    (by omega) (by omega) hzero hfinal hkerH hgroundne hkerQ hQne hv one_pos
    one_pos le_rfl (by rw [hsqrt]; norm_num) hQ hcomm hC1 hC2 hC3
  rw [hsqrt, norm_sq_defect, inner_defect] at hmain
  norm_num at hmain

end FrustrationFree
