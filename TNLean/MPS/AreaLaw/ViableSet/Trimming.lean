/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SequentialTruncation
import TNLean.MPS.AreaLaw.SupportedCutRank
import QICLean.Channel.SchmidtTrimming
import QICLean.Entropy.RightLocalLift

/-!
# Trimming a chain vector across one cut

Let `ψ` be a vector on a chain of `L` sites of local dimension `q`, and fix the cut after
`i` sites. Trimming `ψ` to `m` Schmidt terms across this cut keeps the Schmidt terms with the
`m` largest coefficients. In operator form the trimmed vector is `(P ⊗ 1) ψ`, where `P` is an
orthogonal projection of rank at most `m` on the first `i` sites capturing the `m` largest
eigenvalues of the regional state of `ψ` on those sites. Here `P` is any trimming projection of
the cut vector of `ψ`, so every choice of kept eigenvectors of a repeated eigenvalue is
admitted.

The trimmed vector has rank at most `m` across the cut after `i` sites. Lemma `l:trim2` of
Landau, Vazirani and Vidick states that it has rank at most that of `ψ` across every other cut
after `j` sites. For `j ≥ i` the trimming is `P ⊗ 1` with `P` acting on sites to the left of
the cut after `j` sites. For `j ≤ i` it is also `1 ⊗ Q` with `Q` an orthogonal projection on
the last `L - i` sites, to the right of the cut after `j` sites. In both cases the operator acts
on one side of the cut after `j` sites, so it does not increase the rank there.

No assumption on `L` or `q` is needed. When `q = 0` and `L > 0` there are no configurations,
every vector vanishes, and the statements hold trivially.

## Main definitions

* `TNLean.MPS.AreaLaw.chainTrim`: the vector `(P ⊗ 1) ψ` for a matrix `P` on the
  configurations of the first `i` sites.

## Main results

* `TNLean.MPS.AreaLaw.cutVector_chainTrim`: in the coordinates of the cut after `i` sites,
  the trimmed vector is the bipartite trimmed vector.
* `TNLean.MPS.AreaLaw.rank_cutMatrix_chainTrim_self_le`: the trimmed vector has rank at most
  `m` across the cut after `i` sites.
* `TNLean.MPS.AreaLaw.rank_cutMatrix_chainTrim_le`: Lemma `l:trim2`, trimming across one cut
  does not increase the rank across any cut.
* `TNLean.MPS.AreaLaw.norm_chainTrim_le`: the trimmed vector is no longer than `ψ`.
* `TNLean.MPS.AreaLaw.norm_inner_sub_chainTrim_le`: the corrected trimming error against a
  vector of bounded rank across the same cut.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `References/1307.5143/algo53.tex`: Schmidt
  decomposition across a cut, lines 322–323; trimming, lines 330–333; Lemma `l:trim1`,
  lines 531–542; Lemma `l:trim2` and its proof, lines 544–553.
-/

open Matrix
open scoped Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The vector `(P ⊗ 1) ψ` for a matrix `P` on the configurations of the first `i` sites.
When `P` is a trimming projection of the cut vector of `ψ` at `m`, this is the trimmed vector
`trim^i_m ψ` of Landau, Vazirani and Vidick (arXiv:1307.5143v1, algo53.tex,
lines 330–333). -/
noncomputable def chainTrim (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (i : ℕ)
    (P : LeftBlockMatrix L q i) : EuclideanSpace ℂ (Fin L → Fin q) :=
  toEuclideanLin (Entropy.localLift (leftBlock L i) P) ψ

/-- The coefficient matrix of `(P ⊗ 1) ψ` across the cut after `i` sites is `P C`, where `C`
is that of `ψ`. -/
theorem cutMatrix_chainTrim (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (i : ℕ)
    (P : LeftBlockMatrix L q i) : cutMatrix (chainTrim ψ i P) i = P * cutMatrix ψ i :=
  cutMatrix_localLift i P ψ

/-- In the coordinates of the cut after `i` sites, `(P ⊗ 1) ψ` is the bipartite vector
`(P ⊗ 1) v` for the cut vector `v` of `ψ` (arXiv:1307.5143v1, algo53.tex,
lines 330–333). -/
theorem cutVector_chainTrim (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (i : ℕ)
    (P : LeftBlockMatrix L q i) :
    Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) (chainTrim ψ i P) =
      leftApply P (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ) := by
  ext ⟨a, b⟩
  exact congrFun (congrFun (cutMatrix_chainTrim ψ i P) a) b

/-- **The trimmed vector has rank at most `m` across its cut** (arXiv:1307.5143v1,
algo53.tex, lines 330–333). If `P` is a trimming projection of the cut vector of `ψ` at `m`,
then `trim^i_m ψ` has rank at most `m` across the cut after `i` sites. -/
theorem rank_cutMatrix_chainTrim_self_le {ψ : EuclideanSpace ℂ (Fin L → Fin q)} {i m : ℕ}
    {P : LeftBlockMatrix L q i}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ)
      m P) :
    (cutMatrix (chainTrim ψ i P) i).rank ≤ m :=
  (rank_cutMatrix_localLift_le i P ψ).trans hP.rank_le

/-- **Lemma `l:trim2`** (arXiv:1307.5143v1, algo53.tex, lines 544–553). Trimming a chain
vector across the cut after `i` sites does not increase its rank across the cut after `j`
sites, for every `j`. For `j ≥ i` the trimming `P ⊗ 1` acts to the left of the cut after `j`
sites. For `j ≤ i` it equals `1 ⊗ Q` for an orthogonal projection `Q` on the sites after `i`,
which act to the right of the cut after `j` sites. -/
theorem rank_cutMatrix_chainTrim_le {ψ : EuclideanSpace ℂ (Fin L → Fin q)} {i m : ℕ}
    {P : LeftBlockMatrix L q i}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ)
      m P) (j : ℕ) :
    (cutMatrix (chainTrim ψ i P) j).rank ≤ (cutMatrix ψ j).rank := by
  rcases isEmpty_or_nonempty (Fin L → Fin q) with hσ | ⟨⟨σ⟩⟩
  · have h : cutMatrix (chainTrim ψ i P) j = cutMatrix ψ j := by
      ext a b
      exact isEmptyElim ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L j)).symm (a, b))
    rw [h]
  rcases le_total i j with hij | hji
  · exact rank_cutMatrix_toEuclideanLin_le_of_isOneSided ψ j
      ((Entropy.isSupportedOn_localLift P).isOneSided_of_subset (leftBlock_mono hij)
        fun v ↦ σ v.1)
  · obtain ⟨Q, -, -, -, hPQ⟩ := hP.exists_mul_eq_mul_transpose
    set Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      reindex (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L i)).symm
        (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L i)).symm
        ((1 : LeftBlockMatrix L q i) ⊗ₖ Q) with hY
    have hcut : Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) Y =
        (1 : LeftBlockMatrix L q i) ⊗ₖ Q := by
      ext a b
      simp [hY]
    have htrim : chainTrim ψ i P = toEuclideanLin Y ψ := by
      apply cutMatrix_injective i
      change cutMatrix (chainTrim ψ i P) i = cutMatrix (toEuclideanLin Y ψ) i
      rw [cutMatrix_chainTrim, cutMatrix_toEuclideanLin, hcut,
        schmidtCoeffMatrix_one_kronecker_mulVec]
      exact hPQ
    have hsupp : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) Y (leftBlock L i)ᶜ :=
      Entropy.isSupportedOn_rightCut (n := fun _ : Fin L ↦ q) (leftBlock L i) Q
    rw [htrim]
    exact rank_cutMatrix_toEuclideanLin_le_of_isOneSided ψ j
      (hsupp.isOneSided_of_disjoint (disjoint_compl_left_iff.mpr (leftBlock_mono hji))
        fun v ↦ σ v.1)

/-- The trimmed chain vector is no longer than `ψ` (arXiv:1307.5143v1, algo53.tex,
lines 330–333). -/
theorem norm_chainTrim_le {ψ : EuclideanSpace ℂ (Fin L → Fin q)} {i m : ℕ}
    {P : LeftBlockMatrix L q i}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ)
      m P) :
    ‖chainTrim ψ i P‖ ≤ ‖ψ‖ := by
  rw [← Entropy.norm_cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) (chainTrim ψ i P),
    ← Entropy.norm_cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ, cutVector_chainTrim]
  exact hP.norm_leftApply_le

/-- **Trimming error on the chain** (corrected form of arXiv:1307.5143v1, algo53.tex,
Lemma `l:trim1`, lines 531–542). If `P` is a trimming projection of the cut vector of `ψ` at
`m` and `w` has rank at most `D` across the cut after `i` sites, then
`|⟨ψ - trim^i_m ψ, w⟩| ≤ ‖ψ‖ ‖w‖ √(D / (m + 1))`.

**Local fix (trimming radius):** the source asserts error `ε` for trimming radius `D / ε`,
which is false; the bound here gives error `ε` at radius `D / ε²`. Documented in the QICLean
note <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>. -/
theorem norm_inner_sub_chainTrim_le {ψ : EuclideanSpace ℂ (Fin L → Fin q)} {i m : ℕ}
    {P : LeftBlockMatrix L q i}
    (hP : IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) ψ)
      m P) {D : ℕ} (w : EuclideanSpace ℂ (Fin L → Fin q)) (hw : (cutMatrix w i).rank ≤ D) :
    ‖inner ℂ (ψ - chainTrim ψ i P) w‖ ≤ ‖ψ‖ * ‖w‖ * √((D : ℝ) / (m + 1)) := by
  have h := hP.norm_inner_sub_leftApply_le
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L i) w) hw
  rwa [inner_sub_left, ← cutVector_chainTrim, inner_cutVector, inner_cutVector,
    ← inner_sub_left, Entropy.norm_cutVector, Entropy.norm_cutVector] at h

end TNLean.MPS.AreaLaw
