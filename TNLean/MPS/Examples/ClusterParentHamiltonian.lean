/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinVecEta
import TNLean.MPS.Examples.Cluster
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Cluster-state stabilizer parent Hamiltonian

Cluster states "are unique ground states of the three-body interactions
\(\sum_i \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\)"
(Pérez-García--Verstraete--Wolf--Cirac 2007, arXiv:quant-ph/0608197, local TeX
lines 374--387). This file identifies the three-site local ground space of the
cluster tensor \(A^0 = \ketbra{+}{0}\), \(A^1 = \ketbra{-}{1}\) with the
\(+1\) eigenspace of the stabilizer \(K = \sigma^z_1\sigma^x_2\sigma^z_3\),
\[
  \mathcal G_3(A) = \{v : K v = v\},
\]
so that the three-site parent interaction is the orthogonal projector onto the
\(-1\) eigenspace of \(K\), namely \(\tfrac12(1 - K)\). On a periodic chain of
\(N \ge 3\) sites the common \(+1\) eigenspace of the translated stabilizers
\(K_i = \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\) is the periodic three-site
chain ground space, which the general theorem for normal tensors identifies with
the span of the cluster state.

The stabilizer is written in the same local basis as the tensor: with
\(\sigma^z\ket{s} = (-1)^s\ket{s}\) and \(\sigma^x\ket{s} = \ket{s+1}\),
\[
  (K v)(s_1,s_2,s_3) = (-1)^{s_1+s_3}\, v(s_1, s_2+1, s_3).
\]
Since \(\Gamma_3(X)(s_1,s_2,s_3)
= 2^{-3/2}(-1)^{s_1s_2+s_2s_3}\bigl(X_{s_3 0}+(-1)^{s_1}X_{s_3 1}\bigr)\), the
stabilizer is \(ZXZ\) for this convention as well as for the reflected
convention of arXiv:2011.12127; no local-basis change is needed.

The sign is convention-dependent. On the two matrices displayed in
arXiv:quant-ph/0608197, local TeX lines 378--387, the stabilizer has eigenvalue
\(-1\), so that source's Hamiltonian \(\sum_i \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\)
has its state as a ground state with the sign as printed; the two states differ
by \(\sigma^z\) on every site, which conjugates each stabilizer to its
negative. This file also records that \(-1\) eigenspace identity for the
source's matrices.

## Main results

* The three-site stabilizer \(K = \sigma^z_1\sigma^x_2\sigma^z_3\) and the
  identity \(\mathcal G_3(A) = \{v : Kv = v\}\).
* The translated stabilizers \(K_i\) on a periodic chain, whose common \(+1\)
  eigenspace is the periodic three-site chain ground space.
* That common eigenspace is spanned by the cluster state, which is therefore
  the unique ground state of \(\sum_i \tfrac12(1 - K_i)\).

## References

* Pérez-García--Verstraete--Wolf--Cirac 2007, arXiv:quant-ph/0608197, local
  TeX lines 374--387.
* Cirac--Pérez-García--Schuch--Verstraete 2021, arXiv:2011.12127,
  lines 2364--2371 (the tensor).
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ### The three-site stabilizer -/

/-- The three-site stabilizer \(K = \sigma^z_1\sigma^x_2\sigma^z_3\) of
arXiv:quant-ph/0608197, local TeX lines 374--387, acting on configuration
functions by \((K v)(s_1,s_2,s_3) = (-1)^{s_1+s_3}\, v(s_1, s_2+1, s_3)\). -/
def clusterStabilizer : NSiteSpace 2 3 →ₗ[ℂ] NSiteSpace 2 3 where
  toFun v s := (-1 : ℂ) ^ ((s 0).val + (s 2).val) * v ![s 0, s 1 + 1, s 2]
  map_add' v w := by
    ext s
    simp [mul_add]
  map_smul' c v := by
    ext s
    simp [mul_left_comm]

@[simp] lemma clusterStabilizer_apply (v : NSiteSpace 2 3) (s : Fin 3 → Fin 2) :
    clusterStabilizer v s =
      (-1 : ℂ) ^ ((s 0).val + (s 2).val) * v ![s 0, s 1 + 1, s 2] := rfl

private lemma cluster_groundSpaceMap_three_apply (X : Matrix (Fin 2) (Fin 2) ℂ)
    (a b c : Fin 2) :
    groundSpaceMap clusterTensor 3 X ![a, b, c] =
      Matrix.trace (clusterTensor a * (clusterTensor b * (clusterTensor c * X))) := by
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- Every vector of the three-site local ground space is fixed by the
stabilizer. -/
private lemma clusterStabilizer_groundSpaceMap (X : Matrix (Fin 2) (Fin 2) ℂ) :
    clusterStabilizer (groundSpaceMap clusterTensor 3 X) =
      groundSpaceMap clusterTensor 3 X := by
  ext s
  rw [Matrix.eq_vecCons_fin_three s, clusterStabilizer_apply]
  generalize s 0 = a
  generalize s 1 = b
  generalize s 2 = c
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [cluster_groundSpaceMap_three_apply, clusterTensor_zero, clusterTensor_one,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceAdd, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, smul_eq_mul, mul_zero, zero_mul, add_zero,
      zero_add, mul_one, one_mul, neg_mul, mul_neg, neg_neg, neg_zero, pow_zero, pow_one] <;>
    ring

private lemma cluster_scalar_ne_zero :
    (2 : ℂ) * (↑(1 / Real.sqrt 2) : ℂ) ^ 3 ≠ 0 :=
  mul_ne_zero two_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity)))

/-- **The three-site local ground space of the cluster tensor is the \(+1\)
eigenspace of the stabilizer** \(\sigma^z_1\sigma^x_2\sigma^z_3\),
arXiv:quant-ph/0608197, local TeX lines 374--387:
\[
  \mathcal G_3(A_{\mathrm{cl}}) = \{v : \sigma^z_1\sigma^x_2\sigma^z_3\, v = v\}.
\]
Given \(Kv = v\), the boundary matrix with rows
\((v_{00s} + v_{10s},\ v_{00s} - v_{10s})\), \(s \in \{0,1\}\), satisfies
\(\Gamma_3(X) = 2\cdot 2^{-3/2}\, v\). -/
theorem cluster_groundSpace_three_eq_eigenspace :
    groundSpace clusterTensor 3 = Module.End.eigenspace clusterStabilizer 1 := by
  ext v
  rw [Module.End.mem_eigenspace_iff, one_smul]
  constructor
  · rintro ⟨X, rfl⟩
    exact clusterStabilizer_groundSpaceMap X
  · intro hv
    have h := fun s => congrFun hv s
    have h010 : v ![0, 1, 0] = v ![0, 0, 0] := Eq.symm (by simpa using h ![0, 1, 0])
    have h011 : v ![0, 1, 1] = -v ![0, 0, 1] := Eq.symm (by simpa using h ![0, 1, 1])
    have h110 : v ![1, 1, 0] = -v ![1, 0, 0] := Eq.symm (by simpa using h ![1, 1, 0])
    have h111 : v ![1, 1, 1] = v ![1, 0, 1] := Eq.symm (by simpa using h ![1, 1, 1])
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      !![v ![0, 0, 0] + v ![1, 0, 0], v ![0, 0, 0] - v ![1, 0, 0];
        v ![0, 0, 1] + v ![1, 0, 1], v ![0, 0, 1] - v ![1, 0, 1]]
    have key : groundSpaceMap clusterTensor 3 X =
        ((2 : ℂ) * (↑(1 / Real.sqrt 2) : ℂ) ^ 3) • v := by
      ext s
      rw [Matrix.eq_vecCons_fin_three s]
      generalize s 0 = a
      generalize s 1 = b
      generalize s 2 = c
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        simp only [X, h010, h011, h110, h111, cluster_groundSpaceMap_three_apply,
          clusterTensor_zero, clusterTensor_one, Fin.isValue, Fin.zero_eta, Fin.mk_one,
          Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Pi.smul_apply, mul_zero,
          zero_mul, add_zero, zero_add, mul_one, neg_mul, mul_neg, neg_neg, neg_zero] <;>
        ring
    refine ⟨((2 : ℂ) * (↑(1 / Real.sqrt 2) : ℂ) ^ 3)⁻¹ • X, ?_⟩
    rw [map_smul, key, smul_smul, inv_mul_cancel₀ cluster_scalar_ne_zero, one_smul]

/-! ### The sign of the stabilizer on the source's matrices -/

/-- The two matrices displayed in arXiv:quant-ph/0608197, local TeX lines
378--387, \(A_1 = \begin{pmatrix}0&0\\1&1\end{pmatrix}\),
\(A_2 = \begin{pmatrix}1&-1\\0&0\end{pmatrix}\), with the source's physical
labels \(1, 2\) written as \(0, 1\). -/
def clusterSourceTensor : MPSTensor 2 2 := fun i =>
  match i with
  | 0 => !![0, 0; 1, 1]
  | 1 => !![1, -1; 0, 0]

lemma clusterSourceTensor_zero : clusterSourceTensor 0 = !![0, 0; 1, 1] := rfl

lemma clusterSourceTensor_one : clusterSourceTensor 1 = !![1, -1; 0, 0] := rfl

private lemma clusterSource_groundSpaceMap_three_apply (X : Matrix (Fin 2) (Fin 2) ℂ)
    (a b c : Fin 2) :
    groundSpaceMap clusterSourceTensor 3 X ![a, b, c] =
      Matrix.trace (clusterSourceTensor a * (clusterSourceTensor b *
        (clusterSourceTensor c * X))) := by
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- On the source's matrices the stabilizer acts as \(-1\). -/
private lemma clusterStabilizer_source_groundSpaceMap (X : Matrix (Fin 2) (Fin 2) ℂ) :
    clusterStabilizer (groundSpaceMap clusterSourceTensor 3 X) =
      (-1 : ℂ) • groundSpaceMap clusterSourceTensor 3 X := by
  ext s
  rw [Matrix.eq_vecCons_fin_three s, clusterStabilizer_apply, Pi.smul_apply, smul_eq_mul]
  generalize s 0 = a
  generalize s 1 = b
  generalize s 2 = c
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [clusterSource_groundSpaceMap_three_apply, clusterSourceTensor_zero,
      clusterSourceTensor_one, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceAdd,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add, one_mul,
      neg_mul, mul_neg, neg_neg, neg_zero, pow_zero, pow_one] <;>
    ring

/-- **The stabilizer has eigenvalue \(-1\) on the source's cluster state.** For
the matrices displayed in arXiv:quant-ph/0608197, local TeX lines 378--387,
\[
  \Gamma_3(X)(t_1,t_2,t_3)
    = (-1)^{t_1(1-t_2)+t_2(1-t_3)}\bigl(X_{0,1-t_1} + (-1)^{t_3}X_{1,1-t_1}\bigr),
\]
so the three-site local ground space is the \(-1\) eigenspace of
\(\sigma^z_1\sigma^x_2\sigma^z_3\), and the state is a ground state of the
source's Hamiltonian \(\sum_i \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\) with the
sign as printed there. The present cluster tensor produces the \(+1\)
eigenspace instead; the two states differ by \(\sigma^z\) on every site, which
conjugates each stabilizer to its negative. -/
theorem clusterSource_groundSpace_three_eq_eigenspace_neg_one :
    groundSpace clusterSourceTensor 3 = Module.End.eigenspace clusterStabilizer (-1) := by
  ext v
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨X, rfl⟩
    exact clusterStabilizer_source_groundSpaceMap X
  · intro hv
    have h := fun s => congrFun hv s
    have h010' : v ![0, 0, 0] = -v ![0, 1, 0] := by simpa using h ![0, 1, 0]
    have h010 : v ![0, 1, 0] = -v ![0, 0, 0] := (neg_eq_iff_eq_neg.mpr h010').symm
    have h011 : v ![0, 1, 1] = v ![0, 0, 1] := Eq.symm (by simpa using h ![0, 1, 1])
    have h110 : v ![1, 1, 0] = v ![1, 0, 0] := Eq.symm (by simpa using h ![1, 1, 0])
    have h111' : v ![1, 0, 1] = -v ![1, 1, 1] := by simpa using h ![1, 1, 1]
    have h111 : v ![1, 1, 1] = -v ![1, 0, 1] := (neg_eq_iff_eq_neg.mpr h111').symm
    let X : Matrix (Fin 2) (Fin 2) ℂ :=
      !![-(v ![1, 0, 0] + v ![1, 0, 1]), v ![0, 0, 0] + v ![0, 0, 1];
        -(v ![1, 0, 0] - v ![1, 0, 1]), v ![0, 0, 0] - v ![0, 0, 1]]
    have key : groundSpaceMap clusterSourceTensor 3 X = (2 : ℂ) • v := by
      ext s
      rw [Matrix.eq_vecCons_fin_three s]
      generalize s 0 = a
      generalize s 1 = b
      generalize s 2 = c
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        simp only [X, h010, h011, h110, h111, clusterSource_groundSpaceMap_three_apply,
          clusterSourceTensor_zero, clusterSourceTensor_one, Fin.isValue, Fin.zero_eta,
          Fin.mk_one, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, mul_zero,
          zero_mul, add_zero, zero_add, one_mul, neg_mul, mul_neg, neg_neg, neg_zero] <;>
        ring
    refine ⟨(2 : ℂ)⁻¹ • X, ?_⟩
    rw [map_smul, key, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-! ### The translated stabilizers on a periodic chain -/

/-- The translated stabilizer \(K_i\) on a periodic chain of \(N\) sites, with
site indices taken modulo \(N\), acting by
\((K_i\psi)(\sigma) = (-1)^{\sigma_i + \sigma_{i+2}}\,
\psi(\sigma\text{ with }\sigma_{i+1}\text{ replaced by }\sigma_{i+1}+1)\).
For \(N \ge 3\) the sites \(i, i+1, i+2\) are distinct and this is the Pauli
string \(\sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\); every result below assumes
\(N \ge 3\). On one site the coordinate formula is \(\sigma^x\), not
\(\sigma^z\sigma^x\sigma^z = -\sigma^x\). -/
def clusterChainStabilizer {N : ℕ} (i : Fin N) : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N where
  toFun ψ σ :=
    (-1 : ℂ) ^ ((σ i).val + (σ (cyclicForwardSite i 2)).val) *
      ψ (Function.update σ (cyclicForwardSite i 1) (σ (cyclicForwardSite i 1) + 1))
  map_add' ψ φ := by
    ext σ
    simp [mul_add]
  map_smul' c ψ := by
    ext σ
    simp [mul_left_comm]

@[simp] lemma clusterChainStabilizer_apply {N : ℕ} (i : Fin N) (ψ : NSiteSpace 2 N)
    (σ : Fin N → Fin 2) :
    clusterChainStabilizer i ψ σ =
      (-1 : ℂ) ^ ((σ i).val + (σ (cyclicForwardSite i 2)).val) *
        ψ (Function.update σ (cyclicForwardSite i 1) (σ (cyclicForwardSite i 1) + 1)) := rfl

private lemma update_one_eq (s : Fin 3 → Fin 2) :
    Function.update s 1 (s 1 + 1) = ![s 0, s 1 + 1, s 2] := by
  ext k
  fin_cases k <;> simp

/-- The three-site stabilizer on a cyclic window is the restriction of the
translated stabilizer. -/
private lemma clusterStabilizer_cyclicRestrictₗ {N : ℕ} (hN : 0 < N) (hN3 : 3 ≤ N)
    (i : Fin N) (τ : Fin N → Fin 2) (ψ : NSiteSpace 2 N) :
    clusterStabilizer (cyclicRestrictₗ hN 3 i τ ψ) =
      cyclicRestrictₗ hN 3 i τ (clusterChainStabilizer i ψ) := by
  ext s
  rw [clusterStabilizer_apply, cyclicRestrictₗ_apply, cyclicRestrictₗ_apply,
    clusterChainStabilizer_apply]
  have h0 : cyclicCfg hN 3 i s τ i = s 0 := by
    have := cyclicCfg_cyclicForwardSite_apply hN hN3 i s τ 0
    rwa [Fin.val_zero, cyclicForwardSite_zero] at this
  have h1 : cyclicCfg hN 3 i s τ (cyclicForwardSite i 1) = s 1 :=
    cyclicCfg_cyclicForwardSite_apply hN hN3 i s τ 1
  have h2 : cyclicCfg hN 3 i s τ (cyclicForwardSite i 2) = s 2 :=
    cyclicCfg_cyclicForwardSite_apply hN hN3 i s τ 2
  rw [h0, h1, h2]
  congr 2
  rw [← update_one_eq]
  exact (update_cyclicCfg hN hN3 i s τ 1 (s 1 + 1)).symm

/-- A periodic vector is fixed by \(K_i\) exactly when all its cyclic windows at
\(i\) are fixed by the three-site stabilizer. -/
private lemma mem_eigenspace_clusterChainStabilizer_iff {N : ℕ} (hN : 0 < N) (hN3 : 3 ≤ N)
    (i : Fin N) (ψ : NSiteSpace 2 N) :
    ψ ∈ Module.End.eigenspace (clusterChainStabilizer i) 1 ↔
      ∀ τ : Fin N → Fin 2,
        cyclicRestrictₗ hN 3 i τ ψ ∈ Module.End.eigenspace clusterStabilizer 1 := by
  simp only [Module.End.mem_eigenspace_iff, one_smul]
  constructor
  · intro hψ τ
    rw [clusterStabilizer_cyclicRestrictₗ hN hN3, hψ]
  · intro hτ
    ext σ
    have hσ := congrFun (hτ σ) (extractWindow 3 i σ)
    rw [clusterStabilizer_cyclicRestrictₗ hN hN3, cyclicRestrictₗ_apply, cyclicRestrictₗ_apply,
      cyclicCfg_extractWindow hN hN3] at hσ
    exact hσ

/-- **The common \(+1\) eigenspace of the translated stabilizers is the periodic
three-site chain ground space** of the cluster tensor, for \(N\ge3\). -/
theorem cluster_iInf_eigenspace_eq_chainGroundSpace {N : ℕ} (hN : 3 ≤ N) :
    (⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) 1) =
      chainGroundSpace clusterTensor 3 N := by
  have hNpos : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hNpos, hN⟩]
  ext ψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap,
    cluster_groundSpace_three_eq_eigenspace]
  exact forall_congr' fun i => mem_eigenspace_clusterChainStabilizer_iff hNpos hN i ψ

/-- **The cluster state spans the common \(+1\) eigenspace of the stabilizers**
\(K_i = \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\): on a periodic chain of
\(N\ge3\) sites,
\[
  \bigcap_i \{\psi : K_i\psi = \psi\} = \mathbb C\,V^{(N)}(A_{\mathrm{cl}}).
\]
This is the statement that cluster states are unique ground states of the
three-body interactions \(\sum_i \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2}\)
(arXiv:quant-ph/0608197, local TeX lines 374--387), transported to the present
tensor, on which each stabilizer has eigenvalue \(+1\) rather than \(-1\); see
the module docstring for the sign. The cluster tensor is injective after
blocking two sites, so the general theorem for normal tensors identifies the
periodic three-site chain ground space with the span of the cluster state. -/
theorem cluster_iInf_eigenspace_eq_mpvSubmodule {N : ℕ} (hN : 3 ≤ N) :
    (⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) 1) =
      mpvSubmodule clusterTensor N := by
  rw [cluster_iInf_eigenspace_eq_chainGroundSpace hN]
  exact chainGroundSpace_eq_mpvSubmodule_normal cluster_isNormal cluster_isNBlkInjective_two
    (by norm_num) (by omega) (by norm_num) hN (by omega)

/-- The common \(+1\) eigenspace of the translated cluster stabilizers on
\(N\ge3\) periodic sites is one-dimensional. Since each stabilizer is a
self-adjoint involution, this says that the cluster state is the unique ground
state of \(\sum_i \tfrac12(1 - \sigma^z_i\sigma^x_{i+1}\sigma^z_{i+2})\), the
form the interaction of arXiv:quant-ph/0608197, local TeX lines 374--387,
takes on the present tensor. -/
theorem cluster_stabilizer_unique_gs {N : ℕ} (hN : 3 ≤ N) :
    HasUniqueGroundState
      (⨅ i : Fin N, Module.End.eigenspace (clusterChainStabilizer i) 1) := by
  rw [cluster_iInf_eigenspace_eq_chainGroundSpace hN]
  exact parentHamiltonian_unique_gs cluster_isNBlkInjective_two (by norm_num) (by norm_num) hN

end MPSTensor
