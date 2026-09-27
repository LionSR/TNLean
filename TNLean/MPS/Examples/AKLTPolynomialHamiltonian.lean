/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLTParentHamiltonian
import TNLean.MPS.Examples.SpinOne
import TNLean.MPS.ParentHamiltonian.CoefficientPairing
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

/-!
# AKLT: the polynomial Hamiltonian and the spin-2 projector

**Source.** Pérez-García, Verstraete, Wolf, Cirac 2007 (arXiv:quant-ph/0608197),
Section "Examples", `Papers/quant-ph_0608197/MPSarchive.tex` lines 340–349: "the
father of all matrix product states is the ground state of the AKLT-Hamiltonian
\(H=\sum_i\vec S_i\vec S_{i+1}+\tfrac13(\vec S_i\vec S_{i+1})^2\)", with \(\vec S\)
the spin-1 operators and MPS representation
\(\{\sigma^z,\sqrt2\sigma^+,-\sqrt2\sigma^-\}\).
The same Hamiltonian up to an additive constant is printed in arXiv:1010.3732,
`Papers/1010.3732/paper_v3.tex` lines 2126–2130.

**Formalized here.** On two spin-1 sites the operator \(\tfrac12(h+\tfrac23)\),
with \(h=\mathbf S_0\cdot\mathbf S_1+\tfrac13(\mathbf S_0\cdot\mathbf S_1)^2\), is the
orthogonal projector onto the orthogonal complement of the two-site ground space of
`akltTensor`, that is, its two-site parent interaction; it is also the projector
onto the eigenspace of \(\mathbf S_0\cdot\mathbf S_1\) for \(1\), the total-spin-2
subspace (spin addition, a project result). On a periodic chain of \(N\ge2\) sites
this gives \(H+\tfrac{2N}3=2H^{(2)}_{\mathrm{parent}}\), so every eigenvalue of
\(H\) is real and at least \(-\tfrac{2N}3\). For \(N\ge3\) the eigenspace for
\(-\tfrac{2N}3\) is spanned by the periodic AKLT vector: the AKLT state is the
unique ground state of \(H\). The source fixes no boundary condition or chain
length; the periodic range \(N\ge3\) is that of the existing two-site uniqueness
theorem `aklt_chainGroundSpace_two_eq_mpvSubmodule`. The physical labelling
\(0,1,2\leftrightarrow m=0,+1,-1\) is the convention fixed in
`TNLean.MPS.Examples.SpinOne`.

## Main definitions
* `MPSTensor.akltBondTerm` : the two-site term \(h\)
* `MPSTensor.akltSpinTwoES` : the total-spin-2 subspace of two spin-1 sites
* `MPSTensor.akltHamiltonian` : the periodic AKLT Hamiltonian

## Main results
* `MPSTensor.akltBondTerm_shift_eq_parentInteraction` :
  \(\tfrac12(h+\tfrac23)\) is the two-site parent interaction
* `MPSTensor.akltBondTerm_shift_eq_spinTwo_starProjection` :
  \(\tfrac12(h+\tfrac23)=P^{(2)}\)
* `MPSTensor.akltHamiltonian_add_eq_parentHamiltonian` :
  \(H+\tfrac{2N}3=2H^{(2)}_{\mathrm{parent}}\)
* `MPSTensor.akltHamiltonian_add_isPositive`, `MPSTensor.akltHamiltonian_eigenvalue_ge` :
  \(H\ge-\tfrac{2N}3\)
* `MPSTensor.akltHamiltonian_eigenspace_eq_mpvSubmodule`,
  `MPSTensor.akltHamiltonian_hasUniqueGroundState`,
  `MPSTensor.akltHamiltonian_hasEigenvalue` : the unique ground state

## References
- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix product state representations*
- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch, Pérez-García, Cirac,
  *Classifying quantum phases using MPS and PEPS*
-/

open scoped Matrix BigOperators InnerProductSpace ComplexConjugate ComplexOrder
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### The two-site term -/

/-- The exchange of the two sites of a two-site spin-1 chain. -/
local notation "𝐗" => (spinOneExchange 0 1 : NSiteSpace 3 2 →ₗ[ℂ] NSiteSpace 3 2)

/-- The two-site AKLT term \(\mathbf S_0\cdot\mathbf S_1+\tfrac13(\mathbf S_0\cdot\mathbf S_1)^2\)
on two spin-1 sites. -/
def akltBondTerm : NSiteSpace 3 2 →ₗ[ℂ] NSiteSpace 3 2 :=
  𝐗 + (1 / 3 : ℂ) • (𝐗 ∘ₗ 𝐗)

/-- The shifted and rescaled two-site term \(\tfrac12(h+\tfrac23)\). -/
local notation "𝐐" => ((1 / 2 : ℂ) •
  (akltBondTerm + (2 / 3 : ℂ) • (LinearMap.id : NSiteSpace 3 2 →ₗ[ℂ] NSiteSpace 3 2)))

/-- The shifted two-site term \(\tfrac12(h+\tfrac23)\) as an explicit matrix: it is
\(\sum_kw_kw_k^{\mathsf T}/\lVert w_k\rVert^2\) for the five spin-2 vectors
\(|11\rangle\), \(|22\rangle\), \(|01\rangle+|10\rangle\), \(|02\rangle+|20\rangle\),
\(|12\rangle+2|00\rangle+|21\rangle\). -/
lemma akltBondTerm_shift_apply (v : NSiteSpace 3 2) (p q : Fin 3) :
    𝐐 v ![p, q] =
      !![(2 * v ![0, 0] + v ![1, 2] + v ![2, 1]) / 3, (v ![0, 1] + v ![1, 0]) / 2,
          (v ![0, 2] + v ![2, 0]) / 2;
        (v ![0, 1] + v ![1, 0]) / 2, v ![1, 1], (2 * v ![0, 0] + v ![1, 2] + v ![2, 1]) / 6;
        (v ![0, 2] + v ![2, 0]) / 2, (2 * v ![0, 0] + v ![1, 2] + v ![2, 1]) / 6,
          v ![2, 2]] p q := by
  simp only [akltBondTerm, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    spinOneExchange_zero_one_apply]
  fin_cases p <;> fin_cases q <;> simp <;> ring

/-- A sum over two-site configurations is the double sum over the two site values. -/
private lemma sum_cfg_three_two (f : Cfg 3 2 → ℂ) : ∑ σ, f σ = ∑ a, ∑ b, f ![a, b] := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3) _ _ fun σ => ?_
  simp only [piFinTwoEquiv_apply]
  congr 1
  exact Matrix.eq_vecCons_fin_two σ

/-- The operator \(\tfrac12(h+\tfrac23)\) is symmetric for the \(\ell^2\) pairing
of coefficient vectors, since its matrix is real and symmetric. -/
private lemma akltBondTerm_shift_symm (f g : NSiteSpace 3 2) :
    ∑ σ, conj (f σ) * 𝐐 g σ = ∑ σ, conj (𝐐 f σ) * g σ := by
  simp only [sum_cfg_three_two, Fin.sum_univ_three, akltBondTerm_shift_apply]
  simp [map_add, map_div₀, map_mul, map_ofNat]
  ring

/-- The operator \(\tfrac12(h+\tfrac23)\) is idempotent. -/
private lemma akltBondTerm_shift_idem (v : NSiteSpace 3 2) : 𝐐 (𝐐 v) = 𝐐 v := by
  ext σ
  obtain ⟨p, q, rfl⟩ : ∃ p q, σ = ![p, q] := ⟨σ 0, σ 1, Matrix.eq_vecCons_fin_two σ⟩
  rw [akltBondTerm_shift_apply, akltBondTerm_shift_apply]
  simp only [akltBondTerm_shift_apply]
  fin_cases p <;> fin_cases q <;> simp <;> ring

/-- The kernel of \(\tfrac12(h+\tfrac23)\) is the two-site local ground space of the
AKLT tensor. -/
private lemma mem_aklt_groundSpace_two_iff_shift (v : NSiteSpace 3 2) :
    v ∈ groundSpace akltTensor 2 ↔ 𝐐 v = 0 := by
  rw [mem_aklt_groundSpace_two_iff]
  constructor
  · rintro ⟨h11, h22, h01, h02, h00⟩
    ext σ
    obtain ⟨p, q, rfl⟩ : ∃ p q, σ = ![p, q] := ⟨σ 0, σ 1, Matrix.eq_vecCons_fin_two σ⟩
    rw [akltBondTerm_shift_apply]
    fin_cases p <;> fin_cases q <;> simp [h11, h22, h01, h02, h00]
  · intro h
    have e : ∀ p q : Fin 3, 𝐐 v ![p, q] = 0 := fun p q => by rw [h]; rfl
    simp only [akltBondTerm_shift_apply] at e
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using e 1 1
    · simpa using e 2 2
    · simpa using e 0 1
    · simpa using e 0 2
    · simpa using e 0 0

/-- Bridge: the two-site AKLT term, shifted by \(\tfrac23\) and halved, is the
two-site parent interaction of `akltTensor`, the orthogonal projector onto
\(\mathcal G_2^\perp\). -/
theorem akltBondTerm_shift_eq_parentInteraction :
    (1 / 2 : ℂ) • (akltBondTerm + (2 / 3 : ℂ) • LinearMap.id) =
      parentInteraction akltTensor 2 := by
  set Q := 𝐐 with hQ
  set e := WithLp.linearEquiv 2 ℂ (NSiteSpace 3 2)
  set G := groundSpaceES akltTensor 2
  have hker : ∀ u, u ∈ G ↔ Q (e u) = 0 := fun u => by
    rw [mem_groundSpaceES_iff, mem_aklt_groundSpace_two_iff_shift]
  have hperp : ∀ v, e.symm (Q v) ∈ Gᗮ := by
    intro v
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := akltBondTerm_shift_symm (e u) v
    rw [← hQ, (hker u).1 hu] at h
    rw [← e.symm_apply_apply u, inner_withLpLinearEquiv_symm, h]
    simp
  have hin : ∀ v, e.symm v - e.symm (Q v) ∈ G := by
    intro v
    have h := akltBondTerm_shift_idem v
    rw [← hQ] at h
    rw [hker, ← map_sub, e.apply_symm_apply, map_sub, h, sub_self]
  refine LinearMap.ext fun v => ?_
  change Q v = e (Gᗮ.starProjection (e.symm v))
  rw [Submodule.eq_starProjection_of_mem_orthogonal (hperp v)
    (Submodule.le_orthogonal_orthogonal G (hin v)), e.apply_symm_apply]

/-! ### The spin-2 projector -/

/-- The exchange acts as the identity on the range of \(\tfrac12(h+\tfrac23)\):
\(\mathbf S_0\cdot\mathbf S_1=1\) on total spin \(2\). -/
private lemma spinOneExchange_akltBondTerm_shift (v : NSiteSpace 3 2) : 𝐗 (𝐐 v) = 𝐐 v := by
  ext σ
  obtain ⟨p, q, rfl⟩ : ∃ p q, σ = ![p, q] := ⟨σ 0, σ 1, Matrix.eq_vecCons_fin_two σ⟩
  rw [spinOneExchange_zero_one_apply, akltBondTerm_shift_apply]
  simp only [akltBondTerm_shift_apply]
  fin_cases p <;> fin_cases q <;> simp <;> ring

/-- The eigenspace of the exchange \(\mathbf S_0\cdot\mathbf S_1\) of two spin-1
sites for the eigenvalue \(1\), in the \(\ell^2\) space of coefficient vectors.
Since \(\mathbf S_{\mathrm{tot}}^2=4+2\,\mathbf S_0\cdot\mathbf S_1\), this is the
eigenspace of the squared total spin for \(6=2(2+1)\), the total-spin-\(2\)
subspace. -/
def akltSpinTwoES : Submodule ℂ (EuclideanSpace ℂ (Cfg 3 2)) :=
  (Module.End.eigenspace 𝐗 1).map (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 2)).symm.toLinearMap

/-- A two-site vector is fixed by the exchange exactly when it is fixed by the
parent interaction. -/
private lemma spinOneExchange_eq_self_iff (v : NSiteSpace 3 2) :
    𝐗 v = v ↔ parentInteraction akltTensor 2 v = v := by
  rw [← akltBondTerm_shift_eq_parentInteraction]
  constructor
  · intro h
    simp only [akltBondTerm, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, h]
    module
  · intro h
    rw [← h, spinOneExchange_akltBondTerm_shift]

/-- The total-spin-\(2\) subspace is the orthogonal complement of the two-site local
ground space of `akltTensor`. -/
theorem akltSpinTwoES_eq_orthogonal_groundSpaceES :
    akltSpinTwoES = (groundSpaceES akltTensor 2)ᗮ := by
  set e := WithLp.linearEquiv 2 ℂ (NSiteSpace 3 2)
  ext v
  rw [akltSpinTwoES, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
    ← Submodule.starProjection_eq_self_iff, Module.End.mem_eigenspace_iff, one_smul,
    spinOneExchange_eq_self_iff]
  change _ ↔ e.symm (parentInteraction akltTensor 2 (e v)) = v
  rw [e.symm_apply_eq]

/-- Project result: the addition of two spins \(1\), applied to the AKLT
Hamiltonian of arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex`
lines 340–349. The spin-2 projector identity
\(P^{(2)}=\tfrac12\bigl(\mathbf S_0\cdot\mathbf S_1+\tfrac13(\mathbf S_0\cdot\mathbf S_1)^2
+\tfrac23\bigr)\): the two-site AKLT term shifted by \(\tfrac23\) and halved is the
orthogonal projector onto the total-spin-\(2\) subspace. -/
theorem akltBondTerm_shift_eq_spinTwo_starProjection :
    (1 / 2 : ℂ) • (akltBondTerm + (2 / 3 : ℂ) • LinearMap.id) =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 2)).toLinearMap ∘ₗ
        akltSpinTwoES.starProjection.toLinearMap ∘ₗ
          (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 2)).symm.toLinearMap := by
  rw [akltBondTerm_shift_eq_parentInteraction, parentInteraction,
    akltSpinTwoES_eq_orthogonal_groundSpaceES]

/-! ### The periodic Hamiltonian -/

/-- Source: arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex`
lines 340–349, equation `HAKLT`. The AKLT Hamiltonian
\(H=\sum_i\bigl(\mathbf S_i\cdot\mathbf S_{i+1}+\tfrac13(\mathbf S_i\cdot\mathbf S_{i+1})^2\bigr)\)
on a periodic chain of \(N\) spin-1 sites, indices modulo \(N\). -/
def akltHamiltonian (N : ℕ) : NSiteSpace 3 N →ₗ[ℂ] NSiteSpace 3 N :=
  ∑ i : Fin N, (spinOneExchange i (cyclicForwardSite i 1) +
    (1 / 3 : ℂ) • (spinOneExchange i (cyclicForwardSite i 1) ∘ₗ
      spinOneExchange i (cyclicForwardSite i 1)))

/-- Restricting to the cyclic window of sites \(i,i+1\) intertwines the exchange of
these two sites with the exchange of a two-site chain. -/
lemma cyclicRestrictₗ_spinOneExchange {N : ℕ} (hN : 0 < N) (hN2 : 2 ≤ N) (i : Fin N)
    (τ : Cfg 3 N) (ψ : NSiteSpace 3 N) :
    cyclicRestrictₗ hN 2 i τ (spinOneExchange i (cyclicForwardSite i 1) ψ) =
      spinOneExchange 0 1 (cyclicRestrictₗ hN 2 i τ ψ) := by
  ext ω
  have h0 : cyclicCfg hN 2 i ω τ i = ω 0 := by
    simpa [cyclicForwardSite_zero] using cyclicCfg_cyclicForwardSite_apply hN hN2 i ω τ 0
  have h1 : cyclicCfg hN 2 i ω τ (cyclicForwardSite i 1) = ω 1 :=
    cyclicCfg_cyclicForwardSite_apply hN hN2 i ω τ 1
  have hu : ∀ a b : Fin 3, Function.update (Function.update (cyclicCfg hN 2 i ω τ) i a)
      (cyclicForwardSite i 1) b =
        cyclicCfg hN 2 i (Function.update (Function.update ω 0 a) 1 b) τ := fun a b => by
    have e0 := update_cyclicCfg hN hN2 i ω τ 0 a
    have e1 := update_cyclicCfg hN hN2 i (Function.update ω 0 a) τ 1 b
    simp only [Fin.val_zero, cyclicForwardSite_zero, Fin.val_one] at e0 e1
    rw [e0, e1]
  simp only [cyclicRestrictₗ_apply, spinOneExchange_apply, h0, h1, hu]

/-- On a periodic chain of \(N\ge2\) sites, the two-site local term of the parent
Hamiltonian of `akltTensor` at the window \(i,i+1\) is
\(\tfrac12(h_i+\tfrac23)\), with \(h_i\) the AKLT term of that bond. -/
lemma aklt_localTerm_two_apply {N : ℕ} (hN2 : 2 ≤ N) (i : Fin N) (ψ : NSiteSpace 3 N)
    (σ : Cfg 3 N) :
    localTerm akltTensor 2 N i ψ σ =
      (1 / 2) * (spinOneExchange i (cyclicForwardSite i 1) ψ σ +
        (1 / 3) * spinOneExchange i (cyclicForwardSite i 1)
          (spinOneExchange i (cyclicForwardSite i 1) ψ) σ + (2 / 3) * ψ σ) := by
  have hN : 0 < N := by omega
  rw [localTerm, dite_eq_left hN2]
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [← akltBondTerm_shift_eq_parentInteraction]
  change 𝐐 (cyclicRestrictₗ hN 2 i σ ψ) (extractWindow 2 i σ) = _
  simp only [akltBondTerm, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, ← cyclicRestrictₗ_spinOneExchange hN hN2, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, cyclicRestrictₗ_apply, cyclicCfg_extractWindow hN hN2]

/-- Bridge: on a periodic chain of \(N\ge2\) sites,
\(H+\tfrac{2N}3=2H^{(2)}_{\mathrm{parent}}\), where \(H\) is the AKLT Hamiltonian of
arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex` lines 340–349, and
\(H^{(2)}_{\mathrm{parent}}\) is the two-site parent Hamiltonian of `akltTensor`. -/
theorem akltHamiltonian_add_eq_parentHamiltonian {N : ℕ} (hN2 : 2 ≤ N) :
    akltHamiltonian N + (2 * N / 3 : ℂ) • LinearMap.id =
      (2 : ℂ) • parentHamiltonian akltTensor 2 N := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  simp only [akltHamiltonian, parentHamiltonian, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.sum_apply, LinearMap.comp_apply, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, aklt_localTerm_two_apply hN2, Finset.mul_sum,
    Finset.sum_add_distrib]
  simp only [show ∀ x y z : ℂ, 2 * (1 / 2 * (x + y + z)) = x + y + z from
      fun x y z => by ring, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Project result: on a periodic chain of \(N\ge2\) sites, the operator
\(H+\tfrac{2N}3\), transported to the \(\ell^2\) space of coefficient vectors, is
positive, that is, \(H\ge-\tfrac{2N}3\) as operators. -/
theorem akltHamiltonian_add_isPositive {N : ℕ} (hN2 : 2 ≤ N) :
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).symm.toLinearMap ∘ₗ
      (akltHamiltonian N + (2 * N / 3 : ℂ) • LinearMap.id) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap).IsPositive := by
  have h : (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).symm.toLinearMap ∘ₗ
      (akltHamiltonian N + (2 * N / 3 : ℂ) • LinearMap.id) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 3 N)).toLinearMap =
      (2 : ℂ) • parentHamiltonianES akltTensor 2 N := by
    rw [akltHamiltonian_add_eq_parentHamiltonian hN2]
    ext v
    simp [parentHamiltonianES]
  rw [h]
  exact (parentHamiltonianES_isPositive akltTensor 2 N).smul_of_nonneg
    (by norm_num [Complex.le_def])

/-- The eigenvalue equation of the AKLT Hamiltonian, rewritten through the parent
Hamiltonian. -/
private lemma akltHamiltonian_apply_eq_smul_iff {N : ℕ} (hN2 : 2 ≤ N) (μ : ℂ)
    (v : NSiteSpace 3 N) :
    akltHamiltonian N v = μ • v ↔
      parentHamiltonian akltTensor 2 N v = ((1 / 2) * (μ + 2 * N / 3)) • v := by
  have h := LinearMap.congr_fun (akltHamiltonian_add_eq_parentHamiltonian hN2) v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  constructor
  · intro hv
    rw [hv, ← add_smul] at h
    rw [mul_smul, h, smul_smul]
    norm_num
  · intro hv
    rw [hv, smul_smul, show (2 : ℂ) * (1 / 2 * (μ + 2 * N / 3)) = μ + 2 * N / 3 by ring,
      add_smul] at h
    exact add_right_cancel h

/-- Project result: on a periodic chain of \(N\ge2\) sites, every eigenvalue \(\mu\)
of the AKLT Hamiltonian is real with \(\mu\ge-\tfrac{2N}3\). -/
theorem akltHamiltonian_eigenvalue_ge {N : ℕ} (hN2 : 2 ≤ N) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (akltHamiltonian N) μ) :
    μ.im = 0 ∧ -(2 * N / 3 : ℝ) ≤ μ.re := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hshift : Module.End.HasEigenvalue
      (akltHamiltonian N + (2 * N / 3 : ℂ) • LinearMap.id) (μ + 2 * N / 3) :=
    Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 (by
      simp [Module.End.mem_eigenspace_iff.1 hv.1, add_smul]), hv.2⟩
  have h := Complex.le_def.1 (nonneg_of_hasEigenvalue_of_isPositive_conj
    (akltHamiltonian_add_isPositive hN2) hshift)
  simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im] at h
  norm_num at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Bridge: on a periodic chain of \(N\ge2\) sites, the eigenspace of the AKLT
Hamiltonian for \(-\tfrac{2N}3\) is the kernel of the two-site parent Hamiltonian
of `akltTensor`. -/
theorem akltHamiltonian_eigenspace_eq_ker {N : ℕ} (hN2 : 2 ≤ N) :
    Module.End.eigenspace (akltHamiltonian N) (-(2 * N / 3) : ℂ) =
      LinearMap.ker (parentHamiltonian akltTensor 2 N) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, akltHamiltonian_apply_eq_smul_iff hN2,
    LinearMap.mem_ker]
  norm_num

/-- Source: arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex`
lines 340–349: the AKLT state is the ground state of the AKLT Hamiltonian. On a
periodic chain of \(N\ge3\) sites, the eigenspace of the AKLT Hamiltonian for
\(-\tfrac{2N}3\), its lowest eigenvalue by `akltHamiltonian_eigenvalue_ge`, is
spanned by the periodic vector of `akltTensor`. The source fixes no boundary
condition or chain length; the range \(N\ge3\) is that of the two-site uniqueness
theorem `aklt_chainGroundSpace_two_eq_mpvSubmodule`. -/
theorem akltHamiltonian_eigenspace_eq_mpvSubmodule {N : ℕ} (hN3 : 3 ≤ N) :
    Module.End.eigenspace (akltHamiltonian N) (-(2 * N / 3) : ℂ) =
      mpvSubmodule akltTensor N := by
  rw [akltHamiltonian_eigenspace_eq_ker (by omega),
    ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) (by omega),
    aklt_chainGroundSpace_two_eq_mpvSubmodule hN3]

/-- Source: arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex`
lines 340–349. On a periodic chain of \(N\ge3\) sites the AKLT Hamiltonian has a
unique ground state: its eigenspace for its ground energy \(-\tfrac{2N}3\) is
one-dimensional. -/
theorem akltHamiltonian_hasUniqueGroundState {N : ℕ} (hN3 : 3 ≤ N) :
    HasUniqueGroundState (Module.End.eigenspace (akltHamiltonian N) (-(2 * N / 3) : ℂ)) := by
  rw [akltHamiltonian_eigenspace_eq_mpvSubmodule hN3,
    ← aklt_chainGroundSpace_two_eq_mpvSubmodule hN3]
  exact aklt_parentHamiltonian_two_unique_gs hN3

/-- Project result: on a periodic chain of \(N\ge3\) sites, \(-\tfrac{2N}3\) is an
eigenvalue of the AKLT Hamiltonian, hence its ground energy by
`akltHamiltonian_eigenvalue_ge`. -/
theorem akltHamiltonian_hasEigenvalue {N : ℕ} (hN3 : 3 ≤ N) :
    Module.End.HasEigenvalue (akltHamiltonian N) (-(2 * N / 3) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff]
  intro h
  have h1 := akltHamiltonian_hasUniqueGroundState hN3
  rw [HasUniqueGroundState, h, finrank_bot] at h1
  exact zero_ne_one h1

end MPSTensor

end
