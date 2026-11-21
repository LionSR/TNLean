/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# The nonwrapping open-chain parent Hamiltonian

For a chain of length `N`, this file sums the canonical local parent interactions
only over starts whose length-`L` windows stay inside the linear interval.  Thus
no local term crosses the cut between the last and first sites.

When the tensor has virtual dimension \(D \ge 1\) and is block-injective at
length \(L₀\), with \(0 < L₀\) and \(L₀ + 1 \le N\), the kernel of the
length-\(L₀ + 1\) open Hamiltonian is the open MPS boundary-condition space
`groundSpaceES A N`. This is the finite-volume ground-space input for
Nachtergaele's C1--C3 martingale theorem.

## References

* Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16).
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.

**Transitional (#10948).** The facts are stated twice: for the Euclidean-space operator
`openParentHamiltonianES` (the declarations before the last section, kept until their last users
are converted, then deleted with that definition) and, in the last section, for the Hamiltonian
of `parentChainInteraction`. `NonwrappingStart`, `sum_nonwrappingWindowTerms_le`,
`groundSpaceES_finrank_eq_of_isNBlkInjective` and the suffix Hamiltonian
`openSuffixParentHamiltonianES` with `openParentHamiltonianES_C1` (a later package) are not part
of the transitional block.
-/

open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A start site whose length-`L` window does not cross the right endpoint of an
`N`-site open chain.

This is the index set in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
abbrev NonwrappingStart (L N : ℕ) :=
  {i : Fin N // i.val + L ≤ N}

/-- The open-chain parent Hamiltonian, obtained by summing the canonical local
terms over all nonwrapping length-`L` windows.

For \(L = l + 1\), its starts are \(0, \ldots, N - l - 1\), as in Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
noncomputable def openParentHamiltonianES (A : MPSTensor d D) (L N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i : NonwrappingStart L N, localTermES A L i.1

/-- At volume \(N = L > 0\), the compatible open parent Hamiltonian is the
canonical local projector on the full chain.

This is the fixed-window operator underlying \(γ_{l+1} = 1\) in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(i). -/
theorem openParentHamiltonianES_self_eq_parentInteractionES (A : MPSTensor d D)
    {L : ℕ} (hL : 0 < L) :
    openParentHamiltonianES A L L = parentInteractionES A L := by
  let i : NonwrappingStart L L := ⟨⟨0, hL⟩, by simp⟩
  let : Subsingleton (NonwrappingStart L L) :=
    ⟨fun j k => by
      apply Subtype.ext
      apply Fin.ext
      have hj := j.2
      have hk := k.2
      omega⟩
  rw [openParentHamiltonianES, Fintype.sum_subsingleton _ i]
  ext v σ
  rw [localTermES_apply A L i.1 (le_refl L) v σ]
  have hrestrict : cyclicRestrictES (d := d) hL L i.1 σ v = v := by
    ext ω
    change v (cyclicCfg hL L (⟨0, hL⟩ : Fin L) ω σ) = v ω
    rw [show cyclicCfg hL L (⟨0, hL⟩ : Fin L) ω σ = ω by
      funext k
      simp [cyclicCfg, Nat.mod_eq_of_lt k.isLt]]
  rw [hrestrict]
  rw [show extractWindow L i.1 σ = σ by
    funext k
    simp [i, extractWindow, Nat.mod_eq_of_lt k.isLt]]

/-- The full-window compatible open parent Hamiltonian preserves the norm on
the orthogonal complement of its kernel. -/
theorem openParentHamiltonianES_self_norm_eq_of_mem_orthogonal_ker
    (A : MPSTensor d D) {L : ℕ} (hL : 0 < L)
    (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker (openParentHamiltonianES A L L))ᗮ) :
    ‖openParentHamiltonianES A L L v‖ = ‖v‖ := by
  rw [openParentHamiltonianES_self_eq_parentInteractionES A hL] at hv ⊢
  change ‖(groundSpaceES A L)ᗮ.starProjection v‖ = ‖v‖
  apply Submodule.norm_starProjection_apply
  have hker : LinearMap.ker (parentInteractionES A L) = groundSpaceES A L := by
    ext w
    rw [LinearMap.mem_ker, parentInteractionES_apply_eq_zero_iff]
  rwa [hker] at hv

/-- The compatible open parent Hamiltonian has unit norm gap at the first
full-window volume.

This is \(γ_{l+1} = 1\) in Nachtergaele, arXiv:cond-mat/9410110,
Theorem 2.1(i), for \(L = l + 1\).

**Scope restriction (single-window volume):** This proves only the volume
\(N=L\). It does not establish the general-volume C1--C3 martingale gap; see
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem openParentHamiltonianES_self_unit_gap (A : MPSTensor d D)
    {L : ℕ} (hL : 0 < L) (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker (openParentHamiltonianES A L L))ᗮ) :
    (1 : ℝ) * ‖v‖ ≤ ‖openParentHamiltonianES A L L v‖ := by
  simpa only [one_mul] using
    (openParentHamiltonianES_self_norm_eq_of_mem_orthogonal_ker A hL v hv).symm.le

/-- The open-chain parent Hamiltonian is positive because every summand is an
orthogonal projection. -/
theorem openParentHamiltonianES_isPositive (A : MPSTensor d D) (L N : ℕ) :
    (openParentHamiltonianES A L N).IsPositive := by
  rw [openParentHamiltonianES]
  exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i.1

/-- The parent Hamiltonian on the last \(l\) sites of the prefix of length \(n\),
embedded in an \(N\)-site open chain.

Its summands have starts \(i\) satisfying \(n-l≤i\) and \(i+L≤n\). Thus their
length-\(L\) windows lie in the nonwrapping interval \([n-l,n)\). This is
\(H_{\Lambda_n\setminus\Lambda_{n-l}}\) for \(\Lambda_n=[0,n)\) in
Nachtergaele, arXiv:cond-mat/9410110, condition C1 (lines 1030--1041). -/
noncomputable def openSuffixParentHamiltonianES (A : MPSTensor d D)
    (L l N n : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i ∈ Finset.univ.filter fun i : NonwrappingStart L N =>
    n - l ≤ i.1.val ∧ i.1.val + L ≤ n,
    localTermES A L i.1

/-- Each nonwrapping range-\(R\) term lies in at most \(W-R+1\) complete
length-\(W\) windows. Summing positive terms therefore gives the corresponding
operator bound. This is the counting argument for Nachtergaele,
arXiv:cond-mat/9410110, condition C1. -/
theorem sum_nonwrappingWindowTerms_le {R W N : ℕ} (hRW : R ≤ W)
    {ι : Type*} [Fintype ι]
    (f : NonwrappingStart R N → EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ n ∈ Finset.Icc W N,
      ∑ i ∈ Finset.univ.filter (fun i : NonwrappingStart R N =>
        n - W ≤ i.1.val ∧ i.1.val + R ≤ n), f i) ≤
      ((W - R + 1 : ℕ) : ℂ) • ∑ i, f i := by
  classical
  let windows := fun i : NonwrappingStart R N =>
    (Finset.Icc W N).filter fun n => n - W ≤ i.1.val ∧ i.1.val + R ≤ n
  have hwindows_card (i : NonwrappingStart R N) :
      (windows i).card ≤ W - R + 1 := by
    calc
      (windows i).card ≤ (Finset.Icc (i.1.val + R) (i.1.val + W)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [windows, Finset.mem_filter, Finset.mem_Icc] at hn
        simp only [Finset.mem_Icc]
        omega
      _ = W - R + 1 := by
        rw [Nat.card_Icc]
        omega
  rw [Finset.sum_comm'
    (s := Finset.Icc W N)
    (t := fun n => Finset.univ.filter fun i : NonwrappingStart R N =>
      n - W ≤ i.1.val ∧ i.1.val + R ≤ n)
    (t' := Finset.univ) (s' := windows) (fun n i => by simp [windows]),
    Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  exact nsmul_le_nsmul_left (hf i) (hwindows_card i)
/-- Nachtergaele's condition C1 for the compatible nonwrapping open parent
Hamiltonian.

For the prefixes \(\Lambda_n=[0,n)\), each range-\(L\) local term belongs to at
most \(l-L+1\) of the suffix intervals
\(\Lambda_n\setminus\Lambda_{n-l}\), \(l≤n≤N\). Therefore
\[
0\leq\sum_{n=l}^N H_{\Lambda_n\setminus\Lambda_{n-l}}
  \leq (l-L+1)H_{\Lambda_N}.
\]
The source gives \(d_l=pl-r+1\) for \(\Lambda_n=[1,pn]\). The indexing of
`openParentHamiltonianES` has \(p=1\) and \(r=L\), so its actual counting
constant is \(d_l=l-L+1\).

This is condition C1 in Nachtergaele, arXiv:cond-mat/9410110, lines 1030--1041. -/
theorem openParentHamiltonianES_C1 (A : MPSTensor d D) {L l N : ℕ}
    (hLl : L ≤ l) :
    0 ≤ ∑ n ∈ Finset.Icc l N, openSuffixParentHamiltonianES A L l N n ∧
      ∑ n ∈ Finset.Icc l N, openSuffixParentHamiltonianES A L l N n ≤
        ((l - L + 1 : ℕ) : ℂ) • openParentHamiltonianES A L N := by
  constructor
  · rw [LinearMap.nonneg_iff_isPositive]
    refine LinearMap.isPositive_sum _ fun n _ => ?_
    rw [openSuffixParentHamiltonianES]
    exact LinearMap.isPositive_sum _ fun i _ => localTermES_isPositive A L i.1
  · exact sum_nonwrappingWindowTerms_le hLl
      (fun i => localTermES A L i.1)
      (fun i => LinearMap.nonneg_iff_isPositive.mpr (localTermES_isPositive A L i.1))

/-- If the open-chain Hamiltonian annihilates a vector, then every individual
nonwrapping local term annihilates it.

This is the elementary frustration-free extraction used before the C1--C3
estimate in Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem localTermES_eq_zero_of_openParentHamiltonianES_eq_zero
    (A : MPSTensor d D) (L N : ℕ) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : openParentHamiltonianES A L N v = 0) (i : NonwrappingStart L N) :
    localTermES A L i.1 v = 0 := by
  rw [openParentHamiltonianES] at hv
  exact ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
    (fun i : NonwrappingStart L N => localTermES A L i.1)
    (fun i => localTermES_isSymmetricProjection A L i.1) hv i

/-- A kernel vector of the open-chain Hamiltonian restricts into the local
ground space on every nonwrapping window of length \(L\).

This is the frustration-free extraction of Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12), read in `NSiteSpace` coordinates. -/
theorem cyclicRestrictₗ_mem_groundSpace_of_mem_ker_openParentHamiltonianES
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N)
    {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (openParentHamiltonianES A L N))
    (i : Fin N) (hi : i.val + L ≤ N) (τ : Fin N → Fin d) :
    cyclicRestrictₗ (Fin.pos i) L i τ (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈
      groundSpace A L := by
  have hlocal : localTermES A L i v = 0 :=
    localTermES_eq_zero_of_openParentHamiltonianES_eq_zero A L N
      (LinearMap.mem_ker.mp hv) ⟨i, hi⟩
  have hrestrictES :=
    cyclicRestrictES_mem_groundSpaceES_of_localTermES_eq_zero A hLN i hlocal τ
  simpa [cyclicRestrictES] using (mem_groundSpaceES_iff A L _).1 hrestrictES

/-- The open MPS boundary-condition space is contained in the kernel of the
open-chain parent Hamiltonian.

Every nonwrapping restriction of an open-boundary MPS vector is again an
open-boundary MPS vector on the smaller interval.  This is the frustration-free
direction of Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem groundSpaceES_le_ker_openParentHamiltonianES
    (A : MPSTensor d D) (L N : ℕ) :
    groundSpaceES A N ≤ LinearMap.ker (openParentHamiltonianES A L N) := by
  intro v hv
  rw [LinearMap.mem_ker, openParentHamiltonianES, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [localTermES_eq_zero_iff_forall_cyclicRestrictES_mem_groundSpaceES A
    (by omega : L ≤ N) i.1 v]
  intro τ
  rw [mem_groundSpaceES_iff]
  let eN := WithLp.linearEquiv 2 ℂ (NSiteSpace d N)
  let eL := WithLp.linearEquiv 2 ℂ (NSiteSpace d L)
  have hvNS : eN v ∈ groundSpace A N := (mem_groundSpaceES_iff A N v).1 hv
  rw [groundSpace, LinearMap.mem_range] at hvNS
  obtain ⟨X, hX⟩ := hvNS
  have hrestrict :
      contiguousRestrictₗ i.1.val L i.2 τ (eN v) ∈ groundSpace A L := by
    rw [← hX]
    exact contiguousRestrictₗ_groundSpaceMap_mem_groundSpace i.2 τ X
  rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i.1) (by omega) i.2] at hrestrict
  simpa [cyclicRestrictES, eN, eL] using hrestrict

/-- Under block injectivity, the kernel of the open-chain parent Hamiltonian is
contained in the open MPS boundary-condition space.

The zero-energy condition supplies every nonwrapping length-\(L₀ + 1\) local
constraint.  The open-chain intersection theorem then grows these constraints
to the full interval.  This is the ground-space step in the C1--C3 argument of
Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_openParentHamiltonianES_le_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (openParentHamiltonianES A (L₀ + 1) N) ≤ groundSpaceES A N := by
  intro v hv
  rw [mem_groundSpaceES_iff]
  apply contiguous_mem_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N
  intro s hs τ
  have hrestrict := cyclicRestrictₗ_mem_groundSpace_of_mem_ker_openParentHamiltonianES
    A hL₀N hv ⟨s, by omega⟩ hs τ
  rwa [cyclicRestrictₗ_eq_contiguousRestrictₗ _ hL₀N hs] at hrestrict

/-- For a block-injective tensor, the kernel of the canonical nonwrapping open
parent Hamiltonian is exactly the open MPS boundary-condition space.

Unlike the periodic ground space, this space generally has boundary-matrix
degeneracy.  This is the finite-volume kernel identification used in
Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (openParentHamiltonianES A (L₀ + 1) N) = groundSpaceES A N :=
  le_antisymm
    (ker_openParentHamiltonianES_le_groundSpaceES_of_isNBlkInjective
      hInj hL₀ hL₀N)
    (groundSpaceES_le_ker_openParentHamiltonianES A (L₀ + 1) N)

/-! ### Dimension of the open-boundary ground space -/

/-- The canonical \(\ell^2\) realization of the local ground space has dimension
\(D^2\) under block injectivity at length \(L\). -/
theorem groundSpaceES_finrank_eq_of_isNBlkInjective {A : MPSTensor d D} {L : ℕ}
    (hInj : Kraus.IsNBlkInjective A L) :
    Module.finrank ℂ (groundSpaceES A L) = D ^ 2 := by
  rw [groundSpaceES, LinearEquiv.finrank_map_eq]
  exact groundSpace_finrank_eq_of_isNBlkInjective hInj

/-- Project result: **boundary degeneracy of the open-chain parent Hamiltonian.**
For a tensor block-injective at length \(L₀ > 0\), the kernel of the
length-\((L₀ + 1)\) open parent Hamiltonian on \(N \ge L₀ + 1\) sites has
dimension exactly \(D^2\).

Primary sources. Nachtergaele, arXiv:cond-mat/9410110,
`References/cond-mat_9410110/main.tex` lines 1505--1510, summarizing
Fannes--Nachtergaele--Werner (lines 1484--1486), states that the local support
spaces \(\mathcal G_{[M,N]}\) of a pure generalized valence-bond-solid state with
auxiliary algebra \(M_k\) have dimension \(k^2\) on long intervals, and lines
1545--1558 (equations (3.12)--(3.13)) that the kernel of the open-interval
Hamiltonian is \(\mathcal G_{[M,N]}\). Pérez-García--Verstraete--Wolf--Cirac,
arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex` lines
1211--1233, proves the growth step on an open chain: every ground state of the
nearest-neighbour projector Hamiltonian has the form
\(\operatorname{tr}(Y B^{i_j} \cdots B^{i_{j+2}})\) on growing windows.

arXiv:2011.12127, line 1174, states that the open-boundary ground-state
degeneracy is at least the square of the dimension of the irreducible
projective representation carried by the boundary vectors. That dimension is
at most \(D\), and this theorem gives the exact count \(D^2\) for every
block-injective tensor; it is a sharper statement than the review's lower
bound, not the review's statement itself. -/
theorem finrank_ker_openParentHamiltonianES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (openParentHamiltonianES A (L₀ + 1) N)) = D ^ 2 := by
  rw [ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective hInj hL₀ hL₀N]
  exact groundSpaceES_finrank_eq_of_isNBlkInjective (isNBlkInjective_of_le hL₀ hInj (by omega))

/-! ### The open-chain parent Hamiltonian as the Hamiltonian of `parentChainInteraction`

The same facts for the Hamiltonian of the parent interaction on the open chain
(`parentChainInteraction`), the matrix of the open-chain parent Hamiltonian; statements about
vectors take its operator `Matrix.toEuclideanLin`. -/

section ChainInteraction

open scoped Matrix

private theorem contiguousCfg_chainWindow {L N a : ℕ} (h : a + L ≤ N) (ω : Cfg d L)
    (σ : Cfg d N) (u : Fin L) : contiguousCfg a L ω σ (ManyBody.chainWindow a h u) = ω u := by
  unfold contiguousCfg
  rw [dite_eq_left (show a ≤ (ManyBody.chainWindow a h u).val ∧
    (ManyBody.chainWindow a h u).val < a + L by simp)]
  exact congrArg ω (Fin.ext (by simp))

private theorem contiguousCfg_of_forall_chainWindow_ne {L N a : ℕ} (h : a + L ≤ N)
    (ω : Cfg d L) (σ : Cfg d N) {v : Fin N} (hv : ∀ u, ManyBody.chainWindow a h u ≠ v) :
    contiguousCfg a L ω σ v = σ v := by
  unfold contiguousCfg
  rw [dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact hv ⟨v.val - a, by omega⟩ (Fin.ext (by simp only [ManyBody.val_chainWindow]; omega))

private theorem contiguousCfg_contiguousCfg {L N a : ℕ} (ω ω' : Cfg d L) (τ : Cfg d N) :
    contiguousCfg a L ω' (contiguousCfg a L ω τ) = contiguousCfg a L ω' τ := by
  funext k
  unfold contiguousCfg
  split_ifs <;> rfl

/-- A matrix placed on the window of `L` sites starting at `a` acts at a configuration `σ` as
the matrix on the restriction of the vector to that window, the other sites fixed by `σ`, read
at the window of `σ`. -/
theorem placeAlong_chainWindow_mulVec_apply {L N a : ℕ} (h : a + L ≤ N)
    (K : Matrix (Cfg d L) (Cfg d L) ℂ) (ψ : Cfg d N → ℂ) (σ : Cfg d N) :
    (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a h) K *ᵥ ψ) σ =
      (K *ᵥ contiguousRestrictₗ a L h σ ψ) (fun u ↦ σ (ManyBody.chainWindow a h u)) := by
  rw [ManyBody.placeAlong_mulVec_apply_of _ _ ψ σ (fun ω ↦ contiguousCfg a L ω σ)
    (contiguousCfg_chainWindow h · σ)
    (fun ω _ hv ↦ contiguousCfg_of_forall_chainWindow_ne h ω σ hv)]
  rfl

private theorem toMatrix'_parentInteraction_mulVec_eq_zero_iff (A : MPSTensor d D) {L : ℕ}
    (f : Cfg d L → ℂ) :
    LinearMap.toMatrix' (parentInteraction A L) *ᵥ f = 0 ↔ f ∈ groundSpace A L := by
  have hf : f ∈ groundSpace A L ↔ WithLp.toLp 2 f ∈ groundSpaceES A L :=
    (mem_groundSpaceES_iff A L _).symm
  rw [hf, ← toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, WithLp.toLp_eq_zero]

/-- **Kernel of a term.** The term of the parent interaction on the open chain at the start `i`
annihilates a vector exactly when every restriction of the vector to the window of the term,
the other sites fixed, lies in the local ground space \(G_L(A)\). Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem parentChainInteraction_term_mulVec_eq_zero_iff (A : MPSTensor d D) {L N : ℕ}
    (i : Fin (N + 1 - L)) (ψ : Cfg d N → ℂ) :
    (parentChainInteraction A L N).term i *ᵥ ψ = 0 ↔
      ∀ τ : Cfg d N, contiguousRestrictₗ i.val L (by omega) τ ψ ∈ groundSpace A L := by
  have hi : i.val + L ≤ N := by omega
  rw [ManyBody.Interaction.translates_term]
  constructor
  · intro hψ τ
    rw [← toMatrix'_parentInteraction_mulVec_eq_zero_iff]
    funext ω
    have h := congrFun hψ (contiguousCfg i.val L ω τ)
    rw [placeAlong_chainWindow_mulVec_apply hi] at h
    have hr : contiguousRestrictₗ i.val L hi (contiguousCfg i.val L ω τ) ψ =
        contiguousRestrictₗ i.val L hi τ ψ := by
      funext ω'
      exact congrArg ψ (contiguousCfg_contiguousCfg ω ω' τ)
    have hw : (fun u ↦ contiguousCfg i.val L ω τ (ManyBody.chainWindow i.val hi u)) = ω :=
      funext (contiguousCfg_chainWindow hi ω τ)
    rw [hr, hw] at h
    exact h
  · intro hψ
    funext σ
    rw [placeAlong_chainWindow_mulVec_apply hi,
      (toMatrix'_parentInteraction_mulVec_eq_zero_iff A _).mpr (hψ σ)]
    rfl

private theorem posSemidef_parentChainInteraction_term (A : MPSTensor d D) (L N : ℕ)
    (i : Fin (N + 1 - L)) : ((parentChainInteraction A L N).term i).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (ManyBody.Interaction.translates_term_nonneg _
    (Matrix.nonneg_iff_posSemidef.mpr (posSemidef_toMatrix'_parentInteraction A L)) i)

/-- The Hamiltonian of the parent interaction on the open chain is positive semidefinite. -/
theorem posSemidef_hamiltonian_parentChainInteraction (A : MPSTensor d D) (L N : ℕ) :
    (parentChainInteraction A L N).hamiltonian.PosSemidef :=
  ManyBody.Interaction.posSemidef_hamiltonian (posSemidef_parentChainInteraction_term A L N)

/-- **Frustration-free extraction.** A vector annihilated by the Hamiltonian of the parent
interaction on the open chain has every restriction to a window of `L` sites in the local
ground space. Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D) {L N : ℕ} {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian))
    (s : ℕ) (hs : s + L ≤ N) (τ : Cfg d N) :
    contiguousRestrictₗ s L hs τ (WithLp.ofLp v) ∈ groundSpace A L := by
  have hH : (parentChainInteraction A L N).hamiltonian *ᵥ WithLp.ofLp v = 0 := by
    rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero] at hv
    exact hv
  have hterm := (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff
    (posSemidef_parentChainInteraction_term A L N)).mp hH ⟨s, by omega⟩
  exact (parentChainInteraction_term_mulVec_eq_zero_iff A ⟨s, by omega⟩ _).mp hterm τ

/-- The cyclic form of the frustration-free extraction: for a window that does not cross the
right endpoint, the cyclic restriction is the contiguous one. -/
theorem cyclicRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) {v : EuclideanSpace ℂ (Cfg d N)}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian))
    (i : Fin N) (hi : i.val + L ≤ N) (τ : Fin N → Fin d) :
    cyclicRestrictₗ (Fin.pos i) L i τ (WithLp.linearEquiv 2 ℂ (NSiteSpace d N) v) ∈
      groundSpace A L := by
  rw [cyclicRestrictₗ_eq_contiguousRestrictₗ (Fin.pos i) hLN hi]
  exact contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
    i.val hi τ

/-- The open MPS boundary-condition space lies in the kernel of the Hamiltonian of the parent
interaction on the open chain: every window restriction of an open-boundary MPS vector is an
open-boundary MPS vector. Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem groundSpaceES_le_ker_hamiltonian_parentChainInteraction (A : MPSTensor d D)
    (L N : ℕ) :
    groundSpaceES A N ≤
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A L N).hamiltonian) := by
  intro v hv
  rw [mem_groundSpaceES_iff, groundSpace, LinearMap.mem_range] at hv
  obtain ⟨X, hX⟩ := hv
  rw [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero,
    ManyBody.Interaction.hamiltonian, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun i _ ↦ (parentChainInteraction_term_mulVec_eq_zero_iff A i _).mpr
    fun τ ↦ ?_
  have := contiguousRestrictₗ_groundSpaceMap_mem_groundSpace (A := A)
    (show i.val + L ≤ N by omega) τ X
  rwa [hX] at this

/-- Under block injectivity at length \(L_0 > 0\), the kernel of the Hamiltonian of the
length-\((L_0+1)\) parent interaction on the open chain lies in the open MPS boundary-condition
space. Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_le_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian) ≤
      groundSpaceES A N := by
  intro v hv
  rw [mem_groundSpaceES_iff]
  exact contiguous_mem_groundSpace_of_isNBlkInjective hInj hL₀ hL₀N fun s hs τ ↦
    contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv s hs τ

/-- For a block-injective tensor, the kernel of the Hamiltonian of the parent interaction on the
open chain is exactly the open MPS boundary-condition space. Nachtergaele,
arXiv:cond-mat/9410110, equations (3.12)--(3.16). -/
theorem ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian) =
      groundSpaceES A N :=
  le_antisymm (ker_hamiltonian_parentChainInteraction_le_groundSpaceES_of_isNBlkInjective
    hInj hL₀ hL₀N) (groundSpaceES_le_ker_hamiltonian_parentChainInteraction A (L₀ + 1) N)

/-- Project result: **boundary degeneracy of the open-chain parent Hamiltonian.** For a tensor
block-injective at length \(L_0 > 0\), the kernel of the Hamiltonian of the length-\((L_0+1)\)
parent interaction on \(N \ge L_0 + 1\) sites has dimension exactly \(D^2\). The sources are
those of `finrank_ker_openParentHamiltonianES_of_isNBlkInjective`: Nachtergaele,
arXiv:cond-mat/9410110, lines 1484--1486, 1505--1510, 1545--1558; Pérez-García--Verstraete--
Wolf--Cirac, arXiv:quant-ph/0608197, lines 1211--1233; arXiv:2011.12127, line 1174 (a lower
bound; the theorem is sharper than the review's statement). -/
theorem finrank_ker_hamiltonian_parentChainInteraction_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀) (hL₀N : L₀ + 1 ≤ N) :
    Module.finrank ℂ (LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A (L₀ + 1) N).hamiltonian)) = D ^ 2 := by
  rw [ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective hInj hL₀ hL₀N]
  exact groundSpaceES_finrank_eq_of_isNBlkInjective (isNBlkInjective_of_le hL₀ hInj (by omega))

/-- At volume \(N = L\) the Hamiltonian of the parent interaction on the open chain is the local
parent interaction itself: the only window is the whole chain. -/
theorem hamiltonian_parentChainInteraction_self (A : MPSTensor d D) (L : ℕ) :
    (parentChainInteraction A L L).hamiltonian = LinearMap.toMatrix' (parentInteraction A L) := by
  rw [ManyBody.Interaction.hamiltonian_chainTranslates_eq_sum_range, Nat.add_sub_cancel_left,
    Finset.sum_range_one, dite_eq_left (by omega)]
  have hw : ManyBody.chainWindow (N := L) (k := L) 0 (by omega) = Function.Embedding.refl _ :=
    Function.Embedding.ext fun j ↦ Fin.ext (by simp)
  rw [hw, ManyBody.placeAlong_refl]

/-- At the first full-window volume the operator of the open-chain parent Hamiltonian preserves
the norm on the orthogonal complement of its kernel. -/
theorem norm_toEuclideanLin_hamiltonian_parentChainInteraction_self_of_mem_orthogonal_ker
    (A : MPSTensor d D) (L : ℕ) (v : EuclideanSpace ℂ (Cfg d L))
    (hv : v ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian))ᗮ) :
    ‖Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian v‖ = ‖v‖ := by
  rw [hamiltonian_parentChainInteraction_self, toEuclideanLin_toMatrix'_parentInteraction] at hv ⊢
  change ‖(groundSpaceES A L)ᗮ.starProjection v‖ = ‖v‖
  apply Submodule.norm_starProjection_apply
  have hker : LinearMap.ker ((groundSpaceES A L)ᗮ.starProjection.toLinearMap) =
      groundSpaceES A L := by
    ext w
    rw [LinearMap.mem_ker, ← toEuclideanLin_toMatrix'_parentInteraction,
      toEuclideanLin_toMatrix'_parentInteraction_apply_eq_zero_iff]
  rwa [hker] at hv

/-- The open-chain parent Hamiltonian has unit gap at the first full-window volume: every
eigenvalue is `0` or at least `1`. This is \(γ_{l+1} = 1\) in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(i), for \(L = l + 1\).

**Scope restriction (single-window volume):** This proves only the volume \(N=L\). It does not
establish the general-volume C1--C3 martingale gap; see
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem unit_gap_hamiltonian_parentChainInteraction_self (A : MPSTensor d D) (L : ℕ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A L L).hamiltonian) μ →
        μ = 0 ∨ (1 : ℂ) ≤ μ := by
  have h := (ManyBody.forall_hasEigenvalue_iff_norm (Δ := 1)
    (posSemidef_hamiltonian_parentChainInteraction A L L)).mpr fun v hv ↦ by
      rw [one_mul,
        norm_toEuclideanLin_hamiltonian_parentChainInteraction_self_of_mem_orthogonal_ker A L v hv]
  simpa only [Complex.ofReal_one] using h

end ChainInteraction

end MPSTensor
