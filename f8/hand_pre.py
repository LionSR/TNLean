"""F8 phase 2, hand part run before f8_chain.py: the structures and their constructions.
Each construction becomes an interaction plus a lemma for each of the two former fields."""
import re
M = 'TNLean/MPS/AreaLaw/'


def cut(p, start, end, new):
    """Replace the text from the marker `start` up to (not including) the marker `end`."""
    s = open(p).read()
    a = s.index(start); b = s.index(end, a)
    open(p, 'w').write(s[:a] + new + s[b:])


def sub(p, a, b):
    s = open(p).read(); assert a in s, (p, a[:70]); open(p, 'w').write(s.replace(a, b))


# --- the chain structure, its sum, Hermiticity and zero: QICLean's `ChainInteraction`,
# `Interaction.hamiltonian` and `Interaction.isHermitian_hamiltonian`; the zero family is unused
cut(M + 'Hamiltonian.lean', '/-- A finite-range Hamiltonian on the chain of `L` sites with local dimension `q`: one',
    '/-- The interaction bound is nonnegative whenever the chain contains a site.', '')
cut(M + 'Hamiltonian.lean', '/-- The Hamiltonian `H = ∑_X h_X`. TNLean note, Section 1, `eq:ham`. -/',
    '/-- The budget `ℬ_A = 1 + ∑ log² (e q^{|X|})` of the marginal tail bound', '')
sub(M + 'Hamiltonian.lean', """* `ChainHamiltonian L q R J`: a finite-range Hamiltonian on the chain; `operator` is its
  sum.
""", "")
sub(M + 'Hamiltonian.lean', """A support of range `R` is a nonempty set of sites of the chain of diameter at most `R`,
that is, contained in `R + 1` consecutive positions. A finite-range Hamiltonian has one
Hermitian term per support, acting as the identity off its support and of operator norm
at most `J`.""", """A support of range `R` is a nonempty set of sites of the chain of diameter at most `R`,
that is, contained in `R + 1` consecutive positions. A finite-range Hamiltonian is an
interaction `ManyBody.ChainInteraction L q R`, one term per support acting as the identity off
it, whose terms are Hermitian and of operator norm at most `J`; both are hypotheses of the
statements that use them.""")
sub(M + 'Hamiltonian.lean', "import QICLean.ManyBody.Hamiltonian.GroundSpace\n",
    "import QICLean.ManyBody.Hamiltonian.GroundSpace\nimport QICLean.ManyBody.Hamiltonian.Models\n")

# --- the domain structure, its sum and Hermiticity, and the chain embedding
cut(M + 'ComponentReduction.lean', '/-- An admissible Hamiltonian on a finite set `Λ ⊂ ℤ` with local dimension `q`: one term per',
    '/-- The edge boundary `∂_Λ A`: the edges', '''/-- An interaction on `Λ` as a finite-range interaction on the chain of `|Λ|` sites, with zero
terms on the chain supports that straddle a gap of `Λ`. TNLean note, `part0_preamble.tex`,
`eq:ham`. -/
noncomputable def _root_.ManyBody.DomainInteraction.toChain (h : ManyBody.DomainInteraction Λ q R) :
    ManyBody.ChainInteraction Λ.card q R where
  term Y := if hY : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hY⟩ else 0
  mem Y := by
    split
    · exact h.mem _
    · exact (ManyBody.supportedOperators (fun _ : Fin Λ.card ↦ Fin q) _).zero_mem

/-- The chain terms of Hermitian domain terms are Hermitian. -/
theorem _root_.ManyBody.DomainInteraction.isHermitian_toChain_term
    (h : ManyBody.DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
    (Y : ManyBody.ChainSupport Λ.card R) : (h.toChain.term Y).IsHermitian := by
  change (if hY : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hY⟩ else 0).IsHermitian
  split
  · exact hh _
  · exact Matrix.isHermitian_zero

/-- The chain terms keep the bound `J ≥ 0` of the domain terms. -/
theorem _root_.ManyBody.DomainInteraction.norm_toChain_term_le
    (h : ManyBody.DomainInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 ≤ J)
    (Y : ManyBody.ChainSupport Λ.card R) : ‖h.toChain.term Y‖ ≤ J := by
  change ‖if hY : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hY⟩ else 0‖ ≤ J
  split
  · exact hhJ _
  · simpa using hJ

/-- The chain interaction has the same sum. -/
theorem _root_.ManyBody.DomainInteraction.toChain_hamiltonian
    (h : ManyBody.DomainInteraction Λ q R) : h.toChain.hamiltonian = h.hamiltonian := by
  classical
  refine (Fintype.sum_of_injective
    (DomainSupport.toChainSupport (Λ := Λ) (R := R))
    DomainSupport.toChainSupport_injective _ _ ?_ ?_).symm
  · intro Y hY
    change (if hY : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hY⟩ else 0) = 0
    split_ifs with hY'
    · exact absurd ⟨⟨Y.1, hY'⟩, rfl⟩ hY
    · rfl
  · intro X
    change h.term X = if hY : IsDomainSupport Λ R X.1 then h.term ⟨X.1, hY⟩ else 0
    simp [X.2]

''')
sub(M + 'DomainInteractionBudget.lean', """@[simp] lemma DomainHamiltonian.toChain_term (h : DomainHamiltonian Λ q R J)
    (hJ : 0 ≤ J) (X : DomainSupport Λ R) :
    (h.toChain hJ).term X.toChainSupport = h.term X := by
  simp [DomainHamiltonian.toChain, DomainSupport.toChainSupport, X.2]""",
"""@[simp] lemma _root_.ManyBody.DomainInteraction.toChain_term (h : ManyBody.DomainInteraction Λ q R)
    (X : DomainSupport Λ R) : h.toChain.term X.toChainSupport = h.term X := by
  simp [ManyBody.DomainInteraction.toChain, DomainSupport.toChainSupport, X.2]""")

# --- the chain doubling
cut(M + 'DoubledHamiltonian.lean', '/-- The two-copy Hamiltonian, with the copies paired at each original site.',
    '/-- Summing the paired interactions gives exactly the sum of the two copies of', '''/-- The two-copy interaction, with the copies paired at each original site.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
noncomputable def _root_.ManyBody.ChainInteraction.doubled (h : ManyBody.ChainInteraction L q R) :
    ManyBody.ChainInteraction L (q * q) R where
  term X := Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
    (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)
  mem X := by
    change (Matrix.reindexAddEquiv ℂ (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)) (_ + _) ∈ _
    rw [map_add]
    have hterm := h.mem X
    have hone := one_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) X.1)
    have hleft := QuantumCircuit.reindex_kronecker_mem_supportedOperators hterm hone
    have hright := QuantumCircuit.reindex_kronecker_mem_supportedOperators hone hterm
    simpa only [Finset.union_self, Matrix.coe_reindexAddEquiv] using
      add_mem hleft hright

/-- The paired terms of Hermitian terms are Hermitian.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_doubled_term
    (h : ManyBody.ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (X : ManyBody.ChainSupport L R) : (h.doubled.term X).IsHermitian := by
  apply Matrix.IsHermitian.reindex
  change (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)ᴴ = _
  rw [conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker, hh X,
    conjTranspose_one]

/-- Each paired term has norm at most `2 * J`.
Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.ChainInteraction.norm_doubled_term_le
    (h : ManyBody.ChainInteraction L q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : ManyBody.ChainSupport L R) : ‖h.doubled.term X‖ ≤ 2 * J := by
  change ‖Matrix.reindex (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
    (QuantumCircuit.sitePairConfigurationEquiv (Fin L) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)‖ ≤ 2 * J
  rw [Matrix.l2_opNorm_reindex_equiv]
  calc
    _ ≤ ‖h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)‖ +
        ‖(1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X‖ := norm_add_le _ _
    _ ≤ ‖h.term X‖ + ‖h.term X‖ :=
      add_le_add (Matrix.l2_opNorm_kronecker_one_le _)
        (Matrix.l2_opNorm_one_kronecker_le _)
    _ ≤ J + J := add_le_add (hhJ X) (hhJ X)
    _ = 2 * J := by ring

''')

# --- the chain swapped doubling
cut(M + 'SwappedDoubledHamiltonian.lean', '/-- The doubled interactions conjugated by the regional sheet swap.',
    '/-- The sum of the swapped interactions is the conjugate of the doubled operator.', '''/-- The doubled interactions conjugated by the regional sheet swap.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
noncomputable def _root_.ManyBody.ChainInteraction.swappedDoubled
    {L q R : ℕ} (h : ManyBody.ChainInteraction L q R) (D : Finset (Fin L)) :
    ManyBody.ChainInteraction L (q * q) R where
  term X :=
    let e := sitePairConfigurationEquiv (Fin L) q q
    let F := Matrix.reindex e e (sheetSwapOp q D)
    F * h.doubled.term X * Fᴴ
  mem X := by
    exact reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
      D X.1 (h.mem X)

/-- The swapped doubled terms of Hermitian terms are Hermitian.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_swappedDoubled_term {L q R : ℕ}
    (h : ManyBody.ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin L)) (X : ManyBody.ChainSupport L R) :
    ((h.swappedDoubled D).term X).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (h.isHermitian_doubled_term hh X)

/-- Each swapped doubled term has norm at most `2 * J`.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.ChainInteraction.norm_swappedDoubled_term_le {L q R : ℕ} {J : ℝ}
    (h : ManyBody.ChainInteraction L q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin L)) (X : ManyBody.ChainSupport L R) :
    ‖(h.swappedDoubled D).term X‖ ≤ 2 * J := by
  let e := sitePairConfigurationEquiv (Fin L) q q
  let F := Matrix.reindex e e (sheetSwapOp q D)
  have hF : ‖F‖ ≤ 1 := by
    simpa only [F, Matrix.l2_opNorm_reindex_equiv] using norm_sheetSwapOp_le_one (q := q) D
  have hFadj : ‖Fᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hF
  change ‖F * h.doubled.term X * Fᴴ‖ ≤ 2 * J
  simpa only [one_mul, mul_one] using
    norm_mul_le_of_le (norm_mul_le_of_le hF (h.norm_doubled_term_le hhJ X)) hFadj

''')

# --- the domain doubling and swapped doubling
cut(M + 'DomainPartialSwap.lean', '/-- Two replicas of the original domain interactions, paired at each actual site.',
    '/-- Summing the original doubled terms gives exactly the paired two-copy operator.', '''/-- Two replicas of the original domain interactions, paired at each actual site.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. This definition
preserves the actual domain supports and asserts no ground-state or reset conclusion. -/
noncomputable def _root_.ManyBody.DomainInteraction.doubled (h : ManyBody.DomainInteraction Λ q R) :
    ManyBody.DomainInteraction Λ (q * q) R where
  term X := Matrix.reindex (sitePairConfigurationEquiv (Fin Λ.card) q q)
    (sitePairConfigurationEquiv (Fin Λ.card) q q)
      (h.term X ⊗ₖ 1 + 1 ⊗ₖ h.term X)
  mem X := by
    have hs := h.toChain.doubled.mem X.toChainSupport
    simp only [ManyBody.ChainInteraction.doubled, ManyBody.DomainInteraction.toChain_term] at hs
    simpa only [DomainSupport.toChainSupport] using hs

/-- The paired domain terms of Hermitian terms are Hermitian.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.DomainInteraction.isHermitian_doubled_term
    (h : ManyBody.DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
    (X : DomainSupport Λ R) : (h.doubled.term X).IsHermitian := by
  simpa only [ManyBody.DomainInteraction.doubled, ManyBody.ChainInteraction.doubled,
    ManyBody.DomainInteraction.toChain_term] using
    h.toChain.isHermitian_doubled_term (h.isHermitian_toChain_term hh) X.toChainSupport

/-- Each paired domain term has norm at most `2 * J`.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–360. -/
theorem _root_.ManyBody.DomainInteraction.norm_doubled_term_le
    (h : ManyBody.DomainInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : DomainSupport Λ R) : ‖h.doubled.term X‖ ≤ 2 * J := by
  simpa only [ManyBody.DomainInteraction.doubled, ManyBody.ChainInteraction.doubled,
    ManyBody.DomainInteraction.toChain_term] using
    h.toChain.norm_doubled_term_le
      (h.norm_toChain_term_le hhJ (norm_bound_nonneg_of_support h hhJ X)) X.toChainSupport

''')
cut(M + 'DomainPartialSwap.lean', '/-- Conjugate each original doubled domain interaction by the actual regional swap.',
    '/-- The sum of the original swapped interactions is the conjugated doubled operator.', '''/-- Conjugate each original doubled domain interaction by the actual regional swap.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
noncomputable def _root_.ManyBody.DomainInteraction.swappedDoubled
    (h : ManyBody.DomainInteraction Λ q R) (D : Finset (Fin Λ.card)) :
    ManyBody.DomainInteraction Λ (q * q) R where
  term X :=
    let e := sitePairConfigurationEquiv (Fin Λ.card) q q
    let F := Matrix.reindex e e (TNLean.Lattice.sheetSwapOp q D)
    F * h.doubled.term X * Fᴴ
  mem X := by
    exact (TNLean.Lattice.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
        D X.1 (h.mem X))

/-- The swapped doubled domain terms of Hermitian terms are Hermitian.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.DomainInteraction.isHermitian_swappedDoubled_term
    (h : ManyBody.DomainInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
    (D : Finset (Fin Λ.card)) (X : DomainSupport Λ R) :
    ((h.swappedDoubled D).term X).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (h.isHermitian_doubled_term hh X)

/-- Each swapped doubled domain term has norm at most `2 * J`.
Source: TNLean note, `part2a_mps_information.tex`, lines 355–363. -/
theorem _root_.ManyBody.DomainInteraction.norm_swappedDoubled_term_le
    (h : ManyBody.DomainInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin Λ.card)) (X : DomainSupport Λ R) :
    ‖(h.swappedDoubled D).term X‖ ≤ 2 * J := by
  simpa only [ManyBody.DomainInteraction.swappedDoubled, ManyBody.ChainInteraction.swappedDoubled,
    ManyBody.ChainInteraction.doubled, ManyBody.DomainInteraction.toChain_term,
    ManyBody.DomainInteraction.doubled] using
    (h.toChain.norm_swappedDoubled_term_le
      (h.norm_toChain_term_le hhJ (norm_bound_nonneg_of_support h hhJ X)) D X.toChainSupport)

''')
sub(M + 'DomainPartialSwap.lean', """private theorem norm_bound_nonneg_of_support (h : DomainHamiltonian Λ q R J)
    (X : DomainSupport Λ R) : 0 ≤ J :=
  h.norm_bound_nonneg (Classical.choose X.2.1)""", """private theorem norm_bound_nonneg_of_support (h : ManyBody.DomainInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (X : DomainSupport Λ R) : 0 ≤ J :=
  h.norm_bound_nonneg hhJ (Classical.choose X.2.1)""")

# --- rescaling
cut(M + 'Hastings/ProjectorFactorizationScaling.lean', '/-- **Rescaling a chain Hamiltonian.**',
    'theorem smul_operator', '''/-- **Rescaling a chain interaction.** The terms `c h_X` form a chain interaction of the
same range. -/
noncomputable def _root_.ManyBody.ChainInteraction.smul (h : ManyBody.ChainInteraction L q R)
    (c : ℝ) : ManyBody.ChainInteraction L q R where
  term X := (c : ℂ) • h.term X
  mem X := (ManyBody.supportedOperators (fun _ : Fin L ↦ Fin q) _).smul_mem (h.mem X) _

/-- Real multiples of Hermitian terms are Hermitian. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_smul_term
    (h : ManyBody.ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian) (c : ℝ)
    (X : ManyBody.ChainSupport L R) : ((h.smul c).term X).IsHermitian :=
  (hh X).smul (by simp [IsSelfAdjoint, Complex.conj_ofReal])

/-- For `c ≥ 0`, the rescaled terms have norm at most `c J`. -/
theorem _root_.ManyBody.ChainInteraction.norm_smul_term_le
    (h : ManyBody.ChainInteraction L q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J) (c : ℝ) (hc : 0 ≤ c)
    (X : ManyBody.ChainSupport L R) : ‖(h.smul c).term X‖ ≤ c * J := by
  change ‖(c : ℂ) • h.term X‖ ≤ c * J
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hhJ X) hc

''')
sub(M + 'Hastings/ProjectorFactorizationScaling.lean', """theorem smul_operator (h : ChainHamiltonian L q R J) (c : ℝ) (hc : 0 ≤ c) :
    (h.smul c hc).operator = (c : ℂ) • h.operator := by
  simp only [operator, smul, Finset.smul_sum]

end ChainHamiltonian""", """theorem _root_.ManyBody.ChainInteraction.smul_hamiltonian (h : ManyBody.ChainInteraction L q R)
    (c : ℝ) : (h.smul c).hamiltonian = (c : ℂ) • h.hamiltonian := by
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.ChainInteraction.smul, Finset.smul_sum]

end ChainHamiltonian""")

# --- bond families: the interaction needs only the supports; positivity and the bound give the
# two former fields
V = M + 'ViableSet/PowerProjector.lean'
cut(V, '/-- A family of bond terms `H_i`, supported on `{i, i + 1}` with `0 ≤ H_i ≤ 1`, as a range-one',
    '/-- The Hamiltonian of `ChainHamiltonian.ofBonds` is the sum of the bond terms. -/', '''/-- A family of bond terms `H_i`, supported on `{i, i + 1}`, as a range-one chain interaction.
The term at the support `{i, i + 1}` is `H_i`, and the single-site terms vanish. With
`0 ≤ H_i ≤ 1` this is the Hamiltonian of Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, lines 209–211 and 283, of interaction norm at most one. -/
noncomputable def _root_.ManyBody.ChainInteraction.ofBonds
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2))) :
    ManyBody.ChainInteraction L q 1 where
  term X := ∑ i, if bondSupport i = X then h i else 0
  mem X := (ManyBody.supportedOperators (fun _ : Fin L ↦ Fin q) _).sum_mem fun i _ ↦ by
    split_ifs with hX
    · rw [← hX]
      exact hs i
    · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩

/-- The terms of positive semidefinite bonds are Hermitian. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_ofBonds_term
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (h0 : ∀ i, (h i).PosSemidef) (X : ChainSupport L 1) :
    ((ManyBody.ChainInteraction.ofBonds h hs).term X).IsHermitian :=
  (posSemidef_sum_bondSupport_ite h h0 X).isHermitian

/-- The terms of bonds with `0 ≤ H_i ≤ 1` have norm at most one. -/
theorem _root_.ManyBody.ChainInteraction.norm_ofBonds_term_le
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i) (interval L i (i + 2)))
    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) (X : ChainSupport L 1) :
    ‖(ManyBody.ChainInteraction.ofBonds h hs).term X‖ ≤ 1 := by
  classical
  let S := Finset.univ.filter fun i ↦ bondSupport i = X
  have hcard : S.card ≤ 1 := Finset.card_le_one.mpr fun i hi j hj ↦
    bondSupport_injective ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  change ‖∑ i, if bondSupport i = X then h i else 0‖ ≤ 1
  rw [← Finset.sum_filter]
  calc
    ‖∑ i ∈ S, h i‖ ≤ ∑ _ ∈ S, (1 : ℝ) := norm_sum_le_of_le S fun i _ ↦
        (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i).nonneg).mpr (h1 i)
    _ ≤ 1 := by simpa using (show (S.card : ℝ) ≤ 1 by exact_mod_cast hcard)

''')
sub(V, """    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) :
    (ChainHamiltonian.ofBonds h hs h0 h1).operator = ∑ i, h i := by
  simp only [ChainHamiltonian.operator, ChainHamiltonian.ofBonds]""", """ :
    (ManyBody.ChainInteraction.ofBonds h hs).hamiltonian = ∑ i, h i := by
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.ChainInteraction.ofBonds]""")
sub(V, """    (h0 : ∀ i, (h i).PosSemidef) (h1 : ∀ i, h i ≤ 1) (X : ChainSupport L 1) :
    ((ChainHamiltonian.ofBonds h hs h0 h1).term X).PosSemidef :=""", """    (h0 : ∀ i, (h i).PosSemidef) (X : ChainSupport L 1) :
    ((ManyBody.ChainInteraction.ofBonds h hs).term X).PosSemidef :=""")

P = M + 'Huang/PositiveChainHamiltonian.lean'
cut(P, '/-- The original positive nearest-neighbor contractions, as a range-one chain Hamiltonian',
    'variable {L q : ℕ}', '''/-- The original nearest-neighbor terms as a range-one chain interaction. Original pair terms
are retained and all other terms are zero; for positive contractions its norm bound is one.
LVV13, `algo53.tex`, the local Hamiltonian assumptions; Huang, Section 5.4, Lemmas 18--19. -/
noncomputable def _root_.ManyBody.ChainInteraction.ofNearestNeighborPositive {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) : ManyBody.ChainInteraction L q 1 where
  term := Function.extend nearestNeighborChainSupport h (fun _ ↦ 0)
  mem := forall_nearestNeighborExtension h
    (fun X M ↦ Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) M X.val)
    (fun X ↦ zero_mem (ManyBody.supportedOperators (fun _ : Fin L ↦ Fin q) X.val)) hs

/-- The terms of positive nearest-neighbor terms are Hermitian. -/
theorem _root_.ManyBody.ChainInteraction.isHermitian_ofNearestNeighborPositive_term {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) :
    ∀ X, ((ManyBody.ChainInteraction.ofNearestNeighborPositive h hs).term X).IsHermitian :=
  forall_nearestNeighborExtension h (fun _ M ↦ M.IsHermitian)
    (fun _ ↦ isHermitian_zero)
    (fun i ↦ (IsSelfAdjoint.of_nonneg (h0 i)).isHermitian)

/-- The terms of positive contractions have norm at most one. -/
theorem _root_.ManyBody.ChainInteraction.norm_ofNearestNeighborPositive_term_le {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    ∀ X, ‖(ManyBody.ChainInteraction.ofNearestNeighborPositive h hs).term X‖ ≤ 1 :=
  forall_nearestNeighborExtension h (fun _ M ↦ ‖M‖ ≤ 1) (fun _ ↦ by simp)
    (fun i ↦ (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i))

''')
S = M + 'Hastings/ProjectorFactorizationScaling.lean'
sub(S, "namespace ChainHamiltonian\n\n", "")
sub(S, "\nend ChainHamiltonian\n", "\n")

# ===================== phase 2b: the lattice interactions =====================
LH = 'TNLean/Lattice/LocalHamiltonian.lean'
cut(LH, '/-- One bounded Hermitian operator per nonempty admissible support.',
    'end TNLean.Lattice', '')
sub(LH, """The interaction family has one term for each nonempty support of bounded
induced-graph diameter. A term may be zero.""", """A finite-range Hamiltonian is an interaction `ManyBody.PlaneInteraction Λ q R`, with one term
for each nonempty support of bounded induced-graph diameter, whose terms are Hermitian and of
norm at most `J`; both are hypotheses of the statements that use them. A term may be zero.""")
sub(LH, """* `LocalHamiltonian`: the bounded Hermitian interaction family.
* `LocalHamiltonian.operator`: its finite sum.
""", """* `StateSpace`: the physical Hilbert space in configuration coordinates.
""")
sub(LH, "import Mathlib.Analysis.CStarAlgebra.Matrix\n",
    "import Mathlib.Analysis.CStarAlgebra.Matrix\nimport QICLean.ManyBody.Hamiltonian.Models\n")

RH = 'TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean'
cut(RH, '/-- The rectangular interaction, with Hermitian parts at its actual range-one supports and',
    '/-- The original unit ground vector and full-system gap are preserved by the actual', '''/-- The rectangular interaction as a range-one interaction on the integer rectangle, with the
Hermitian parts at its actual range-one supports and zero at unused supports.
Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
def toAreaLawHamiltonian (Φ : RectangleInteraction width height q) :
    ManyBody.PlaneInteraction (rectangularDomain width height) q 1 where
  term := Function.extend (rectangleAreaLawSupport width height)
    (fun i ↦ Matrix.reindex (rectangleConfigurationEquiv width height q)
      (rectangleConfigurationEquiv width height q) (Φ.hermitianPart.term i)) 0
  mem X := by
    classical
    by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(rectangleAreaLawSupport_injective width height).extend_apply]
      have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
        (rectangleSiteEquiv width height).injective
        (Φ.hermitianPart.mem i)
      rw [embedOp_rectangular_eq_reindex] at hs
      simpa only [rectangleAreaLawSupport, Finset.coe_image] using hs
    · rw [Function.extend_apply' _ _ _ hx]
      exact zero_mem _

/-- The terms of the conversion are Hermitian: they are Hermitian parts or zero.
Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem isHermitian_toAreaLawHamiltonian_term (Φ : RectangleInteraction width height q)
    (X : ManyBody.AdmissibleSupport (rectangularDomain width height) 1) :
    (Φ.toAreaLawHamiltonian.term X).IsHermitian := by
  classical
  change (Function.extend (rectangleAreaLawSupport width height)
    (fun i ↦ Matrix.reindex (rectangleConfigurationEquiv width height q)
      (rectangleConfigurationEquiv width height q) (Φ.hermitianPart.term i)) 0 X).IsHermitian
  by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
  · obtain ⟨i, rfl⟩ := hx
    rw [(rectangleAreaLawSupport_injective width height).extend_apply]
    exact (Φ.isHermitian_hermitianPart_term i).submatrix _
  · rw [Function.extend_apply' _ _ _ hx]
    exact Matrix.isHermitian_zero

/-- The terms of the conversion keep the bound `J`, for every real `J`: each unused admissible
support is nonempty, so one of its sites supplies the nonnegative bound needed for its zero
term. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem norm_toAreaLawHamiltonian_term_le (Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (X : ManyBody.AdmissibleSupport (rectangularDomain width height) 1) :
    ‖Φ.toAreaLawHamiltonian.term X‖ ≤ J := by
  classical
  let e := rectangleConfigurationEquiv width height q
  change ‖Function.extend (rectangleAreaLawSupport width height)
    (fun i ↦ Matrix.reindex e e (Φ.hermitianPart.term i)) 0 X‖ ≤ J
  by_cases hx : ∃ i, rectangleAreaLawSupport width height i = X
  · obtain ⟨i, rfl⟩ := hx
    rw [(rectangleAreaLawSupport_injective width height).extend_apply]
    exact (Matrix.l2_opNorm_reindex_equiv e (Φ.hermitianPart.term i)).le.trans
      ((Φ.norm_hermitianPart_term_le i).trans (hΦ i))
  · rw [Function.extend_apply' _ _ _ hx]
    obtain ⟨v, _⟩ := X.property.1
    simpa only [Pi.zero_apply, norm_zero] using
      (norm_nonneg _).trans (hΦ (.inl ((rectangleSiteEquiv width height).symm v)))

/-- For a Hermitian total, the interaction conversion has exactly the transported original
sum. Source: area-law Corollary 1.2 and polynomial-PEPS `eq:model`. -/
theorem toAreaLawHamiltonian_hamiltonian (Φ : RectangleInteraction width height q)
    (hH : Φ.hamiltonian.IsHermitian) :
    Φ.toAreaLawHamiltonian.hamiltonian =
      Matrix.reindex (rectangleConfigurationEquiv width height q)
        (rectangleConfigurationEquiv width height q) Φ.hamiltonian := by
  classical
  let e := rectangleConfigurationEquiv width height q
  let T := fun i : SquareLatticeSiteOrEdge width height =>
    Matrix.reindex e e (Φ.hermitianPart.term i)
  let f := Function.extend (rectangleAreaLawSupport width height) T 0
  have hsum : (∑ i : SquareLatticeSiteOrEdge width height, T i) =
      ∑ X : ManyBody.AdmissibleSupport (rectangularDomain width height) 1, f X := by
    apply Finset.sum_of_injOn (rectangleAreaLawSupport width height)
      (rectangleAreaLawSupport_injective width height).injOn (fun _ _ => Finset.mem_univ _)
    · intro X _ hX
      exact Function.extend_apply' _ _ _ (by simpa using hX)
    · intro i _
      exact ((rectangleAreaLawSupport_injective width height).extend_apply T 0 i).symm
  change (∑ X, f X) = _
  rw [← hsum]
  change (∑ i : SquareLatticeSiteOrEdge width height,
    (Matrix.reindexAlgEquiv ℂ ℂ e) (Φ.hermitianPart.term i)) = _
  rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e)]
  change (Matrix.reindexAlgEquiv ℂ ℂ e) Φ.hermitianPart.hamiltonian = _
  rw [Φ.hamiltonian_hermitianPart hH]
  rfl

''')
s = open(RH).read()
i = s.index('theorem isGapped_toAreaLawHamiltonian')
j = s.index('end ManyBody.RectangleInteraction')
t = s[i:j]
t = t.replace("""(Φ : RectangleInteraction width height q)
    (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (hH : Φ.hamiltonian.IsHermitian)""", """(Φ : RectangleInteraction width height q)
    (hH : Φ.hamiltonian.IsHermitian)""")
t = t.replace("(Φ.toAreaLawHamiltonian hΦ).operator", "Φ.toAreaLawHamiltonian.hamiltonian")
t = t.replace("Φ.toAreaLawHamiltonian_operator hΦ hH", "Φ.toAreaLawHamiltonian_hamiltonian hH")
open(RH, 'w').write(s[:i] + t + s[j:])

# lemmas declared in the namespace of the structure move to the namespace of the interaction
import glob, re as _re
for p in glob.glob('TNLean/**/*.lean', recursive=True):
    s = open(p).read(); t = s
    t = _re.sub(r"^namespace TNLean\.Lattice\.LocalHamiltonian$",
                "namespace ManyBody.PlaneInteraction\n\nopen TNLean.Lattice", t, flags=_re.M)
    t = _re.sub(r"^end TNLean\.Lattice\.LocalHamiltonian$", "end ManyBody.PlaneInteraction", t, flags=_re.M)
    if t != s:
        open(p, 'w').write(t)
SL = 'TNLean/PEPS/Approximation/SwappedLocalHamiltonian.lean'
sub(SL, "\nnamespace LocalHamiltonian\n", """
end TNLean.Lattice

namespace ManyBody.PlaneInteraction

open TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
""")
sub(SL, "\nend LocalHamiltonian\n\nend TNLean.Lattice\n", "\nend ManyBody.PlaneInteraction\n")
cut(SL, '/-- **The partially swapped doubled Hamiltonian at range `R`.**',
    '/-- The doubling map is additive. -/', '''/-- **The partially swapped doubled interaction at range `R`.** Its term at a support `X` is
the doubled term of `h` at `X`, in paired-site coordinates, conjugated by the swap of the two
replicas on `A`. It is an interaction of range `R` with local dimension `q²`.
Source: polynomial-PEPS `02-information.tex`, lines 416–424, at range `R`. -/
def swappedDoubled (h : ManyBody.PlaneInteraction Λ q R) (A : Finset (Site Λ)) :
    ManyBody.PlaneInteraction Λ (q * q) R where
  term X :=
    Matrix.reindex (sitePairConfigurationEquiv (Site Λ) q q)
        (sitePairConfigurationEquiv (Site Λ) q q) (sheetSwapOp q A) *
      Matrix.reindex (sitePairConfigurationEquiv (Site Λ) q q)
        (sitePairConfigurationEquiv (Site Λ) q q) (doubledHamiltonian (h.term X)) *
      (Matrix.reindex (sitePairConfigurationEquiv (Site Λ) q q)
        (sitePairConfigurationEquiv (Site Λ) q q) (sheetSwapOp q A))ᴴ
  mem X :=
    reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators A X.1 (h.mem X)

/-- The swapped doubled terms of Hermitian terms are Hermitian.
Source: polynomial-PEPS `02-information.tex`, lines 416–424, at range `R`. -/
theorem isHermitian_swappedDoubled_term (h : ManyBody.PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian) (A : Finset (Site Λ)) (X : AdmissibleSupport Λ R) :
    ((h.swappedDoubled A).term X).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _
    ((doubledHamiltonian_isHermitian (hh X)).reindex _)

/-- Each swapped doubled term has norm at most `2 * J`.
Source: polynomial-PEPS `02-information.tex`, lines 416–424, at range `R`. -/
theorem norm_swappedDoubled_term_le (h : ManyBody.PlaneInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (A : Finset (Site Λ)) (X : AdmissibleSupport Λ R) :
    ‖(h.swappedDoubled A).term X‖ ≤ 2 * J := by
  set p := sitePairConfigurationEquiv (Site Λ) q q
  set F := Matrix.reindex p p (sheetSwapOp q A)
  have hFn : ‖F‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv p (sheetSwapOp q A)).le.trans
      (norm_sheetSwapOp_le_one A)
  have hDn : ‖doubledHamiltonian (h.term X)‖ ≤ J + J :=
    (norm_add_le _ _).trans (add_le_add
      ((Matrix.l2_opNorm_kronecker_one_le _).trans (hhJ X))
      ((Matrix.l2_opNorm_one_kronecker_le _).trans (hhJ X)))
  change ‖F * Matrix.reindex p p (doubledHamiltonian (h.term X)) * Fᴴ‖ ≤ 2 * J
  simpa only [one_mul, mul_one, two_mul] using
    norm_mul_le_of_le
      (norm_mul_le_of_le hFn ((Matrix.l2_opNorm_reindex_equiv p _).le.trans hDn))
      ((Matrix.l2_opNorm_conjTranspose F).trans_le hFn)

''')
# the sums of the swapped construction are Hamiltonians; the block left the `TNLean` namespace
s = open(SL).read()
s = s.replace("theorem swappedDoubled_operator (", "theorem swappedDoubled_hamiltonian (")
s = s.replace("theorem sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing (",
              "theorem sheetSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing (")
s = s.replace("(h.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing A)",
              "(h.sheetSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing A)")
s = s.replace("h.swappedDoubled_operator A", "h.swappedDoubled_hamiltonian A")
s = re.sub(r"(?<![\w.])PEPS\.(AreaLaw|EncodedFrame)\.", r"TNLean.PEPS.\1.", s)
open(SL, 'w').write(s)
for p in ('TNLean/PEPS/Approximation/RangeResetUnitary.lean', 'TNLean/PEPS/Approximation/RangeInformationReset.lean',
          'TNLean/PEPS/Approximation/SwappedDoubledEdgeBoundary.lean', 'TNLean/PEPS/AreaLaw/GraphPropagation.lean'):
    s = open(p).read()
    i = s.find("namespace ManyBody.PlaneInteraction")
    if i >= 0:
        s = s[:i] + re.sub(r"(?<![\w.])PEPS\.(AreaLaw|EncodedFrame|Approximation)\.", r"TNLean.PEPS.\1.", s[i:])
        open(p, 'w').write(s)
