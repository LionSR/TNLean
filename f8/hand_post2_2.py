"""F8 phase 2b, hand part after threading: existential families of lattice interactions,
the definitions whose value depends on the former bound `J`, and calls of statements whose
universal quantifier over the interaction now also quantifies over its two hypotheses."""
import glob, re
P = 'TNLean/PEPS/'


def sub(p, a, b, count=None):
    s = open(p).read(); assert a in s, (p, a[:70])
    if count is not None:
        assert s.count(a) == count, (p, a[:70], s.count(a))
    open(p, 'w').write(s.replace(a, b))


def soft(p, a, b):
    """A replacement that the threading may already have made."""
    s = open(p).read(); open(p, 'w').write(s.replace(a, b))


HYPS = "(_ : ∀ X, ({v}.term X).IsHermitian) (_ : ∀ X, ‖{v}.term X‖ ≤ J)"
# --- existential families: the interaction comes with its two hypotheses
IB = P + 'AreaLaw/InitialBoxEstimate.lean'
for p in (IB, P + 'AreaLaw/SafeRectangleAreaLaw.lean', P + 'AreaLaw/Scan/BoxEntropySupremum.lean'):
    soft(p, "⟨Λ, h, E₀, Ω, A, Q,", "⟨Λ, h, hh, hhJ, E₀, Ω, A, Q,")
soft(IB, "regionalEntropy_le_boxEntropy hq h hΩ", "regionalEntropy_le_boxEntropy hq h hh hhJ hΩ")
soft(IB, "(fun _ h _ _ hΩ hgap hspan _ _ hsafe _ hr _ hQ₀ hpad ↦\n"
        "      condEntropy_le_initialBufferConst q R hq hJ hΔ hD₀ h hΩ",
    "(fun _ h hh hhJ _ _ hΩ hgap hspan _ _ hsafe _ hr _ hQ₀ hpad ↦\n"
    "      condEntropy_le_initialBufferConst q R hq hJ hΔ hD₀ h hh hhJ hΩ")
RG = P + 'Approximation/RangeSquareGroundState.lean'
sub(RG, "obtain ⟨_, _, hgap⟩ := hΩ", "obtain ⟨_, _, _, _, hgap⟩ := hΩ")
sub(RG, "exact ⟨h.toAreaLawHamiltonian, E₀,",
    "exact ⟨h.toAreaLawHamiltonian, h.isHermitian_toAreaLawHamiltonian_term,\n"
    "    h.norm_toAreaLawHamiltonian_term_le hhJ, E₀,")
# --- the rectangular interaction placed on the lattice, passed to a statement over all of them
soft(P + 'Approximation/SquareAreaLawSpecialization.lean',
    "hbound (AreaLaw.rectangularDomain L L) h.toAreaLawHamiltonian E₀",
    "hbound (AreaLaw.rectangularDomain L L) h.toAreaLawHamiltonian\n"
    "    h.isHermitian_toAreaLawHamiltonian_term (h.norm_toAreaLawHamiltonian_term_le hhJ) E₀")
soft(P + 'AreaLaw/RectangularSpecialization.lean',
    "hbound (rectangularDomain width height) h.toAreaLawHamiltonian E₀",
    "hbound (rectangularDomain width height) h.toAreaLawHamiltonian\n"
    "    h.isHermitian_toAreaLawHamiltonian_term (h.norm_toAreaLawHamiltonian_term_le hΦ) E₀")
sub(RG, "fun L Ω ⟨H, E₀, hΩ, hgap, hspan⟩ A ↦", "fun L Ω ⟨H, hH, hHJ, E₀, hΩ, hgap, hspan⟩ A ↦")
# --- statements quantifying over the interaction
soft(P + 'AreaLaw/Amplification/TypicalProjectors.lean', "hn) Λ h E₀ Ω", "hn) Λ h hh hhJ E₀ Ω")
AC = P + 'AreaLaw/AmplificationCutClearance.lean'
sub(AC, "fun n hn2 hn Λ hH E₀ Ω", "fun n hn2 hn Λ hH hhH hhHJ E₀ Ω")
sub(AC, "(le_of_max_le_left hn) Λ hH E₀ Ω", "(le_of_max_le_left hn) Λ hH hhH hhHJ E₀ Ω")
GP = P + 'AreaLaw/GraphPropagation.lean'
soft(GP, "h.normBound_nonneg X", "h.normBound_nonneg hhJ X")
soft(GP, "(h.sum_norm_term_containing_le (", "(h.sum_norm_term_containing_le hhJ (")
soft(GP, "(h.sum_norm_term_containing_le hJ)", "(h.sum_norm_term_containing_le hhJ hJ)")
soft(GP, "(h.norm_sub_regionExpectation_graphBall_le X", "(h.norm_sub_regionExpectation_graphBall_le hh hhJ X")
sub(P + 'AreaLaw/Scan/BoxClearanceComparison.lean', "intro Λ h E₀ Ω hΩ hgap hspan A Q hsafe hQ\n",
    "intro Λ h hh hhJ E₀ Ω hΩ hgap hspan A Q hsafe hQ\n")
sub(P + 'AreaLaw/Scan/ActualRoundEntropy.lean', "intro Λ T q R J Δ _ _ aux _ h Ω S", "intro Λ T q R J Δ _ _ aux _ h hh hhJ Ω S")
sub(P + 'AreaLaw/Scan/PhysicalBoxBootstrap.lean', "intro Λ h E₀ Ω hΩ hgap hspan A Q hsafe hQN\n",
    "intro Λ h hh hhJ E₀ Ω hΩ hgap hspan A Q hsafe hQN\n")
soft(P + 'AreaLaw/Scan/BoxClearanceComparison.lean', "regionalEntropy_le_boxEntropy hq h hΩ",
    "regionalEntropy_le_boxEntropy hq h hh hhJ hΩ")
s_ = open(P + 'AreaLaw/Scan/ActualRoundEntropy.lean').read()
s_ = re.sub(r"(actualRounds_transport_domainGraph_of_finiteFamilyTransportBound[^\n]*\n?[^\n]*?aux h) Ω", r"\1 hh hhJ Ω", s_, count=1)
open(P + 'AreaLaw/Scan/ActualRoundEntropy.lean', 'w').write(s_)
# a local positivity hypothesis `hM` read as a statement over interactions
for p in glob.glob(P + 'AreaLaw/Scan/*.lean'):
    s_ = open(p).read()
    t_ = re.sub(r"(meanEnergy_eq_globalReplicaMeanHamiltonian(?:\s+[^\s\]\)]+)*?\s+)h hh hhJ ", r"\1h ", s_)
    if t_ != s_:
        open(p, 'w').write(t_)
# calls the threading cannot read: an argument with a projection, and histories named `h`
soft(P + 'AreaLaw/SupportedGaussianIntegral.lean', "(graphBallLocalizationVelocity_nonneg R hJ) g\n",
     "(graphBallLocalizationVelocity_nonneg R hJ) g hg hgJ\n")
LC = P + 'AreaLaw/LatticeConstraints.lean'
soft(LC, "sum_norm_term_containing_le hJ)", "sum_norm_term_containing_le hhJ hJ)")
soft(LC, "PlaneInteraction.sum_norm_term_containing_le h hJ", "PlaneInteraction.sum_norm_term_containing_le h hhJ hJ")
TI = P + 'AreaLaw/Scan/ActualScanTransportInputs.lean'
soft(TI, "(fun k p h hh hhJ c ↦", "(fun k p h c ↦")
soft(TI, "(hpre k) hp h hh hhJ)", "(hpre k) hp h)")
soft(P + 'Approximation/SupportedPhysicalBufferGaussian.lean', "Λ gH K", "Λ gH hgH hgHJ K")
# a local `have h` read as the interaction, and calls whose arguments before the interaction
# include a named argument or a projection
for p in glob.glob('TNLean/**/*.lean', recursive=True):
    s_ = open(p).read()
    t_ = re.sub(r"\bat h hh hhJ\b", "at h", s_)
    if t_ != s_:
        open(p, 'w').write(t_)
soft(P + 'AreaLaw/AmplificationProof.lean', "    exact h hh hhJ\n", "    exact h\n")
soft(P + 'Approximation/RangeNestedPatchApproximation.lean', "_ H E₀ _ hgs.1", "_ H hH hHJ E₀ _ hgs.1")
CI = P + 'Approximation/CoarseInformation.lean'
soft(CI, "hnN)) Λ h E₀ Ω", "hnN)) Λ h hh hhJ E₀ Ω")
soft(CI, "hmain u hu (AreaLaw.rectangularDomain L L) h.toAreaLawHamiltonian E₀",
     "hmain u hu (AreaLaw.rectangularDomain L L) h.toAreaLawHamiltonian\n"
     "    h.isHermitian_toAreaLawHamiltonian_term (h.norm_toAreaLawHamiltonian_term_le hhJ) E₀")
soft(P + 'AreaLaw/Scan/TargetTypicalWindow.lean', "htr Λ h S E₀", "htr Λ h hh hhJ S E₀")
soft(P + 'Approximation/CellConditionalInformation.lean', "      Λ h E₀ Ω hΩ hgap hspan (P.piece i)",
     "      Λ h hh hhJ E₀ Ω hΩ hgap hspan (P.piece i)")
RI = P + 'Approximation/RangeInformationReset.lean'
soft(RI, "hLn hh hhJ hΛ E₀", "hLn hΛ hh hhJ E₀")
soft(RI, "(card_rectangularDomain L) hh hhJ.le", "(card_rectangularDomain L).le hh hhJ")
# --- the swapped square interaction: unfold the anonymous interaction before rewriting
SW = P + 'Approximation/SwappedSquareHamiltonianInteraction.lean'
s = open(SW).read()
i = s.index("mem := ?_ }, ?_, ?_, rfl, ?_⟩")
j = s.index("  · intro X\n    by_cases hx", i) + 1
s = s[:j] + s[j:].replace("  · intro X\n    by_cases hx", "  · intro X\n    dsimp only\n    by_cases hx")
open(SW, 'w').write(s)
# --- the bound `J` is a parameter of the positive constraint and of everything built on it
ET = P + 'AreaLaw/Scan/ActualEnergyTerms.lean'
sub(ET, """/-- The source positive constraint of the actual labelled interaction.
Source: `03-quasilocal.tex`, lines 250–266. -/
def _root_.ManyBody.PlaneInteraction.positiveTerm
    (h : PlaneInteraction Λ q R) (Δ : ℝ)""", """/-- The source positive constraint of the actual labelled interaction, normalized by the bound
`J` on the norms of its terms. Source: `03-quasilocal.tex`, lines 250–266. -/
def _root_.ManyBody.PlaneInteraction.positiveTerm
    (h : PlaneInteraction Λ q R) (J Δ : ℝ)""")
sub(ET, "def truncatedEnergyTerm (Δ : ℝ)", "def truncatedEnergyTerm (J Δ : ℝ)")
sub(ET, "def actualEnergyTerms (Δ : ℝ)", "def actualEnergyTerms (J Δ : ℝ)")
ARG = r"(?:\w[\w.'₀-₉⁻¹]*|\((?:[^()]|\([^()]*\))*\))"
for p in glob.glob('TNLean/**/*.lean', recursive=True):
    s = open(p).read()
    t = re.sub(rf"(\.(?:truncatedEnergyTerm|actualEnergyTerms)\s+{ARG}\s+{ARG}\s+)Δ\b", r"\1J Δ", s)
    t = re.sub(rf"(\.positiveTerm\s+)Δ\b", r"\1J Δ", t)
    if t != s:
        open(p, 'w').write(t)
# --- the Trotter product does not depend on a bound
sub('TNLean/Lattice/ProductForm.lean', "trotterProduct {R : ℕ} {J : ℝ}\n", "trotterProduct {R : ℕ}\n")
