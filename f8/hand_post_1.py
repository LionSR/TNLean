"""Hand fixes after the phase-2 builds: calls of local hypotheses quantified over interactions."""
def sub(p, a, b):
    s = open(p).read(); assert a in s, (p, a[:70]); open(p, 'w').write(s.replace(a, b))
M = 'TNLean/MPS/AreaLaw/'
sub(M + 'MPSApproximation.lean', 'harea L h hwindow', 'harea L h hh hhJ hwindow')
sub(M + 'LogarithmicAreaLaw.lean', 'hchain q R J Δ hq hJ hΔ Λ.card (h.toChain)\n',
    'hchain q R J Δ hq hJ hΔ Λ.card (h.toChain) (h.isHermitian_toChain_term hh)\n    (h.norm_toChain_term_le hhJ hJ)\n')
sub(M + 'LogarithmicAreaLaw.lean', 'hbound L h hwindow', 'hbound L h hh hhJ hwindow')
P = M + 'Huang/PositiveChainHamiltonian.lean'
s = open(P).read()
import re
i = s.index('variable {L q : ℕ}\n    (h : Fin (L - 1)')
head, tail = s[:i], s[i:]
tail = re.sub(r"(?<![\w.])(ofNearestNeighborPositive(?:_\w+)?)\b", r"ManyBody.ChainInteraction.\1", tail)
tail = tail.replace("theorem _root_.ManyBody.ChainInteraction.ManyBody.ChainInteraction.", "theorem _root_.ManyBody.ChainInteraction.")
for name, hyp in (('nonneg', 'h0'), ('le_one', 'h1')):
    tail = re.sub(rf"(/--(?:(?!-/).)*-/\ntheorem _root_\.ManyBody\.ChainInteraction\.ofNearestNeighborPositive_term_{name}\b)",
                  rf"include {hyp} in\n\1", tail, flags=re.S)
open(P, 'w').write(head + tail)

s = open(P).read()
s = s.replace('ofNearestNeighborPositive_term h hs h0 h1 i', 'ofNearestNeighborPositive_term h hs i')
open(P, 'w').write(s)
# local hypotheses quantified over interactions
s = open(M + 'Hastings/LemmaOneConstant.lean').read()
s = s.replace('hF hJ hΔ h hΩ hgap hspan c l', 'hF hJ hΔ h hh hhJ hΩ hgap hspan c l')
open(M + 'Hastings/LemmaOneConstant.lean', 'w').write(s)
# the local hypothesis `hF` of the Hastings factorization, quantified over interactions
import glob
for p in glob.glob(M + 'Hastings/*.lean'):
    s = open(p).read()
    n = re.sub(r"\bhF hJ hΔ h hΩ\b", "hF hJ hΔ h hh hhJ hΩ", s)
    if n != s:
        open(p, 'w').write(n)
# the second section opens the norm scope of its own
s = open(M + 'Hastings/RenyiBootstrapLemma.lean').read()
s = s.replace("open Hastings Matrix TNLean.Lattice\nopen ManyBody (IsGapped groundSpace)\nopen scoped InnerProductSpace ComplexOrder\n",
              "open Hastings Matrix TNLean.Lattice\nopen ManyBody (IsGapped groundSpace)\nopen scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator\n")
open(M + 'Hastings/RenyiBootstrapLemma.lean', 'w').write(s)
# the family of all instances: the two hypotheses join the subtype condition after `L₀ ≤ L`
P = M + 'ProtocolUniformPreparation.lean'
sub(P, 'i.val.2.1 (ground i) i.val.2.2.2 i.property.2.1 i.property.2.2.1 i.property.2.2.2',
    'i.val.2.1 i.property.2.1 i.property.2.2.1 (ground i) i.val.2.2.2 i.property.2.2.2.1\n'
    '      i.property.2.2.2.2.1 i.property.2.2.2.2.2')
sub(P, '        i.property.2.1\n  · rw [outerProduct_mainCoordinates]', '        i.property.2.2.2.1\n  · rw [outerProduct_mainCoordinates]')
# the proof introduces the statement's own family instead of restating it, which keeps the
# elaboration within the default budget now that each instance carries two more conjuncts
s = open(P).read()
i = s.index("  refine ⟨D, K, s, L₀, hL₀, hD, hK, ?_⟩\n  let ι :=")
j = s.index("  have hfamily", i)
s = s[:i] + "  refine ⟨D, K, s, L₀, hL₀, hD, hK, ?_⟩\n  intro ι length width ground hL Fs holder H\n" + s[j:]
open(P, 'w').write(s)
sub(M + 'ProtocolMPSApproximation.lean', 'let i : ι := ⟨⟨L, h, Ω, E₀⟩, hlarge, hΩ, hgap, hspan⟩',
    'let i : ι := ⟨⟨L, h, Ω, E₀⟩, hlarge, hh, hhJ, hΩ, hgap, hspan⟩')
# the simp lemmas the renaming duplicated, and the bound that the domain windows no longer need
# the interaction is now the chain interaction itself, so only the velocity goal remains
sub(M + 'Hastings/LiebRobinson.lean',
    "convert hBound using 1 <;>\n    simp only [Φ, ManyBody.Interaction.hamiltonian, ManyBody.Interaction.hamiltonian,\n        chainLRVelocity,",
    "convert hBound using 1\n  simp only [chainLRVelocity,")
# module docstrings naming the deleted structures
sub(M + 'ComponentReduction.lean',
    "* `DomainHamiltonian`: admissible Hamiltonians, one term for each support of range `R` in\n"
    "  the sense of `ManyBody.IsDomainSupport`.\n",
    "* `ManyBody.DomainInteraction.toChain`: an interaction on `Λ`, one term for each support of\n"
    "  range `R` in the sense of `ManyBody.IsDomainSupport`, as an interaction on the chain.\n")
sub(M + 'WindowCounting.lean', "the three theorems about `ChainHamiltonian` in\nthis module",
    "the three theorems about chain interactions in\nthis module")
