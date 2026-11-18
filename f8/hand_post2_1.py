"""Hand fixes after the threading pass."""
def sub(p, a, b):
    s = open(p).read(); assert a in s, (p, a[:70]); open(p, 'w').write(s.replace(a, b))
# the bound `0 ≤ J` comes from a site of the support
sub('TNLean/MPS/AreaLaw/DomainPartialSwap.lean', """(h.toChain).partialSwap_term_difference_spec (h.isHermitian_toChain_term hh)
        (h.norm_toChain_term_le hhJ hJ)""", """(h.toChain).partialSwap_term_difference_spec (h.isHermitian_toChain_term hh)
        (h.norm_toChain_term_le hhJ (norm_bound_nonneg_of_support h hhJ X))""")
# calls through local hypotheses, and with named arguments, that the threading pass does not reach
import re
for p, a in (('TNLean/MPS/AreaLaw/Hastings/ProjectorFactorizationScaling.lean', 'exact hF (h.smul ΔE⁻¹) hΩ'),
             ('TNLean/MPS/AreaLaw/Hastings/LemmaOneConstant.lean', '    (h.smul ΔE⁻¹) hΩ')):
    sub(p, a, a.replace('(h.smul ΔE⁻¹) hΩ', '(h.smul ΔE⁻¹) (h.isHermitian_smul_term hh ΔE⁻¹)\n'
        '      (h.norm_smul_term_le hhJ ΔE⁻¹ (inv_nonneg.mpr hΔ.le)) hΩ'))
