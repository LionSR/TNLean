"""Hand fixes before the threading pass, which then passes the hypotheses."""
def sub(p, a, b):
    s = open(p).read(); assert a in s, (p, a[:70]); open(p, 'w').write(s.replace(a, b))
# the bound `0 ≤ J` comes from a site, not from a hypothesis
sub('TNLean/MPS/AreaLaw/DomainInteractionBudget.lean', '((h.toChain).sum_norm_terms_containing_le x)',
    '((h.toChain).sum_norm_terms_containing_le\n'
    '        (h.norm_toChain_term_le hhJ (h.norm_bound_nonneg x)) x)')
