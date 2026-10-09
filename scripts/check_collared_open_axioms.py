#!/usr/bin/env python3
"""Reject missing or nonstandard axiom audits in the strict collared-open check."""
import re
import sys
from pathlib import Path

REQUIRED = {
    'TNLean.PEPS.DependentBondNetwork.network_deltaCompletedTensor',
    'TNLean.PEPS.labelledNetwork_eq_torusBondNetwork',
    'TNLean.PEPS.torusBondNetwork_deltaCompletedTensor',
    'TNLean.PEPS.TorusDualCollar.neighbors_mem',
    'TNLean.PEPS.TorusDualCollar.exists_internalFluxGauge',
    'TNLean.PEPS.TorusDualCollar.openCoefficient_eq',
    'TNLean.PEPS.TorusDualCollar.correlatedBoundary_eq',
    'TNLean.PEPS.torusOpenCoefficient_eq_zero_of_isEmpty',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def check(text):
    found = {}
    for name, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text):
        if name in REQUIRED:
            axioms = {a.strip() for a in names.split(',') if a.strip()}
            if axioms - ALLOWED:
                raise ValueError(f'{name}: unexpected axioms {sorted(axioms - ALLOWED)}')
            found[name] = axioms
    if REQUIRED - found.keys():
        raise ValueError(f'missing audits: {sorted(REQUIRED - found.keys())}')


def self_test():
    valid = '\n'.join(f"'{name}' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
                      for name in sorted(REQUIRED))
    check(valid)
    for invalid in [valid.replace('propext', 'sorryAx', 1),
                    valid.replace('Quot.sound', 'untrustedAxiom', 1), '',
                    valid.replace(sorted(REQUIRED)[0], 'unrelated')]:
        try:
            check(invalid)
        except ValueError:
            continue
        raise AssertionError('accepted missing or nonstandard axiom audit')


if __name__ == '__main__':
    self_test()
    if len(sys.argv) > 1:
        check(Path(sys.argv[1]).read_text())
    print('PASS: collared-open axiom guard')
