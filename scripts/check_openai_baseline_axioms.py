#!/usr/bin/env python3
"""Fail closed unless each exact upstream regression has only standard axioms."""
import argparse
import json
from pathlib import Path
import re
from audit_openai_closure import ROOTS

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
AXIOMS = re.compile(r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")


def check(text, expected):
    results = {}
    for name, axioms, empty in AXIOMS.findall(text):
        if name not in expected:
            raise ValueError(f'unexpected axiom report: {name}')
        if name in results:
            raise ValueError(f'duplicate axiom report: {name}')
        names = [] if empty else [s.strip() for s in axioms.split(',') if s.strip()]
        rejected = set(names) - ALLOWED
        if rejected:
            raise ValueError(f'{name}: unsupported axioms {sorted(rejected)}')
        results[name] = names
    if set(results) != set(expected):
        raise ValueError(f'missing axiom reports: {sorted(set(expected)-set(results))}')
    return results


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--audit-directory', type=Path, required=True)
    a = p.parse_args()
    report_path = a.audit_directory/'result.json'
    report = json.loads(report_path.read_text())
    if report['library_build_status'] != 'passed' or report['axiom_status'] != 'command_passed_requires_review':
        raise SystemExit('root builds and #print axioms must succeed first')
    report['axiom_status'] = 'failed_allowlist'
    try:
        report['root_axioms'] = check((a.audit_directory/'axioms.log').read_text(), set(ROOTS.values()))
        report['axiom_status'] = 'passed_standard_axioms_only'
    finally:
        report_path.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__': main()
