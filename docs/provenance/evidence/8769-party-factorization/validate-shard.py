#!/usr/bin/env python3
"""Run the packaged canonical provenance checker for the requested shards."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[1] /
                       'canonical-policy-18a6dd4d' / 'validate-shards.py'),
                   run_name='__main__')
