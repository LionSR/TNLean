from pathlib import Path
import hashlib, importlib.util, json, sys, time
sys.dont_write_bytecode=True
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-original-compression-sampling')
spec=importlib.util.spec_from_file_location('provenance',root/'scripts/check_openai_provenance.py')
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
base=root/'docs/provenance'
ledger=json.loads((base/'openai-math.d/8769-original-compression-sampling.json').read_text())
schema=json.loads((base/'openai-math.schema.json').read_text())
start=time.monotonic()
n=checker.validate([ledger],schema,{'LionSR/TNLean':root,
 'openai/math':Path('/private/tmp/tnlean-openai-math-audit.git')},scan=False)
assert n==15
out=base/'evidence/8769-original-construction-reference-refresh'
text=f'PASS: all {n} entries of the original-compression shard, including five refreshed exact-source entries.\nScope: canonical schema, exact committed source bytes, manuscript labels, legal notices, evidence hashes, and stock-axiom reports; no repository-wide notice scan or Lean invocation.\n'
(out/'shard-provenance.log').write_text(text)
(out/'shard-provenance-command.json').write_text(json.dumps({'command':sys.argv,
 'returncode':0,'seconds':time.monotonic()-start,'checked_entries':n,
 'log_sha256':hashlib.sha256(text.encode()).hexdigest()},indent=2)+'\n')
(out/'manifest.json').write_text(json.dumps([{'path':str(p.relative_to(out)),
 'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
 for p in sorted(out.rglob('*')) if p.is_file() and p.name!='manifest.json'],indent=2)+'\n')
print(text)
