from pathlib import Path
import hashlib,json,subprocess,time
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-corrections');out=root/'docs/provenance/evidence/8769-source-corrections'
cmd=['uv','run','--no-project','--with','jsonschema==4.26.0','python','scripts/check_openai_provenance.py','--root',str(root),'--upstream-root','/private/tmp/tnlean-openai-math-audit.git']
t=time.monotonic();r=subprocess.run(cmd,cwd=root,capture_output=True,text=True);(out/'full-provenance.log').write_text(r.stdout+r.stderr)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(out/'full-provenance-command.json').write_text(json.dumps({'source_revision':'f932b80f1b67668584120403b983be0633f62602','command':cmd,'cwd':str(root),'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(out/'full-provenance.log'),'checker_sha256':sha(root/'scripts/check_openai_provenance.py'),'schema_sha256':sha(root/'docs/provenance/openai-math.schema.json')},indent=2)+'\n')
print(r.stdout+r.stderr);assert r.returncode==0
