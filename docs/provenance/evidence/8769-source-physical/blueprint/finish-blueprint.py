from pathlib import Path
import hashlib,json,os,shutil,subprocess,time,tempfile
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-physical');r=Path('/private/tmp/tnlean-source-physical');b=Path((r/'blueprint-dir').read_text().strip());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();src=root/'blueprint/src/chapter/ch24_peps_source_physical.tex';tmp=Path(tempfile.mkdtemp(prefix='tn-gaussian-format-'))/src.name;shutil.copy2(src,tmp);cmd=[str(root/'scripts/latexindent'),'-l',str(root/'blueprint/latexindent.yaml'),'-w','-s',str(tmp)];subprocess.run(cmd,check=True,capture_output=True);src.write_bytes(tmp.read_bytes());subprocess.run(cmd,check=True,capture_output=True);assert src.read_bytes()==tmp.read_bytes();(r/'format-command.json').write_text(json.dumps({'command':cmd,'returncode':0,'idempotent':True,'source_path':str(src.relative_to(root)),'source_sha256':sha(src),'new_tags':77},indent=2)+'\n');shutil.copy2(src,b/src.relative_to(root))
rows=json.loads((b/'commands.json').read_text())
for name in ['pdf','web','browser']:
 p=b/(name+'.log');shutil.copy2(p,b/('initial-'+name+'.log'))
 for row in rows:
  if row['name']==name:row['name']='initial-'+name
shutil.copy2(b/'blueprint/src/focused.log',b/'initial-tex.log')
def run(name,cmd,cwd,env=None):
 t=time.monotonic();x=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True);p=b/(name+'.log');p.write_text(x.stdout+x.stderr);rows.append({'name':name,'command':cmd,'cwd':str(cwd),'seconds':round(time.monotonic()-t,3),'returncode':x.returncode,'log_sha256':sha(p)});(b/'commands.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,x.returncode,flush=True);assert x.returncode==0,(x.stdout+x.stderr)[-5000:]
env=os.environ.copy();env['PATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin:'+env['PATH'];env['TEXINPUTS']=str(b/'.deps/tenkz/tex')+'//:'
run('pdf',['latexmk','-lualatex','-interaction=nonstopmode','-halt-on-error','focused.tex'],b/'blueprint/src',env)
run('bbl',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/texra-blueprint','--root',str(b),'bbl'],b)
run('web',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/leanblueprint','web'],b/'blueprint',env)
env['PYTHONPATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/lib/python3.14/site-packages';run('browser',['/tmp/qic-regional-blueprint-env/bin/python',str(b/'scoped_web_check.py')],b,env)
run('sync-final',['python3','scripts/blueprint_lean_sync.py','--root',str(b),'--report',str(b/'sync-final.json'),'--ci','--report-duplicate-tags','--update-lean-decls'],root)
shutil.copy2(b/'blueprint/lean_decls',b/'full-lean-decls.txt')
p=b/'blueprint-source-sha256.json';s=json.loads(p.read_text());s[str(src.relative_to(root))]=sha(src);p.write_text(json.dumps(s,indent=2)+'\n')
print('FINAL_RENDER_PASS',b)
