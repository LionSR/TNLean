from pathlib import Path
import tempfile,subprocess,hashlib,json,shutil
w=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-message-resource-bounds');b=Path('/private/tmp/tnlean-message-resource-bounds');records=[]
for name in ['ch24_peps_message_expansion.tex','ch24_peps_physical_first_resources.tex']:
 src=w/'blueprint/src/chapter'/name;tmp=Path(tempfile.mkdtemp(prefix='approximate-physical-format-'))/name;shutil.copy2(src,tmp);cmd=[str(w/'scripts/latexindent'),'-l',str(w/'blueprint/latexindent.yaml'),'-w','-s',str(tmp)];x=subprocess.run(cmd,capture_output=True,text=True);assert x.returncode==0,x.stdout+x.stderr;src.write_bytes(tmp.read_bytes());x=subprocess.run(cmd,capture_output=True,text=True);assert x.returncode==0 and src.read_bytes()==tmp.read_bytes();records.append({'command':cmd,'returncode':0,'idempotent':True,'source_path':str(src.relative_to(w)),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()})
(b/'format-command.json').write_text(json.dumps({'chapters':records,'new_tags':65},indent=2)+'\n')
