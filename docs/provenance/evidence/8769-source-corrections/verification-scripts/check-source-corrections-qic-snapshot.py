from pathlib import Path
import hashlib,json,subprocess
bp=Path(Path('/tmp/tnlean-source-corrections/blueprint-dir').read_text().strip());qic=Path('/Users/siruilu/Local/agentFormalization/QICLean');rev='4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0'
rows=json.loads((bp/'QICLean-source-sha256.json').read_text());proc=subprocess.Popen(['git','-C',str(qic),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for p,s in rows.items():
 proc.stdin.write((rev+':'+p+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();assert len(h)==3,(p,h);data=proc.stdout.read(int(h[2]));assert proc.stdout.read(1)==b'\n';assert hashlib.sha256(data).hexdigest()==s,p
proc.stdin.close();assert proc.wait()==0
(bp/'qic-snapshot-check.json').write_text(json.dumps({'qic_revision':rev,'checked_files':len(rows),'all_hashes_match':True},indent=2)+'\n');print('QIC_SNAPSHOT_PASS',len(rows))
