import os,fcntl,subprocess,sys,pathlib
common=subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],text=True).strip()
lock=pathlib.Path(common).resolve()/'tnlean-lake-cache.lock'
fd=os.open(lock,os.O_RDWR|os.O_CREAT,0o600)
if fd!=9:
    os.dup2(fd,9)
    os.close(fd)
print('Waiting for the canonical repository lock without busy waiting.',flush=True)
fcntl.flock(9,fcntl.LOCK_EX)
print('Canonical repository lock acquired; invoking the worktree wrapper.',flush=True)
env=os.environ.copy(); env['TNLEAN_LAKE_LOCK_HELD']='1'
result=subprocess.run(sys.argv[1:],env=env,pass_fds=(9,))
os.close(9)
sys.exit(result.returncode)
