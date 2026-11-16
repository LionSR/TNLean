#!/usr/bin/env python3
"""Exact arithmetic evidence for #8053 item 2; this is not a Lean proof.

Run with SymPy 1.14.0: python3 scripts/fibonacci_action_l_check.py
Matrices are read from the existing Lean definitions without evaluating Lean
source. All contractions use Q[s]/(s^4+s^2-1), with s the positive real root.
See docs/audits/2026-11-15_fibonacci_l_matrix.md for conventions and obligations.
"""
from pathlib import Path
from itertools import product
import re
import sympy as sp
from sympy.polys.domains import QQ
if not __debug__:
    raise RuntimeError('Run without -O: assertions perform the exact checks.')
s=sp.Symbol('s')
K=QQ.algebraic_field(sp.CRootOf(s**4+s**2-1,1))
sig=K.unit
zero,one=K.zero,K.one

def mat(rows): return [[K.convert(v) for v in row] for row in rows]
def zeros(n,m): return [[zero]*m for _ in range(n)]
def eye(n): return mat([[int(i==j) for j in range(n)] for i in range(n)])
def add(a,b): return [[x+y for x,y in zip(r,t)] for r,t in zip(a,b)]
def scale(k,a): return [[k*x for x in r] for r in a]
def mm(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),zero) for j in range(len(b[0]))] for i in range(len(a))]
def kron(a,b): return [[x*y for x in r for y in t] for r in a for t in b]
def show(a): return [[str(K.to_sympy(x)).replace(str(K.ext),'s') for x in r] for r in a]
root=Path(__file__).resolve().parents[1] / 'TNLean/MPS/Examples/Fibonacci'
def read_matrix(file,name):
    src=(root/file).read_text().split('def '+name+' :',1)[1].split('!![',1)[1].split(']',1)[0]
    return [[sum((K.convert(int(v))*sig**i for i,v in enumerate(c.split(','))),zero) for c in re.findall(r'⟨([^⟩]+)⟩',row)] for row in src.split(';')]

def gauge_pair(file,prefix):
    v=read_matrix(file,prefix+'GaugeGolden'); w=read_matrix(file,prefix+'GaugeInvGolden')
    assert mm(v,w)==eye(len(v)) and mm(w,v)==eye(len(v))
    return v,w

dim=[2,3]; state_dim=[1,2]
N=lambda a,b,c: int(c in ([a+b] if a+b<2 else [0,1]))
V={};W={}
for a,b,prefix,file in [(0,0,'fibOneOne','FibonacciUnit.lean'),(0,1,'fibOneTau','FibonacciUnit.lean'),(1,0,'fibTauOne','FibonacciUnit.lean'),(1,1,'fib','Fibonacci.lean')]:
    v,w=gauge_pair(file,prefix)
    for c in range(2):
        if N(a,b,c):
            off=2*c if a==b==1 else 0
            V[a,b,c]=v[off:off+dim[c]]
            W[a,b,c]=[r[off:off+dim[c]] for r in w]

O={}
O[0,0,0]=mat([[0,1],[0,0]]); O[0,1,1]=mat([[0,0],[1,1]])
O[1,0,1]=mat([[0,sig**2,sig],[0,0,0],[0,0,0]])
O[1,1,0]=mat([[0,0,0],[1,0,1],[0,0,0]])
O[1,1,1]=mat([[0,0,0],[0,0,0],[1,sig,-sig**2]])
for a,i,j in product(range(2),repeat=3): O.setdefault((a,i,j),zeros(dim[a],dim[a]))

# Verify exact fusion reconstruction, including cross-channel orthogonality.
for a,b in product(range(2),repeat=2):
    cs=[c for c in range(2) if N(a,b,c)]
    for c,e in product(cs,repeat=2):
        assert mm(V[a,b,c],W[a,b,e])==(eye(dim[c]) if c==e else zeros(dim[c],dim[e]))
    for i,j in product(range(2),repeat=2):
        stack=add(kron(O[a,i,0],O[b,0,j]),kron(O[a,i,1],O[b,1,j]))
        recon=zeros(dim[a]*dim[b],dim[a]*dim[b])
        for c in cs: recon=add(recon,mm(mm(W[a,b,c],O[c,i,j]),V[a,b,c]))
        assert stack==recon

A={(0,0):zeros(1,1),(0,1):eye(1),(1,0):mat([[0,sig],[0,0]]),(1,1):mat([[0,0],[1,-sig**2]])}
VA={};WA={}
for a,x,prefix in [(0,0,'fibUnitAllTau'),(1,0,'fibActAllTau'),(1,1,'fibActChain')]:
    v,w=gauge_pair('FibonacciAction.lean',prefix)
    for y in range(2):
        if N(a,x,y):
            off=y if a==x==1 else 0
            VA[a,x,y]=v[off:off+state_dim[y]]
            WA[a,x,y]=[r[off:off+state_dim[y]] for r in w]

# Find the missing unit-on-chain intertwiner over the exact number field.
def nullspace(rows,n):
    a=[r[:] for r in rows]; piv=[]; row=0
    for col in range(n):
        k=next((k for k in range(row,len(a)) if a[k][col]),None)
        if k is None: continue
        a[row],a[k]=a[k],a[row]; inv=one/a[row][col]; a[row]=[x*inv for x in a[row]]
        for k in range(len(a)):
            if k!=row and a[k][col]:
                f=a[k][col]; a[k]=[x-f*y for x,y in zip(a[k],a[row])]
        piv.append(col); row+=1
        if row==len(a): break
    result=[]
    for col in range(n):
        if col in piv: continue
        v=[zero]*n; v[col]=one
        for k,p in enumerate(piv): v[p]=-a[k][col]
        result.append(v)
    return result
B=[add(kron(O[0,i,0],A[1,0]),kron(O[0,i,1],A[1,1])) for i in range(2)]
def intertwiner(left,right,n,m):
    eq=[]
    for l,r in zip(left,right):
        for i,j in product(range(n),range(m)):
            row=[zero]*(n*m)
            for k in range(n): row[k*m+j]+=l[i][k]
            for k in range(m): row[i*m+k]-=r[k][j]
            eq.append(row)
    ns=nullspace(eq,n*m); assert len(ns)==1
    return [ns[0][i*m:(i+1)*m] for i in range(n)]
v=intertwiner([A[1,i] for i in range(2)],B,2,4)
w=intertwiner(B,[A[1,i] for i in range(2)],4,2)
f=mm(v,w)[0][0]; VA[0,1,1]=scale(one/f,v); WA[0,1,1]=w
for a,x in product(range(2),repeat=2):
    ys=[y for y in range(2) if N(a,x,y)]
    for y,z in product(ys,repeat=2):
        assert mm(VA[a,x,y],WA[a,x,z])==(eye(state_dim[y]) if y==z else zeros(state_dim[y],state_dim[z]))
    for i in range(2):
        stack=add(kron(O[a,i,0],A[x,0]),kron(O[a,i,1],A[x,1]))
        recon=zeros(dim[a]*state_dim[x],dim[a]*state_dim[x])
        for y in ys: recon=add(recon,mm(mm(WA[a,x,y],A[y,i]),VA[a,x,y]))
        assert stack==recon
print('All four fusion and all four action decompositions verified exactly.')
print('Unit-on-chain VA:',show(VA[0,1,1]));print('Unit-on-chain WA:',show(WA[0,1,1]))

# Flatten ((xa,xb),xx) in precisely the order of BoundaryActionTreeEntries.
def trees(a,b,x,y,c,z):
    fa=mm(VA[c,x,y],kron(V[a,b,c],eye(state_dim[x])))
    fs=mm(kron(W[a,b,c],eye(state_dim[x])),WA[c,x,y])
    sa=zeros(state_dim[y],dim[a]*dim[b]*state_dim[x])
    ss=zeros(dim[a]*dim[b]*state_dim[x],state_dim[y])
    for u,xa,xb,xx in product(range(state_dim[y]),range(dim[a]),range(dim[b]),range(state_dim[x])):
        k=(xa*dim[b]+xb)*state_dim[x]+xx
        sa[u][k]=sum((VA[a,z,y][u][xa*state_dim[z]+v]*VA[b,x,z][v][xb*state_dim[x]+xx] for v in range(state_dim[z])),zero)
        ss[k][u]=sum((WA[b,x,z][xb*state_dim[x]+xx][v]*WA[a,z,y][xa*state_dim[z]+v][u] for v in range(state_dim[z])),zero)
    return fa,fs,sa,ss
L={}
for a,b,x,y in product(range(2),repeat=4):
    cs=[c for c in range(2) if N(a,b,c) and N(c,x,y)]
    zs=[z for z in range(2) if N(b,x,z) and N(a,z,y)]
    assert len(cs)==len(zs)
    L[a,b,x,y]=[]
    for z in zs:
        lr=[]
        for c in cs:
            fa,fs,sa,ss=trees(a,b,x,y,c,z)
            cross=mm(sa,fs); l=sum((cross[i][i] for i in range(state_dim[y])),zero)/K.convert(state_dim[y])
            assert cross==scale(l,eye(state_dim[y]))
            lr.append(l)
        L[a,b,x,y].append(lr)
    if cs: print((a,b,x,y),'rows z=',zs,'cols c=',cs,show(L[a,b,x,y]))

# The source gauge acts on analysis, and reciprocally on synthesis.
alpha=lambda a,x,y: sig if (a,x,y)==(1,1,1) else one
beta=lambda a,b,c: sig if (a,b,c)==(1,1,0) else -one/sig if (a,b,c)==(1,1,1) else one
for key in V: V[key]=scale(beta(*key),V[key]); W[key]=scale(one/beta(*key),W[key])
for key in VA: VA[key]=scale(alpha(*key),VA[key]); WA[key]=scale(one/alpha(*key),WA[key])

def target(a,b,x,y,z,c):
    if (a,b,x,y)==(1,1,1,1): return [[sig**2,sig],[sig,-sig**2]][z][c]
    return one

sectors=entries=crosses=0
for a,b,x,y in product(range(2),repeat=4):
    cs=[c for c in range(2) if N(a,b,c) and N(c,x,y)]
    zs=[z for z in range(2) if N(b,x,z) and N(a,z,y)]
    if cs: sectors+=1
    forward=zeros(len(zs),len(cs)); backward=zeros(len(cs),len(zs))
    for iz,z in enumerate(zs):
        for ic,c in enumerate(cs):
            fa,fs,sa,ss=trees(a,b,x,y,c,z)
            f=target(a,b,x,y,z,c)
            assert mm(sa,fs)==scale(f,eye(state_dim[y]))
            # The forward scalar must also agree with the gauge formula.
            g=alpha(a,z,y)*alpha(b,x,z)/(alpha(c,x,y)*beta(a,b,c))
            assert g*L[a,b,x,y][iz][ic]==f
            cross=mm(fa,ss)
            inv=sum((cross[i][i] for i in range(state_dim[y])),zero)/K.convert(state_dim[y])
            assert cross==scale(inv,eye(state_dim[y]))
            forward[iz][ic]=f; backward[ic][iz]=inv; entries+=1
    assert mm(forward,backward)==eye(len(zs))
    assert mm(backward,forward)==eye(len(cs))
    # Both mixed comparisons vanish between distinct final blocks.
    for yy in range(2):
        if yy==y: continue
        for c in cs:
            for z in range(2):
                if N(b,x,z) and N(a,z,yy):
                    sa=trees(a,b,x,yy,next(cc for cc in range(2) if N(a,b,cc) and N(cc,x,yy)),z)[2]
                    fs=trees(a,b,x,y,c,next(zz for zz in range(2) if N(b,x,zz) and N(a,zz,y)))[1]
                    assert mm(sa,fs)==zeros(state_dim[yy],state_dim[y]); crosses+=1
print(f'Gauged L = standard Fibonacci F in all {sectors} nonempty sectors ({entries} entries); both inverse laws and {crosses} cross-final zero products verified.')

# Check that the SAME fusion gauge gives the printed standard F, rather than
# merely allowing independent row/column changes in the action comparison.
saved_VA,saved_WA,saved_dim=VA,WA,state_dim
VA,WA,state_dim=V,W,dim
for a,b,x,y in product(range(2),repeat=4):
    for c,z in product(range(2),repeat=2):
        if N(a,b,c) and N(c,x,y) and N(b,x,z) and N(a,z,y):
            fa,fs,sa,ss=trees(a,b,x,y,c,z)
            f=target(a,b,x,y,z,c)
            assert mm(fa,ss)==scale(f,eye(dim[y]))
            assert mm(sa,fs)==scale(f,eye(dim[y]))
VA,WA,state_dim=saved_VA,saved_WA,saved_dim
print('The same fusion gauge gives standard F for fusionFMatrix in every admissible sector.')

# A common length-three word span contains every pair of block matrices.
word_rows=[]
for word in product(range(2),repeat=3):
    blocks=[]
    for x in range(2):
        m=eye(state_dim[x])
        for i in word: m=mm(m,A[x,i])
        blocks.extend(v for row in m for v in row)
    word_rows.append(blocks)
assert not nullspace(word_rows,5)
print('The simultaneous length-three word span has dimension 1 + 4 = 5.')

# Both actual double-action trees reconstruct the same unblocked tensor.
for a,b,x in product(range(2),repeat=3):
    n=dim[a]*dim[b]*state_dim[x]
    for i in range(2):
        double=zeros(n,n)
        for j,k in product(range(2),repeat=2):
            double=add(double,kron(kron(O[a,i,j],O[b,j,k]),A[x,k]))
        fused=sequential=zeros(n,n)
        for y in range(2):
            cs=[c for c in range(2) if N(a,b,c) and N(c,x,y)]
            zs=[z for z in range(2) if N(b,x,z) and N(a,z,y)]
            for c in cs:
                fa,fs,_,_=trees(a,b,x,y,c,zs[0])
                fused=add(fused,mm(mm(fs,A[y,i]),fa))
            for z in zs:
                _,_,sa,ss=trees(a,b,x,y,cs[0],z)
                sequential=add(sequential,mm(mm(ss,A[y,i]),sa))
        assert double==fused==sequential
print('Both action trees reconstruct every unblocked double-action letter exactly.')
