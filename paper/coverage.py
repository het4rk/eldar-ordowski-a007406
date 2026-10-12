from sympy import primefactors, isprime
def HU_mod(U,q):
    return sum(pow(u*u,-1,q) for u in range(1,U+1))%q
N=100000; comp=0; cov=0; first=[]
for n in range(4,N+1):
    if isprime(n): continue
    comp+=1; m=n-1; ok=True
    for q in primefactors(n):
        s=0
        while q**(s+1)<=m: s+=1
        if HU_mod(m//q**s,q)==0: ok=False;break
    if ok: cov+=1
    elif len(first)<15: first.append(n)
print(comp,cov,cov/comp,first)
