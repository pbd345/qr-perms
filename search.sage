# fuzzy permutation matrices
def genPermMatrix(p,n):
    k=len(p)
    if k==n:
        return matrix(n,n,lambda x,y:p[x]==y)
    return factorial(n-k)/binomial(n,k)*matrix(n,n,lambda x,y:sum([binomial(x,j)*binomial(n-1-x,k-1-j)*binomial(y,p[j])*binomial(n-1-y,k-1-p[j]) for j in range(k)]))
# check if a list of matrices has a constant cover
def hasConstantComb(matlist):
    n=len(matlist[0].list())
    M=matrix([A.list() for A in matlist]).transpose()
    try:
        sol=M.solve_right(vector(n*[1]))
        return "covers with coefficients",sol
    except ValueError:
        return "does not cover"
# make nice coefficients
def standardize(c):
    g=gcd(c)
    return [x/g for x in c]
# dihedral equivalence
def D4perms(p):
    n=len(p)
    ans=[p]
    ans+=[[n-1-p[i] for i in range(n)]]
    ans+=[[p[n-1-i] for i in range(n)]]
    ans+=[[n-1-p[n-1-i] for i in range(n)]]
    q=[0]*n
    for i in range(n):
        q[p[i]]=i
    ans+=[q]
    ans+=[[n-1-q[i] for i in range(n)]]
    ans+=[[q[n-1-i] for i in range(n)]]
    ans+=[[n-1-q[n-1-i] for i in range(n)]]
    return ans
def equivCombsOfPerms(comb1,comb2):
    if len(comb1)!=len(comb2):
        return False
    for j in range(8):
        if sorted([(D4perms(c[0])[j],c[1]) for c in comb1])==sorted([(c[0],c[1]) for c in comb2]):
            return True
    return False
# some setup for repeated entry strategy
def leadingOne(w):
    for x in w:
        if x!=0:
            scaled=tuple(1/x*vector(w))
            return scaled
    return tuple(w)
def mostRepeats(w,nonzero_only=True):
    w=list(w)
    return max([0]+[w.count(x) for x in w if (x!=0 or not nonzero_only)])
def mostRepeatsPair(u,v,give_coeffs=False):
    n=len(u)
    bestc=(0,0)
    maxsofar=0
    coeffs=[leadingOne([v[j]-v[i],u[i]-u[j]]) for i in range(n) for j in range(i)]
    for c in set(coeffs):
        this_comb=c[0]*vector(u)+c[1]*vector(v)
        m=maxRepeats(this_comb)
        if m>maxsofar:
            bestc=c
            maxsofar=m
    if give_coeffs:
        return maxsofar,bestc
    else:
        return maxsofar
# display a linear combination of permutations in a nice way
def displayComb(comb,latex=False):
    s=len(comb)
    if comb[0][1]==1:
        ans=str(comb[0][0])
    else:
        ans=str(comb[0][1])+'*'+str(comb[0][0])
    for i in range(1,s):
        if comb[i][1]>0:
            ans+=' +'
        else:
            ans+=' '
        if comb[i][1]==1:
            ans+=' '+str(comb[i][0])
        else:
            ans+=str(comb[i][1])+'*'+str(comb[i][0])
    return ans
# search using repeated entries of the last matrix out of four
def searchRRRX(d):
    d0,d1,d2,d3=d
    n=d0
    print("Verifying no constant cover via repeated nonzero entries.")
    print(f"First three permutations leave at least {(n-3)*n} zeros.")
    print(f"Computing most repeated nonzero entries in a {n}x{n} generalized {d3}-perm matrix.")
    print()
    gpm={}
    for p in Permutations(list(range(d3))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    record_repeats=0
    for q3 in Permutations(d3):
        p3=[x-1 for x in q3]
        U=gpm[(tuple(p3),n)]
        u=U.list()
        maxrepeats_nonzero=mostRepeats(u)
        if maxrepeats_nonzero>record_repeats:
            record_repeats=maxrepeats_nonzero
            print(f" new record: perm {p3} produces {maxrepeats_nonzero} repeats")
    print()
    if record_repeats<(n-3)*n:
        print(f"NO CONSTANT COVER POSSIBLE, since max repeats = {record_repeats} < {(n-3)*n}.")
    else:
        print("CONSTANT COVER NOT RULED OUT")
    return
# search using repeated entries of the last matrix out of five
def searchRRRRX(d):
    d0,d1,d2,d3,d4=d
    n=d0
    print("Verifying no constant cover via repeated nonzero entries.")
    print(f"First four permutations leave at least {(n-4)*n} zeros.")
    print(f"Computing most repeated nonzero entries in a {n}x{n} generalized {d4}-perm matrix.")
    print()
    gpm={}
    for p in Permutations(list(range(d4))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    record_repeats=0
    for q4 in Permutations(d4):
        p4=[x-1 for x in q4]
        U=gpm[(tuple(p4),n)]
        u=U.list()
        maxrepeats_nonzero=mostRepeats(u)
        if maxrepeats_nonzero>record_repeats:
            record_repeats=maxrepeats_nonzero
            print(f" new record: perm {p3} produces {maxrepeats_nonzero} repeats")
    print()
    if record_repeats<(n-4)*n:
        print(f"NO CONSTANT COVER POSSIBLE, since max repeats = {record_repeats} < {(n-4)*n}.")
    else:
        print("CONSTANT COVER NOT RULED OUT")
    return
# search over four permutations of specified lengths
def searchXXXX(d):
    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/Hessians.sage')
    d0,d1,d2,d3=d
    n=d0
    gpm={}
    for di in Set(d):
        for p in Permutations(list(range(di))):
            gpm[(tuple(p),n)]=genPermMatrix(p,n)
    constant_covers=[]
    for q0 in Permutations(d0):
        for q1 in Permutations(d1):
            if d1<d0 or q1<q0:
                for q2 in Permutations(d2):
                    if d2<d1 or q2<q1:
                        for q3 in Permutations(d3):
                            if d3<d2 or q3<q2:
                                        rawperms=[q0,q1,q2,q3]
                                        perms=[[x-1 for x in q] for q in rawperms]
                                        mats=[gpm[(tuple(p),n)] for p in perms]
                                        result=hasConstantComb(mats)
                                        if result!='does not cover' and 0 not in result[1]:
                                            coeffs=standardize(result[1].list())
                                            this_comb=[(perms[i],coeffs[i]) for i in range(len(perms))]
                                            already_found=False
                                            for c in constant_covers:
                                                if equivCombsOfPerms(this_comb,c):
                                                    already_found=True
                                                    break
                                            if not already_found:
                                                constant_covers+=[this_comb]
                                                print(f"CONSTANT COVER {displayComb(this_comb)}")
                                                H=sum([coeffs[i]*Hessians[tuple(perms[i])] for i in range(len(perms))])
                                                evals=H.eigenvalues()
                                                print("Min Hessian eigenvalue ",end='')
                                                lam_min=min(evals)
                                                if lam_min<0:
                                                    print(f"= {numerical_approx(lam_min, digits=6)} < 0.")
                                                else:
                                                    print(">= 0; ad-hoc construction needed.")
                                                print("Max Hessian eigenvalue ",end='')
                                                lam_max=max(evals)
                                                if lam_max>0:
                                                    print(f"= {numerical_approx(lam_max, digits=6)} > 0.")
                                                else:
                                                    print("<= 0; ad-hoc construction needed.")                                                    
                                                print()
    if constant_covers==[]:
        print("No nonzero covers found.")
    else:
        print(f"Found {len(constant_covers)} distinct nonzero covers.")
    return
# search constant covers based on latin squares of order 5
def search55555(showall=False):
    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/55555-modD4.sage')
    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/Hessians.sage')
    for L in D4distinct_lists:
        H=matrix(QQ,16,16)
        for p in L:
            H+=Hessians[tuple(p)]
        evals=H.eigenvalues()
        lam_min=min(evals)
        lam_max=max(evals)
        if lam_min>=0 or lam_max<=0 or showall:
            print(f"CONSTANT COVER {displayComb([[p,1] for p in L])}")
            print(f"Min Hessian eigenvalue ",end='')
            if lam_min<0:
                print(f"= {numerical_approx(lam_min, digits=6)} < 0.")
            else:
                print(">= 0; ad-hoc construction needed.")
            print("Max Hessian eigenvalue ",end='')
            if lam_max>0:
                print(f"= {numerical_approx(lam_max, digits=6)} > 0.")
            else:
                print("<= 0; ad-hoc construction needed.")                                                    
            print()
    print(f"Found {len(D4distinct_lists)} distinct nonzero covers.")
    return
# search over five permutations of lengths 5,5,4,*,* exploiting structure on the first two
def search554XX(d):
    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/Hessians.sage')
    d0,d1,d2,d3,d4=d
    n=d0 # should equal 5
    gpm={}
    for di in Set(d):
        for p in Permutations(list(range(di))):
            gpm[(tuple(p),n)]=genPermMatrix(p,n)
    constant_covers=[]
    for q0 in Permutations(d0):
        #print(q0)
        for q1 in Permutations(d1):
            if q1<q0 and [(q0[i]+q1[i]-6)*(q0[i]-q1[i]) for i in range(n)]==[0]*n:
                for q2 in Permutations(d2):
                    if d2<d1 or q2<q1:
                        for q3 in Permutations(d3):
                            if d3<d2 or q3<q2:
                                for q4 in Permutations(d4):
                                    if d4<d3 or q4<q3:
                                        rawperms=[q0,q1,q2,q3,q4]
                                        perms=[[x-1 for x in q] for q in rawperms]
                                        mats=[gpm[(tuple(p),n)] for p in perms]
                                        result=hasConstantComb(mats)
                                        if result!='does not cover' and 0 not in result[1]:
                                            coeffs=standardize(result[1].list())
                                            this_comb=[(perms[i],coeffs[i]) for i in range(len(perms))]
                                            already_found=False
                                            for c in constant_covers:
                                                if equivCombsOfPerms(this_comb,c):
                                                    already_found=True
                                                    break
                                            if not already_found:
                                                constant_covers+=[this_comb]
                                                print(f"CONSTANT COVER {displayComb(this_comb)}")
                                                H=sum([coeffs[i]*Hessians[tuple(perms[i])] for i in range(len(perms))])
                                                evals=H.eigenvalues()
                                                print("Min Hessian eigenvalue ",end='')
                                                lam_min=min(evals)
                                                if lam_min<0:
                                                    print(f"= {numerical_approx(lam_min, digits=6)} < 0.")
                                                else:
                                                    print(">= 0; ad-hoc construction needed.")
                                                print("Max Hessian eigenvalue ",end='')
                                                lam_max=max(evals)
                                                if lam_max>0:
                                                    print(f"= {numerical_approx(lam_max, digits=6)} > 0.")
                                                else:
                                                    print("<= 0; ad-hoc construction needed.")                                                    
                                                print()
    if constant_covers==[]:
        print("No nonzero covers found.")
    else:
        print(f"Found {len(constant_covers)} distinct nonzero covers.")
    return
# search over five permutations of lengths 6,6,5,5,* exploiting structure on the first two
def search6655X(d):
    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/Hessians.sage')
    d0,d1,d2,d3,d4=d
    n=d0 # should equal 6
    gpm={}
    for di in Set(d):
        for p in Permutations(list(range(di))):
            gpm[(tuple(p),n)]=genPermMatrix(p,n)
    constant_covers=[]
    for q0 in Permutations(d0):
        #print(q0)
        for q1 in Permutations(d1):
            if q1<q0 and [q0[i]+q1[i]-7 for i in range(n)]==[0]*n:
                for q2 in Permutations(d2):
                    if d2<d1 or q2<q1:
                        for q3 in Permutations(d3):
                            if d3<d2 or q3<q2:
                                for q4 in Permutations(d4):
                                    if d4<d3 or q4<q3:
                                        rawperms=[q0,q1,q2,q3,q4]
                                        perms=[[x-1 for x in q] for q in rawperms]
                                        mats=[gpm[(tuple(p),n)] for p in perms]
                                        result=hasConstantComb(mats)
                                        if result!='does not cover' and 0 not in result[1]:
                                            coeffs=standardize(result[1].list())
                                            this_comb=[(perms[i],coeffs[i]) for i in range(len(perms))]
                                            already_found=False
                                            for c in constant_covers:
                                                if equivCombsOfPerms(this_comb,c):
                                                    already_found=True
                                                    break
                                            if not already_found:
                                                constant_covers+=[this_comb]
                                                print(f"CONSTANT COVER {displayComb(this_comb)}")
                                                H=sum([coeffs[i]*Hessians[tuple(perms[i])] for i in range(len(perms))])
                                                evals=H.eigenvalues()
                                                print("Min Hessian eigenvalue ",end='')
                                                lam_min=min(evals)
                                                if lam_min<0:
                                                    print(f"= {numerical_approx(lam_min, digits=6)} < 0.")
                                                else:
                                                    print(">= 0; ad-hoc construction needed.")
                                                print("Max Hessian eigenvalue ",end='')
                                                lam_max=max(evals)
                                                if lam_max>0:
                                                    print(f"= {numerical_approx(lam_max, digits=6)} > 0.")
                                                else:
                                                    print("<= 0; ad-hoc construction needed.")                                                    
                                                print()
    if constant_covers==[]:
        print("No nonzero covers found.")
    else:
        print(f"Found {len(constant_covers)} distinct nonzero covers.")
    return
# search over five permutations of specified lengths
def searchXXXXX(d):
    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/Hessians.sage')
    d0,d1,d2,d3,d4=d
    n=d0
    gpm={}
    for di in Set(d):
        for p in Permutations(list(range(di))):
            gpm[(tuple(p),n)]=genPermMatrix(p,n)
    constant_covers=[]
    for q0 in Permutations(d0):
        #print(q0)
        for q1 in Permutations(d1):
            if d1<d0 or q1<q0:
                for q2 in Permutations(d2):
                    if d2<d1 or q2<q1:
                        for q3 in Permutations(d3):
                            if d3<d2 or q3<q2:
                                for q4 in Permutations(d4):
                                    if d4<d3 or q4<q3:
                                        rawperms=[q0,q1,q2,q3,q4]
                                        perms=[[x-1 for x in q] for q in rawperms]
                                        mats=[gpm[(tuple(p),n)] for p in perms]
                                        result=hasConstantComb(mats)
                                        if result!='does not cover' and 0 not in result[1]:
                                            coeffs=standardize(result[1].list())
                                            this_comb=[(perms[i],coeffs[i]) for i in range(len(perms))]
                                            already_found=False
                                            for c in constant_covers:
                                                if equivCombsOfPerms(this_comb,c):
                                                    already_found=True
                                                    break
                                            if not already_found:
                                                constant_covers+=[this_comb]
                                                print(f"CONSTANT COVER {displayComb(this_comb)}")
                                                H=sum([coeffs[i]*Hessians[tuple(perms[i])] for i in range(len(perms))])
                                                evals=H.eigenvalues()
                                                print("Min Hessian eigenvalue ",end='')
                                                lam_min=min(evals)
                                                if lam_min<0:
                                                    print(f"= {numerical_approx(lam_min, digits=6)} < 0.")
                                                else:
                                                    print(">= 0; ad-hoc construction needed.")
                                                print("Max Hessian eigenvalue ",end='')
                                                lam_max=max(evals)
                                                if lam_max>0:
                                                    print(f"= {numerical_approx(lam_max, digits=6)} > 0.")
                                                else:
                                                    print("<= 0; ad-hoc construction needed.")                                                    
                                                print()
    if constant_covers==[]:
        print("No nonzero covers found.")
    else:
        print(f"Found {len(constant_covers)} distinct nonzero covers.")
    return
# handles case assignment
def search(d):
    r=len(d)
    if r not in [4,5]:
        print("Please enter a list of four or five permutation lengths, each at least two.")
        return
    d.sort(reverse=True)
    if d[-1]<2:
        print("Please enter a list of four or five permutation lengths, each at least two.")
        return
    if d[0]<4:
        print("QR-forcing expressions require a permutation of length at least four.")
        return
    if d[0]!=d[1]:
        print("NO CONSTANT COVER POSSIBLE, since the maximum length must be repeated.")
        return
    if d[2]<d[0]-1:
        print("NO CONSTANT COVER POSSIBLE, since third largest length is too short.")
        return        
    if (r==4 and d[0]>6) or (r==5 and d[0]>10):
        print("NO CONSTANT COVER POSSIBLE, via first row alone.")
        return
    if r==4 and d[0:2] in [[5,5,5],[6,6,6]]:
        searchRRRX(d)
        return
    if r==4 and d[0:2]==[6,6,5]:
        searchRRXX(d)
        return
    if r==4:
        searchXXXX(d)
        return
    if d==[5,5,5,5,5]:
        search55555(True) # True: show all covers; False: show only those failing the Hessian check
        return
    if d[0:3] in [[5,5,5],[6,6,6]]:
        searchRRRRX(d)
        return
    if d[0:4]==[6,6,5,5]:
        search6655X(d)
        return
    if d[0]<=4:
        searchXXXXX(d)
        return
    if d[0]==5:
        search554XX(d)
        return
    if d[0] in [9,10]:
        print("NO CONSTANT COVER POSSIBLE, since the first row can't interpolate.")
        return
    if d[0] in [6,7,8]:
        print("Not yet implemented; stay tuned.")
        return
    return
