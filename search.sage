# fuzzy permutation matrices
def genPermMatrix(p,n):
    k=len(p)
    if k==n:
        return matrix(QQ,n,n,lambda x,y:p[x]==y)
    return factorial(n-k)/binomial(n,k)*matrix(n,n,lambda x,y:sum([binomial(x,j)*binomial(n-1-x,k-1-j)*binomial(y,p[j])*binomial(n-1-y,k-1-p[j]) for j in range(k)]))
# first m rows of the above based on a k-permutation of [n]
def genPermMatrixByRow(p,n,m=None,k=None):
    if m==None:
        m=n
    l=len(p)
    if k==None:
        k=l
    if l==n:
        return matrix(QQ,m,n,lambda x,y:p[x]==y)
    return factorial(n-k)/binomial(n,k)*matrix(m,n,lambda x,y:sum([binomial(x,j)*binomial(n-1-x,k-1-j)*binomial(y,p[j])*binomial(n-1-y,k-1-p[j]) for j in range(l)]))
# check if a list of matrices has a constant cover
def hasConstantComb(matlist):
    n=len(matlist[0].list())
    M=matrix(QQ,[A.list() for A in matlist]+[n*[1]]).transpose()
    if M.rank()==len(matlist)+1:
        return "does not cover",0
    B=M.right_kernel().basis()
    if len(B)==1:
        v=B[0]
        if v[-1]!=0:
            return "covers",vector(v[0:len(matlist)])/v[-1]
        else:
            return "zero cover",0
    for v in B:
        if v[-1]!=0:
            return "many covers",vector(v[0:len(matlist)])/v[-1]
    return "zero cover",0
# make nice integer coefficients
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
        m=mostRepeats(this_comb)
        if m>maxsofar:
            bestc=c
            maxsofar=m
    if give_coeffs:
        return maxsofar,bestc
    else:
        return maxsofar
# search using repeated entries of the last matrix out of four
def searchRRRX(d):
    d0,d1,d2,d3=d
    n=d0
    print("Verifying no constant cover via count of repeated nonzero entries.")
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
        print(f"No non-vanishing constant cover possible, since max repeats = {record_repeats} < {(n-3)*n}.")
    else:
        print("CONSTANT COVER NOT RULED OUT")
    return
# search using repeated entries from the last two matrices out of four
def searchRRXX(d):
    d0,d1,d2,d3=d
    n=d0
    print("Verifying no constant cover via count of repeated nonzero entries.")
    print(f"First two permutations leave at least {(n-2)*n} zeros.")
    print(f"Computing most repeated nonzero entries in a {n}x{n} linear combination of a {d2}-perm and a {d3}-perm.")
    print()
    gpm={}
    for p in Permutations(list(range(d2))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    for p in Permutations(list(range(d3))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    record_repeats=0
    maxrepeats_nonzero=0
    for q2 in Permutations(d2):
        p2=[x-1 for x in q2]
        U=gpm[(tuple(p2),n)]
        u=U.list()
        for q3 in Permutations(d3):
            if d3<d2 or q3<q2:
                p3=[x-1 for x in q3]
                V=gpm[(tuple(p3),n)]
                v=V.list()
                maxrepeats_nonzero=mostRepeatsPair(u,v)
        if maxrepeats_nonzero>record_repeats:
            record_repeats=maxrepeats_nonzero
            print(f" new record: pair {p2}, {p3} produces {maxrepeats_nonzero} repeats")
    print()
    if record_repeats<(n-2)*n:
        print(f"No non-vanishing constant cover possible, since max repeats = {record_repeats} < {(n-2)*n}.")
    else:
        print("CONSTANT COVER NOT RULED OUT")
    return
# search using repeated entries from the last two matrices out of five
def searchRRRXX(d):
    d0,d1,d2,d3,d4=d
    n=d0
    print("Verifying no non-vanishing constant cover via count of repeated nonzero entries.")
    print(f"First three permutations leave at least {(n-3)*n} zeros.")
    print(f"Computing most repeated entries in a {n}x{n} linear combination of a {d3}-perm and a {d4}-perm.")
    print()
    gpm={}
    for p in Permutations(list(range(d3))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    for p in Permutations(list(range(d4))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    record_repeats=0
    maxrepeats_nonzero=0
    for q3 in Permutations(d3):
        p3=[x-1 for x in q3]
        U=gpm[(tuple(p3),n)]
        u=U.list()
        for q4 in Permutations(d4):
            if d4<d3 or q4<q3:
                p4=[x-1 for x in q4]
                V=gpm[(tuple(p4),n)]
                v=V.list()
                maxrepeats_nonzero=mostRepeatsPair(u,v)
        if maxrepeats_nonzero>record_repeats:
            record_repeats=maxrepeats_nonzero
            print(f" new record: pair {p3}, {p4} produces {maxrepeats_nonzero} repeats")
    print()
    if record_repeats<(n-3)*n:
        print(f"No non-vanishing constant cover possible, since max repeats = {record_repeats} < {(n-3)*n}.")
    else:
        print("CONSTANT COVER NOT RULED OUT")
    return
# special search considering structure of repeated entries in shortest two perms
def searchRRRST(d):
    d0,d1,d2,d3,d4=d
    n=d0
    print("Verifying no non-vanishing constant cover via structure of repeated nonzero entries.")
    print(f"First three permutations leave at least {(n-3)*n} zeros.")
    print(f"Linear combinations of a {d3}-perm and a {d4}-perm with this many repeats (X).")
    print()
    structures=[]
    gpm={}
    for p in Permutations(list(range(d3))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    for p in Permutations(list(range(d4))):
        gpm[(tuple(p),n)]=genPermMatrix(p,n)
    for q3 in Permutations(d3):
        p3=[x-1 for x in q3]
        U=gpm[(tuple(p3),n)]
        u=U.list()
        for q4 in Permutations(d4):
            if d4<d3 or q4<q3:
                p4=[x-1 for x in q4]
                V=gpm[(tuple(p4),n)]
                v=V.list()
                coeffs=[leadingOne([v[j]-v[i],u[i]-u[j]]) for i in range(n) for j in range(i)]
                for c in set(coeffs):
                    entrylist=(c[0]*vector(u)+c[1]*vector(v)).list()
                    if mostRepeats(entrylist)>=n*(n-3):
                        this_comb=[[p3,c[0]],[p4,c[1]]]
                        M=c[0]*U+c[1]*V
                        print(f"LINEAR COMB {displayComb(this_comb)}")
                        for x in set(entrylist):
                            if entrylist.count(x)>=n*(n-3):
                                for i in range(n):
                                    rowcounter=0
                                    for j in range(n):
                                        if M[i,j]==x:
                                            print("X",end='')
                                            rowcounter+=1
                                        else:
                                            print("O",end='')
                                    if rowcounter<n-3:
                                        print(" <--- can't be covered with three permutations",end='')
                                    print()
                        print()
    print("No constant cover possible.")
    return
# Hessian matrices, normalized as in earlier paper but extended to include 5-perms
#load('https://raw.githubusercontent.com/pbd345/qr-perms/main/Hessians.sage')
load('Hessians.sage')
# check Hessian eigenvalues for a linear combination [[perm1,coeff1],[perm2,coeff2],...]
def saddleCheck(comb):
    H=sum([term[1]*Hessians[tuple(term[0])] for term in comb])
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
    return
# display a linear combination of permutations in a nice way
def displayComb(comb):
    s=len(comb)
    if comb[0][1]==1:
        ans=str(comb[0][0])
    else:
        ans=str(comb[0][1])+'*'+str(comb[0][0])
    for i in range(1,s):
        if comb[i][1]>=0:
            ans+=' +'
        else:
            ans+=' '
        if comb[i][1]==1:
            ans+=' '+str(comb[i][0])
        else:
            ans+=str(comb[i][1])+'*'+str(comb[i][0])
    return ans
# search over four permutations of specified lengths
def searchXXXX(d):
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
                                        if (result[0]=='covers' and 0 not in result[1]) or result[0]=='many covers':
                                            coeffs=standardize(result[1])
                                            this_comb=[(perms[i],coeffs[i]) for i in range(len(perms))]
                                            already_found=False
                                            for c in constant_covers:
                                                if equivCombsOfPerms(this_comb,c):
                                                    already_found=True
                                                    break
                                            if not already_found:
                                                constant_covers+=[this_comb]
                                                if result[0]=='many covers':
                                                    print("Warning: cover is not unique")
                                                print(f"CONSTANT COVER {displayComb(this_comb)}")
                                                saddleCheck(this_comb)
    if constant_covers==[]:
        print("No non-vanishing constant covers found.")
    else:
        print(f"Found {len(constant_covers)} distinct non-vanishing covers.")
    return
# search constant covers based on latin squares of order 5
def search55555(showall=False):
#    load('https://raw.githubusercontent.com/pbd345/qr-perms/main/55555-modD4.sage')
    load('55555-modD4.sage')
    print("Checking all D4-inequivalent latin squares of order 5.")
    for L in D4distinct_lists:
        H=matrix(QQ,16,16)
        for p in L:
            H+=Hessians[tuple(p)]
        evals=H.eigenvalues()
        lam_min=min(evals)
        lam_max=max(evals)
        if lam_min>=0 or lam_max<=0 or showall:
            this_comb=[[p,1] for p in L]
            print(f"CONSTANT COVER {displayComb(this_comb)}")
            saddleCheck(this_comb)
    print(f"Found {len(D4distinct_lists)} distinct covers.")
    return
# search over five permutations of specified lengths
def searchXXXXX(d):
    d0,d1,d2,d3,d4=d
    n=d0
    gpm={}
    for di in Set(d):
        for p in Permutations(list(range(di))):
            gpm[(tuple(p),n)]=genPermMatrix(p,n)
    print("Conducting full search for non-vanishing constant covers.")
    constant_covers=[]
    for q0 in Permutations(d0):
        for q1 in Permutations(d1):
            if q1<q0 and (d2==d1 or [(q0[i]+q1[i]-(n+1))*(q0[i]+(-1)^n*q1[i]) for i in range(n)]==[0]*n):
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
                                        if (result[0]=='covers' and 0 not in result[1]) or result[0]=='many covers':
                                            coeffs=standardize(result[1])
                                            this_comb=[(perms[i],coeffs[i]) for i in range(len(perms))]
                                            already_found=False
                                            for c in constant_covers:
                                                if equivCombsOfPerms(this_comb,c):
                                                    already_found=True
                                                    break
                                            if not already_found:
                                                constant_covers+=[this_comb]
                                                if result[0]=='many covers':
                                                    print("Warning: cover is not unique")
                                                print(f"CONSTANT COVER {displayComb(this_comb)}")
                                                saddleCheck(this_comb)
    if constant_covers==[]:
        print("No non-vanishing constant covers found.")
    else:
        print(f"Found {len(constant_covers)} distinct non-vanishing covers.")
    return
# search using partial permutations on the first few rows, storing candidates for consideration of next row
def searchByRow(d):
    d0,d1,d2,d3,d4=d
    n=d0
    prefixes=[[[[]]*5]]
    print("Searching for non-vanishing constant covers by rows.")
    for m in range(1,d4+1):
        gpm={}
        for di in Set(d):
            for p in Permutations(list(range(di)),m):
                gpm[(tuple(p),n,m,di)]=genPermMatrixByRow(p,n,m,di)
        if m==1:
            rowstring="row"
        else:
            rowstring=str(m)+" rows"
        print(f"Checking first {rowstring}.")
        these_prefixes=[]
        for q0 in Permutations(d0,m):
            rawperms=[q0]
            perms=[[x-1 for x in q] for q in rawperms]
            if [Q[0:m-1] for Q in perms] in [R[0:len(perms)] for R in prefixes[-1]]:
                for q1 in Permutations(d1,m):
                    if q1<=q0:
                        rawperms=[q0,q1]
                        perms=[[x-1 for x in q] for q in rawperms]
                        if [Q[0:m-1] for Q in perms] in [R[0:len(perms)] for R in prefixes[-1]]:
                            for q2 in Permutations(d2,m):
                                if d2<d1 or q2<=q1:
                                    rawperms=[q0,q1,q2]
                                    perms=[[x-1 for x in q] for q in rawperms]
                                    if [Q[0:m-1] for Q in perms] in [R[0:len(perms)] for R in prefixes[-1]]:
                                        for q3 in Permutations(d3,m):
                                            if d3<d2 or q3<=q2:
                                                rawperms=[q0,q1,q2,q3]
                                                perms=[[x-1 for x in q] for q in rawperms]
                                                if [Q[0:m-1] for Q in perms] in [R[0:len(perms)] for R in prefixes[-1]]:
                                                    for q4 in Permutations(d4,m):
                                                        if d4<d3 or q4<=q3:
                                                            rawperms=[q0,q1,q2,q3,q4]
                                                            perms=[[x-1 for x in q] for q in rawperms]
                                                            if [Q[0:m-1] for Q in perms] in [R[0:len(perms)] for R in prefixes[-1]]:
                                                                mats=[gpm[(tuple(perms[i]),n,m,d[i])] for i in range(5)]
                                                                result=hasConstantComb(mats)
                                                                if result[0] in ['covers','many covers']:
                                                                    these_prefixes+=[perms]
                                                                #print(perms)
        if these_prefixes==[]:
            print(f"No non-vanishing constant cover.")
            return
        print(f"List of valid prefixes after searching first {rowstring}:")
        for R in these_prefixes:
            print(R)
        prefixes+=[these_prefixes]
    print("CONSTANT COVER NOT RULED OUT")
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
        print("No constant cover possible, since the maximum length must be repeated.")
        return
    if d[0]-d[2]>1:
        print("No constant cover possible, since third largest length is too short.")
        return
    if d[0]-d[3]>2+(d[0]-d[2]):
        print("No constant cover possible, since fourth largest length is too short.")
        return
    if r==4 and d[0]>6:
        print("No non-vanishing constant cover possible, since first three permutations leave more than two entries uncovered.")
        return
    if r==4 and d[0:3] in [[5,5,5],[6,6,6]]:
        searchRRRX(d)
        return
    if r==4 and d[0:3]==[6,6,5]:
        searchRRXX(d)
        return
    if r==4:
        searchXXXX(d)
        return
# r = 5 cases start here    
    #r=5 begins here
    if d[0]-d[4]>3+(d[0]-d[2])+(d[0]-d[3]):
        print("No constant cover possible, since fifth largest length is too short.")
        return
    if d[0]>10 or 4+(d[0]-d[2])+(d[0]-d[3])<d[0]-2:
        print("No non-vanishing constant cover possible, since first four permutations leave more than two entries uncovered.")
        return
    if d==[5,5,5,5,5]:
        search55555(True) # True: show all covers; False: show only those failing the Hessian check
        return
    if d in [[5,5,5,3,2],[5,5,5,4,2],[5,5,5,4,4]]:
        searchRRRXX(d)
        return
    if d==[5,5,5,4,3]:
        searchRRRST(d)
        return
    if d[0]<=4 or d[0:3]==[5,5,4]:
        searchXXXXX(d)
        return
    if d[0]>=5:
        searchByRow(d)
        return
    searchXXXXX(d)
    return
