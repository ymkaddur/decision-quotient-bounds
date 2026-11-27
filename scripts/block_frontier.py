"""Exhaustive membership synthesis for two blocks."""
from itertools import product
from itertools import combinations_with_replacement


def block_laws(m,n):
    size=m+n
    costs=[2,5,1,4,3,1][:size]
    sets=range(1<<size)
    def count(s):
        return ((s&((1<<m)-1)).bit_count(),(s>>m).bit_count())
    def subsets(s):
        t=s
        while True:
            yield t
            if not t:
                break
            t=(t-1)&s
    law_count=0
    max_calls=0
    for reversed_cut in combinations_with_replacement(range(n+2),m+1):
        cut=reversed_cut[::-1]
        def bad(s):
            i,j=count(s)
            return j>=cut[i]
        j=n+1
        found=[]
        calls=0
        for i in range(m+1):
            while j>0:
                calls+=1
                mask=(1<<i)-1 | (((1<<(j-1))-1)<<m)
                if not bad(mask):
                    break
                j-=1
            found.append(j)
        assert tuple(found)==cut
        safe=[]
        for r in sets:
            free=((1<<size)-1)^r
            ok=all(not bad(t) for t in subsets(free))
            assert ok==(not bad(free))
            if ok:
                safe.append(sum(costs[i] for i in range(size) if r&(1<<i)))
        fast=[]
        for a,b in product(range(m+1),range(n+1)):
            if n-b<found[m-a]:
                fast.append(sum(sorted(costs[:m])[:a])+sum(sorted(costs[m:])[:b]))
        assert min(fast,default=None)==min(safe,default=None)
        law_count+=1
        max_calls=max(max_calls,calls)
    return {"block_sizes":[m,n],"monotone_laws":law_count,"max_membership_queries":max_calls,
            "bound":m+n+2,"labelled_masks_per_law":1<<size}


if __name__ == "__main__":
    print(block_laws(3,3))
