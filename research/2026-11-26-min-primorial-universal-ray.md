# Universal offset ray, exact doubling, and the cost of a false record

2026-11-26 JST. Continuation of primorial-neighborhood checkpoint 881a606bee41345fb469cb38a4d410ffd1f113a6. Paper results and executed finite Python audit; no Lean verification or twin-infinitude claim.

## 1. Universal offset ray and exact prefix transfer

Start at (u,v)=(4,5). In the uncut offset ray use the lexicographically least (w,p) among all odd prime factors of u-1 with next clock n=v+w=0 mod 2p and of u+1 with clock n=p+2 mod 2p. Update (u,v)->(u+p-1,n). Every state has a next event. The standard MIN nonnegative-deficit argument applies: at an even firing the positive defect 2n-u+1 is divisible by p, so u+p-1<=2n; at an odd firing 2n-u-5 is odd, either positive and at least p, or negative of absolute value <=3 (as n>v and u<=2v), in which case p=3 and the same envelope holds. Thus u<=2v.

A finite universal prefix including all quiet ticks lifts to actual adaptive MIN from canonical M=R+3, H=2R+u, t=R+v by setting R even and R=0 mod every odd prime dividing any of its relative raw defects. Also impose R=0 mod each odd p<=S if desired. Choose R arbitrarily large so that every selected label is adaptive-eligible. Parity is preserved and raw GCD prime sets agree at each tick, since the actual GCD is gcd(R+n,2n-u+1) or gcd(R+n-2,2n-u-5). For any actual prime factor of a relative defect, R is zero modulo that factor. This lift is for the uncut universal prefix, not an arbitrary restricted shadow after it diverges.

For any S the previous small-label shadow agrees exactly with the universal ray up to its first event of label p>S, excluding that event. This follows by first-clock/least-label selection and induction. Let r be the previous record (0 at start), then this first omitted event is a record and its range of thresholds is r<=S<p. Labels on the universal ray are unbounded: otherwise a sufficiently large even multiple of their finite product cannot be strictly crossed by any of them, contrary to u increasing without bound. A finite number of previous events have labels <=u-3 at any later state (after a firing p the new u is >=p+3). Thus at any visited twin center u>=12 one may take S=u-2: all previous labels <=S, the shadow stops at u, u<=S^2-2, and the full finite universal prefix including the following event is liftable as above. No extra upper bound on number of events or raw defect size is needed for this particular choice of J. Infinitely many twin visits suffice, but are not known.

## 2. Sharp time envelope and exact doubling classification

The new upper envelope is v<=u+1. Indeed some prime q|u+1 fires at odd n=u+3, strictly later than v. The winning time V<=u+3 and U=u+p-1>=u+2 imply V<=U+1. Base (4,5). Consequently 0<=d=2v-u<=u+2. Write L=u+3-v>=2.

At u>=6, if both u-1,u+1 prime, their first clocks are 2(u-1) and u+3 respectively; the plus label wins, p=u+1, U=2u, V=u+3, D=6. It is a strict new record since every earlier label <=u-3. Also any event p>(u+1)/3 at u>=6 is necessarily this doubling-type event (not necessarily twin): composite neighbors have every prime factor <=(u+1)/3, and a prime minus neighbor u-1 has its even clock at 2(u-1)>u+3. A prime plus neighbor can win only at u+3.

Exact classification of doubling at u>=6: let q be the least prime divisor of u-1. Doubling occurs iff u+1 is prime, q>=5, and L<=q+4. Proof: q=3 gives an earlier even clock at u+2>v. For any minus prime a>=5 the greatest even clock at or before u+3 is u-a-1, because the next is u+a-1>u+3. The greatest among these is u-q-1. All earlier clocks are excluded exactly when v>=u-q-1, or L<=q+4. If u+1 prime the plus clock is u+3, so this is necessary and sufficient. If q=3 then doubling impossible; prime u+1>3 and q>=5 force u=0 mod6. For non-twin doubling q<=sqrt(u-1), hence

    d=u+6-2L >= u-2q-2 >= u-2sqrt(u-1)-2.

This is a near-maximal deficit condition, not an exclusion. For example the local state (u,v)=(66,67) respects the envelope, but its next label is 67 at n=69 although 65 is composite. This does not demonstrate reachability from (4,5).

Additional exact clocks: if a minus p>=5 wins, V<=u-p-1, L>=p+5. If a plus p is not the least factor of u+1, it cannot win at u+3 (tie loses to smaller factor); hence V<=u+3-2p and L>=2p+1. Always L'=U+3-V>=p-1. These conditions supply a lag coordinate alternative to the deficit.

## 3. Event-count toll for false doubles and false records

Between consecutive doubling events, starting from the preceding poststate (X,X/2+3), all intervening pre-offsets >=6 are non-twin: every twin would double. If the next doubling at u>=X is non-twin, the bound above implies v>=u-sqrt(u-1)-1. For each of the m intervening events the previous potential Phi(v)=sqrt(2v+1) increases by less than 2 because a composite neighbor has least factor <=sqrt(u+1) and wait <=2sqrt(u+1), using that event's own offset in the potential proof. Thus

    2m >= sqrt(2u-2sqrt(u-1)-1)-sqrt(X+7)
        >= (sqrt(2)-1)*sqrt(u)-O(1).

In particular a doubling reached from the last reset in o(sqrt(u)) events must be a twin. This is unconditional, even if the previous doubling was false.

A different bound applies to the NEXT RECORD after a doubling with label r>=7. Its poststate is X=2r-2, v0=r+2, d0=6, and r was a record (all earlier labels <=r-4). The next record p>r exists by unbounded labels. If this next record is not twin, ALL events from X through it are non-twin, since any intermediate twin would have label u+1>r. Let m count these events including the next record, whose pre-offset is u>=X. Each wait <=2sqrt(u+1) and the final deficit is nonnegative. Therefore

    u+p-1-X <= 6+4m sqrt(u+1),
    m >= (u-r-3)/(4sqrt(u+1))
      >= (r-5)/(4sqrt(2r-1)),

since p>=r+2 and (u-r-3)/sqrt(u+1) is increasing on u>=2r-2. This bound does not require a cap on u/r. It proves that a next record occurring within o(sqrt(r)) events after a doubling is itself twin. To iterate into a twin-infinitude proof, one could establish such a bound (or a fixed smaller constant than 1/(4sqrt(2)) times sqrt(r)) uniformly for reached large doubling resets. That upper bound is open. Another sufficient condition: unbounded records with p-1>d+4sqrt(u+1) are twin, by the composite-neighbor wait bound and nonnegative postdeficit.

## 4. Cutoff boundary

At a twin record p=u+1 with previous record r, thresholds r<=S<=u-2 stop at this exact offset if u<=S^2-2. At S=u-1 or S=u the cutoff retains the minus prime u-1 only, so that shadow diverges at the record by taking u-1 instead. At thresholds S>=p the universal prefix includes the doubling. Thus a large family of shadow experiments counts the same prefixes, with precisely identified one-prime boundary cases. No assertion that all universal records are twins follows from these prefix facts.

## 5. Executed diagnostics

Source: research/min_primorial_universal_audit.py, commit 1bcbc9e290372c86ff44d785c564fc14c55d2f3d, verified blob c372c45cf4446beac08be1c0836febcd4236fcf3 equals locally executed source. Python/SymPy execution with cap 10^18:
- 5,326 events, final (u,v)=(1551315334856163024,775657667428081515).
- 58 twin pre-offsets (includes initial u=4), 58 records, zero non-twin records; 57 doubles, zero non-twin doubles.
- Only 3 non-twin events had p^2>u+1; maximum observed deficit 42,642,012. Finite observations only.
- 88,000 literal gcd tick comparisons at u<=100000.
- 246 cutoff boundary/prefix checks (133 rough, 113 one-prime boundary), overlapping prefixes.
- Local false-double control (66,67)->(132,69), selected p67, confirms local envelope alone cannot exclude it.
- Last twin center 775657667428081512; neighbors 775657667428081511 and 775657667428081513. Previous twin center 387828833711245470; 203 events between their firing indices (203 from preceding poststate through next record inclusive). These are finite witnesses, not a new record in known twin prime size.
- Run: python research/min_primorial_universal_audit.py 1000000000000000000.

An exploratory independent scan of 2500 canonical offset seeds u=4,8,...,10000, v=u/2+3 for up to 100 events and pre-offset <=100000 found no non-twin double. This exploratory scan is not part of the persisted main audit and is not used in any theorem.

## 6. Next target

The new uniform upper-bound problem is short next-record time from a genuine doubling reset, or equivalently an exclusion of the alternative long no-twin blocks of length at least order sqrt(r). The observed doubling mechanism itself depends on encountering twin centers, so its finite repetitions do not prove that another will occur. The lag envelope and exact false-double threshold identify which non-twin alternative needs genuine canonical-ancestry arithmetic. No asymptotic upper bound, Lean verification or proof of twin infinitude yet.
