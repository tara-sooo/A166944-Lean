# A166944: exact permutation energy, common-core CRT, and overlap-depth bridge

Date: 2026-11-22 JST. **Status:** new elementary paper proofs and exact integer audits; **no new Lean kernel compilation, no proof of Cap B or infinitude of twin primes.** This extends the [return-span permutation note](2026-11-22-return-span-entropy-permutation-lattice.md), the [rainbow CRT capacity note](2026-11-22-cross-prime-rainbow-CRT-capacity.md), and the [aligned reset 12-wheel note](2026-11-22-reset-backbone-mod12-recharge-and-sentinel.md). All recurrences below use original parity-dependent gcd and post-event horizon `D(r)`.

## 1. Inversion energy is exactly weighted return-span dispersion

Let `A` and `B` be permutations of the same `k` distinct prime increment values `p>=5`. Between the blocks may be any event word `W_middle`; each displayed event increment must equal its named prime. Let `w_p=p-1`, `S=sum_p w_p`, `H=sum_{e in W_middle}(e-1)`, and `T0=S+H`. Write `A_before(p)` and `B_before(p)` for sums of other key weights preceding `p` in each block; define `Delta_p=B_before(p)-A_before(p)`. The inclusive horizon growth from the first `p` event to the second one is

    T_p=D(second p)-D(first p)=T0+Delta_p.            (1)

Let `Inv(A,B)` be the ordered pairs `(p,q)` with `p before q` in A and `q before p` in B. Every inversion contributes `+w_q` to `Delta_p`, and `-w_p` to `Delta_q`. Hence

    sum_p w_p*Delta_p=0,                             (2)
    boxed: E=sum_p w_p*Delta_p^2
            =sum_{(p,q) in Inv} w_p*w_q*(Delta_p-Delta_q). (3)

For an inverted `(p,q)`, the difference is **exactly**

    Delta_p-Delta_q = w_p+w_q
         +sum_{keys strictly between p,q in A}w
         +sum_{keys strictly between q,p in B}w.  (4)

Consequently the positive inversion-energy lower bound is

    boxed: E>=sum_{Inv}(p-1)(q-1)(p+q-2).           (5)

This is an exact, overlap-safe representation of the **L2 dispersion** of return spans, not a sum of duplicated horizon-growth charges.

**Sharp upper bounds:** Put `S=sum w_p`, `Delta_min=min Delta_p`, `Delta_max=max Delta_p`. By the weighted mean-zero identity and `(Delta_max-Delta_p)(Delta_p-Delta_min)>=0`,

    E<=S*Delta_max*(-Delta_min)
      <= S*(Delta_max-Delta_min)^2/4.               (6)

An independent **optimal over all permutations** bound is

    boxed: E <= (S^3-sum_p w_p^3)/3.                 (7)

Equality in (7) holds when B is the complete reverse of A. To prove (7), view each key p as an interval of length w_p in a packing of `[0,S]`, with center `c_A(p)=A_before(p)+w_p/2` and `c_B(p)` analogously. `Delta_p=c_B-c_A` and `E=sum w_p(c_B-c_A)^2`. Each `sum w_p*c_A(p)^2` is invariant under block order, because `integral_0^S t^2 dt=sum_p(w_p*c_A(p)^2+w_p^3/12)`. The cross term `sum w_p*c_A*c_B` is minimized when B reverses A: swapping an adjacent pair that remains in A order decreases the cross term by `w_pw_q*(c_A(q)-c_A(p))>0`. In the reverse arrangement `c_B=S-c_A`; evaluating the centered integral gives `E=(S^3-sum w^3)/3`.

**Combined order-or-spread theorem:**

    boxed: S*(Tmax-T0)*(T0-Tmin)
        >=sum_{Inv}(p-1)(q-1)(p+q-2).              (8)

Unlike an unweighted inversion count, this charges every reversed pair by its actual prime sizes. This is a genuine necessary condition, but (7) shows it is also an ordinary permutation-geometry bound; it does not by itself exclude long canonical paths.

**Authentic sharp case:** the real A166944 event subword `7,13,...,13,7` at indices `9,15,...,1326,1339` has `w7=6`, `w13=12`, `Delta7=12`, `Delta13=-6`, `T0=2634`, `T7=2646`, `T13=2628`. Thus `E=1296`, equal to the inversion lower (5) AND the two-sided bound in (6).

## 2. Exact CRT minimum for ANY two corresponding prime blocks

Return-span residues from the original gcd are

    tau_p= 0  for same parity;
           -2 for first even, second odd;
           +2 for first odd, second even.

By (1), for each distinct key p,

    boxed: H == tau_p-S-Delta_p (mod p).            (9)

The Chinese remainder theorem gives one residue `h0` in `[0,P)` modulo `P=product_p p`. Since H>=0,

    boxed: actual middle growth H>=h0,
           total two-block growth >=2*S+h0.        (10)

This is a **single CRT capacity constraint** on all distinct keys; no cost is double counted. If every middle increment e is `1 mod 12`, add `H==0 mod12` to (9), obtaining a unique least `h0` modulo `12P` (all p>=5 are coprime to 12). The CRT minimum is **necessary and sufficient for the listed prime-return residue equations alone**, not for realizing the complete first-hit trajectory.

**Concrete 12-frozen reversed-key exclusion:** take `A=(421,2521)`, `B=(2521,421)`, all hits at odd indices. Then `S=2940`, `(Delta421,Delta2521)=(2520,-420)`, and (9) plus `12|H` yields

    H==1,479,828 (mod 12,736,092);
    boxed: required total growth >=1,485,708.     (11)

For the artificial canonical start at the **actual twin-prime input** `M=500113` (`M-2=500111` also prime), `K=floor((7M-1)/4)=875197` and the universal horizon bound gives `G_M<=2K-(2M-2)=750170`. Thus a 12-frozen `421,2521,...,2521,421` return motif is impossible **inside this canonical window**, regardless of what middle event word it attempts. This is a rigorous finite pattern exclusion, **not a statement that M=500113 is an attained record of the original recurrence**.

The previous genuine `7,13,...,13,7` motif has actual `H=2616`; its CRT minimum without a 12-wheel assumption is `h0=68 (mod 91)` and actual `H=68+28*91`.

## 3. Common-core CRT for arbitrary factor-reuse intervals

We can remove the identical-prime-increment and two-contiguous-block assumptions entirely. Let `p_i>=5` be DISTINCT primes and `(u_i,v_i)` selected occurrences (not necessarily consecutive) with `p_i|d(u_i),p_i|d(v_i)`, and assume all first occurrences precede all second occurrences:

    u=max_i u_i < v=min_i v_i.

Define the **shared core growth** `H=D(v)-D(u)`, and the nonnegative **fringe growth**

    F_i = [D(u)-D(u_i)] + [D(v_i)-D(v)].

The complete return growth for key pi equals `H+F_i`, and the parity-dependent residue requires

    boxed: H == tau_i-F_i (mod pi) for all i.       (12)

Hence CRT yields `H==h0 (mod P)` with `P=product pi`. No ordering, parity, pure reset, or prime-valued increments is required. As long as every selected endpoint is a genuine event with the indicated prime factor, (12) is exact.

The original recurrence satisfies `X(n)=2n-D(n)>=0`. Thus

    0<=H=2(v-u)+X(u)-X(v)<=2(v-u)+X(u).            (13)

If `P>2(v-u)+X(u)`, then **H must equal h0 exactly**; if `h0>2(v-u)+X(u)`, the proposed partial history is impossible. This is an exact *CRT bridge certificate* for a central unknown interval, with no horizon growth counted more than once. When BOTH u,v are aligned reset endpoints, equation (13) already determines H from their indices and offsets, so CRT uniqueness then checks arithmetic consistency rather than supplying an independent contradiction.

**True original examples:** Selected keys `(5,13,149,313)`, using their earliest/latest events through n=2.5M, have `u=356857,v=357004`, `X(u)=304`, `P=3031405`, `h0=300`, and real `D(v)-D(u)=300`; local cap is 598. More strongly, 12 DISTINCT keys `(5,7,11,13,17,19,29,31,37,47,149,313)` have *consecutive* reuse intervals overlapping the event n=356874. Their common core is `[356873,356883]`, their prime product is `117868154539690555`, local upper bound 308, and **CRT residue and actual core growth are both only 8**. This is a concrete warning: even a huge product and high overlap do NOT force a large CRT residue or contradict the original recurrence.

## 4. Interval-graph overlap charging: a global inequality without double counting

For each odd prime p>=5, select ALL **consecutive** occurrences of p as a divisor of nonunit increments in a finite path segment. Each consecutive return interval `(u_i,v_i]` carries inclusive growth `T_i=D(v_i)-D(u_i)`. For a given p, these intervals do not overlap in their interiors (the closing event is covered by the earlier interval only).

At every event r, let `m(r)` be the number of selected return intervals covering r, and `d=max_r m(r)`. All intervals covering a single r belong to DIFFERENT prime keys. The exact weighted covering identity is

    boxed: sum_i T_i = sum_{events r} m(r)*(d(r)-1)
                   <= d*[D(final)-D(initial)].     (14)

The generic Lean-proved factor reuse bound plus the growth at the second event gives `T_i>=2(p_i-1)` for each p>=5; thus `2*sum_i(p_i-1)<=d*G`. Under a 12-frozen segment (every increment congruent to 1 mod12) with each reused p==1 mod12, the **sharp inclusive return minima** are

    first -> second      T_i minimum
    even -> even         12p
    even -> odd          2p-2
    odd  -> even         10p+2
    odd  -> odd          12p.                      (15)

For p with `t_p` occurrences, `m_p=t_p-1` consecutive returns, cheap even->odd returns cannot occur consecutively. Therefore at least `floor(m_p/2)` returns have minimum `10p+2` or greater. So the **new exact overlap-depth/refill inequality** is

    boxed: sum_p [2(p-1)*m_p+(8p+4)*floor(m_p/2)]
                  <= d*G.                           (16)

This upgrades the earlier per-prime 12-wheel estimates to a *global concurrent-demand inequality*, with multiplicity d accounting explicitly for every overlapping payment. No assumption that different keys have nonoverlapping returns is made.

**Conditional asymptotic triple-overlap theorem.** Let M tend to infinity along actually attained canonical records and suppose a contiguous, aligned k=1-only, 12-frozen, all-prime reset run in the cutoff window has event increments in `[a*sqrt(M),b*sqrt(M)]`, with fixed `0<a<=b`, and occupies at least `delta*M` index units for fixed delta>0. Write N for its event count and J for its number of different prime keys. Aligned endpoints have offset 0/6 so the run growth `G=2*travel+O(1)=Omega(M)`. Since each increment <=b sqrt(M), `N=Omega(sqrt(M))`; the elementary prime-counting estimate gives `J<=pi(b sqrt(M))=O(sqrt(M)/log(M))=o(N)`. In (16), `sum m_p=N-J` and `sum floor(m_p/2)>=(N-2J)/2`. Hence, with alpha=a sqrt(M) and beta=b sqrt(M),

    d*(beta-1)*N >= d*G
       >= 2*(alpha-1)*(N-J)+(8*alpha+4)*(N-2J)/2
       = 6*alpha*N-(10*alpha+2)*J.

Consequently

    boxed: d>=6*a/b - o(1).                         (17)

For the dyadic band `b=2a`, this forces `d>=3` for sufficiently large M. Because at any event the d overlapping **consecutive** returns have different prime keys, some common core is crossed by THREE distinct primes of size `>=a sqrt M`; their product exceeds the O(M) entire cutoff horizon budget, so the core's exact growth is CRT-rigid as in (12)-(13).

If the run uses only odd-index aligned reset hits, all same-prime returns have positive growth divisible by `12p`, strengthening (17) to `d>=12*a/b-o(1)` and yielding `d>=6` in a dyadic band.

These are **conditional reductions**, not a proof that a macroscopic dyadic 12-frozen run actually occurs, or that a CRT-rigid core must be contradictory. The simpler counterexample above with 12 simultaneous real reuse keys and tiny CRT residue shows why mere product size is insufficient.

**Independent finite audit:** the actual original A166944 through index 2,500,000 has 250 nonunit events (including n=2), 45 distinct prime factor keys >=5, and 125 consecutive return intervals. Their inclusive growth sums to 30,879,800, while total horizon growth after n=2 is 2,860,768; the maximal overlap depth is 12, so (14) holds. The 12-wheel inclusive minima were checked for all qualifying primes p<1200. All 129,440 permutations of ranks 2..5 with weights 1..4 passed (2)-(7), including 1,360 reversal extremizers. The exact actual 7,13 reversed event word and the 4/12-key CRT cores were independently checked from original per-index gcds.

## 5. A full first-hit ARTIFICIAL inverse-word construction: a real limitation

The minimum middle growth in (11) is a hard necessary capacity cost, but not a universal ban on reversed-key returns. Let

    p=421, q=2521, r=2497753861,

all prime and 1 mod420. The prime r satisfies `r==14 mod 421`, `r==2 mod 2521`, and `r==1 mod420`. Choose a large artificial canonical-shaped state `(s0,C0)`, `s0=(C0+6)/2`, with `C0==0 mod420` and exact starting horizon-neighbor congruences:

    C0+1==0 mod p;
    C0+1+(p-1)==0 mod q;
    C0+1+(p-1)+(q-1)==0 mod r.

The horizon shifts before the five proposed events `p,q,r,q,p` are `0,p-1,p+q-2,p+q+r-3,2p+q+r-4`. The designated selected prime is the ONLY one active on C_i±1 at each respective stage: p at stages 0,4; q at stages 1,3; r at stage2. Every other odd prime ell>=11 and <=r+6 can be deactivated in ALL five stages by choosing C0 mod ell outside at most 10 forbidden residues (fewer than ell), while 3,5,7 stay inert because C_i=0 mod420 throughout. CRT yields arbitrarily large solutions C0, making all intermediate gcds 1 and each odd-index reset first hit exactly the listed prime at gap `(prime-1)/2`. Choosing C0 sufficiently large places the entire five-event word inside the artificial canonical cutoff window.

Here `H=r-1=2497753860`, which indeed satisfies `H==1479828 mod 12736092`. Thus the reverse word **is first-hit realizable** with sufficiently large artificial starting M, despite the potentially enormous CRT middle-growth cost. It is NOT asserted that such a start is attained by the original recurrence, nor that it has a twin-prime input M.

## 6. Next precise target

The present research resolves overlap *accounting*: (3) is exact inversion energy, (12) is universal common-core CRT, and (14)-(17) convert many prime reuses into overlapping different-key core constraints. It does NOT turn the constraints into an asymptotic contradiction. A viable new target is a **first-hit anti-resonance theorem**: in a genuine attained canonical window, after the complete fringe first-hit restrictions are imposed, at least one forced large-prime common core must have a CRT residue incompatible with `H=2(v-u)+X(u)-X(v)`, or directly force a long unit suffix / terminal twin pair. That statement remains unproved. No new Lean compilation was performed.