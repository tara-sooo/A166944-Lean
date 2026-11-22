// A166944 canonical artificial starts: exact first-hit growth and event-time audit.
// Build: g++ -O3 -std=c++17 research/canonical_growth_travel_audit.cpp -o growth_audit
// Run: ./growth_audit 10000000
// Finite experiment only; NO global Cap B or twin-prime infinitude theorem.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using i64 = long long;
vector<int> spf;

vector<int> factors(int x) {
    vector<int> out;
    while (x > 1) {
        int p = spf[x] ? spf[x] : x;
        out.push_back(p);
        do { x /= p; } while (x % p == 0);
    }
    return out;
}

i64 next_at(i64 pos, i64 p, i64 residue) {
    i64 g = (residue - pos) % (2*p);
    if (g <= 0) g += 2*p;
    return pos + g;
}

int main(int argc, char** argv) {
    int maxM = argc > 1 ? atoi(argv[1]) : 1000000;
    if (maxM < 7 || maxM > 10000000) return 2;
    int bound = int((7LL*maxM + 3)/2 + 5);
    spf.assign(bound + 1, 0);
    for (i64 p = 2; p*p <= bound; ++p)
        if (!spf[p])
            for (i64 n = p*p; n <= bound; n += p)
                if (!spf[n]) spf[n] = int(p);

    const array<int,5> threshold{377,1000,10000,100000,1000000};
    array<i64,5> bestG{}, bestM{}, countOverQuarter{};
    i64 tested = 0, bad = 0, late = 0;
    i64 largestQuarterM = 0, largestBadM = 0, largestLateM = 0;
    i64 absoluteMaxG = 0, absoluteMaxGM = 0;
    vector<int> badStarts;
    for (int M = 7; M <= maxM; M += 2) {
        ++tested;
        i64 s = M+2, K = (7LL*M-1)/4;
        i64 pos=s, last=s, C=2LL*M-2;
        while (pos < K) {
            i64 next=K+1;
            for (int p : factors(int(C-1)))
                next = min(next,next_at(pos,p,0));
            for (int p : factors(int(C+1)))
                next = min(next,next_at(pos,p,p+2));
            if (next>K) break;
            i64 e = gcd((next & 1) ? next-2 : next,
                        (next & 1) ? C+1 : C-1);
            if (e<=1) { cerr << "bad first-hit at M="<<M; return 3; }
            C+=e-1;
            last=pos=next;
        }
        i64 G=C-(2LL*M-2), L=last-s;
        // Exact paper theorem; no large-M/prime assumptions.
        if (3*L>8*G+(M%3==1?0:21)) {
            cerr<<"growth/last-event inequality failed M="<<M; return 4;
        }
        if (G>absoluteMaxG) {absoluteMaxG=G; absoluteMaxGM=M;}
        for (int j=0; j<5; ++j) if (M>=threshold[j]) {
            if (bestM[j]==0 || G*bestM[j]>bestG[j]*M) {
                bestG[j]=G; bestM[j]=M;
            }
            if (4*G>=M) ++countOverQuarter[j];
        }
        if (M>=377 && 4*G>=M) largestQuarterM=M;
        if (2*L>M) {++late; largestLateM=M;}
        bool good = C-1>1 && spf[C-1]==0
                 && C+1>1 && spf[C+1]==0;
        if (!good) {
            ++bad;largestBadM=M;badStarts.push_back(M);
        }
    }
    cout << "Starts="<<tested<<" BAD="<<bad<<" latestBAD="<<largestBadM
         <<" lateLastEvent="<<late<<" latestLate="<<largestLateM
         <<" maxGrowth="<<absoluteMaxG<<" at M="<<absoluteMaxGM<<"\n";
    for (int j=0; j<5; ++j)
        if (bestM[j])
            cout << "M>="<<threshold[j]<<" max G/M="<<bestG[j]
                 <<"/"<<bestM[j]<<" = "<<double(bestG[j])/bestM[j]
                 <<"; violations G>=M/4: "<<countOverQuarter[j]<<"\n";
    cout<<"Last G>=M/4 for M>=377: "<<largestQuarterM<<"\n";
    if (maxM==10000000) {
        const vector<int> expected{11,13,23,25,39,41,43,45,305};
        if (tested!=4999997 || badStarts!=expected || late!=21
            || largestLateM!=375 || largestQuarterM!=1441
            || countOverQuarter[0]!=70 || countOverQuarter[2]!=0
            || absoluteMaxG!=69652 || absoluteMaxGM!=7209299
            || bestM[2]!=11687 || bestG[2]!=1930
            || bestM[3]!=274775 || bestG[3]!=14722
            || bestM[4]!=1086431 || bestG[4]!=15748) {
            cerr<<"10M finite-regression mismatch\n"; return 5;
        }
    }
    cout<<"PASS finite original first-hit/gcd scan; global growth bound OPEN\n";
}
