// Rare high-factor exposure of shallow canonical MIN histories.
// Run: node research/min_clock_shallow_high_audit.mjs 1024 4096 16384 65536 262144
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,len=7*X/2+1;
 const ell=Math.log(Math.log(B)),S=Math.max(1,Math.log(ell)),Q=Math.ceil(B/Math.exp(Math.sqrt(ell))),P=Math.floor(B**.25);
 const check=(x,m)=>{if(!x)throw Error(m)};
 check(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(7*X+4),primes=[];
 for(let p=2;p<spf.length;p++)if(!spf[p]){
  spf[p]=p;if(p<=B)primes.push(p);
  if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 let L=2,y=2;
 for(const p of primes)if(p>2){if(L*p>6*S**.25)break;L*=p;y=p;}
 check(y<Q&&P<Q,'thresholds');
 const small=primes.filter(p=>y<p&&p<=P),high=primes.filter(p=>p>=Q);
 const hasHigh=new Uint8Array(len),r=new Int32Array(len);
 function highFactor(n){
  while(n>1){const p=spf[n];if(p>B)return 0;if(p>=Q)return p;while(n%p===0)n/=p;}
  return 0;
 }
 const highByShift=new Int32Array(4);let candidates=0,mixedCandidateVisits=0,maxMixed=0,maxD=0,S0=0;
 const shifts=[-1,0,1,2],W=new Float64Array(len),WK=new Float64Array(len),mixed=new Int32Array(len);
 const dcount=new Int16Array(len),logsum=new Float64Array(len);
 function prob(J,p){
  const i=J/2;if(!dcount[i]){
   for(let n of [J,J+2])while(n>1){const q=spf[n];if(q>B)break;if(q>y){dcount[i]++;logsum[i]+=Math.log(q);}while(n%q===0)n/=q;}
   maxD=Math.max(maxD,dcount[i]);
  }
  check(dcount[i]>0,'candidate divisor');return .5/dcount[i]+.5*Math.log(p)/logsum[i];
 }
 for(let C=2*X;C<7*X;C+=2){
  const i=C/2;
  for(let j=0;j<4;j++)if(highFactor(C+shifts[j])){hasHigh[i]|=1<<j;highByShift[j]++;}
  if(hasHigh[i])candidates++;
  let q=Math.min(spf[C-1],spf[C+1]);if(q<=B){r[i]=q;S0+=q;}
 }
 // Each CRT tuple determines the original root from C and its word.
 // Count all possible even horizons satisfying each tuple, with exact CRT on C/2.
 const mod=(a,m)=>((a%m)+m)%m;
 const inv=(a,p)=>{let x=1,b=mod(a,p),n=p-2;while(n){if(n%2)x=x*b%p;b=b*b%p;n=Math.floor(n/2);}return x;};
 function crt(a,m,b,p){
  if(m%p===0)return a%p===b?[a,m]:null;
  const k=mod((b-a)*inv(m,p),p);return [a+m*k,m*p];
 }
 function addConstraint(state,offset,p){
  if(!state)return null;
  return crt(state[0],state[1],mod(-offset*((p+1)/2),p),p);
 }
 const tupleCounts=[0,0,0];let crtUpper=0,tuples=0,consistent=0;
 function countWord(ps,es,sg){
  let suffix=0,conds=[];
  for(let k=ps.length-1;k>=0;k--){
   suffix+=es[k+1];conds.push([sg[k]-suffix,ps[k]]);suffix+=ps[k]-1;
  }
  for(const p of high)for(const s of shifts){
   tuples++;let state=addConstraint([0,1],s,p);
   for(const [off,q] of conds)state=addConstraint(state,off,q);
   if(!state)continue;consistent++;
   const [a,m]=state,lo=X,hi=7*X/2-1;
   const n=Math.max(0,Math.floor((hi-a)/m)-Math.ceil((lo-a)/m)+1);
   tupleCounts[ps.length]+=n;crtUpper+=n;
  }
 }
 const es=Array.from({length:L/2},(_,i)=>2*i);
 for(const e0 of es){
  countWord([],[e0],[]);
  for(const p of small)for(const e1 of es)for(const s1 of [0,2]){
   countWord([p],[e0,e1],[s1]);
   for(const q of small)for(const e2 of es)for(const s2 of [0,2])countWord([p,q],[e0,e1,e2],[s1,s2]);
  }
 }
 function hit(t,C,K){
  let T=K+1,P=0;
  for(const side of [-1,1]){
   let v=C+side;while(v>1){const p=spf[v];if(p>B)break;
    const m=2*p,res=side===-1?0:p+2,u=t+1+((res-(t+1)%m+m)%m);
    if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
    while(v%p===0)v/=p;
   }
  }return [T,P];
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
 const V=new Map(),key=(t,C)=>t*(7*X+4)+C;
 const newCounts=()=>[0,0,0,0,0]; // total, shallow, high, shallow&high, shallow unflagged
 function get(t,C){const k=key(t,C);if(!V.has(k))V.set(k,{a:newCounts(),edges:new Map()});return V.get(k);}
 let roots=0,smallRoots=0,mixedRoots=0,firstHighRoots=0,reverseOnly=0,selectedShallowHigh=0,
     firstMeet=0,markedMeet=0,events=0,literal=0,R=0,RK=0,shallowKeptCost=0,keptRoots=0,finished=0,keptFinished=0,shallowMaxAge=0,maxMixedK=0;
 const seenTuple=new Set();
 const costByDepth=[0,0,0];
 for(let M=X+1;M<2*X;M+=2){
  const s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),records=[];
  let t=s,C=C0,medium=0,large=0,low=0,prev=null,last=0,flag=false,firstType='',firstHigh=false,firstMask=0,smallHistory=true,kappa=L;
  const word=[],offsets=[],sides=[];
  for(;;){
   check(C<=2*t&&C-C0<=2*H+B+6,'prefix gain');
   const mask=hasHigh[C/2],shallow=medium<=2;
   if(shallow&&!large&&mask){
    if(smallHistory){
     const allE=[...offsets,low],ps=word,sg=sides;
     check(allE.length===ps.length+1&&ps.length===medium,'compressed word');
     check(allE.reduce((a,b)=>a+b,0)+ps.reduce((a,p)=>a+p-1,0)===C-C0,'gain reconstruction');
     let suffix=0;
     for(let k=ps.length-1;k>=0;k--){suffix+=allE[k+1];check((C-suffix+sg[k])%ps[k]===0,'small-word congruence');suffix+=ps[k]-1;}
     const j=shifts.findIndex((_,j)=>mask&(1<<j)),p=highFactor(C+shifts[j]);
     check(p>=Q,'high witness');
     const tk=[C,p,shifts[j],ps.join(','),allE.join(','),sg.join(',')].join('|');
     check(!seenTuple.has(tk),'root/visit tuple injective');seenTuple.add(tk);
    }else{
     mixedCandidateVisits++;mixed[C/2]++;maxMixed=Math.max(maxMixed,mixed[C/2]);maxMixedK=Math.max(maxMixedK,kappa);
    }
    if(!flag){flag=true;firstType=smallHistory?'small':'mixed';firstMask=mask;costByDepth[medium]++;}
   }
   const v=get(t,C),ic=v.edges.get(prev)||newCounts(),fresh=v.a.map((n,i)=>n-ic[i]),incomingHigh=last>=Q;
   check(fresh.every(n=>n>=0),'incoming subset');
   firstMeet+=fresh[0];
   const marked=shallow?(incomingHigh?fresh[0]:fresh[2]):(incomingHigh?fresh[1]:fresh[3]);
   if(marked&&shallow)check(flag,'shallow first-meeting high exposure');
   if(incomingHigh)check(fresh[4]===0,'prior shallow with incoming high flagged');
   markedMeet+=marked;
   const inc=[1,+shallow,+incomingHigh,+(shallow&&incomingHigh),+(shallow&&!flag)];
   for(let i=0;i<5;i++){v.a[i]+=inc[i];ic[i]+=inc[i];}v.edges.set(prev,ic);
   if(t>=s+H)break;
   const [u,p]=hit(t,C,K);
   if(X<=1024){
    let aa=K+1,bb=0;for(let j=t+1;j<=K;j++){const g=gcd(j%2?j-2:j,j%2?C+1:C-1);
     if(g>1&&spf[g]<=B){aa=j;bb=spf[g];break;}}
    check(aa===u&&bb===p,'literal MIN');literal++;
   }
   if(!p){check(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');finished++;break;}
   const D=C+p-1,q=r[C/2],dur=Math.max(0,Math.min(u-s,H)-Math.max(t-s,a)),w=dur/(2*q);
   check(u-t<=2*q&&q<=p,'wait bound');
   if(p>=Q&&shallow){check(flag,'selected high exposure');selectedShallowHigh++;if(!large)firstHigh=true;}
   if(shallow&&!flag){
    check(!large&&p<Q&&C-C0<=2*(Q-1)+3*(L-2),'unflagged shallow gain');
    check(u-s<=8*Q+9*L,'unflagged shallow age');
    shallowMaxAge=Math.max(shallowMaxAge,u-s);
   }
   if(dur)records.push({C,w,dur,shallow});
   if(p<=y){low+=p-1;check(low<L,'LOW barrier');}
   else{
    const sg=D%p===0?0:2;check((D+sg)%p===0,'post congruence');
    if(!large&&medium<=2){offsets.push(low);word.push(p);sides.push(sg);}
    kappa*=L/prob(D,p);low=0;
    if(p>=Q)large++;else{medium++;if(p>P)smallHistory=false;}
   }
   prev=key(t,C);last=p;t=u;C=D;events++;
  }
  if(firstHigh){check(flag,'first high root flagged');firstHighRoots++;}
  if(flag){roots++;if(firstType==='small')smallRoots++;else mixedRoots++;if((firstMask&5)===0)reverseOnly++;}
  else{keptRoots++;if(t<s+H)keptFinished++;}
  let cost=0;
  for(const v of records){W[v.C/2]+=v.w;R+=v.dur/2;cost+=v.dur/2;
   if(!flag){WK[v.C/2]+=v.w;RK+=v.dur/2;if(v.shallow)shallowKeptCost+=v.dur/2;}
  }
  check(cost<=B,'per-root cost');
 }
 check(roots===smallRoots+mixedRoots&&roots+keptRoots===N,'root partition');
 check(seenTuple.size<=crtUpper&&smallRoots<=seenTuple.size,'CRT upper bound');
 // Uniform finite mixed-history cap from Kraft. At most two non-LOW labels,
 // one >P, using the actual maximum reverse divisor count (over visited J).
 const largeFactor=4*L*Math.log(7*X+2)/Math.log(P+1),anyFactor=2*L*maxD;
 const mixedCap=L*Math.max(1,largeFactor,largeFactor*anyFactor);
 check(maxMixedK<=mixedCap+1e-6*Math.max(1,mixedCap),'mixed complexity cap');
 check(maxMixed<=mixedCap+1e-6&&mixedCandidateVisits<=candidates*mixedCap+1e-6,'mixed incidence cap');
 check(mixedRoots<=mixedCandidateVisits&&R-RK<=B*roots,'linear root deletion');
 if(8*Q+9*L<=a)check(shallowKeptCost===0,'eventual no shallow slab');
 let E=0,EK=0;
 for(let C=2*X;C<7*X;C+=2){E+=r[C/2]*W[C/2]**2;EK+=r[C/2]*WK[C/2]**2;}
 check(EK<=E+1e-6*Math.max(1,E),'energy monotone');
 return {X,B,Q,P,L,y,candidates,highByShift:[...highByShift],tupleCounts,crtUpper,tuples,consistent,smallVisits:seenTuple.size,mixedCandidateVisits,maxMixed,maxMixedK,mixedCap,maxD,roots,smallRoots,mixedRoots,firstHighRoots,reverseOnly,selectedShallowHigh,firstMeet,markedMeet,events,literal,R,RK,shallowKeptCost,keptRoots,finished,keptFinished,shallowMaxAge,costByDepth,E,EK,S0};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144])console.log(JSON.stringify(audit(X)));
