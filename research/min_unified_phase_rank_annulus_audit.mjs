// Phase-rank trim, true-tick entropy stability and far-phase witness audit.
function audit(X,focus=false){
const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),Ps=[30,210,2310],theta=.5,epsilon=.5,lim=7*X+B+20,S=new Int32Array(lim);
const ok=(x,m)=>{if(!x)throw Error(`${X}/${focus} ${m}`)},eq=(x,y)=>Math.abs(x-y)<=1e-7*Math.max(1,Math.abs(x),Math.abs(y)),mod=(a,b)=>(a%b+b)%b;
for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
let paths=[],proj=new Map(),tick=new Map(),N=0,hit=0,G=0,W=0,events=0,entropy=0,rankChecks=0,phaseKeys=0,rankThin=0,phaseStable=0,phaseFar=0,farChecks=0,positiveLower=0,positiveStableLower=0,stableChecks=0,farMass=0,actualFarMax=0,allRankPaid=0,allGood=0,moderate=0,energy=0,weightedClock=0,synthetic=0;
const key=(C,t)=>C+"|"+t;
function inc(C,t,b){let k=key(C,t),z=tick.get(k);if(!z){z={n:0,b:0};tick.set(k,z)}z.n++;z.b+=b}
for(let M=X;M<2*X;M++)if(S[M]===M){
 N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[];
 while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
  if(!p||v>cut)break;
  let J=C+p-1,g=p-1,w=v-t,k=C+"|"+p,o=proj.get(k);if(!o){o={C,p,n:0,slots:new Map()};proj.set(k,o)}
  let sl=o.slots.get(v);if(!sl){sl={v,b:0};o.slots.set(v,sl)}sl.b++;o.n++;
  for(let j=t;j<v;j++)inc(C,j,1);
  es.push({C,J,t,v,p,g,r,w,o,sl});events++;G+=g;W+=w;C=J;t=v;
 }
 inc(C,t,0);if(C-C0>=T)hit++;paths.push(es);
}
for(let o of proj.values()){let arr=[...o.slots.values()].sort((a,b)=>a.b-b.b||a.v-b.v),cum=0,paid=0;for(let s of arr){cum+=s.b;s.thin=cum<=theta*o.n;if(s.thin){paid+=s.b;rankThin++}s.smaller=arr.filter(t=>t.b<=s.b).reduce((a,b)=>a+b.b,0);ok(s.smaller>=cum&&(!s.thin?s.smaller>theta*o.n:true),"mass rank");ok(s.b===tick.get(key(o.C,s.v-1)).b,"phase tick capacity");rankChecks++;phaseKeys++}
ok(paid<=theta*o.n&&cum===o.n,"rank budget");
}
let gridStats=Ps.map(P=>({P,raw:0,rankPaid:0,capacity:0,eligible:0,stable:0,farPositive:0,farStablePositive:0,farMass:0,pairEnergy:0,weightedClock:0,checks:0}));
for(let es of paths){let prefix=[0];
 for(let e of es){let sum=0;for(let j=e.t;j<e.v;j++){let z=tick.get(key(e.C,j)),u=tick.get(key(j+1===e.v?e.J:e.C,j+1));ok(z.b>0&&u.n>=z.b&&z.n>=z.b,"tick branch");sum+=Math.log(z.n/z.b)+Math.log(u.n/z.b)}
 entropy+=sum;prefix.push(prefix.at(-1)+sum);e.n=tick.get(key(e.C,e.t)).n;
 }
 for(let z of gridStats){let P=z.P,prev=-1,next=new Int32Array(es.length),k=-1,cross=es.map(e=>Math.ceil(e.J/P)-Math.ceil(e.C/P));
 for(let i=es.length-1;i>=0;i--){if(cross[i])k=i;next[i]=k}
 let left=new Map(),right=new Map(),tagPaid=0;
 function add(m,k,v){m.set(k,(m.get(k)||0)+v)}
 for(let i=0;i<es.length;i++){let e=es[i];if(cross[i])prev=i;let l=prev,r=next[i];if(l>=0)add(left,l,e.w);if(r>=0)add(right,r,e.w);
 if(l<0||r<0)continue;
 if(es[l].sl.thin||es[r].sl.thin){tagPaid+=e.w;continue;}
 z.eligible++;allGood++;
 let stable=prefix[r+1]-prefix[l]<=epsilon+1e-10;
 if(stable){z.stable++;phaseStable++;for(let j of [l,r]){ok(es[j].sl.b<=Math.exp(epsilon)*e.n+1e-7,"stable phase upper");stableChecks++}}
 let minRatio=Infinity;
 for(let j of new Set([l,r])){let b=es[j],o=b.o,s=b.sl,R=b.p; // diagnostic radius: one selected prime, smaller than any nonzero exit lag
 let near=o.slots.size?Math.floor(R/b.p)+1:0,far=0;
 for(let a of o.slots.values())if(a.b<=s.b&&Math.abs(a.v-s.v)>R)far+=a.b;
 ok(far>=s.smaller-near*s.b&&far>theta*o.n-near*s.b-1e-7,"far rank lower");farChecks++;z.checks++;
 if(far>0){phaseFar++;farMass+=far;z.farMass+=far;actualFarMax=Math.max(actualFarMax,far)}
 if(theta*o.n-near*s.b>0){positiveLower++;z.farPositive++}
 if(stable&&theta*o.n-near*Math.exp(epsilon)*e.n>0){positiveStableLower++;z.farStablePositive++;ok(far>=theta*o.n-near*Math.exp(epsilon)*e.n-1e-7,"stable far lower")}
 minRatio=Math.min(minRatio,far/o.n);
 }
 if(minRatio>=theta/2){moderate++;weightedClock+=e.w;z.weightedClock+=e.w;}
 }
 let paidL=0,paidR=0;
 for(let [i,w] of left){let e=es[i];ok(w<=9*P*cross[i],"left cap");z.capacity++;if(e.sl.thin)paidL+=w}
 for(let [i,w] of right){let e=es[i];ok(w<=9*P*cross[i],"right cap");z.capacity++;if(e.sl.thin)paidR+=w}
 ok(tagPaid<=paidL+paidR+1e-7,"rank union");z.rankPaid+=tagPaid;allRankPaid+=tagPaid;
 z.raw+=P*cross.reduce((s,x)=>s+x,0);
 }
}
ok(entropy<=N*(2+Math.log(N))+1e-7,"entropy total");
for(let z of gridStats){let P=z.P,cap=0;for(let o of proj.values()){let n=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!n)continue;let thin=[...o.slots.values()].filter(s=>s.thin).reduce((a,s)=>a+s.b,0);cap+=9*P*n*thin;
 for(let s of o.slots.values())if(!s.thin){let far=[...o.slots.values()].filter(t=>t.b<=s.b&&Math.abs(t.v-s.v)>o.p).reduce((a,t)=>a+t.b,0);z.pairEnergy+=P*n*s.b*far/o.n}
 }
 ok(z.rankPaid<=2*cap+1e-7&&cap<=9*theta*z.raw+1e-7&&z.weightedClock<=36*z.pairEnergy/theta+1e-7,"aggregate rank/energy");
 energy+=z.pairEnergy;
}
for(let n of [8,16,32]){let a=Array.from({length:n},(_,i)=>({v:10*i,b:2})),s=a.at(-1),R=20,far=a.filter(x=>Math.abs(x.v-s.v)>R).reduce((z,x)=>z+x.b,0);ok(far>=theta*2*n-(Math.floor(R/5)+1)*s.b,"synthetic rank spacing");synthetic++}
let rd=x=>+x.toFixed(6);return {X,focus,B,T,N,hit,events,G,W,tickKeys:tick.size,projectedKeys:proj.size,phaseKeys,entropy:rd(entropy),entropyBound:rd(N*(2+Math.log(N))),rankChecks,rankThin,phaseStable,stableChecks,phaseFar,farChecks,positiveLower,positiveStableLower,farMass,actualFarMax,allRankPaid,allGood,moderate,weightedClock,energy:rd(energy),synthetic,grids:gridStats.map(z=>({...z,pairEnergy:rd(z.pairEnergy)}))};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
