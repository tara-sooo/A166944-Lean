// Near-square-root horizons, rough endpoint exceptions, idle overlap and diagonal key capacity.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let x=p*p;x<=N+2;x+=p)if(!spf[x])spf[x]=p;
 function fac(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);n/=p}return a}
 function fs(n){return [...new Set(fac(n))]}
 function lp(n){return n<=1?Infinity:spf[n]||n}
 function ev(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 let z={slabs:[],roots:0,events:0,roughStates:0,semiprimeChecks:0,coverChecks:0,energyChecks:0,clockStripChecks:0,bandKeys:0,capacityChecks:0,overlapChecks:0,diagonalChecks:0,highGainChecks:0};
 for(let R of [12000,48000,192000,480000,1000000]){
  let S=Math.sqrt(2*R+1),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),K=Math.max(5,Math.floor(Math.sqrt(R)/Math.log(R)**.5)),T=Math.floor(4*K),L=Math.floor(2*T/9),n=(hi-lo)/6+1,lower=R-2*T-6;
  if(lower<=0)continue;
  let candidates=new Set(),rough=new Set(),bad=new Set(),incidences=0;
  for(let a=2*Math.ceil(lower/2);a<=2*R;a+=2){
   if(Math.min(lp(a-1),lp(a+1))<=K)continue;
   rough.add(a);z.roughStates++;
   let f=fac(a-1),g=fac(a+1);if(f.length===1&&g.length===1)continue;
   bad.add(a);
   if(K**3>2*R+1){
    ck(f.length<=2&&g.length<=2,"semiprime");
    for(let [d,F] of [[a-1,f],[a+1,g]])if(F.length===2){
     ck(F[0]>K&&F[0]<=S&&F[0]*F[1]===d,"small factor");candidates.add(a);incidences++;z.semiprimeChecks++;
    }
   }
  }
  if(K**3>2*R+1)ck(candidates.size===bad.size,"bad cover");
  let sumG=0,sumI=0,idle=0,small=0,smallBad=0,idleBad=0,masses=new Map(),selected=new Map(),keys=new Map(),keyRoot=new Map(),squareT=Math.ceil(8*S),sumSquareG=0,squareWitness=0,firstIdle=0,firstIdleBad=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,v=3-A/2,v0=v,W=0,G=0,twinSeen=false,hadFirst=false;
   while(true){let x=ev(a,v);if(v+x.w>v0+T)break;
    let t=v+x.w,h=a/2+t;
    ck(h>=1&&h<=T+3&&x.p<=2*T+7,"strip");
    let k=a+":"+t,e=keys.get(k)||{a,t,p:x.p,e:x.e,m:0,g:x.p-1,wait:0};
    ck(e.p===x.p,"same key");e.m++;e.wait+=x.w;keys.set(k,e);
    a-=x.p-1;v=t;W+=x.w;z.events++;z.clockStripChecks++;
   }
   G=A-a;let I=T-W,x=ev(a,v),isTwin=x.q>S; // q>sqrt(a+1) is exact; using S can miss a twin at small R only
   isTwin=x.q>Math.sqrt(a+1);sumG+=G;sumI+=I;z.roots++;
   ck(W<=9*G/4+8&&G<=2*T+6&&I<x.w,"gain idle");
   if(I>2*K){idle++;ck(rough.has(a),"idle rough");masses.set(a,(masses.get(a)||0)+1);if(!isTwin){idleBad++;ck(bad.has(a),"bad idle")}}
   if(G<=L&&I>2*K){small++;if(!isTwin)smallBad++;let arr=selected.get(a)||[];arr.push({A,G,W,I,begin:v,end:v0+T});selected.set(a,arr)}
   let first=ev(A,v0);if(first.w>2*K){firstIdle++;if(first.q<=Math.sqrt(A+1))firstIdleBad++}
   // Separate square-root horizon
   let b=a,u=v;
   while(true){let e=ev(b,u);if(u+e.w>v0+squareT)break;b-=e.p-1;u+=e.w}
   let gg=A-b;sumSquareG+=gg;if(gg<(4/9)*(squareT-2*S-8)){ck(ev(b,u).q>Math.sqrt(b+1),"square witness");squareWitness++}
  }
  let C=[...masses.values()].reduce((s,m)=>s+m*m,0),D=masses.size;
  ck(idle*idle<=D*C&&idleBad<=bad.size*(Math.floor((2*T+6)/6)+1),"energy cover");z.energyChecks++;
  ck(smallBad<=bad.size*(Math.floor(L/6)+1),"small bad cover");z.coverChecks++;
  let Cs=0,Ds=selected.size;
  for(let [a,arr] of selected){
   Cs+=arr.length**2;
   let beg=Math.max(...arr.map(x=>x.begin)),end=Math.min(...arr.map(x=>x.end));
   ck(beg<=end,"shared idle overlap");z.overlapChecks++;
   for(let x of arr){ck(x.G===x.A-a&&x.begin<=end&&x.end>=end,"common tick");z.diagonalChecks++}
  }
  ck(small*small<=Ds*Cs,"selected energy");
  // Fixed prime/side physical keys have strip width T+3, independent of R.
  let groups=new Map(),gainAll=0;
  for(let e of keys.values()){let k=e.p+":"+e.e,g=groups.get(k)||{p:e.p,e:e.e,n:0};g.n++;groups.set(k,g);gainAll+=e.m*e.g}
  ck(gainAll===sumG,"gain ledger");
  let cap=0;
  for(let g of groups.values()){
   let npos=Math.floor((2*R-lower)/(2*g.p))+1,nt=Math.floor((T+2)/(2*g.p))+1;
   ck(g.n<=npos*nt,"diagonal key capacity");z.capacityChecks++;z.bandKeys+=g.n
  }
  let high=[];
  for(let Y of [Math.max(5,Math.floor(T/Math.log(R))),Math.max(5,Math.floor(T/2)),T]){
   let arr=[...keys.values()].filter(e=>e.p>=Y),actual=arr.reduce((s,e)=>s+e.m*e.g,0),unweighted=arr.reduce((s,e)=>s+e.g,0),sumSecond=arr.reduce((s,e)=>s+e.g*e.m*e.m,0);
   // Pair energy restricted to roots sharing a key. Each pair shares
   // at most 2T+6 gain counted over keys.
   let approx=arr.reduce((s,e)=>s+e.g*Math.min(e.m,4),0);
   ck(actual*actual<=unweighted*sumSecond+1e-6&&approx<=4*unweighted,"high gain CS");z.highGainChecks++;
   high.push({Y,actualPerRoot:actual/n,unweighted,keys:arr.length})
  }
  z.slabs.push({R,n,K,T,L,rough:rough.size,bad:bad.size,semiprimeIncidences:incidences,meanGOverT:sumG/n/T,idle,idleBad,D,CperIdle:idle?C/idle:0,small,smallBad,Ds,CsPerSmall:small?Cs/small:0,firstIdle,firstIdleBad,squareT,meanSquareGOverT:sumSquareG/n/squareT,squareWitness,high})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
