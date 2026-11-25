// Two-sided actual reset-cohort energy transfer.
// Run node research/min_clock_reset_energy_transfer_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>B**(1/16))break;L*=p;z=p;}}
 else {z=3;L=6;}
 const T=mode==='analytic'?Math.max(z+1,Math.ceil(B**.25)):Math.ceil(Math.sqrt(B));
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'||mode==='stress'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'||mode==='stress'?12:24;
 const D0=mode==='analytic'?Math.ceil(40*ell)+1:4;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),degrees=new Uint8Array(len);
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let rare=0,maxDegree=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;for(const C of [2*j,2*j+2])fac(C,()=>degrees[j]++);maxDegree=Math.max(maxDegree,degrees[j]+1);rare+=+(degrees[j]+1>D0);}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1])fac(C+side,q=>{const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(w<v||(w===v&&w<=K&&q<p)){v=w;p=q;}});return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],at=new Map(),W0=new Float64Array(len),WM=new Float64Array(len),WH=new Float64Array(len);
 let R=0,RM=0,RH=0,events=0,literal=0,twins=0;
 for(let i=0;i<N;i++){const M=X+1+2*i,s=M+2,K=Math.floor((7*M-1)/4),path=[];let t=s,C=2*M-2,inc=0,rr=0;
  for(;;){const e={i,M,C,t,inc,p:0,w:0};path.push(e);let row=at.get(C);if(!row){row=[];at.set(C,row);}row.push(e);
   ok(C<=2*t&&C-(2*M-2)<=G,'prefix gain');
   if(t>=s+H)break;
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');twins++;break;}
   const q=r[C/2],cost=Math.max(0,Math.min(v,s+H)-Math.max(t,s+a))/2;
   ok(v-t<=2*q&&q<=p,'wait');e.p=p;e.w=cost/q;rr+=cost;R+=cost;W0[C/2]+=e.w;
   if(p>z&&p<=T){RM+=cost;WM[C/2]+=e.w;}if(p>T){RH+=cost;WH[C/2]+=e.w;}
   t=v;C+=p-1;inc=p;events++;
  }
  ok(rr<=B,'root cost');paths.push(path);
 }





 const P=mode==='analytic'?Math.ceil(B/u**.125):Math.max(19,Math.ceil(B/(mode==='stress'?8:4)));
 const V=mode==='analytic'?Math.max(1,Math.floor(B**.0625)):Math.max(1,Math.min(8,Math.floor((P-9)/10)));
 const A=mode==='analytic'?2*Math.floor(u**.125):mode==='stress'?24:12;
 const kappa=mode==='analytic'?1/u:mode==='stress'?1:.25;
 const keys=new Map(),witnessDest=new Map(),entries=[],accept=[e=>e.p>0,e=>e.p>z&&e.p<=T,e=>e.p>T],nsec=accept.length;
 const phys=e=>e.C+':'+e.t,lab=e=>phys(e)+':'+e.inc;
 let short=0,eligible=0,fullWitness=0,checks=0,distinctWitness=0;
 for(const path of paths){let reset=0;
  for(let j=1;j<path.length;j++){
   const v=path[j],a0=path[j-1],p=v.inc,d=2*v.t-v.C;
   if(d!==6*(v.t%2))continue;
   if(p>=P&&v.t-a0.t<=V){
    short++;const l0=Math.ceil(p/4),l1=Math.floor(p/2);
    if(l0>6&&l1<=2*a0.t-a0.C){
     eligible++;
     const last=new Map();
     for(let k=reset+1;k<j;k++){
      const a=path[k-1],b=path[k],da=2*a.t-a.C,db=2*b.t-b.C;
      for(let l=Math.max(l0,da+1);l<=Math.min(l1,db);l++)last.set(l,k);
     }
     ok(last.size===l1-l0+1,'complete level cutset');
     const k=Math.min(...last.values()),w=path[k],pre=path[k-1],q=w.inc,id=lab(v),gkey=lab(w);
     const prev=witnessDest.get(gkey);ok(!prev||prev===id,'one next labeled reset for each actual witness key');witnessDest.set(gkey,id);
     for(let a=k+1;a<j;a++){const e=path[a];ok(2*e.t-e.C!==6*(e.t%2),'no reset between witness and destination');checks++;}
     let a=keys.get(id);if(!a){a={id,J:v.C,t:v.t,p,n:0,groups:new Map(),entries:[],neighbors:[],A:Array(nsec).fill(0),F:Array(nsec).fill(0),bound:Array(nsec).fill(0),tail:Array(nsec).fill(0),maxTail:Array(nsec).fill(0)};keys.set(id,a);}
     let g=a.groups.get(gkey);
     if(!g){const drift=accept.map(f=>{let d=0;for(let b=k;b<j-1;b++){const x=path[b],y=path[b+1];if(f(x))d+=Math.max(0,2*(y.t-x.t)-(y.C-x.C));}return d;});
      const K=accept.map((f,b)=>(f(pre)?r[pre.C/2]/36:0)+drift[b]/24);
      g={gkey,n:0,full:0,K,drift,q,preC:pre.C};a.groups.set(gkey,g);distinctWitness++;
     }
     const full=pre.t>=v.M+2+2*B&&v.t<=v.M+2+H;
     if(full){fullWitness++;g.full++;ok(pre.w>=(q-1)/(4*q)-1e-9,'full positive witness weight');}
     g.n++;a.n++;
     const entry={a,root:v.i,j,k,reset,full,tail:Array(nsec).fill(0)};entries.push(entry);a.entries.push(entry);
     // Prior excursion excludes reset-entry wait, and is disjoint per root.
     for(let b=reset;b<j-1;b++){ok(path[b].past===undefined,'disjoint prior excursions');path[b].past=entry;}
     v.entry=entry;
    }
   }
   reset=j;
  }
  let latest=null;for(const e of path){if(e.entry)latest=e.entry;if(latest){e.future=latest;for(let b=0;b<nsec;b++)if(accept[b](e))latest.tail[b]+=r[e.C/2]*e.w;}}
 }
 const arr=[...keys.values()],atJ=new Map();for(const a of arr){let q=atJ.get(a.J);if(!q){q=[];atJ.set(a.J,q);}q.push(a);}
 let edges=0,degree=0;
 for(const a of arr){for(let d=-4*Math.floor(A/4);d<=A;d+=4)for(const b of atJ.get(a.J+d)||[])if(a!==b){a.neighbors.push(b);edges++;}degree=Math.max(degree,a.neighbors.length);}
 ok(edges%2===0,'symmetric graph');
 for(const a of arr){
  for(const g of a.groups.values())for(let b=0;b<nsec;b++)a.bound[b]+=g.K[b]*g.full*g.full;
  for(const e of a.entries)for(let b=0;b<nsec;b++){a.tail[b]+=e.tail[b];a.maxTail[b]=Math.max(a.maxTail[b],e.tail[b]);}
 }
 const results=[];
 for(let sector=0;sector<nsec;sector++){
  const f=accept[sector];let E=0,diag=0,RA=0,RF=0,asum=0,fsum=0,eligibleFuture=0,credit=0,good=0,goodF=0,goodA=0,lowTail=0,positive=0,certKeys=0,certEntries=0;
  for(const [C,row] of at){const q=r[C/2];let all=0;const past=new Map(),future=new Map();
   for(const e of row){if(!e.w||!f(e))continue;all+=e.w;diag+=q*e.w*e.w;if(e.past){const a=e.past.a;past.set(a,(past.get(a)||0)+e.w);RA+=q*e.w;}if(e.future){const a=e.future.a;future.set(a,(future.get(a)||0)+e.w);RF+=q*e.w;}}
   E+=q*all*all;let eA=0,eF=0;for(const [a,w] of past){const v=q*w*w;a.A[sector]+=v;eA+=v;}for(const [a,w] of future){const v=q*w*w;a.F[sector]+=v;eF+=v;}
   ok(eA<=q*all*all+1e-6&&eF<=q*all*all+1e-6,'pointwise partitions');
  }
  for(const a of arr){const A0=a.A[sector],F=a.F[sector],b=a.bound[sector],eps=1e-7*Math.max(1,A0,F);
   ok(b<=A0+eps,'witness credit bound');ok(F<=a.n*a.tail[sector]+eps&&a.tail[sector]<=a.n*a.maxTail[sector]+eps,'tail bound');
   asum+=A0;fsum+=F;credit+=b;positive+=+(F>0);a.good=F<=kappa*A0+1e-9;
   if(a.good){good++;goodF+=F;goodA+=A0;}
   if(b>0&&a.n*a.n*a.maxTail[sector]<=kappa*b+1e-9){ok(a.good,'tail-dispersion sufficient test');lowTail++;}
   if(b>=a.p/3000){certKeys++;certEntries+=a.n;}
  }
  let cross=0,one=0,both=0,self=0,selfGood=0,sync=0,async=0,oracle=0,edgeHits=0;
  for(const [C,row] of at){const q=r[C/2],tags=row.filter(e=>e.w>0&&f(e)&&e.future),groups=new Map();
   for(const e of tags){const a=e.future.a;let s=groups.get(a);if(!s){s={w:0,d:0};groups.set(a,s);}s.w+=e.w;s.d+=e.w*e.w;}
   for(const [a,s] of groups){const val=q*(s.w*s.w-s.d);self+=val;if(a.good)selfGood+=val;
    for(const b of a.neighbors){if(a.id>=b.id||!groups.has(b))continue;const e=2*q*s.w*groups.get(b).w;cross+=e;edgeHits++;if(a.good||b.good)one+=e;if(a.good&&b.good)both+=e;}
   }
   for(let i=0;i<tags.length;i++)for(let j=0;j<i;j++){const x=tags[i],y=tags[j],a=x.future.a,b=y.future.a;if(a===b||Math.abs(a.J-b.J)<=A){const e=2*q*x.w*y.w;oracle+=e;if(x.t===y.t)sync+=e;else async+=e;}}
  }
  const eps=1e-6*Math.max(1,E);
  ok(asum<=E+eps&&fsum<=E+eps&&goodF<=kappa*goodA+eps,'global partitions');
  ok(Math.abs(oracle-self-cross)<=eps&&Math.abs(oracle-sync-async)<=eps,'pair oracle');
  ok(selfGood<=kappa*E+eps&&one<=2*degree*Math.sqrt(kappa)*E+eps&&both<=degree*kappa*E+eps,'absorption');
  results.push({sector,E,diag,RA,RF,asum,fsum,credit,good,goodF,goodA,lowTail,positive,certKeys,certEntries,self,selfGood,cross,one,both,sync,async,edgeHits,rest:self+cross-selfGood-one});
 }
 return {X,B,mode,P,V,A,kappa,z,T,events,literal,R,short,eligible,fullWitness,checks,distinctWitness,keys:arr.length,edges:edges/2,degree,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','stress'])console.log(JSON.stringify(audit(X,mode)));
