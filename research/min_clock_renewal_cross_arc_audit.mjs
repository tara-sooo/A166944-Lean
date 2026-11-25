// Virtual boundary absorption, synchronous cross-arc terminal tails, and cumulative medium-gain reverse bound.
// Run node research/min_clock_renewal_cross_arc_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,startAge=mode==='full'?0:mode==='early'?B:2*B,a=startAge,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
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
  ok(rr<=(H-startAge)/2,'root cost');paths.push(path);
 }







 const Y=mode==='analytic'?Math.max(17,Math.ceil(Math.sqrt(u))):17;
 const Qr=Math.ceil(Math.sqrt(B)),Kr=mode==='analytic'?Math.floor(Math.sqrt(ell)):mode==='wide'?4:2;
 const budget=mode==='analytic'?u**2.5:mode==='wide'||mode==='full'?64:16;
 const Ds=Array.from({length:Kr+1},(_,k)=>Math.floor(budget**(1/(k+1))));
 const A0=2*Math.floor(Math.log(7*X+2)/Math.log(Qr));
 function choose(n,k){let a=1;for(let i=1;i<=k;i++)a*=((n-k+i)/i);return a;}
 const reverseCap=Ds.reduce((s,D,k)=>s+A0**k*choose(Math.floor(D/2)+k+1,k+1),0);
 const cnt=new Uint32Array(len),goodW=[new Float64Array(len),new Float64Array(len)];
 let virtual=0,virtualPositive=0,canonical=0,phaseChecks=0,goodInc=0,goodPositive=0,maxGood=0;
 const overlap=(l,h,x,y)=>Math.max(0,Math.min(h,y)-Math.max(l,x));
 for(const path of paths){
  const root=path[0],cut=root.t+H,lower=root.t+a,cs=[];
  for(let j=0;j<path.length;j++){const e=path[j],n=path[j+1],v=e.C/2+3;
   if(e.C%4===0&&e.t<=v&&v<=cut&&((n&&v<n.t)||!n&&v===e.t)){cs.push({j,M:e.C/2+1,t:v});canonical++;virtual+=+(v!==e.t);}
  }
  ok(cs.length&&cs[0].M===root.M,'root canonical');
  let ci=0,k=0,g=0;
  for(let j=0;j<path.length;j++){
   const e=path[j],n=path[j+1];if(j){if(e.inc>=Qr)k++;else g+=e.inc-1;}
   if(k<=Kr&&g<=Ds[k]){goodInc++;const h=e.C/2;cnt[h]++;maxGood=Math.max(maxGood,cnt[h]);ok(cnt[h]<=reverseCap,'mixed gain reverse bound');if(e.w){goodPositive++;if(e.p>z&&e.p<=T)goodW[0][h]+=e.w;if(e.p>T)goodW[1][h]+=e.w;}}
   if(!n)continue;
   const q=r[e.C/2],c=e.C/2+3,split=e.C%4===0&&e.t<c&&c<n.t;
   while(ci+1<cs.length&&cs[ci+1].j===j&&cs[ci+1].t<=e.t)ci++;
   e.oldArc=cs[ci].M;e.pre=split?overlap(e.t,c,lower,cut)/(2*q):0;
   e.l=Math.max(split?c:e.t,lower);e.h=Math.min(n.t,cut);e.non=Math.max(0,e.h-e.l)/(2*q);
   if(split&&e.p>=17){ok(c-e.t<=3&&n.t-c>=e.p/4&&8*q>=e.p,'virtual boundary clock');phaseChecks++;}
   if(split&&ci+1<cs.length&&cs[ci+1].j===j){ok(cs[ci+1].t===c,'virtual canonical');ci++;}
   e.arc=cs[ci].M;e.end=ci+1<cs.length?cs[ci+1].t:0;
   e.c=c;e.nextTime=n.t;e.cut=cut;e.stop=Math.min(cut,path[path.length-1].t);e.qual=e.p>=Y&&split;
   if(e.non>0&&split)ok(e.arc===e.C/2+1,'post-boundary arc');
   if(e.pre>0){virtualPositive++;ok(e.oldArc!==e.C/2+1,'pre-boundary arc');}
   ok(Math.abs(e.w-e.pre-e.non)<1e-9,'exact split');
  }
 }
 // Independently shorten all original prefixes by a common relative cutoff.
 // This exercises the thin (near-cutoff) boundary class even when late/full
 // natural windows contain no such instance. No change to original dynamics.
 const boundaryTests=[];
 for(let hh=2;hh<=H;hh*=2){
  let thinInc=0,strongInc=0,maxThin=0,preCost=0,postCost=0,checked=0;
  for(const [C,row] of at){let thin=0;const q=r[C/2];for(const e of row){
   if(!e.qual)continue;const cut=e.M+2+hh,pre=Math.max(0,Math.min(cut,e.c)-e.t)/(2*q);if(!pre)continue;
   const post=Math.max(0,Math.min(cut,e.nextTime)-e.c)/(2*q);checked++;preCost+=q*pre;postCost+=q*post;
   if(cut<e.c+e.p/4){thin+=pre;thinInc++;}else{strongInc++;ok(pre<=12/e.p*post+1e-9,'shortened prefix boundary ratio');}
  }ok(thin<=3+1e-9,'shortened prefix uniform thin bound');maxThin=Math.max(maxThin,thin);}
  boundaryTests.push({hh,thinInc,strongInc,maxThin,preCost,postCost,checked});
 }
 const results=[];
 for(const b of [0,1]){
  const f=e=>b===0?e.p>z&&e.p<=T:e.p>T;
  const m=mode==='analytic'?u**2.5*(b===0?B**.625:1):mode==='wide'||mode==='full'?32:4;
  let E=0,Rb=0,splitPaid=0,splitRaw=0,cross=0,crossAfter=0,crossAfterEligible=0,crossSync=0,crossAsync=0,tail=0,tailShort=0,tailPairs=0,unreturned=0,returnedTail=0,unreturnedTail=0,thinMax=0,good=0,goodR=0,oracleChecks=0;
  const tails=new Map(),bands=new Map();
  const crossMap=(a)=>{let u0=0,s=0;for(const v of a.values()){u0+=v;s+=v*v;}return u0*u0-s;};
  const add=(a,k,v)=>{if(v)a.set(k,(a.get(k)||0)+v);};
  for(const [C,row] of at){
   const q=r[C/2],tags=row.filter(e=>e.w>0&&f(e));if(!tags.length)continue;
   let U0=0,pre=0,eligible=0,thin=0,strong=0;const all=new Map(),rest=new Map(),post=new Map();
   for(const e of tags){
    U0+=e.w;pre+=e.pre;
    if(e.qual){eligible+=e.pre;if(e.cut<e.c+e.p/4)thin+=e.pre;else{ok(e.pre<=12/e.p*e.non+1e-9,'long remaining boundary ratio');strong+=e.pre;}}
    add(all,e.oldArc,e.pre);add(all,e.arc,e.non);
    if(!e.qual)add(rest,e.oldArc,e.pre);add(rest,e.arc,e.non);add(post,e.arc,e.non);
   }
   ok(thin<=3+1e-9&&strong<=12/Y*U0+1e-9,'uniform thin boundary mass');thinMax=Math.max(thinMax,thin);
   E+=q*U0*U0;Rb+=q*U0;splitPaid+=q*(2*U0*eligible-eligible*eligible);splitRaw+=q*(2*U0*pre-pre*pre);
   const c0=q*crossMap(all),c1=q*crossMap(rest),c2=q*crossMap(post);cross+=c0;crossAfterEligible+=c1;crossAfter+=c2;
   const gw=goodW[b][C/2];good+=q*(2*U0*gw-gw*gw);goodR+=q*gw;
   let oracle=0;
   for(let i=0;i<tags.length;i++){const x=tags[i];if(!x.non)continue;for(let j=0;j<i;j++){const y=tags[j];if(!y.non||x.arc===y.arc)continue;
    const val=2*q*x.non*y.non;oracle+=val;
    if(x.t!==y.t){crossAsync+=val;continue;}
    crossSync+=val;oracleChecks++;
    if(x.end&&y.end)ok(x.end===y.end,'common next canonical endpoint');
    const known=x.end||y.end,shorter=x.stop<=y.stop?x:y;
    const end=known?Math.min(known,x.stop,y.stop):Math.min(x.stop,y.stop);
    if(!known||known>Math.min(x.stop,y.stop))unreturned+=val;
    ok(shorter.h<=end,'shorter arc before endpoint');
    const d=Math.abs(x.M-y.M),d0=8*B,j0=Math.floor(Math.log2(d0/d)),db=d0/2**j0,lim=B*m/(db*(j0+1)**2);
    ok(j0>=0&&d<=db&&d>db/2,'source distance band');
    const wx=overlap(x.l,x.h,end-lim,end)/(2*q),wy=overlap(y.l,y.h,end-lim,end)/(2*q);
    const v=2*q*(x.non*y.non-(x.non-wx)*(y.non-wy));ok(v>=-1e-8&&v<=val+1e-8,'tail charge');
    if(v<=1e-10)continue;tail+=v;tailPairs++;if(known&&known<=Math.min(x.stop,y.stop))returnedTail+=v;else unreturnedTail+=v;
    if(end-x.t<=lim)tailShort+=val;
    const id=Math.min(x.i,y.i)+':'+Math.max(x.i,y.i),s=tails.get(id)||{end,lim,cost:0,d};
    ok(s.end===end&&s.lim===lim,'one common endpoint for distinct arcs');s.cost+=v;tails.set(id,s);
    const band=bands.get(j0)||{db,lim,energy:0};band.energy+=v;bands.set(j0,band);
   }}
   ok(Math.abs(oracle-c2)<=1e-6*Math.max(1,c2),'cross-arc independent pair oracle');
  }
  for(const s of tails.values())ok(s.cost<=2*s.lim+1e-6,'per-pair tail budget');
  for(const s of bands.values())ok(s.energy<=2*N*(s.db+2)*s.lim+1e-6,'distance band budget');
  const ep=1e-6*Math.max(1,E);
  ok(splitPaid<=24/Y*E+6*Rb+ep&&Math.abs(crossAfter-crossSync-crossAsync)<=ep&&crossAfter<=crossAfterEligible+ep&&crossAfterEligible<=cross+ep&&tail<=crossSync+ep&&good<=2*maxGood*Rb+ep,'sector budgets');
  results.push({sector:b,E,R:Rb,m,splitPaid,splitRaw,cross,crossAfterEligible,crossAfter,crossBoundaryPaid:cross-crossAfterEligible,crossBoundaryUnpaid:crossAfterEligible-crossAfter,crossSync,crossAsync,tail,tailShort,tailPairs,distinctTailPairs:tails.size,unreturned,returnedTail,unreturnedTail,thinMax,good,goodR,oracleChecks,restCross:crossAfterEligible-tail,bands:[...bands.entries()]});
 }
 return {boundaryTests,X,B,mode,Y,Qr,Kr,Ds,A0,reverseCap,goodInc,goodPositive,maxGood,N,R,events,literal,canonical,virtual,virtualPositive,phaseChecks,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide','full'])console.log(JSON.stringify(audit(X,mode)));
