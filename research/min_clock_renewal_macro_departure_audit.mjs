// Physical departure groups and one-large-event renewal inverse blocks.
// Run node research/min_clock_renewal_macro_departure_audit.mjs 1024 4096 16384 65536
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







 const Y=mode==='analytic'?Math.max(17,Math.ceil(B**.125)):mode==='wide'?17:31;
 const d0=mode==='analytic'?Math.floor(u**.125):mode==='wide'?4:2;
 const y=mode==='analytic'?z:mode==='wide'?5:3;
 let Lp=2;for(let q=3;q<=y;q+=2)if(spf[q]===q)Lp*=q;
 const P=Math.max(Y,10*Lp+16),m=mode==='analytic'?Math.floor(u**2.75):mode==='wide'?8:2,eps0=mode==='analytic'?u**(-.125):.1;
 const bridge=J=>{let k=0;while(J%3===2||J%5===1){J+=4;k++;ok(k<=2,'bridge');}return {J,k};};
 const ky=(J,t,p)=>J+':'+t+':'+p;
 let env=0,envGain=0,maxTimes=0,envNear=0;
 // Independent relaxed arithmetic envelope: all allowed post phases with
 // post deficit bounded by 4p+6, not a source enumeration.
 const envelope=new Set();
 for(let D=2*X;D<7*X;D+=2){
  for(const s of [0,1])fac(D+2*s-1,p=>{
   if(p<Y||8*r[D/2]<p)return;
   const J=D+p-1;if(J>=7*X)return;
   let count=0;
   for(let k=0;6*s+2*p*k<=4*p+6;k++){
    const t=(J+6*s+2*p*k)/2;if(t%2!==s)continue;
    const id=ky(J,t,p);ok(!envelope.has(id),'unique envelope key');envelope.add(id);env++;envGain+=p-1;count++;
   }maxTimes=Math.max(maxTimes,count);ok(count<=3,'constant clock phases');
  });
 }
 const groups=new Map(),rootGroups=Array.from({length:N},()=>[]),inverse=new Map(),arcs=new Map();
 let canonical=0,virtual=0,checks=0,rawGain=0,rawClock=0,wideGain=0,wideClock=0,wideInc=0,origNarrow=0,inc=0,macroInc=0,lowArcInc=0,nonMacro=0,macroGain=0,macroClock=0,maxPre=0,macroVirtual=0;
 for(const path of paths){
  const root=path[0],cut=root.t+H,cs=[];
  for(let j=0;j<path.length;j++){const e=path[j],n=path[j+1],v=e.C/2+3;
   if(e.C%4===0&&e.t<=v&&v<=cut&&((n&&v<n.t)||!n&&v===e.t)){
    cs.push({j,M:e.C/2+1,t:v,C:e.C});canonical++;virtual+=+(v!==e.t);
   }
  }
  ok(cs.length&&cs[0].M===root.M,'canonical start');let ci=0;
  for(let j=0;j+1<path.length;j++){
   if(ci+1<cs.length&&cs[ci+1].j===j)ci++;
   const a=cs[ci],e=path[j],v=path[j+1],p=v.inc,g=e.C-a.C,t0=j===a.j?a.t:e.t,w=v.t-t0;
   if(p<Y||p<10*g+16)continue;
   const delta=2*t0-e.C,post=2*v.t-v.C;
   ok(g>=0&&delta<=6+5*g&&w>=p/4&&8*r[e.C/2]>=p&&post<=4*p+6,'proportional rough departure');checks++;
   const id=ky(v.C,v.t,p);ok(envelope.has(id),'actual physical key in envelope');
   let row=groups.get(id);if(!row){row={id,p,n:0,wide:0,origins:new Set(),clock:0};groups.set(id,row);}
   row.n++;row.origins.add(a.M);row.clock+=r[e.C/2]*e.w;rootGroups[root.i].push(row);rawGain+=p-1;rawClock+=r[e.C/2]*e.w;inc++;
   if(g>d0){row.wide++;wideInc++;wideGain+=p-1;wideClock+=r[e.C/2]*e.w;}else origNarrow++;
  }
  for(let j=1;j<cs.length;j++){
   const a=cs[j-1],b=cs[j],id=a.M+':'+b.M,ns=[];
   for(let k=a.j+1;k<=b.j;k++)if(path[k].inc>y)ns.push(k);
   let cls=2;if(!ns.length){cls=0;lowArcInc++;ok(b.C-a.C<Lp,'LOW-only arc bound');}
   else if(ns.length===1&&path[ns[0]].inc>=P){
    cls=1;macroInc++;const k=ns[0],v=path[k],p=v.inc,s=v.t%2,e=path[k-1],g=e.C-a.C,after=b.C-v.C;
    ok(g<Lp&&after<Lp&&2*v.t-v.C===6*s,'one-large reset forced');
    const br=s?{J:v.C,k:0}:bridge(v.C);ok(br.J===b.C&&b.t===b.C/2+3,'one-large endpoint');
    ok(s?b.M%p===0:(b.M-1-2*br.k)%p===0,'inverse factors');
    const key=ky(v.C,v.t,p),D=e.C;ok(envelope.has(key),'one-large physical envelope');
    let x=inverse.get(b.M);if(!x){x=new Map();inverse.set(b.M,x);}let k0=x.get(key);
    if(!k0){k0={p,D,origins:new Set()};x.set(key,k0);}k0.origins.add(a.M);
    ok(k0.D===D&&a.C<=D&&a.C>D-Lp,'inverse origin block');
    macroGain+=p-1;macroClock+=r[e.C/2]*e.w;maxPre=Math.max(maxPre,g);macroVirtual+=+(a.t!==path[a.j].t);
   }else nonMacro++;
   const prior=arcs.get(id);ok(prior===undefined||prior===cls,'fixed renewal class');arcs.set(id,cls);
  }
 }
 let invKeys=0,invSources=0,maxInvKeys=0,maxInvSources=0,maxOriginBlock=0;
 for(const [n,rows] of inverse){
  let deg=0;for(const v of [n,n-1,n-3,n-5])fac(v,p=>{if(p>=P)deg++;});
  ok(rows.size<=deg,'inverse physical branch degree');invKeys+=rows.size;maxInvKeys=Math.max(maxInvKeys,rows.size);
  let ns=0;for(const v of rows.values()){
   const a=[...v.origins];ns+=a.length;ok(a.length<=Math.ceil(Lp/4)+1,'inverse source block count');maxOriginBlock=Math.max(maxOriginBlock,a.length);
  }ok(ns<=deg*(Math.ceil(Lp/4)+1),'inverse total degree');invSources+=ns;maxInvSources=Math.max(maxInvSources,ns);
 }
 const counts=new Map([...groups].map(([id,g])=>[id,g.n])),charges=new Map(),deleted=new Uint8Array(N);
 let thinGain=0,thinWideGain=0,thinClock=0,multiOrigin=0,maxOrigins=0,maxMass=0,usedGain=0;
 for(const g of groups.values()){usedGain+=g.p-1;maxMass=Math.max(maxMass,g.n);maxOrigins=Math.max(maxOrigins,g.origins.size);multiOrigin+=+(g.origins.size>1);if(g.n<=m){thinGain+=g.n*(g.p-1);thinWideGain+=g.wide*(g.p-1);thinClock+=g.clock;}}
 ok(thinGain<=m*envGain&&usedGain<=envGain,'support gain');
 let removed=0,rounds=0,charged=0;
 for(;;){let n=0;for(let i=0;i<N;i++){if(deleted[i])continue;const gs=rootGroups[i],thin=gs.filter(g=>counts.get(g.id)<=m),cost=thin.reduce((s,g)=>s+g.p-1,0);
   if(cost<eps0*B)continue;for(const g of thin){const k=(charges.get(g.id)||0)+1;ok(k<=m,'lifetime');charges.set(g.id,k);charged+=g.p-1;}
   deleted[i]=1;removed++;n++;for(const g of gs){const c=counts.get(g.id);ok(c>0,'active');counts.set(g.id,c-1);}
  }if(!n)break;rounds++;
 }
 let retainedThin=0,retainedThick=0,maxRootThin=0;
 for(let i=0;i<N;i++)if(!deleted[i]){let s=0;for(const g of rootGroups[i]){if(counts.get(g.id)<=m)s+=g.p-1;else retainedThick+=g.p-1;}ok(s<eps0*B,'fixed point');retainedThin+=s;maxRootThin=Math.max(maxRootThin,s);}
 ok(charged<=m*envGain&&charged>=removed*eps0*B-1e-8,'peel budget');

 // Independent prefix reverse-word bound, no regular-degree or reset assumption.
 // Finite thresholds are diagnostic; the paper chooses a growing slow primorial
 // and K=floor(log log B/(8 log(20(L+1)))).
 const Qr=Math.max(y+1,Math.ceil(Math.sqrt(B))),Kr=mode==='analytic'?Math.max(0,Math.floor(ell/(8*Math.log(20*(Lp+1))))):mode==='wide'?3:2,Jr=2;
 const A0=2*Math.floor(Math.log(7*X+2)/Math.log(Qr)),A1=2*Math.floor(Math.log(7*X+2)/Math.log(Math.max(3,y+1))),Wl=Math.ceil(Lp/2)+1;
 let wordCap=0;for(let i=0;i<=Kr;i++)for(let j=0;j<=Jr;j++){let choose=1;for(let k=1;k<=j;k++)choose*=((i+k)/k);wordCap+=Wl*choose*(Wl*A0)**i*(Wl*A1)**j;}
 const goodW=new Float64Array(len),goodM=new Float64Array(len),goodH=new Float64Array(len),goodCount=new Int32Array(len),rootSets=new Map();
 let goodR=0,goodInc=0,goodPositive=0,lowChecks=0,reverseChecks=0,maxGood=0,goodDiag=0;
 for(const path of paths){let i=0,j=0,F=path[0].C;
  for(let k=0;k<path.length;k++){
   const e=path[k];if(k){const p=e.inc;if(p<=y){ok(e.C-F<Lp,'LOW block gain');lowChecks++;}else{
     const D=path[k-1].C;ok(D-F<Lp&&(e.C%p===0||(e.C+2)%p===0)&&D===e.C-p+1,'reverse nonLOW step');
     reverseChecks++;F=e.C;if(p>=Qr)i++;else j++;
   }}
   if(i>Kr||j>Jr)continue;
   goodInc++;const h=e.C/2;goodCount[h]++;maxGood=Math.max(maxGood,goodCount[h]);ok(goodCount[h]<=wordCap,'reverse-word support');
   if(e.w>0){goodPositive++;goodW[h]+=e.w;goodR+=r[h]*e.w;goodDiag+=r[h]*e.w*e.w;if(e.p>z&&e.p<=T)goodM[h]+=e.w;if(e.p>T)goodH[h]+=e.w;}
  }
 }
 let goodE=0,goodCross=0,goodME=0,goodHE=0,goodRest=0;
 for(let j=lo;j<=hi;j++){const q=r[j];goodE+=q*goodW[j]**2;goodCross+=2*q*goodW[j]*(W0[j]-goodW[j]);goodRest+=q*(W0[j]-goodW[j])**2;goodME+=q*(2*WM[j]*goodM[j]-goodM[j]**2);goodHE+=q*(2*WH[j]*goodH[j]-goodH[j]**2);}
 let Etot=0;for(let j=lo;j<=hi;j++)Etot+=r[j]*W0[j]**2;
 ok(Math.abs(Etot-goodE-goodCross-goodRest)<=1e-6*Math.max(1,Etot)&&goodE+goodCross<=2*maxGood*R+1e-6*Math.max(1,Etot),'good prefix energy partition');
 const reverse={Qr,Kr,Jr,A0,A1,Wl,wordCap,goodInc,goodPositive,lowChecks,reverseChecks,maxGood,goodR,goodE,goodCross,goodRest,goodME,goodHE,goodDiag,Etot};
 const arcClasses=[0,0,0];for(const x of arcs.values())arcClasses[x]++;
 return {reverse,X,B,mode,Y,d0,y,Lp,P,m,eps0,N,R,events,literal,canonical,virtual,env,envGain,maxTimes,checks,inc,rawGain,rawClock,wideInc,wideGain,wideClock,origNarrow,groups:groups.size,multiOrigin,maxOrigins,maxMass,usedGain,thinGain,thinWideGain,thinClock,removed,rounds,charged,retainedThin,retainedThick,maxRootThin,macroInc,lowArcInc,nonMacro,arcClasses,macroGain,macroClock,macroVirtual,maxPre,invKeys,invSources,maxInvKeys,maxInvSources,maxOriginBlock};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
