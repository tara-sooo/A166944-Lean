// Reproduce: node research/min_prime_root_physical_tail_potential_audit.mjs
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),T=mode==="analytic"?Math.floor(X/u**.25):mode==="short"?B:4*B,Q=mode==="wide"?7:Math.max(5,Math.ceil(B/(mode==="analytic"?u:8))),m0=mode==="analytic"?Math.max(1,Math.floor(B*u**1.5)):mode==="short"?4:8,lim=7*X+5,spf=new Int32Array(lim+1),ok=(x,s)=>{if(!x)throw Error(s);},mod=(a,b)=>((a%b)+b)%b,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;};
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)spf[j]=spf[j]||n;}
 const fs=n=>{let a=[];while(n>1){let p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const vertices=new Map(),roots=new Map();let N=0,R=0,G=0,events=0,high=0,literal=0,hiR=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,cut=Math.floor((7*M-1)/4),a=[],cost=0;
  while(true){let e={M,C,t,p:0,r:0,w:0,prev:a.length?a[a.length-1]:null};a.push(e);let id=C+":"+t;if(!vertices.has(id))vertices.set(id,[]);vertices.get(id).push(e);
   if(C-(2*M-2)>=T)break;
   let tt=Infinity,p=Infinity;for(const s of [-1,1])for(const q of fs(C+s)){let tick=t+1+mod((s===-1?0:q+2)-(t+1),2*q);if(tick<tt||(tick===tt&&q<p)){tt=tick;p=q;}}
   if(X<=1024){let lt=Infinity,lp=Infinity;for(let s=t+1;s<=cut;s++){let f=fs(gcd(s%2?s-2:s,C+(s%2?1:-1)));if(f.length){lt=s;lp=f[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal");literal++;}
   if(tt>cut)break;
   let r=Math.min(...fs(C-1),...fs(C+1));ok(r<=p&&tt-t<=2*r,"clock");e.p=p;e.r=r;cost+=r;events++;if(p>=Q&&r>p/(mode==="analytic"?Math.sqrt(Math.log(p)):2)){e.w=r;hiR+=r;high++;}
   t=tt;C+=p-1;ok(C<=2*t,"horizon");
  }
  let gain=C-(2*M-2);R+=cost;G+=gain;ok(gain<T+B&&2*cost<=3*gain,"gain");
  let tail=0;for(let i=a.length-1;i>=0;i--){tail+=a[i].w;a[i].tail=tail;a[i].next=a[i+1]||null;}roots.set(M,a);
 }
 const vlist=[...vertices.values()].sort((a,b)=>a[0].C-b[0].C||a[0].t-b[0].t);
 const f=(n,m)=>n<=m?n*n:2*m*n-m*m;
 let syncEnergy=0,diag=0,mergers=0,firstPairs=0,exactProfile=0,exactPair=0,smallRaw=0,largeRawSmallTail=0,allLightLarge=0,heavyBranches=0,lightAttach=0,pot=0,loss=0,rootPot=0,rawMassMax=0,profileCuts=0,tailDrop=0;
 const layers=[...new Set([1,2,4,8,16,32,64,128,256,512,1024,2048,4096,Math.max(1,Math.floor(T/2))])].sort((a,b)=>a-b);
 const layer=layers.map(x=>({x,m:Math.max(1,Math.floor(m0*Math.sqrt((T+B)/x))),birth:0,small:0,delta:0,loss:0,start:0,heavy:0,light:0,largeLight:0,root:0}));
 const upper=1.5*(T+B);let maxTail=0,smallProfileE=0,largeProfileE=0,lateSmallE=0,groupCount=0,layerIntervals=0,capE=0,resE=0,sameExtra=0,mixedExtra=0,mixedVertices=0,mixedChecks=0,rawSame=0,rawMixed=0,profileMixed=0,profileSame=0;const cap0=mode==='analytic'?Math.floor(B*u**.75):16;
 const pred=e=>e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M;
 for(const es of vlist){
   const n=es.length;rawMassMax=Math.max(rawMassMax,n);const groups=new Map();for(const e of es){let k=pred(e);if(!groups.has(k))groups.set(k,[]);groups.get(k).push(e);maxTail=Math.max(maxTail,e.tail);}
   const gs=[...groups.values()],sizes=gs.map(a=>a.length),bb=n*n-sizes.reduce((s,a)=>s+a*a,0),ends=es.filter(e=>!e.next).length,rt=es.filter(e=>!e.prev).length;
   const delta=f(n,m0)-sizes.reduce((s,a)=>s+f(a,m0),0);ok(delta>=0,"raw convex potential");pot+=delta;loss+=f(n,m0)-f(n-ends,m0);rootPot+=rt;
   const h=sizes.filter(a=>a>=m0).length,s=sizes.filter(a=>a<m0).reduce((s,a)=>s+a,0);
   if(h){ok(delta>=m0*m0*(h-1)+m0*s,"heavy budget");heavyBranches+=h-1;lightAttach+=s;}else if(n>=2*m0){ok(delta>=m0*n/2,"large light");allLightLarge+=n;}
   if(bb){mergers++;firstPairs+=bb/2;}
   let w=es[0].w;if(w){ok(es.every(e=>e.w===0||e.w===w),"clock");}else w=es.find(e=>e.w)?.w||0;
   const active=es.filter(e=>e.w).length;syncEnergy+=w*active*(active-1);diag+=w*active;
   for(const o of layer){
     const sel=es.filter(e=>e.tail>=o.x),nn=sel.length;if(!nn)continue;
     const sz=new Map();let ee=0,rr=0;for(const e of sel){let k=pred(e);sz.set(k,(sz.get(k)||0)+1);if(!e.next||e.next.tail<o.x)ee++;if(!e.prev)rr++;else ok(e.prev.tail>=o.x,"tail prefix");}
     const a=[...sz.values()],d=f(nn,o.m)-a.reduce((s,v)=>s+f(v,o.m),0),b=nn*nn-a.reduce((s,v)=>s+v*v,0);
     o.delta+=d;o.loss+=f(nn,o.m)-f(nn-ee,o.m);o.start+=rr;o.birth+=b;
     if(nn<=o.m){ok(d===b,"small tail profile");o.small+=b;}
     const hh=a.filter(v=>v>=o.m).length,ss=a.filter(v=>v<o.m).reduce((s,v)=>s+v,0);
     if(hh){ok(d>=o.m*o.m*(hh-1)+o.m*ss,"profile heavy");o.heavy+=hh-1;o.light+=ss;}else if(nn>=2*o.m){ok(d>=o.m*nn/2,"profile light");o.largeLight+=nn;}
   }
   if(!bb)continue;
   const il=[...new Set(es.filter(e=>e.prev&&e.prev.p>=Q).map(e=>e.prev.p))];
   if(il.length>=2){mixedVertices++;const J=es[0].C,t=es[0].t,eps=t%2?6:0;for(let i=0;i<il.length;i++)for(let j=i+1;j<il.length;j++){let p=il[i],q=il[j];ok((2*t-J-eps)%(2*p*q)===0,"mixed incoming congruence");mixedChecks++;}}
   let pair=0;for(let i=0;i<gs.length;i++)for(let j=i+1;j<gs.length;j++)for(const a of gs[i])for(const b of gs[j])pair+=2*Math.min(a.tail,b.tail);
   exactPair+=pair;if(n<=m0)smallRaw+=pair;
   // Integer threshold integration, using constant profile between successive tail breakpoints,
   // and splitting at threshold m(x)=floor(m0 sqrt((T+B)/x)).
   const cuts=[...new Set(es.map(e=>e.tail).filter(x=>x>0))].sort((a,b)=>a-b);let last=0;
   for(const end of cuts){
     const sel=es.filter(e=>e.tail>=end),nn=sel.length,a=new Map();for(const e of sel){let k=pred(e);a.set(k,(a.get(k)||0)+1);}
     const b=nn*nn-[...a.values()].reduce((s,v)=>s+v*v,0),len=end-last;
     const lab=new Map(),labsq=new Map();
     for(const e of sel){let p=e.prev?e.prev.p:0;lab.set(p,(lab.get(p)||0)+1);}
     for(const g of gs){let p=g[0].prev?g[0].prev.p:0,ct=g.filter(e=>e.tail>=end).length;labsq.set(p,(labsq.get(p)||0)+ct*ct);}
     let bs=0,bh=0,hh=0,hhsq=0;for(const [p,v] of lab){bs+=v*v-labsq.get(p);if(p>=Q){hh+=v;hhsq+=v*v;}}bh=hh*hh-hhsq;
     profileSame+=len*bs;profileMixed+=len*bh;
     ok(bs+bh<=b,"label refinement");
     exactProfile+=len*b;layerIntervals++;
     // floor(m0 sqrt((T+B)/x)) >= nn iff x<=m0^2(T+B)/nn^2.
     const stop=Math.min(end,Math.floor(m0*m0*(T+B)/(nn*nn)));
     const good=Math.max(0,stop-last);smallProfileE+=good*b;largeProfileE+=(len-good)*b;
     const remainingStart=last+good;
     for(const [p,v] of lab){const ib=v*v-labsq.get(p),cut=Math.min(end,Math.floor(m0*m0*(T+B)/(v*v))),extra=Math.max(0,cut-remainingStart);sameExtra+=extra*ib;}
     if(bh){const cut=Math.min(end,Math.floor(cap0*cap0*(T+B)/(bh*bh)));mixedExtra+=Math.max(0,cut-remainingStart)*bh;}
     if(n>m0){largeRawSmallTail+=good*b;if(nn<n)lateSmallE+=good*b;}
     last=end;
   }
 }
 ok(diag===hiR&&syncEnergy===exactPair&&exactPair===exactProfile&&syncEnergy===smallProfileE+largeProfileE,"exact physical energy");
 ok(pot===loss-rootPot&&pot<=2*m0*N&&heavyBranches*m0*m0+lightAttach*m0<=pot&&allLightLarge*m0/2<=pot,"raw potential telescoping");
 for(const o of layer){ok(o.delta===o.loss-o.start&&o.delta<=2*o.m*o.start&&o.small<=o.delta&&o.heavy*o.m*o.m+o.light*o.m<=o.delta&&o.largeLight*o.m/2<=o.delta,"tail potential telescope");}
 ok(sameExtra+mixedExtra<=largeProfileE&&smallProfileE+sameExtra<=4*N*m0*Math.sqrt((T+B)*Math.ceil(upper))+1e-6,"hierarchical profile bound");
 ok(smallProfileE<=4*N*m0*Math.sqrt((T+B)*Math.ceil(upper))+1e-6&&maxTail<=upper,"integrated small bound");
 return {mode,X,B,T,Q,m0,N,R,G,events,high,literal,hiR,physicalVertices:vlist.length,mergers,firstPairs,syncEnergy,exactPair,exactProfile,smallRaw,smallProfileE,largeProfileE,largeRawSmallTail,lateSmallE,allLightLarge,heavyBranches,lightAttach,pot,loss,rootPot,rawMassMax,layerIntervals,maxTail,layer,sameExtra,mixedExtra,mixedVertices,mixedChecks,profileMixed,profileSame,cap0,finalResidual:largeProfileE-sameExtra-mixedExtra};
}
const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
