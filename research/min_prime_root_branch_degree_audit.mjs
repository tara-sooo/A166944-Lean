// Reproduce: node research/min_prime_root_branch_degree_audit.mjs
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
 const H=T+B,Z=mode==="analytic"?Math.max(1,Math.floor(u**.25)):mode==="short"?2:4,baseMix=mode==="analytic"?Math.max(1,Math.floor(B*Math.sqrt(u))):m0,baseSame=mode==="analytic"?Math.max(1,Math.floor(B*u**.25)):m0;
 const pred=e=>e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M,label=e=>e.prev?.p||0;
 const scales=[{d:0,m:m0},{d:mode==="analytic"?B:Math.max(4,Math.floor(B/16)),m:mode==="analytic"?Math.floor(u**1.75):2},{d:mode==="analytic"?4*B:4*Math.max(4,Math.floor(B/16)),m:mode==="analytic"?Math.floor(4*u**1.75):4}];
 const cell=(M,d)=>d?Math.floor((M-X)/d):0,rankCounters=scales.map(()=>new Map()),inc=(m,k,n=1)=>m.set(k,(m.get(k)||0)+n);
 const Dmax=Math.max(...Array.from({length:0},()=>0),1);let maxDiv=0;
 const labels=new Map();function divs(D){if(!labels.has(D)){let a=[...fs(D),...fs(D+2)];labels.set(D,a);maxDiv=Math.max(maxDiv,a.length);}return labels.get(D);}
 const layer=[1,128,512].map(x=>({x,mix:Math.max(1,Math.floor(baseMix*Math.sqrt(H/x))),same:Math.max(1,Math.floor(baseSame*Math.sqrt(H/x))),mixD:0,sameD:0,mixL:0,sameL:0,start:0,mixCover:0,sameCover:0,maxMixDeg:0,maxSameDeg:0}));
 let E=0,exact=0,old=0,newMix=0,newSame=0,oldExtraMix=0,oldExtraSame=0,remaining=0,mergers=0,pairs=0,regChecks=0,rootChecks=0,sameEdges=0,mixedEdges=0,shortEdges=0,regEdges=0,regularOnly=0,maxDegree=0,maxReg=0,layerChecks=0,irregResidual=0,largeBranchResidual=0;
 const massCut=(b,n)=>n?Math.floor(b*b*H/(n*n)):Infinity;
 for(const es of vlist){
   const w=es.find(e=>e.w)?.w||0,act=es.filter(e=>e.w).length;E+=w*act*(act-1);
   const gs=[],gm=new Map();
   for(const e of es){const k=pred(e);if(!gm.has(k)){gm.set(k,gs.length);gs.push({p:label(e),ar:[],regular:false,time:e.prev?.t??e.t,r:e.prev?.r??0,D:e.prev?.C??e.C});}const g=gs[gm.get(k)];g.ar.push(e);
     if(!e.prev){rootChecks++;ok(es.length===1,"prime root no incoming");continue;}
     ok(e.t-e.prev.t>=1&&e.t-e.prev.t<=2*e.prev.r,"predecessor time window");
     const q=e.prev.prev?.p||0;if(!q){g.regular=true;}else{const D=e.prev.C,t=e.prev.t;ok(D%q===0||(D+2)%q===0,"incoming predecessor divisor");ok(mod(t,2*q)===(t%2?mod(q+2,2*q):0),"incoming predecessor clock");regChecks++;if(q*Z>=e.prev.r)g.regular=true;}
   }
   const n=es.length,bylab=new Map();for(let i=0;i<gs.length;i++){const p=gs[i].p;if(!bylab.has(p))bylab.set(p,[]);bylab.get(p).push(i);}
   let md=bylab.size-1,sd=0;const graph=new Set();
   if(gs.length>1){mergers++;for(const [p,ix] of bylab){if(!p)continue;const r=gs[ix[0]].r,D=gs[ix[0]].D,reg=ix.filter(i=>gs[i].regular).length;ok(reg<=1+(Z+1)*divs(D).length,"regular state capacity");maxReg=Math.max(maxReg,reg);
     const ds=new Map();for(let a=0;a<ix.length;a++)for(let b=a+1;b<ix.length;b++){const i=ix[a],j=ix[b],g=gs[i],h=gs[j];ok(g.D===h.D&&g.r===h.r&&Math.abs(g.time-h.time)<2*r,"same label predecessor window");const close=Math.abs(g.time-h.time)<=2*Z,regular=g.regular&&h.regular;if(close||regular){graph.add(i+":"+j);inc(ds,i);inc(ds,j);sameEdges++;if(close)shortEdges++;if(regular)regEdges++;if(regular&&!close)regularOnly++;}}
     for(const d of ds.values()){ok(d<=4*Z+1+(Z+1)*divs(D).length,"same graph degree");sd=Math.max(sd,d);}
   }mixedEdges+=bylab.size*(bylab.size-1)/2;maxDegree=Math.max(maxDegree,sd);}
   const calc=(sel,m)=>{const sz=Array(gs.length).fill(0),lab=new Map();for(const e of sel){sz[gm.get(pred(e))]++;inc(lab,label(e));}const nn=sel.length,dp=f(nn,m)-sz.reduce((s,a)=>s+f(a,m),0),dm=f(nn,m)-[...lab.values()].reduce((s,a)=>s+f(a,m),0);return {sz,lab,dp,dm,ds:dp-dm};};
   for(const o of layer){
     const sel=es.filter(e=>e.tail>=o.x);if(!sel.length)continue;let ends=0,starts=0;for(const e of sel){if(!e.next||e.next.tail<o.x)ends++;if(!e.prev)starts++;else ok(e.prev.tail>=o.x,"layer prefix");}
     const a=calc(sel,o.mix),b=calc(sel,o.same);o.mixD+=a.dp;o.sameD+=b.dp;o.start+=starts;o.mixL+=f(sel.length,o.mix)-f(sel.length-ends,o.mix);o.sameL+=f(sel.length,o.same)-f(sel.length-ends,o.same);
     let cm=0,cs=0;const l=[...a.lab.values()].filter(n=>n<=o.mix);for(let i=0;i<l.length;i++)for(let j=i+1;j<l.length;j++)cm+=2*l[i]*l[j];
     for(const key of graph){const [i,j]=key.split(":").map(Number),x=b.sz[i],y=b.sz[j];if(x<=o.same&&y<=o.same)cs+=2*x*y;}
     ok(cm<=2*Math.max(0,2*md-1)*a.dm&&cs<=2*Math.max(0,2*sd-1)*b.ds,"matching potential bound");
     o.mixCover+=cm;o.sameCover+=cs;o.maxMixDeg=Math.max(o.maxMixDeg,md);o.maxSameDeg=Math.max(o.maxSameDeg,sd);layerChecks++;
   }
   if(gs.length<2)continue;
   const pp=[];for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){const a=es[i],b=es[j],gi=gm.get(pred(a)),gj=gm.get(pred(b));if(gi===gj)continue;ok(a.M<b.M&&a.tail<=b.tail,"ordered tails");pairs++;exact+=2*a.tail;
     const caps=scales.map((s,z)=>{let k=a.M+":"+cell(b.M,s.d),rho=(rankCounters[z].get(k)||0)+1;rankCounters[z].set(k,rho);return z&&cell(a.M,s.d)===cell(b.M,s.d)?0:massCut(s.m,rho);});
     pp.push({a,b,gi,gj,rank:Math.max(...caps)});
   }
   const cuts=[...new Set(es.map(e=>e.tail).filter(x=>x>0))].sort((a,b)=>a-b);let last=0;
   for(const end of cuts){const sel=es.filter(e=>e.tail>=end),{sz,lab}=calc(sel,m0);const len=end-last;
     for(const {a,b,gi,gj,rank} of pp){if(a.tail<end)continue;const same=label(a)===label(b);let base=Math.max(rank,massCut(m0,sel.length),same?massCut(m0,lab.get(label(a))):0);
       for(let z=1;z<scales.length;z++){const s=scales[z],i=cell(a.M,s.d),j=cell(b.M,s.d);if(i===j)continue;const ss=sel.filter(e=>{let c=cell(e.M,s.d);return c===i||c===j;});base=Math.max(base,massCut(s.m,ss.length),same?massCut(s.m,ss.filter(e=>label(e)===label(a)).length):0);}
       const cover=c=>Math.max(0,Math.min(end,c)-last),o=cover(base);old+=2*o;
       let cap=0,qual=false;if(!same){cap=massCut(baseMix,Math.max(lab.get(label(a)),lab.get(label(b))));newMix+=2*cover(cap);}
       else{const k=Math.min(gi,gj)+":"+Math.max(gi,gj);qual=graph.has(k);if(qual){cap=massCut(baseSame,Math.max(sz[gi],sz[gj]));newSame+=2*cover(cap);}}
       const v=cover(Math.max(base,cap));if(same)oldExtraSame+=2*(v-o);else oldExtraMix+=2*(v-o);remaining+=2*(len-v);
       if(same){if(!qual)irregResidual+=2*(len-v);else largeBranchResidual+=2*(len-v);}
     }last=end;
   }
 }
 for(const o of layer){ok(o.mixD===o.mixL-o.start&&o.sameD===o.sameL-o.start&&o.mixD<=2*o.mix*o.start&&o.sameD<=2*o.same*o.start,"layer telescope");ok(o.mixCover<=2*Math.max(0,2*o.maxMixDeg-1)*o.mixD&&o.sameCover<=2*Math.max(0,2*o.maxSameDeg-1)*o.sameD,"layer global matching");}
 ok(E===exact&&E===old+oldExtraMix+oldExtraSame+remaining,"energy partition");
 return {mode,X,B,T,Q,N,R,G,events,high,literal,Z,baseMix,baseSame,E,old,newMix,newSame,oldExtraMix,oldExtraSame,remaining,mergers,pairs,regChecks,rootChecks,sameEdges,mixedEdges,shortEdges,regEdges,regularOnly,maxDegree,maxReg,maxDiv,layerChecks,irregResidual,largeBranchResidual,layer};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
