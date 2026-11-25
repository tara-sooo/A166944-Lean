// Multiscale actual first-contact cuts and summable opposite-cohort peeling.
function multiscale(g,live,z,edges,L,y,B,X,f,m,ok,close,fac,ledger){
 const base=L*Math.floor((g.C-1)/L),cuts=[],levels=[],minRoot=Math.min(...live.map(e=>2*e.P.M-2));
 for(let j=0;;j++){let K=base-L*(2**j-1);cuts.push(K);if(K<minRoot)break}
 const entries=new Map(live.map(e=>[e.P.M,e]));
 function at(e,K){
   const P=e.P,root=2*P.M-2;
   if(root>K)return {key:"root:"+P.M,q:0,J:root,t:P.s,root:true};
   for(let k=0;k<e.i;k++){const h=P.records[k],J=h.C+h.p-1;
     if(J>K){ok(h.C<=K&&h.p>y,"primorial crossing");return {key:J+','+h.v+','+h.p,q:h.p,J,t:h.v,root:false}}}
   throw Error("missing cut crossing");
 }
 for(const K of cuts)levels.push(new Map(live.map(e=>[e.P.M,at(e,K)])));
 for(let j=1;j<levels.length;j++){
   const parent=new Map();for(const e of live){const a=levels[j].get(e.P.M).key,b=levels[j-1].get(e.P.M).key;ok(!parent.has(a)||parent.get(a)===b,"nested cut partitions");parent.set(a,b)}
 }
 function first(a,b){
   let i=0,j=0,A=a.P.records,Q=b.P.records;
   while(i<=a.i&&j<=b.i){
     const x=A[i],y=Q[j];if(x.C<y.C){i++;continue}if(x.C>y.C){j++;continue}
     const t=Math.max(x.b,y.b);
     if(t<Math.min(x.v,y.v)){
       const p=x.b===t?(i?A[i-1].p:0):-1,q=y.b===t?(j?Q[j-1].p:0):-1;
       ok(p!==q,"first contact incoming labels");
       let type=p===0||q===0?0:p===-1||q===-1?1:2;
       if(type===2){const s=t%2,d=2*t-x.C-6*s;ok(p>=3&&q>=3&&d%p===0&&d%q===0,"two jump divisor");if(d!==0)ok(p*q<=Math.abs(d)&&Math.abs(d)<=12*B+6,"nonreset product");else type=3}
       return {J:x.C,t,type,p,q}
     }i++;j++;
   }throw Error("no original common tick");
 }
 const shellRaw=cuts.map(()=>0),shellPaid=cuts.map(()=>0),shellRemain=cuts.map(()=>0),shellPairs=cuts.map(()=>0),types=[0,0,0,0],remTypes=[0,0,0,0],constraints=new Map(),inc=new Map(),alive=new Set(),parents=new Map();let oracle=0;
 for(const e of edges){
   const a=entries.get(e.i),b=entries.get(e.j),F=first(a,b);
   let j=levels.findIndex(l=>l.get(e.i).key!==l.get(e.j).key);ok(j>=0,"separation at root singleton");
   for(let k=0;k<cuts.length;k++)ok((levels[k].get(e.i).key===levels[k].get(e.j).key)===(F.J<=cuts[k]),"exact contact-cut equivalence");
   const upper=j?cuts[j-1]:g.C;ok(cuts[j]<F.J&&F.J<=upper,"first contact shell");
   const parent=j?levels[j-1].get(e.i).key:"TOP";if(j)ok(parent===levels[j-1].get(e.j).key,"common upper cohort");
   const pmax=Math.max(F.p,F.q),Q=Math.max(5,Math.ceil(B/4));
   const pk=Math.min(e.i,e.j)+','+Math.max(e.i,e.j),pl=pk+','+(2*z-g.C);
   ok(!ledger.seen.has(pl),"no duplicate old pair-level across sampled origins");ledger.seen.add(pl);
   ledger.pairs.set(pk,(ledger.pairs.get(pk)||0)+e.w);
   if(pmax>=Q){
     const s=F.t%2,d=2*F.t-F.J-6*s;
     ok(d>=0&&d%(2*pmax)===0&&(F.J+2*s)%pmax===0,"large first-contact phase");
     const key=F.t+','+F.J+','+pmax;let c=ledger.keys.get(key);
     if(!c){c={w:0,reset:d===0,pairs:new Set()};ledger.keys.set(key,c)}
     c.w+=e.w;c.pairs.add(pk);
   }
   e.shell=j;e.first=F;e.parent=parent;shellRaw[j]+=e.w;shellPairs[j]++;types[F.type]+=e.w;
   const k=j+"|"+parent;let p=parents.get(k);if(!p){p={j,parent,groups:[new Set(),new Set(),new Set()]};parents.set(k,p)}
   for(const v of [e.i,e.j]){
     const a0=levels[j].get(v),ty=a0.root?0:a0.q*f>=g.r?1:2;
     ok(a0.J<=F.J&&a0.J<=upper&&a0.t<=F.t,"precontact entry");
     if(!a0.root)ok(z-a0.t<=2*g.r+3*(g.C-cuts[j]),"entry phase window");
     p.groups[ty].add(a0.key);
   }
   if(oracle<64){
     const from=Math.max(a.P.s,b.P.s),to=z-1;let ia=0,ib=0,hit=null;
     for(let t=from;t<=to;t++){while(a.P.records[ia].v<=t)ia++;while(b.P.records[ib].v<=t)ib++;if(a.P.records[ia].C===b.P.records[ib].C){hit={J:a.P.records[ia].C,t};break}}
     ok(hit&&hit.J===F.J&&hit.t===F.t,"literal first contact oracle");oracle++;
   }
 }
 function add(k,e,cap){
   let c=constraints.get(k);if(!c){c={cap,es:[],degree:0,done:false};constraints.set(k,c)}ok(close(c.cap,cap),"fixed quota");c.es.push(e);c.degree+=e.w;
   if(!inc.has(e))inc.set(e,[]);inc.get(e).push(c);
 }
 let maxComp=0,maxSmall=0,maxParent=0,compBound=0;
 for(const p of parents.values()){
   const j=p.j,upper=j?cuts[j-1]:g.C,K=cuts[j],n=upper-K;let envelope=0;
   for(let J=Math.max(K+2,2*X-2);J<=upper;J+=2)for(let s=0;s<2;s++)for(const q of fac(J+2*s)){
     if(q<=y||q>B||q*f<g.r)continue;let res=s?q+2:0,lo=z-2*g.r-3*(g.C-K),hi=z-1;
     envelope+=Math.max(0,Math.floor((hi-res)/(2*q))-Math.ceil((lo-res)/(2*q))+1)
   }
   ok(p.groups[1].size<=envelope,"comparable shell envelope");ok(p.groups[0].size<=Math.floor(n/2)+1,"root singleton shell envelope");
   maxComp=Math.max(maxComp,p.groups[1].size);maxSmall=Math.max(maxSmall,p.groups[2].size);maxParent=Math.max(maxParent,...p.groups.map(s=>s.size));compBound=Math.max(compBound,envelope);
 }
 for(const e of edges){
   alive.add(e);const j=e.shell,p=parents.get(j+"|"+e.parent),theta=1/(j+1)**2;
   for(const [v,o] of [[e.i,e.j],[e.j,e.i]]){const a=levels[j].get(o),ty=a.root?0:a.q*f>=g.r?1:2;add(v+"|"+j+"|"+a.key,e,m*theta/Math.max(1,p.groups[ty].size))}
 }
 const queue=[...constraints.values()].filter(c=>c.degree<=c.cap+1e-10);
 for(let i=0;i<queue.length;i++){const c=queue[i];if(c.done||c.degree>c.cap+1e-10)continue;c.done=true;
   for(const e of c.es){if(!alive.delete(e))continue;shellPaid[e.shell]+=e.w;
     for(const a of inc.get(e)){let before=a.degree;a.degree-=e.w;if(before>a.cap+1e-10&&a.degree<=a.cap+1e-10)queue.push(a)}}
 }
 let budget=0;for(const c of constraints.values())budget+=c.cap;let minCompPartners=null,keptPairs=0;
 for(const e of alive){
   keptPairs++;shellRemain[e.shell]+=e.w;remTypes[e.first.type]+=e.w;for(const c of inc.get(e))ok(c.degree>c.cap-1e-9,"multiscale core");
   for(const [v,o] of [[e.i,e.j],[e.j,e.i]]){const a=levels[e.shell].get(o);if(!a.root&&a.q*f>=g.r){const cs=constraints.get(v+"|"+e.shell+"|"+a.key),n=cs.es.filter(x=>alive.has(x)).length;ok(n>2*cs.cap-1e-8,"actual opposite partners");minCompPartners=minCompPartners===null?n:Math.min(minCompPartners,n)}}
 }
 const vertices=new Set(edges.flatMap(e=>[e.i,e.j]));
 ok(budget<=6*m*vertices.size+1e-7,"summable capacity");ok(shellPaid.reduce((a,b)=>a+b,0)<=budget+1e-7,"absolute multiscale budget");
 for(let j=0;j<cuts.length;j++)ok(close(shellRaw[j],shellPaid[j]+shellRemain[j]),"shell ledger");
 return {cuts,shellRaw,shellPaid,shellRemain,shellPairs,types,remTypes,oracle,budget,vertices:vertices.size,keptPairs,parents:parents.size,maxComp,maxSmall,maxParent,compBound,minCompPartners};
}
// Exact compressed inverse stationary intervals, primorial entry cuts and cohort quotas.
function audit(X,stress=true,scaleCap=4){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),rmin=Math.max(3,Math.ceil(D/4)),eta=stress?1/8:u**(-1/4),f=stress?4:u**(1/16),m=stress?4:u**(11/4),L=stress?30:2,y=stress?5:2;
 const ok=(x,s)=>{if(!x)throw Error(s)},close=(a,b)=>Math.abs(a-b)<1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 const sp=new Int32Array(8*X+100);for(let i=2;i<sp.length;i++)if(!sp[i])for(let j=i;j<sp.length;j+=i)if(!sp[j])sp[j]=i;
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return a}
 function fac(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
 function rr(C){let p=Math.min(sp[C-1]||Infinity,sp[C+1]||Infinity);return p<=B?p:0}
 function select(t,C){let k=t%2,p=sp[gcd(t-2*k,C+2*k-1)]||0;return p<=B?p:0}
 const slots=new Map(),paths=new Map();let clock=0,roughVisits=0;
 for(let M=X+1;M<2*X;M+=2){
   let s=M+2,t=s,C=2*M-2,records=[];
   ok(s+H+2*B<=Math.floor((7*M-1)/4),"gate");
   const P={M,s,records,end:0,min:null};paths.set(M,P);
   while(t<s+H){
     let r=rr(C);if(!r)break;
     let b=t,p=0;while(!p){t++;p=select(t,C)}
     ok(t-b<=2*r,"wait");
     const e={C,b,v:t,p,r,P,i:records.length,post:2*t-(C+p-1)};records.push(e);
     if(r>=rmin&&r>L+1){
       let key=C+','+t,g=slots.get(key);if(!g){g={C,v:t,p,r,entries:[]};slots.set(key,g)}g.entries.push(e);roughVisits++;
     }
     C+=p-1;ok(C<=2*t,"deficit");
   }
   P.end=t;P.endC=C;clock+=t-s;
   const min=new Int32Array(records.length);let d=2*t-C;for(let i=records.length-1;i>=0;i--){d=Math.min(d,records[i].post);min[i]=d}P.min=min;
 }
 function previous(C,t){
   let a=Math.ceil(C/2);
   for(let k=0;k<2;k++)for(const p of fac(C+2*k-1)){
     if(p>B)continue;let res=k?p+2:0,b=res+2*p*Math.floor((t-res)/(2*p));a=Math.max(a,b);
   }
   return a;
 }
 function inv(C,t,lo){
   const a=previous(C,t),out=[];
   ok(a<=t,"stationary interval");
   for(let k=0;k<2;k++)for(const p of fac(C+2*k)){
     if(p>B||p===2)continue;
     let res=k?p+2:0,b=res+2*p*Math.ceil((a-res)/(2*p));
     for(;b<=t;b+=2*p){
       let J=C-p+1;if(J<2*lo-2||J>2*(b-1))continue;
       if(select(b,J)===p)out.push({b,J,p,side:k});
     }
   }
   return {a,out};
 }
 function reverse(g,z,cut=null){
   const C0=g.C,t0=z-1,low0=Math.max(X+1,g.v-2*g.r-H-1);
   const memo=new Map(),found=new Set(),front=[],stats={queries:0,edges:0,stationaryTicks:0,maxInterval:0,frontiers:0,intervalOracle:0};
   // Exact partial exploration: stop below/at a horizon cut, retain a safe original-source interval.
   function go(C,t,lo,top=false){
     lo=Math.max(lo,X+1,t-H-2*B-2);
     const hi=Math.min(2*X-1,C/2+1,t-2);
     if(lo>hi||C>2*t||C<2*X-2)return;
     const k=C+','+t+','+lo+','+Number(top);
     if(memo.has(k))return;memo.set(k,1);
     if(!top&&cut!==null&&C<=cut){front.push([lo,hi]);stats.frontiers++;return}
     stats.queries++;
     const {a,out}=inv(C,t,lo);
     stats.stationaryTicks+=t-a+1;stats.maxInterval=Math.max(stats.maxInterval,t-a+1);
     if(stats.intervalOracle<64){
       let literal=Math.ceil(C/2);for(let b=t;b>=Math.ceil(C/2);b--)if(select(b,C)){literal=b;break}
       ok(a===literal,"stationary last eligible tick oracle");
       // All actual one-step incoming events across the compressed interval.
       const expected=new Set();
       for(let b=a;b<=t;b++){
         let side=b%2,h=gcd(b-2*side,C+2*side);
         for(const p of fac(h)){
           if(p===2||p>B)continue;let J=C-p+1;
           if(J<2*lo-2||J>2*(b-1))continue;
           if(select(b,J)===p)expected.add(b+','+J+','+p);
         }
       }
       ok(expected.size===out.length&&out.every(e=>expected.has(e.b+','+e.J+','+e.p)),"incoming arithmetic oracle");
       stats.intervalOracle++;
     }
     const M=C/2+1,s=M+2;
     if(M%2===1&&M>=lo&&M<=hi&&s>=a&&s<=t)found.add(M);
     for(const e of out){
       stats.edges++;
       // Only the top target arrival needs the original nominal stop condition.
       const nextLo=top?Math.max(lo,e.b-H-1):lo;
       go(e.J,e.b-1,nextLo);
     }
   }
   go(C0,t0,low0,true);
   const possible=new Set(found);
   for(const [a,b] of front)for(let M=Math.ceil(a);M<=b;M++)if(M%2===1)possible.add(M);
   return {found,possible,stats};
 }
 // The first entry into the final even-primorial block is independent of the later last nonLOW anchor.
 function entry(e,K){
   const P=e.P;
   if(2*P.M-2>K)return {key:"root",q:0,J:2*P.M-2,t:P.s};
   for(let j=0;j<e.i;j++){
     const x=P.records[j],J=x.C+x.p-1;
     if(J>K){ok(x.C<=K&&x.p>y,"primorial block entry");return {key:J+','+x.v+','+x.p,q:x.p,J,t:x.v}}
   }
   throw Error("missing block entry");
 }
 function capGroup(edges,groups){
   const alive=new Set(edges),inc=new Map(),constraints=new Map();
   function add(k,e,cap){if(!constraints.has(k))constraints.set(k,{es:[],degree:0,cap,done:false});let z=constraints.get(k);z.es.push(e);z.degree+=e.w;if(!inc.has(e))inc.set(e,[]);inc.get(e).push(z)}
   const comp=new Set([...groups.values()].filter(g=>g.q&&g.q*f>=g.r).map(g=>g.key));
   const small=new Set([...groups.values()].filter(g=>g.q&&g.q*f<g.r).map(g=>g.key));
   for(const e of edges)for(const [v,o] of [[e.i,e.j],[e.j,e.i]]){
     let own=groups.get(v),other=groups.get(o);
     let cap=own.key===other.key?m:m/Math.max(1,comp.has(other.key)?comp.size:small.size);
     add(v+'|'+other.key,e,cap);
   }
   const queue=[...constraints.values()].filter(c=>c.degree<=c.cap+1e-10);
   let paid=0;
   for(let i=0;i<queue.length;i++){
     const c=queue[i];if(c.done||c.degree>c.cap+1e-10)continue;c.done=true;
     for(const e of c.es){
       if(!alive.delete(e))continue;paid+=e.w;
       for(const z of inc.get(e)){let prev=z.degree;z.degree-=e.w;if(prev>z.cap+1e-10&&z.degree<=z.cap+1e-10)queue.push(z)}
     }
   }
   let budget=0,minCompPartners=Infinity,kept=[...alive];
   for(const c of constraints.values())budget+=c.cap;
   for(const e of kept)for(const c of inc.get(e))ok(c.degree>c.cap-1e-9,"entry-cohort fixed core");
   for(const e of kept)for(const [v,o] of [[e.i,e.j],[e.j,e.i]])if(groups.get(v).key!==groups.get(o).key&&comp.has(groups.get(o).key)){
     const z=constraints.get(v+'|'+groups.get(o).key);minCompPartners=Math.min(minCompPartners,z.es.filter(e=>alive.has(e)).length);
   }
   ok(paid<=budget+1e-7&&budget<=3*m*groups.size+1e-7,"entry quota capacity");
   return {paid,remaining:kept.reduce((s,e)=>s+e.w,0),budget,edges:kept.length,comp:comp.size,small:small.size,minCompPartners:Number.isFinite(minCompPartners)?minCompPartners:null};
 }
 const sorted=[...slots.values()].sort((a,b)=>b.entries.length-a.entries.length||a.C-b.C||a.v-b.v);
 const pick=new Map();for(const g of sorted.slice(0,6))pick.set(g.C+','+g.v,g);
 for(let j=1;j<=6;j++){const g=sorted[Math.floor((sorted.length-1)*j/7)];if(g)pick.set(g.C+','+g.v,g)}
 const ledgers=[0,1].map(()=>({seen:new Set(),pairs:new Map(),keys:new Map()}));
 const out=[];let checks=0,maxRoots=0,totalQuery=0,totalEdges=0,totalStationary=0;
 for(const g of pick.values()){
   const z=Math.min(g.v-1,Math.max(...g.entries.map(e=>e.b))+1);
   if(z<=Math.min(...g.entries.map(e=>e.b)))continue;
   const live=g.entries.filter(e=>e.b<z),expected=new Set(live.map(e=>e.P.M));
   const K=L*Math.floor((g.C-1)/L),lam=2*z-g.C,ell=Math.max(1,Math.floor(eta*g.r));
   if(lam<1)continue;
   const ex=reverse(g,z);
   ok(ex.found.size===expected.size&&[...expected].every(M=>ex.found.has(M)),"exact compressed inverse vs original forward roots");
   const partial=[K,K-4*L,K-16*L].map(c=>{let q=reverse(g,z,c);ok([...expected].every(M=>q.possible.has(M)),"partial reverse support");return {cut:c,upper:q.possible.size,known:q.found.size,queries:q.stats.queries,frontiers:q.stats.frontiers}});
   ok(partial[1].upper<=partial[0].upper&&partial[2].upper<=partial[1].upper,"nested frontier upper envelopes");
   checks++;maxRoots=Math.max(maxRoots,expected.size);totalQuery+=ex.stats.queries;totalEdges+=ex.stats.edges;totalStationary+=ex.stats.stationaryTicks;
   const groups=new Map(),actualComp=new Set();let rootsInside=0,largestGroup=0;const counts=new Map();
   for(const e of live){
     let a=entry(e,K);a.r=g.r;groups.set(e.P.M,a);
     ok(a.J>K&&a.J<=g.C&&a.t<=z-1&&z-a.t<=2*g.r+3*L,"block entry window");
     if(!a.q)rootsInside++;else if(a.q*f>=g.r)actualComp.add(a.key);
     counts.set(a.key,(counts.get(a.key)||0)+1);largestGroup=Math.max(largestGroup,counts.get(a.key));
   }
   ok(rootsInside<=L/2+1,"inside roots");
   let compEnvelope=0;
   for(let J=K+2;J<=g.C;J+=2)for(let side=0;side<2;side++)for(const p of fac(J+2*side)){
     if(p<=y||p>B||p*f<g.r)continue;
     let res=side?p+2:0,lo=z-2*g.r-3*L,hi=z-1;
     compEnvelope+=Math.max(0,Math.floor((hi-res)/(2*p))-Math.ceil((lo-res)/(2*p))+1);
   }
   ok(actualComp.size<=compEnvelope,"comparable entry arithmetic envelope");
   // Same original delayed masks, one charged level lambda at sampled origin.
   const byClass=[[],[],[]];
   for(const e of g.entries){
     let q=0;for(let j=e.i-1;j>=0;j--)if(e.P.records[j].p>y){q=e.P.records[j].p;break}
     byClass[q===0?0:q*f>=g.r?1:2].push(e);
   }
   const gates=byClass.map(a=>{a.sort((x,y)=>x.b-y.b);return a.length>(stress?12:u**2.75)?a[Math.floor(stress?12:u**2.75)].b:Infinity});
   const modes=[];
   for(let mode=0;mode<2;mode++){
     let ret=[];
     for(let c=0;c<3;c++)for(const e of byClass[c]){
       if(e.b>=z||g.p>f*g.r||(mode===0?g.p<=Math.ceil(B**.25):2*(g.v-e.b)<=g.p-1))continue;
       let lo=Math.max(e.b+ell+1,gates[c]+ell,mode===0?e.P.s+2*B:e.b),hi=mode===0?Math.min(g.v,e.P.s+H):g.v;
       if(lo>=hi)continue;ret.push({e,lo,hi,w:(hi-lo)/(2*g.r)});
     }
     let raw=0,inside=0,edges=[],allEdges=[],same=0,cross=0;
     for(let i=0;i<ret.length;i++)for(let j=i+1;j<ret.length;j++){
       let a=ret[i],b=ret[j],F=a.e.b>=b.e.b?a:b,O=F===a?b:a,early=a.e.P.end<=b.e.P.end?a.e:b.e;
       if(z+ell<F.lo||z+ell>=F.hi||lam>early.P.min[early.i])continue;
       let w=O.w/2,ii=a.e.P.M,jj=b.e.P.M;raw+=w;allEdges.push({i:ii,j:jj,w});
       if(!groups.get(ii).q||!groups.get(jj).q){inside+=w;continue}
       edges.push({i:ii,j:jj,w});
       if(groups.get(ii).key===groups.get(jj).key)same+=w;else cross+=w;
     }
     const vertices=new Map();for(const e of edges){vertices.set(e.i,groups.get(e.i));vertices.set(e.j,groups.get(e.j))}
     let c=capGroup(edges,vertices);
     ok(close(raw,inside+c.paid+c.remaining)&&close(same+cross,c.paid+c.remaining),"sample origin energy ledger");
     const ms=multiscale(g,live,z,allEdges,L,y,B,X,f,stress?scaleCap:u**2.75,ok,close,fac,ledgers[mode]);
     ok(close(raw,ms.shellRaw.reduce((a,b)=>a+b,0)),"all original charges assigned once");
     modes.push({mode:mode?"full-positive":"late-high",raw,inside,same,cross,...c,multiscale:ms});
   }
   out.push({C:g.C,v:g.v,z,lambda:lam,r:g.r,roots:expected.size,exact:ex.stats,partial,entryGroups:counts.size,largestGroup,rootsInside,actualComp:actualComp.size,compEnvelope,modes});
 }
 const Q=Math.max(5,Math.ceil(B/4)),support=[0,0];
 for(let p=Q;p<=B;p++)if(sp[p]===p)for(let s=0;s<2;s++)for(let k=0;6*s+2*p*k<=12*B+6;k++){
   const d=6*s+2*p*k;
   const j0=2*p*Math.ceil((2*X-2+2*s)/(2*p))-2*s;
   for(let J=j0;J<7*X;J+=2*p){
     let t=(J+d)/2;
     if(t%2!==s||(t-2*s)%p)continue;
     support[k===0?0:1]++;
   }
 }
 const firstContact=ledgers.map(g=>{
   let stats=[0,1].map(ty=>({keys:0,weight:0,quotaPaid:0,remaining:0,maxPairs:0}));
   for(const v of g.pairs.values())ok(v<=6*B+3+1e-6,"aggregate original terminal pair budget");
   for(const c of g.keys.values()){const i=c.reset?0:1,z=stats[i],cap=i===0?32:8;z.keys++;z.weight+=c.w;z.quotaPaid+=Math.min(c.w,cap);z.remaining+=Math.max(0,c.w-cap);z.maxPairs=Math.max(z.maxPairs,c.pairs.size)}
   for(let i=0;i<2;i++)ok(stats[i].keys<=support[i],"large first-contact key arithmetic envelope");
   return {Q,support,pairLevels:g.seen.size,distinctPairs:g.pairs.size,stats};
 });
 return {X,B,L,y,rmin,f,m,scaleCap,firstContact,clock,roughVisits,slots:slots.size,checks,maxRoots,totalQuery,totalEdges,totalStationary,out};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[4096,16384,65536]))for(const m of [4,16])console.log(JSON.stringify(audit(X,true,m)));
