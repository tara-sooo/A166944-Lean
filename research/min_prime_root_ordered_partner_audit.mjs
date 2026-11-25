// Reproduce: node research/min_prime_root_ordered_partner_audit.mjs
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
 const H=T+B,d0=mode==="analytic"?B:Math.max(4,Math.floor(B/16)),scales=[{d:0,m:m0},{d:d0,m:mode==="analytic"?Math.floor(u**1.75):2},{d:4*d0,m:mode==="analytic"?Math.floor(4*u**1.75):4}];
 const cell=(M,d)=>d?Math.floor((M-X)/d):0,pred=e=>e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M,label=e=>e.prev?.p||0;
 const counters=scales.map(()=>new Map()),ledger=scales.map(s=>({...s,keys:0,maxRank:0,all:0,old:0,extra:0,oneSide:0,partial:0,rankChecks:0,counts:0,layer:[0,0,0]})),xs=[1,128,512];
 let E=0,exact=0,old=0,union=0,extra=0,remaining=0,pairs=0,ordered=0,largeGroupExtra=0,oneSideExtra=0,partialExtra=0,groups=0;
 for(const es of vlist){
   const w=es.find(e=>e.w)?.w||0,n=es.filter(e=>e.w).length;E+=w*n*(n-1);
   const pp=[];for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){const a=es[i],b=es[j];ok(a.M<b.M&&a.tail<=b.tail,"ordered tails");ordered++;if(pred(a)!==pred(b))pp.push([a,b]);}
   // Pairs are in increasing smaller root then increasing larger root order at each vertex.
   for(const [a,b] of pp){
     pairs++;ok(2*(b.M-a.M)<H,"source locality");const tail=a.tail;exact+=2*tail;
     const ranks=[];
     for(let z=0;z<scales.length;z++){
       const s=scales[z],l=ledger[z],i=cell(a.M,s.d),j=cell(b.M,s.d),key=a.M+":"+j;
       const prev=counters[z].get(key)||0,rank=prev+1;counters[z].set(key,rank);
       // Independent reconstruction: larger tags in the same old predecessor are already
       // companions; newly encountered larger tags are ordered by source at this vertex.
       const expected=es.filter(e=>e.M>a.M&&cell(e.M,s.d)===j&&(pred(e)===pred(a)||e.M<=b.M)).length;
       ok(rank===expected,"persistent larger companion rank");l.rankChecks++;l.maxRank=Math.max(l.maxRank,rank);
       if(z&&i===j){ranks.push(null);continue;}
       const cap=Math.floor(s.m*s.m*H/(rank*rank)),big=es.filter(e=>e.M>a.M&&cell(e.M,s.d)===j).length,whole=Math.floor(s.m*s.m*H/(big*big));
       ok(cap>=whole,"partial batch cutoff");ranks.push({cap,whole});l.all+=2*Math.min(tail,cap);l.oneSide+=2*Math.min(tail,whole);l.partial+=2*(Math.min(tail,cap)-Math.min(tail,whole));l.counts++;
       for(let h=0;h<xs.length;h++)if(tail>=xs[h]&&rank<=Math.floor(s.m*Math.sqrt(H/xs[h])))l.layer[h]++;
     }
     if(!tail)continue;
     const cuts=[...new Set(es.map(e=>e.tail).filter(x=>x>0&&x<tail)),tail].sort((a,b)=>a-b);let last=0;
     for(const end of cuts){
       const sel=es.filter(e=>e.tail>=end),lab=label(a),same=lab===label(b),cnt=sel.filter(e=>label(e)===lab).length;
       let base=Math.max(Math.floor(m0*m0*H/sel.length**2),same?Math.floor(m0*m0*H/cnt**2):0),newCap=0,wholeCap=0;
       const bases=[base];
       for(let z=1;z<scales.length;z++){
         const s=scales[z],i=cell(a.M,s.d),j=cell(b.M,s.d);
         if(i===j){bases.push(0);continue;}
         const rr=sel.filter(e=>{let c=cell(e.M,s.d);return c===i||c===j;}),ll=rr.filter(e=>label(e)===lab).length,ct=Math.max(Math.floor(s.m*s.m*H/rr.length**2),same?Math.floor(s.m*s.m*H/ll**2):0);bases.push(ct);base=Math.max(base,ct);
       }
       const len=end-last,measure=v=>Math.max(0,Math.min(end,v)-last),g=measure(base);old+=2*g;
       for(let z=0;z<scales.length;z++)if(ranks[z]){
         const l=ledger[z],rr=ranks[z];ok(rr.cap>=bases[z]||same,"rank dominates small total");
         l.old+=2*measure(bases[z]);l.extra+=2*(measure(Math.max(base,rr.cap))-g);newCap=Math.max(newCap,rr.cap);wholeCap=Math.max(wholeCap,rr.whole);
       }
       const r=measure(Math.max(base,newCap)),os=measure(Math.max(base,wholeCap));union+=2*r;extra+=2*(r-g);remaining+=2*(len-r);oneSideExtra+=2*(os-g);partialExtra+=2*(r-os);
       last=end;
     }
   }
 }
 ok(E===exact&&E===union+remaining&&union===old+extra&&extra===oneSideExtra+partialExtra,"exact energy partition");
 for(let z=0;z<scales.length;z++){
   const l=ledger[z],s=scales[z],K=s.d?Math.ceil(H/(2*s.d))+1:1;
   l.keys=counters[z].size;ok(l.keys<=N*(K+1),"root cell count");ok(l.all<=4*l.keys*s.m*Math.sqrt(H*1.5*H)+1e-5,"rank integral bound");
   for(let h=0;h<xs.length;h++)ok(l.layer[h]<=l.keys*Math.floor(s.m*Math.sqrt(H/xs[h])),"layer rank budget");
 }
 return {mode,X,B,T,N,Q,R,G,events,high,literal,E,exact,old,union,extra,remaining,pairs,ordered,oneSideExtra,partialExtra,ledger};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
