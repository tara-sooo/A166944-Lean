// Reproduce: node research/min_prime_root_cell_merger_audit.mjs
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
 const H=T+B;
 const d0=mode==="analytic"?B:Math.max(4,Math.floor(B/16)),d1=d0*4;
 const scales=[d0,d1].map((d,i)=>({d,m:mode==="analytic"?Math.max(1,Math.floor(d/B*u**1.75)):i?4:2,adj:new Map(),near:0,small:0,extra:0,sameLabelExtra:0,checks:0,layer:[]}));
 const cell=(M,d)=>Math.floor((M-X)/d),pred=e=>e.prev?e.prev.C+":"+e.prev.t:"root:"+e.M,label=e=>e.prev?.p||0;
 const inc=(m,k,n=1)=>m.set(k,(m.get(k)||0)+n),link=(s,a,b)=>{if(a===b)return;if(!s.adj.has(a))s.adj.set(a,new Set());if(!s.adj.has(b))s.adj.set(b,new Set());s.adj.get(a).add(b);s.adj.get(b).add(a);};
 let energy=0,exact=0,global=0,extra=0,residual=0,monotone=0,merged=0,pairs=0,intervals=0,nearBoth=0;
 for(const es of vlist){
   for(let i=1;i<es.length;i++){ok(es[i-1].M<es[i].M&&es[i-1].tail<=es[i].tail,"ordered cutoff tails");monotone++;}
   const w=es.find(e=>e.w)?.w||0,active=es.filter(e=>e.w).length;energy+=w*active*(active-1);
   const pp=[];for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++)if(pred(es[i])!==pred(es[j])){const a=es[i],b=es[j];ok(2*(b.M-a.M)<H,"source locality");pp.push([a,b]);pairs++;for(const s of scales)link(s,cell(a.M,s.d),cell(b.M,s.d));}
   if(!pp.length)continue;merged++;
   const cuts=[...new Set(es.map(e=>e.tail).filter(x=>x>0))].sort((a,b)=>a-b);let last=0;
   for(const end of cuts){
     const sel=es.filter(e=>e.tail>=end),n=sel.length,lab=new Map();for(const e of sel)inc(lab,label(e));
     const maps=scales.map(s=>{const m=new Map(),l=new Map();for(const e of sel){const c=cell(e.M,s.d);inc(m,c);inc(l,c+":"+label(e));}return {m,l};});
     for(const [a,b] of pp){if(a.tail<end||b.tail<end)continue;const same=label(a)===label(b),lim0=Math.floor(m0*m0*H/(n*n)),lim1=same?Math.floor(m0*m0*H/lab.get(label(a))**2):0,base=Math.max(lim0,lim1),good=Math.max(0,Math.min(end,base)-last);let union=base;
       exact+=2*(end-last);global+=2*good;
       for(let z=0;z<scales.length;z++){const s=scales[z],m=maps[z],i=cell(a.M,s.d),j=cell(b.M,s.d);if(i===j){s.near+=2*(end-last);continue;}
         const mass=m.m.get(i)+m.m.get(j),lm=same?(m.l.get(i+":"+label(a))||0)+(m.l.get(j+":"+label(a))||0):0;
         const ct=Math.floor(s.m*s.m*H/mass**2),cl=same?Math.floor(s.m*s.m*H/lm**2):0,cap=Math.max(ct,cl),g=Math.max(0,Math.min(end,cap)-last);
         s.small+=2*g;s.extra+=2*Math.max(0,Math.min(end,cap)-Math.max(last,base));s.sameLabelExtra+=2*Math.max(0,Math.min(end,cl)-Math.max(last,base,ct));union=Math.max(union,cap);s.checks++;
       }
       const all=Math.max(0,Math.min(end,union)-last);extra+=2*(all-good);residual+=2*(end-last-all);
     }last=end;intervals++;
   }
 }
 ok(energy===exact&&energy===global+extra+residual,"integral ledger");
 // Independent layer potential: observed cross-cell merger pairs suffice. Count every
 // vertex of their restricted prefix forest, even if only one cell is present.
 for(const s of scales){
   let degreeMax=0,edges=0;for(const [c,adj] of s.adj){degreeMax=Math.max(degreeMax,adj.size);edges+=adj.size;for(const j of adj)ok(Math.abs(c-j)<=Math.ceil(H/(2*s.d))+1,"cell locality");}
   s.edges=edges/2;s.degreeMax=degreeMax;
   for(const x of [1,128,512]){
     const m=Math.max(1,Math.floor(s.m*Math.sqrt(H/x)));let delta=0,loss=0,start=0,eligible=0,eligibleSame=0,heavy=0;
     for(const es of vlist){
       const cm=new Map();for(const e of es){if(e.tail<x)continue;let c=cell(e.M,s.d);if(!s.adj.has(c))continue;if(!cm.has(c))cm.set(c,[]);cm.get(c).push(e);}
       const evalGroup=(aa,bb)=>{
         const all=bb?aa.concat(bb):aa,n=all.length,gr=new Map(),lab=new Map(),lgr=new Map();let e=0,r=0;
         for(const v of all){inc(gr,pred(v));inc(lab,label(v));inc(lgr,label(v)+":"+pred(v));if(!v.next||v.next.tail<x)e++;if(!v.prev)r++;else ok(v.prev.tail>=x,"prefix layer");}
         const dd=f(n,m)-[...gr.values()].reduce((s,v)=>s+f(v,m),0);
         return {d:dd,l:f(n,m)-f(n-e,m),r};
       };
       const cache=new Map();for(const [c,aa] of cm){const v=evalGroup(aa,null),deg=s.adj.get(c).size;cache.set(c,v);delta+=deg*v.d;loss+=deg*v.l;start+=deg*v.r;}
       for(const [c,aa] of cm)for(const j of s.adj.get(c)){if(j<=c||!cm.has(j))continue;const bb=cm.get(j),v=evalGroup(aa,bb),a=cache.get(c),b=cache.get(j);delta+=v.d-a.d-b.d;loss+=v.l-a.l-b.l;start+=v.r-a.r-b.r;
         let low=0,ls=0;const n=aa.length+bb.length,lab=new Map();for(const e of aa.concat(bb))inc(lab,label(e));
         for(const a of aa)for(const b of bb)if(pred(a)!==pred(b)){if(n<=m)low+=2;else if(label(a)===label(b)&&lab.get(label(a))<=m)ls+=2;}
         ok(low+ls<=v.d,"restricted hierarchical cap");eligible+=low;eligibleSame+=ls;if(n>m)heavy++;
       }
     }
     ok(delta===loss-start&&delta<=2*m*start&&eligible+eligibleSame<=delta,"cell potential");
     s.layer.push({x,m,delta,loss,start,eligible,eligibleSame,heavy});
   }
   delete s.adj;
 }
 return {X,B,T,Q,mode,N,R,G,events,high,literal,energy,global,extra,residual,monotone,merged,pairs,intervals,scales};
}

const xs=process.argv.slice(2).map(Number);for(const mode of ['short','wide','analytic'])for(const X of (xs.length?xs:[256,1024,4096,16384,65536,262144]))console.log(JSON.stringify(audit(X,mode)));
