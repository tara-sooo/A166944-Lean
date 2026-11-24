// Node.js: global weighted forest ledger and exact local cycle rank.
function auditCycle(X) {
 const B=Math.ceil(Math.sqrt(7*X)),spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{while(b){let z=a%b;a=b;b=z}return a},check=b=>{if(!b)throw Error("check")};
 function hit(t,C,K){let u=K+1,q=0;for(const s of [-1,1]){let v=C+s;while(v>1){let p=spf[v];if(p>B)break;let m=2*p,r=s===-1?0:p+2,h=t+1+((r-t-1)%m+m)%m;if(h<u||(h===u&&p<q)){u=h;q=p}while(v%p===0)v/=p}}return [u,q]}
 const cuts=[11,Math.max(11,Math.ceil(Math.sqrt(B))),Math.max(11,Math.ceil(B/Math.log(B)**(2/3))),Math.max(11,Math.ceil(B/Math.log(B)**(1/16)))], J=210, T=Math.ceil(B*Math.log(B)**(1/16)), hs=[8,16,32];
 const stat=cuts.map(Q=>({Q,small:0,smallGain:0,large:0,largeCount:0,last:0,heavy:0,heavyCount:0,forest:0,surplus:0,lightCount:0,forestEdges:0,surplusEdges:0,distinct:0,components:0,cycleSources:0,local:hs.map(h=>({h,windows:0,short:0,cyclic:0,cycles:0,certified:0,certifiedEdges:0,certifiedTagR:0,deficient:0,forest:0,localR:0,cycleR:0,longR:0}))}));
 function rank(rows,k){let a=rows.map(r=>r.map(BigInt)),i=0,prev=1n;for(let j=0;j<k;j++){let z=i;while(z<a.length&&!a[z][j])z++;if(z===a.length)continue;[a[i],a[z]]=[a[z],a[i]];let p=a[i][j];for(let b=i+1;b<a.length;b++){for(let c=j+1;c<k;c++){let x=a[b][c]*p-a[b][j]*a[i][c];check(x%prev===0n);a[b][c]=x/prev}a[b][j]=0n}prev=p;i++;if(i===a.length)break}return i}
 function local(w,s){
  s.windows++;s.localR+=w.reduce((a,b)=>a+b[3],0);if(w[w.length-1][0]-w[0][0]>T){s.longR+=w.reduce((a,b)=>a+b[3],0);return} s.short++;
  const ps=[...new Set(w.map(e=>e[1]))],k=ps.length,ids=w.map(e=>ps.indexOf(e[1])),ref=Array(k).fill(null),d=[];
  for(let j=0;j<w.length;j++){let i=ids[j],H=w[j][0]+w[j][2];if(ref[i]===null)ref[i]=H;check((H-ref[i])%ps[i]===0);d.push((H-ref[i])/ps[i])}
  const par=ps.map((_,i)=>i),root=i=>{while(par[i]!==i)i=par[i];return i},edges=[],adj=ps.map(()=>[]),rows=[];
  for(let j=0;j+1<w.length;j++){let g=w[j+1][0]-w[j][0]-w[j][1]+1;if(g>J)continue;let u=ids[j],v=ids[j+1],row=Array(k+1).fill(0);row[u]+=d[j]+1;row[v]-=d[j+1];row[k]=g-1+w[j+1][2]-w[j][2];check(row.slice(0,k).reduce((a,b,i)=>a+b*ps[i],row[k])===ref[v]-ref[u]);edges.push([u,v,j]);
   if(root(u)!==root(v)){par[root(v)]=root(u);adj[u].push([v,row]);adj[v].push([u,row.map(x=>-x)])}
   else {let stack=[[u,Array(k+1).fill(0)]],seen=new Set([u]),path=null;while(stack.length){let [a,z]=stack.pop();if(a===v){path=z;break}for(let [b,r] of adj[a])if(!seen.has(b)){seen.add(b);stack.push([b,z.map((x,i)=>x+r[i])])}}check(path!==null);let eq=row.map((x,i)=>x-path[i]);check(eq.slice(0,k).reduce((a,b,i)=>a+b*ps[i],eq[k])===0);rows.push([u,eq])}
  }
  const comps=new Set(ps.map((_,i)=>root(i)));check(rows.length===edges.length-k+comps.size);
  if(!rows.length){s.forest++;return}s.cyclic++;s.cycles+=rows.length;s.cycleR+=w.reduce((a,b)=>a+b[3],0);
  for(let c of comps){let idsC=ps.map((_,i)=>i).filter(i=>root(i)===c),rr=rows.filter(([i])=>root(i)===c).map(([i,a])=>idsC.map(j=>a[j]));if(!rr.length)continue;let r=rank(rr,idsC.length);if(idsC.length>=2&&r>=idsC.length-1){s.certified++;let seen=new Set();for(let [u,v,j] of edges)if(root(u)===c){s.certifiedEdges++;seen.add(j);seen.add(j+1)}for(let j of seen)s.certifiedTagR+=w[j][3]}else s.deficient++}
 }
 let R=0,events=0,literal=0;
 for(let M=X+1;M<2*X;M+=2){let C=2*M-2,t=M+2,K=Math.floor((7*M-1)/4),a=[];
  for(;;){let [u,p]=hit(t,C,K);if(X<=1024){let v=K+1,q=0;for(let j=t+1;j<=K;j++){let g=gcd(j%2?j-2:j,C+(j%2?1:-1));if(g>1&&spf[g]<=B){v=j;q=spf[g];break}}check(u===v&&p===q);literal++}if(!p)break;let r=Math.min(spf[C-1],spf[C+1]);check(u-t<=2*r);R+=r;events++;a.push([C,p,u%2?1:-1,r]);C+=p-1;t=u;check(C<=2*t)}
  for(let s of stat){let w=[];for(let e of a)if(e[1]<s.Q){s.small+=e[3];s.smallGain+=e[1]-1}else{w.push(e);s.large+=e[3];s.largeCount++}if(!w.length)continue;
   const ps=[...new Set(w.map(e=>e[1]))],par=ps.map((_,i)=>i),ids=w.map(e=>ps.indexOf(e[1])),root=i=>{while(par[i]!==i)i=par[i];return i},edges=[];
   s.distinct+=ps.length;s.last+=w[w.length-1][3];
   for(let j=0;j+1<w.length;j++){let g=w[j+1][0]-w[j][0]-w[j][1]+1;check(g>=0);if(g>J){s.heavy+=w[j][3];s.heavyCount++}else{edges.push([ids[j],ids[j+1],w[j][3]]);s.lightCount++}}
   edges.sort((a,b)=>b[2]-a[2]);let cyc=0,forest=0;for(let [u,v,r] of edges)if(root(u)===root(v)){s.surplus+=r;s.surplusEdges++;cyc++}else{par[root(v)]=root(u);s.forest+=r;s.forestEdges++;forest++}
   let comps=new Set(ps.map((_,i)=>root(i))).size;s.components+=comps;check(forest===ps.length-comps&&cyc===edges.length-ps.length+comps);s.cycleSources+=+(cyc>0);
   for(let ls of s.local){for(let j=0;j<w.length;j+=ls.h)local(w.slice(j,j+ls.h),ls)}
  }
 }
 for(let s of stat){check(s.small+s.large===R);check(s.last+s.heavy+s.forest+s.surplus===s.large);check(s.forestEdges+s.surplusEdges===s.lightCount);check(s.lightCount-s.distinct+s.components===s.surplusEdges);check(s.last+s.forest<=B*s.distinct);for(let l of s.local){check(l.localR===s.large&&l.windows===l.short+(l.windows-l.short)&&l.short===l.forest+l.cyclic)}}
 return {X,B,J,T,R,events,literal,stat};
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(auditCycle(Number(a))));
