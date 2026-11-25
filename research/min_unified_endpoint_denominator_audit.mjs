// Endpoint-cohort denominator freezing and ideal gain-terminal rank census.
function audit(X,focus=false,scale=1,gainFactor=8,coarse=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(Math.floor(gainFactor*B),Math.floor(X/2)),H=T+B,Ps=[6,30,210],L=6,y=3,theta=scale*L*Math.max(2,Math.floor(Math.sqrt(B))),logTheta=Math.log(theta),bmin=3,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(v,m)=>{if(!v)throw Error(`${X}/${focus}: ${m}`)},eq=(a,b)=>Math.abs(a-b)<1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b, key=(a,b)=>Math.min(a,b)+"|"+Math.max(a,b);
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const tags=[],at=new Map(),slots=new Map(),costs=new Map(),weights=new Map();let events=0,hit=0;
 function cost(J,p){if(p<=y)return 0;let k=J+"|"+p;if(costs.has(k))return costs.get(k);let a=weights.get(J);if(!a){let ps=[...new Set([...fac(J),...fac(J+2)])].filter(q=>q>y),sum=ps.reduce((v,q)=>v+Math.log(q),0);a=new Map(ps.map(q=>[q,1/(2*ps.length)+Math.log(q)/(2*sum)]));ok(eq([...a.values()].reduce((v,w)=>v+w,0),ps.length?1:0),"probability mass");weights.set(J,a)}let pi=a.get(p);ok(pi>0,"actual reverse prime");let v=Math.log(L/pi);costs.set(k,v);return v}
 for(let M=X;M<2*X;M++)if(S[M]===M){let C=2*M-2,t=M+2,stop=Math.floor((7*M-1)/4),es=[],tag={M,id:tags.length,es,byC:new Map()};tags.push(tag);
  for(;;){let e={C,t,end:t,p:0,w:0,tag,i:es.length};es.push(e);tag.byC.set(C,e);let ar=at.get(C)||[];ar.push(e);at.set(C,ar);if(C-(2*M-2)>=T){hit++;break}
   let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;Object.assign(e,{p,w:v-t,v,r,J:C+p-1,end:v-1});let k=C+"|"+p+"|"+v,a=slots.get(k)||[];a.push(e);slots.set(k,a);events++;C=e.J;t=v;
  }
 }

 const m=Math.max(2,Math.floor(scale*Math.sqrt(B)/3)),eta=.25,verts=new Map(),all=[];
 let degree=1;
 function branch(e,t){return e.t<t?"w":e.i===0?"r":String(e.tag.es[e.i-1].p)}
 for(let [C,ar] of at){let times=[...new Set(ar.map(e=>e.t))];for(let t of times){let present=ar.filter(e=>e.t<=t&&t<=e.end),groups=new Map();for(let e of present){let k=branch(e,t),a=groups.get(k)||[];a.push(e);groups.set(k,a)}
  let n=present.length,ret=present.filter(e=>!e.p).length;degree=Math.max(degree,groups.size);let U={C,t,n,ret,present,groups,loads:Ps.map(()=>0)};verts.set(C+"|"+t,U);all.push(U);
 }}

 const large=2*m,byH=new Map(),edges=new Map();
 for(let U of all){U.key=U.C+"|"+U.t;let a=byH.get(U.C)||[];a.push(U);byH.set(U.C,a)}
 for(let a of byH.values())a.sort((x,y)=>x.t-y.t);
 let edgeChecks=0,flowChecks=0;
 for(let tag of tags){let seq=[];for(let e of tag.es)for(let U of byH.get(e.C))if(e.t<=U.t&&U.t<=e.end)seq.push(U);
  tag.seq=seq;tag.pos=new Map(seq.map((v,i)=>[v.key,i]));tag.firstBig=seq.find(v=>v.n>=large);
  for(let i=1;i<seq.length;i++){let U=seq[i-1],V=seq[i];ok(U.t<V.t,"time order");let k=U.key+"->"+V.key,e=edges.get(k)||{k,U,V,ids:new Set()};edges.set(k,e);e.ids.add(tag.id);seq[i-1].out=e;edgeChecks++}
 }
 for(let U of all){ok((U.out?U.out.ids.size:0)===U.n-U.ret,"compressed flow");flowChecks++}



 const s=coarse?large:Math.max(2,Math.floor(scale*Math.sqrt(B)/4)),h=Math.floor(.02*H)+.5,age=Math.floor(.03*H)+.5;
 const par=Int32Array.from(tags.map(t=>t.id)),mass=new Int32Array(tags.length).fill(1),growth=new Float64Array(tags.length),selected=new Int32Array(tags.length);
 function find(i){while(par[i]!==i){par[i]=par[par[i]];i=par[i]}return i}
 let logBudget=0,selectedBudget=0,historyChecks=0;
 for(let U of [...all].sort((a,b)=>a.t-b.t||a.C-b.C)){let branches=[...U.groups.entries()],ids=branches.map(([k,a])=>find(a[0].tag.id)),n=ids.reduce((v,x)=>v+mass[x],0);
  ok(new Set(ids).size===ids.length,"distinct historical branches");U.hist=new Map();U.histMass=n;
  for(let j=0;j<ids.length;j++){let [k,a]=branches[j],r=ids[j],v=Math.log(n/mass[r]);U.hist.set(k,mass[r]);for(let f of a){ok(find(f.tag.id)===r,"historical incoming");growth[f.tag.id]+=v;logBudget+=v;if(2*mass[r]<=n){selected[f.tag.id]++;selectedBudget+=v;}historyChecks++}}
  let r=ids[0];for(let x of ids.slice(1))par[x]=r;mass[r]=n;
 }
 ok(logBudget<=tags.length*Math.log(tags.length)+1e-6&&growth.every(x=>x<=Math.log(tags.length)+1e-8)&&selected.every(x=>x<=Math.log2(tags.length)+1e-8),"historical growth budgets");

 const D=Math.max(2,Math.floor(h/2)),xi=.25,b0=large,gate=Math.ceil((1-xi)*b0),cache=new Map();
 function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 function pairInterval(f,g){if(!f.tag.firstBig||!g.tag.firstBig)return null;let [u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),k1=branch(u,t),k2=branch(v,t);if(Math.max(U.groups.get(k1).length,U.groups.get(k2).length)<large)return null;
  let a0=eta*H*Math.log(U.histMass/Math.min(U.hist.get(k1),U.hist.get(k2)))/Math.log(tags.length);
  let lo=Math.max(f.tag.firstBig.C+h,g.tag.firstBig.C+h,U.C+age,U.C+Math.floor(a0)+.5),hi=Math.min(f.tag.es.at(-1).C-h,g.tag.es.at(-1).C-h);return lo<hi?[lo,hi]:null
 }
 function ent(n){return n?n*Math.log(n):0}
 let mergeEntropy=0,retireEntropy=0;for(let U of all){mergeEntropy+=ent(U.n)-[...U.groups.values()].reduce((v,a)=>v+ent(a.length),0);retireEntropy+=ent(U.n)-ent(U.n-U.ret)}
 ok(eq(mergeEntropy,retireEntropy)&&mergeEntropy<=tags.length*(Math.log(tags.length)+1)+1e-6,"entropy telescope");
 let ends=new Map(),endMap=new Map(),endMass=0;
 for(let a of slots.values()){let e=a[0];for(let k=Math.floor(e.C/D)+1;k*D<=e.J;k++){let end=k*D;if(end<=e.C)continue;let mp=endMap.get(k)||new Map();endMap.set(k,mp);let ar=ends.get(k)||[];ends.set(k,ar);let g={a,k,b:a.length};ar.push(g);endMass+=a.length;for(let f of a){ok(!mp.has(f.tag.id),"unique endpoint crossing");mp.set(f.tag.id,g)}}}
 let rows=Ps.map(P=>({P,old:0,frozenOnOld:0,endpoint:0,gr:0,ret:0,gateLoss:0,gridError:0,quadratureCap:0})),old=0,frozenOnOld=0,endpoint=0,gr=0,ret=0,gateLoss=0,positiveDiff=0,negativeDiff=0,slotPieces=0,endPairs=0,sourcePairs=0,gatePieces=0,idealArea=0,idealError=0,idealSlots=0,idealPairs=0;
 function count(P,l,r){return l<r?Math.max(0,Math.ceil(r/P)-Math.ceil(l/P)):0}
 for(let a of slots.values()){let b=a.length,e=a[0];
   let rr=a.filter(f=>f.tag.es.at(-1).C-f.tag.es[0].C>=T);
   if(rr.length){let bp=rr.length,cut=[e.C,e.J,...rr.map(f=>f.tag.es[0].C+T).filter(x=>x>e.C&&x<e.J)].sort((x,y)=>x-y);idealSlots++;
    for(let j=1;j<cut.length;j++){let l=cut[j-1],r=cut[j],K=(l+r)/2;if(l===r)continue;let rank=rr.filter(f=>f.tag.es[0].C+T>K).length,elig=rr.filter(f=>f.tag.es.at(-1).C-K>=B+1).length;ok(rank<=bp&&elig<=rank,"ideal rank subset");idealArea+=(r-l)*(bp-rank);if(rank){let q=elig*(elig-1),error=q/rank-q/bp;ok(error<=bp-rank+1e-7,"rank denominator error");idealError+=(r-l)*error;idealPairs+=q;}}
   }
   if(b<b0)continue;
   for(let k=Math.floor(e.C/D)+1;(k-1)*D<e.J;k++){let l=Math.max(e.C,(k-1)*D),r=Math.min(e.J,k*D);if(l>=r)continue;let mp=endMap.get(k),alive=a.filter(f=>mp?.has(f.tag.id)),n=alive.length,g=n?mp.get(alive[0].tag.id):null,bb=g?.b||0;ok(alive.every(f=>mp.get(f.tag.id)===g),"common endpoint cohort");ok(n<=bb&&n<=b,"survivor subset");slotPieces++;
    let gc=n?n*Math.log(bb/n):0,rc=b-n;gr+=(r-l)*gc;ret+=(r-l)*rc;let gated=bb<gate;if(gated)gatePieces++;
    for(let z of rows){let len=z.P*count(z.P,l,r);z.gr+=len*gc;z.ret+=len*rc}
    let A=0;for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let f=a[i],g=a[j],iv=pairInterval(f,g);if(!iv)continue;let x=Math.max(l,iv[0]),y=Math.min(r,iv[1]);if(x>=y)continue;ok(mp?.has(f.tag.id)&&mp?.has(g.tag.id)&&bb>=2,"pair survives slab");let w=2*(y-x);A+=w;sourcePairs++;old+=w/b;if(gated)gateLoss+=w/b;else frozenOnOld+=w/Math.max(b0,bb);
      for(let z of rows){let w=2*z.P*count(z.P,x,y);z.old+=w/b;if(gated)z.gateLoss+=w/b;else z.frozenOnOld+=w/Math.max(b0,bb)}
    }
    ok(A<=(r-l)*n*n+1e-7,"pair area cap");
    if(!gated){let diff=A/b-A/Math.max(b0,bb);positiveDiff+=Math.max(0,diff);negativeDiff+=Math.max(0,-diff);ok(diff<=(r-l)*gc+1e-7&&-diff<=(r-l)*rc+1e-7,"local denominator change")}
    else ok(A/b<=(r-l)*rc/xi+1e-7,"gate retirement");
   }
 }
 for(let [k,groups] of ends)for(let g of groups){let b=g.b;if(b<gate)continue;let l=(k-1)*D,r=k*D;
   for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let iv=pairInterval(g.a[i],g.a[j]);if(!iv)continue;let x=Math.max(l,iv[0]),y=Math.min(r,iv[1]);if(x>=y)continue;let w=2/Math.max(b0,b);endpoint+=w*(y-x);endPairs++;for(let z of rows)z.endpoint+=z.P*count(z.P,x,y)*w}
 }
 ok(idealArea<=tags.filter(t=>t.es.at(-1).C-t.es[0].C>=T).length*B+1e-7&&idealError<=idealArea+1e-7,"ideal overshoot budget");
 ok(endMass<=tags.length*(H/D+2)+1e-7&&gr<=D*mergeEntropy+1e-6&&ret<=D*tags.length+1e-6&&gateLoss<=ret/xi+1e-6&&positiveDiff<=gr+1e-6&&negativeDiff<=ret+1e-6&&frozenOnOld<=endpoint+1e-6&&old<=endpoint+gr+gateLoss+1e-6,"integrated endpoint bounds");
 for(let z of rows){let P=z.P;z.gridError=Math.abs(z.endpoint-endpoint);z.quadratureCap=P*endMass;ok(z.gr<=(D+P)*mergeEntropy+1e-6&&z.ret<=(D+P)*tags.length+1e-6&&z.gateLoss<=z.ret/xi+1e-6&&z.frozenOnOld<=z.endpoint+1e-6&&z.old<=z.endpoint+z.gr+z.gateLoss+1e-6&&z.gridError<=z.quadratureCap+1e-6,"grid endpoint bounds");for(let k of Object.keys(z))z[k]=+z[k].toFixed(6)}
 return {X,focus,scale,gainFactor,B,T,H,N:tags.length,events,hit,b0,gate,D,h,slotPieces,endPairs,sourcePairs,gatePieces,endMass,idealSlots,idealPairs,idealArea:+idealArea.toFixed(6),idealError:+idealError.toFixed(6),mergeEntropy:+mergeEntropy.toFixed(6),old:+old.toFixed(6),frozenOnOld:+frozenOnOld.toFixed(6),endpoint:+endpoint.toFixed(6),gr:+gr.toFixed(6),ret:+ret.toFixed(6),gateLoss:+gateLoss.toFixed(6),positiveDiff:+positiveDiff.toFixed(6),negativeDiff:+negativeDiff.toFixed(6),rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2,true)));
console.log(JSON.stringify(audit(65536,false,1,2,true)));
