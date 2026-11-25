// Continuous joint lifetime cut, exact grid quadrature and bounded variation.
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
 const cache=new Map(),delta=new Map(),deltaRaw=new Map(),staticPairs=new Set();
 function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 function add(m,x,w){m.set(x,(m.get(x)||0)+w)}
 let pieces=0,pairs=0,slotCount=0,thresholdChecks=0,integral=0,integralRaw=0,insertChecks=0,maxInsert=0,primeAgeChecks=0;
 let rows=Ps.map(P=>({P,grid:0,rawGrid:0,sweep:0,rawSweep:0,err:0,bound:0}));
 function census(a,b,fullPairs,K){
   let ids=new Set(a.map(f=>f.tag.id)),nodes=new Map();
   for(let f of a)for(let U of f.tag.seq){if(U.t>f.end)break;let g=nodes.get(U)||new Map();nodes.set(U,g);let v=f.tag.byC.get(U.C);let k=branch(v,U.t);g.set(k,(g.get(k)||0)+1)}
   let val=0,raw=0;for(let q of fullPairs){if(!ids.has(q.i)||!ids.has(q.j))continue;let g=nodes.get(q.U),x=g.get(q.k1),y=g.get(q.k2);if(Math.max(x,y)<s)continue;raw+=2;if(q.allowed&&K>=q.lo)val+=2;}
   let sm=0;for(let g of nodes.values()){let a=[...g.values()].filter(x=>x<s);sm+=a.reduce((v,x)=>v+x,0)**2-a.reduce((v,x)=>v+x*x,0)}
   ok(raw===a.length*(a.length-1)-sm,"raw induced count");return {val,raw};
 }
 for(let ar of slots.values()){let b=ar.length;if(b<large)continue;slotCount++;let e=ar[0],cuts=new Set([e.C,e.J]),a=ar.filter(f=>f.tag.firstBig),fullPairs=[];
   for(let f of a){let lo=f.tag.firstBig.C+h,hi=f.tag.es.at(-1).C-h;for(let k of [lo,hi])if(k>e.C&&k<e.J)cuts.add(k)}
   for(let i=0;i<a.length;i++)for(let j=i+1;j<a.length;j++){let f=a[i],g=a[j],[u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),k1=branch(u,t),k2=branch(v,t),x=U.groups.get(k1).length,y=U.groups.get(k2).length,allowed=Math.max(x,y)>=large,lo=U.C+age;if(allowed){staticPairs.add(key(f.tag.id,g.tag.id));if(lo>e.C&&lo<e.J)cuts.add(lo)}fullPairs.push({i:f.tag.id,j:g.tag.id,U,k1,k2,allowed,lo});pairs++}
   let times=[...cuts].sort((a,b)=>a-b);
   for(let i=1;i<times.length;i++){let l=times[i-1],r=times[i],K=(l+r)/2,eligible=a.filter(f=>K>=f.tag.firstBig.C+h&&K<f.tag.es.at(-1).C-h);
    let {val,raw}=census(eligible,b,fullPairs,K);ok(val<=raw,"joint cut");thresholdChecks++;
    // Independently check the single-member change bound on the raw induced count.
    if(eligible.length){let other=eligible.slice(0,-1),r0=census(other,b,fullPairs,K).raw,change=Math.abs(raw-r0);ok(change<=2*b+2*degree*s*s,"leaf update bound");maxInsert=Math.max(maxInsert,change);insertChecks++}
    let w=val/b,v=raw/b;add(delta,l,w);add(delta,r,-w);add(deltaRaw,l,v);add(deltaRaw,r,-v);integral+=(r-l)*w;integralRaw+=(r-l)*v;pieces++;
    for(let z of rows){let n=Math.ceil(r/z.P)-Math.ceil(l/z.P);z.grid+=z.P*n*w;z.rawGrid+=z.P*n*v}
   }
 }
 function sweep(m,which){let xs=[...m.keys()].sort((a,b)=>a-b),tv=0,area=0,f=0,last=xs[0]||0;
  for(let x of xs){let l=last,r=x;if(r>l){area+=(r-l)*f;for(let z of rows)z[which]+=z.P*(Math.ceil(r/z.P)-Math.ceil(l/z.P))*f}
   let d=m.get(x);tv+=Math.abs(d);f+=d;ok(f>=-1e-6,"nonnegative global cut");last=x;
  }ok(Math.abs(f)<1e-6,"finite support");return {tv,area,keys:xs.length}}
 let sv=sweep(delta,"sweep"),sr=sweep(deltaRaw,"rawSweep");ok(eq(sv.area,integral)&&eq(sr.area,integralRaw)&&integral<=integralRaw+1e-6,"integral identity");
 // Loose absolute theorem constant; includes threshold crossing, historical merges and pair activations.
 let theoretical=32*tags.length*(large+Math.log2(2+tags.length)+1+degree*s*s/large)+8*staticPairs.size/large;
 ok(sv.tv<=theoretical+1e-6&&sr.tv<=theoretical+1e-6,"global variation bound");
 for(let z of rows){ok(eq(z.grid,z.sweep)&&eq(z.rawGrid,z.rawSweep),"independent grid sum");z.err=Math.abs(z.grid-integral);z.bound=z.P*sv.tv;ok(z.err<=z.bound+1e-6&&Math.abs(z.rawGrid-integralRaw)<=z.P*sr.tv+1e-6,"quadrature");for(let k of Object.keys(z))z[k]=+z[k].toFixed(6)}
 return {X,focus,scale,gainFactor,coarse,B,T,H,N:tags.length,events,hit,m,large,s,h,age,d:degree,pieces,pairs,slotCount,thresholdChecks,insertChecks,maxInsert,staticPairs:staticPairs.size,integral:+integral.toFixed(6),integralRaw:+integralRaw.toFixed(6),tv:+sv.tv.toFixed(6),rawTV:+sr.tv.toFixed(6),breakpoints:sv.keys,theoretical:+theoretical.toFixed(6),rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2,true)));
console.log(JSON.stringify(audit(65536,false,1,2,true)));
