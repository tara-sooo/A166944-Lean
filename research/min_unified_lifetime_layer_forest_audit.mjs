// Lifetime-layer induced forest: founder, attachment and merge area budget.
function audit(X,focus=false,scale=1,gainFactor=8){
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


 const s=Math.max(2,Math.floor(scale*Math.sqrt(B)/4)),h=.02*H;
 const d=degree;
 let rows=Ps.map(P=>({P,eligible:0,founder:0,attach:0,mergeBudget:0,small:0,oldResidual:0,merge:0,attachment:0,smallShare:0,thinMerge:0,support:0,primeAgeChecks:0,activeLayers:0,pairChecks:0,forestChecks:0,keyChecks:0,newAttachment:0}));
 const cache=new Map();function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 for(let z of rows){let P=z.P,keys=new Map();
  for(let ar of slots.values()){let b=ar.length;if(b<large)continue;let e=ar[0];
   for(let K=P*Math.ceil(e.C/P);K<e.J;K+=P){let a=ar.filter(f=>f.tag.firstBig&&K>=f.tag.firstBig.C+h&&K<=f.tag.es.at(-1).C-h),n=a.length;if(!n)continue;
    z.eligible+=P*n;z.activeLayers++;let idset=new Set(a.map(f=>f.tag.id)),nodes=new Map();
    for(let f of a)for(let U of f.tag.seq){if(U.t>f.end)break;let g=nodes.get(U)||{U,counts:new Map()};nodes.set(U,g);let v=f.tag.byC.get(U.C);ok(v&&v.t<=U.t&&v.end>=U.t,"actual induced member");let k=branch(v,U.t);g.counts.set(k,(g.counts.get(k)||0)+1);}
    let A=0,S=0,J=0,ss=0,smallMembership=new Set();
    for(let g of nodes.values()){let U=g.U,ns=[...g.counts.values()],v=ns.reduce((a,b)=>a+b,0),k=ns.filter(x=>x>=s).length,sm=ns.filter(x=>x<s),t=sm.reduce((a,b)=>a+b,0);
     g.k=k;g.big=v-t;g.small=t;ss+=t*t-sm.reduce((a,b)=>a+b*b,0);
     if(!k&&v>=s)S+=v;
     if(k){A+=t;J+=k-1;for(let [label,n0] of g.counts)if(n0<s)for(let f of U.groups.get(label))if(idset.has(f.tag.id)){ok(!smallMembership.has(f.tag.id),"unique induced attachment");smallMembership.add(f.tag.id);}}
     if(k>=2){let g0=keys.get(U.key)||{support:0,load:0};keys.set(U.key,g0);g0.support+=P*(k-1);z.support+=P*(k-1);
       let old=[...U.groups.values()].map(a=>a.filter(f=>f.tag.es.at(-1).C>=K+h).length).filter(x=>x>=s).length;ok(old>=k,"terminal survival support");
       ok(U.C+H-h-K+1e-7>=4*(k*s-1),"prime origin spacing window");z.primeAgeChecks++}
     z.forestChecks++;
    }
    ok(A+S<=n&&s*J<=S&&A+s*J<=n&&ss<=2*d*s*n&&smallMembership.size===A,"layer founder budget");z.founder+=P*S;z.attach+=P*A;z.mergeBudget+=P*s*J;
    let loadSmall=0,loadAtt=0,loadMerge=0,loadThin=0;
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let f=a[i],g=a[j],[u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),k1=branch(u,t),k2=branch(v,t),x=U.groups.get(k1).length,y=U.groups.get(k2).length;if(Math.max(x,y)<large)continue;
      let v0=nodes.get(U),l=v0.counts.get(k1),r=v0.counts.get(k2),w=2*P/b;z.oldResidual+=w;z.pairChecks++;
      if(l<s&&r<s){loadSmall+=w;continue}
      if(l>=s&&r>=s){loadMerge+=w;ok(v0.k>=2,"merge layer support");keys.get(U.key).load+=w;continue}
      loadAtt+=w;let small=l<s?f:g;ok(smallMembership.has(small.tag.id),"actual induced attachment");if(Math.min(x,y)>=large)z.newAttachment+=w;if(v0.big<=eta*b)loadThin+=w;
    }
    ok(loadSmall<=P*ss/b+1e-7&&loadThin<=2*eta*P*A+1e-7&&loadAtt<=2*P*A+1e-7,"layer clock caps");
    z.small+=loadSmall;z.attachment+=loadAtt;z.merge+=loadMerge;z.smallShare+=loadThin;
   }
  }
  for(let g of keys.values()){if(g.load<=eta*s*g.support)z.thinMerge+=g.load;z.keyChecks++}
  ok(z.attach+z.mergeBudget<=z.eligible&&z.attach+z.founder<=z.eligible&&eq(z.mergeBudget,s*z.support)&&eq(z.oldResidual,z.small+z.merge+z.attachment)&&z.smallShare<=2*eta*z.attach+1e-6&&z.thinMerge<=eta*z.mergeBudget+1e-6,"global layer budget");for(let k of Object.keys(z))z[k]=+z[k].toFixed(6)
 }
 return {X,focus,scale,gainFactor,B,T,H,N:tags.length,events,hit,m,large,s,h,d,rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2)));
console.log(JSON.stringify(audit(65536,false,1,2)));
