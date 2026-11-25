// Hysteretic physical edge return, unique large attachment, and joint residence audit.
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
 const ret=new Map(),bad=new Set(),retired=new Map();let returnInc=0,retireChecks=0;
 for(let tag of tags){let witness=null;for(let U of tag.seq){if(U.n>=large)witness=U;if(witness&&U.out&&U.out.ids.has(tag.id)&&U.out.ids.size<m){let e=U.out,g=ret.get(e.k)||{e,witness,ids:new Set()};ret.set(e.k,g);g.ids.add(tag.id);returnInc++;bad.add(tag.id);witness=null}}}
 for(let g of ret.values()){let {e,witness}=g,loss=0;for(let f of witness.present){let tag=f.tag,idx=tag.pos.get(witness.key),z=null;for(let U of tag.seq.slice(idx)){if(U.out&&U.out.ids.has(tag.id)&&U.out.ids.size<m){z=U.out;break}}
   if(z){ok(z===e&&g.ids.has(tag.id),"shared first small edge")}else{ok(tag.seq.at(-1).t<=e.U.t,"retirement before edge");ok(!retired.has(tag.id),"disjoint retirement");retired.set(tag.id,e.k);loss++;retireChecks++}
  }ok(loss>=large-m+1&&g.ids.size<m,"loss lower bound");
 }
 ok(ret.size*(large-m+1)<=retired.size&&returnInc<=(m-1)*ret.size,"global small edge returns");
 let entries=0,entryChecks=0,seedAge=0,freshAge=0,freshGroups=new Map(),maxEntries=0;
 for(let U of all){let fresh=U.present.filter(e=>e.tag.firstBig===U);if(fresh.length){let ages=fresh.map(e=>U.C-e.tag.es[0].C).sort((a,b)=>a-b);ok(ages.every((x,i)=>x>=4*i),"fresh root spacing");freshAge+=ages.reduce((a,b)=>a+b,0);freshGroups.set(U,fresh.length);if(fresh.length===U.n)seedAge+=ages.reduce((a,b)=>a+b,0)}
  let masses=[...U.groups.values()].map(a=>a.length);if(!masses.some(a=>a>=large))continue;
  for(let a of U.groups.values())if(a.length<m)for(let f of a){if(bad.has(f.tag.id))continue;ok(f.tag.firstBig===U,"attachment is first large vertex");f.tag.entries=(f.tag.entries||0)+1;maxEntries=Math.max(maxEntries,f.tag.entries);ok(f.tag.entries===1,"unique attachment");entries++;entryChecks++}
 }
 const cache=new Map();function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 let rows=Ps.map(P=>({P,raw:0,small:0,bad:0,attachment:0,heavy:0,attachLinear:0,familyCap:0,attachCap:0,ageBound:0})),pairs=0,attachPairs=0,heavyPairs=0,sourceChecks=0;
 const age=.05*H;
 for(let a of slots.values()){let b=a.length;if(b<large)continue;let e=a[0],n=a.filter(x=>!bad.has(x.tag.id)).length,groups=new Map();for(let f of a)if(!bad.has(f.tag.id)){ok(f.tag.firstBig,"first big");let v=f.tag.firstBig;groups.set(v,(groups.get(v)||0)+1)}
  let attach=new Map();
  for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let f=a[i],g=a[j],type="bad";if(!bad.has(f.tag.id)&&!bad.has(g.tag.id)){let [u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),x=U.groups.get(branch(u,t)).length,y=U.groups.get(branch(v,t)).length;
    if(Math.max(x,y)<large)type="small";else {ok(f.tag.firstBig!==g.tag.firstBig,"distinct first large families");if(Math.min(x,y)<m){type="attachment";let z=x<m?f:g;ok(z.tag.firstBig===U&&z.tag.entries===1,"unique source attachment");let c=attach.get(z)||0;attach.set(z,c+1);attachPairs++;}else{type="heavy";heavyPairs++;}}}
   for(let z of rows){let P=z.P,nk=Math.ceil(e.J/P)-Math.ceil(e.C/P),w=2*P*nk/b;z.raw+=w;z[type]+=w}pairs++;
  }
  for(let z of rows){let P=z.P,nk=Math.ceil(e.J/P)-Math.ceil(e.C/P);z.familyCap+=P*nk*(n*n-[...groups.values()].reduce((s,x)=>s+x*x,0))/b;z.attachCap+=2*P*nk*[...attach.values()].reduce((s,x)=>s+x,0)/b;z.attachLinear+=2*P*nk*attach.size}
  sourceChecks++;
 }
 for(let z of rows){let P=z.P;for(let tag of tags)if(tag.entries)z.ageBound+=2*(Math.max(0,tag.es.at(-1).C-tag.firstBig.C)+P);
  ok(eq(z.raw,z.bad+z.small+z.attachment+z.heavy)&&eq(z.attachment,z.attachCap)&&z.attachment<=z.attachLinear+1e-6&&z.attachLinear<=z.ageBound+1e-6&&z.attachment+z.heavy<=z.familyCap+1e-6,"global bounds");for(let k of Object.keys(z))z[k]=+z[k].toFixed(6)}
 return {X,focus,scale,gainFactor,B,T,H,N:tags.length,events,hit,m,large,edgeChecks,flowChecks,returnKeys:ret.size,returnInc,bad:bad.size,retired:retired.size,retireChecks,entries,entryChecks,maxEntries,freshGroups:freshGroups.size,freshAge,seedAge,pairs,attachPairs,heavyPairs,sourceChecks,rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2)));
console.log(JSON.stringify(audit(65536,false,1,2)));
