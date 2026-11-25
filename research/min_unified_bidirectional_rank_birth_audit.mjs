// Two-sided root rank growth age and branch census at endpoint snapshots.
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

 const par=Int32Array.from(tags.map(t=>t.id)),members=tags.map(t=>[t.id]),g0=new Float64Array(tags.length),g1=new Float64Array(tags.length),g2=new Float64Array(tags.length),ageCount=new Int32Array(tags.length);
 function find(i){while(par[i]!==i){par[i]=par[par[i]];i=par[i]}return i}
 const aScale=eta*H/Math.log(tags.length),D=Math.max(2,Math.floor(h/2)),rho=.25,b0=large;
 let checks=0,strictAge=0,ageBudget=0,largeAgeBudget=0,incidences=0;
 function rank(a,id){let l=0,r=a.length;while(l<r){let k=(l+r)>>1;if(a[k]<id)l=k+1;else r=k}ok(a[l]===id,"root member");return [l+1,a.length-l]}
 for(let U of [...all].sort((a,b)=>a.t-b.t||a.C-b.C)){let branches=[...U.groups.entries()],ids=branches.map(([k,a])=>find(a[0].tag.id)),allIds=ids.flatMap(i=>members[i]).sort((a,b)=>a-b);ok(new Set(ids).size===ids.length,"distinct historical components");U.histMass=allIds.length;U.hist=new Map();U.ages=new Map();
  for(let j=0;j<ids.length;j++){let [k,a]=branches[j],old=members[ids[j]],z=Math.log(allIds.length/old.length);U.hist.set(k,old.length);
   for(let f of a){let i=f.tag.id,[p0,s0]=rank(old,i),[p1,s1]=rank(allIds,i),l=Math.log(p1/p0),r=Math.log(s1/s0),tot=z+l+r;ok(l>=-1e-12&&r>=-1e-12,"rank monotonicity");g0[i]+=z;g1[i]+=l;g2[i]+=r;let A=aScale*tot;U.ages.set(i,{A,old:aScale*z,pre:p1,suf:s1});ageBudget+=A;if(A>aScale*Math.log(2)){ageCount[i]++;largeAgeBudget+=A;incidences++}if(l+r>1e-12)strictAge++;checks++}
  }
  let r=ids[0];for(let id of ids.slice(1))par[id]=r;members[r]=allIds;
 }
 ok([g0,g1,g2].every(a=>a.every(x=>x<=Math.log(tags.length)+1e-8))&&ageBudget<=3*eta*H*tags.length+1e-6&&ageCount.every(x=>x<=3*Math.log2(tags.length)+1e-8),"three logarithmic budgets");
 const cache=new Map();
 function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 let old=0,newAge=0,trim=0,rankTrim=0,branchSum=0,rankSum=0,endpointGroups=0,pairChecks=0,branchChecks=0,rankChecks=0,prefixChecks=0,spacingChecks=0,youngChecks=0,rankBudget=0,endpointArea=0,rankAllowed=0;
 let rows=Ps.map(P=>({P,old:0,newAge:0,rank:0,branch:0,rankBranch:0,agePaid:0,rankPaid:0,ageCap:0,rankCap:0}));
 function count(P,l,r){return l<r?Math.max(0,Math.ceil(r/P)-Math.ceil(l/P)):0}
 for(let a of slots.values()){let e0=a[0],q=a.length;if(q<b0)continue;
  for(let k=Math.floor(e0.C/D)+1;k*D<=e0.J;k++){let e=k*D,l=e-D;if(e<=e0.C)continue;endpointGroups++;endpointArea+=D*q;
   let arr=a.filter(f=>f.tag.firstBig).sort((a,b)=>a.tag.id-b.tag.id),fullIds=a.map(f=>f.tag.id).sort((a,b)=>a-b),nodes=new Map(),ps=[];
   for(let f of arr)for(let U of f.tag.seq){if(U.t>f.end)break;let g=nodes.get(U)||new Map();nodes.set(U,g);let v=f.tag.byC.get(U.C),key0=branch(v,U.t),ar=g.get(key0)||[];g.set(key0,ar);ar.push(f)}
   let endpoints=new Set([l,e]);
   function interval(f,U,oldAge=false){let A=U.ages.get(f.tag.id);ok(A,"birth age member");let lo=Math.max(l,f.tag.firstBig.C+h,U.C+age,U.C+Math.floor(oldAge?A.old:A.A)+.5),hi=Math.min(e,f.tag.es.at(-1).C-h);return [lo,hi]}
   for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length;j++){let f=arr[i],g=arr[j],[u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),k1=branch(u,t),k2=branch(v,t);if(Math.max(U.groups.get(k1).length,U.groups.get(k2).length)<large)continue;pairChecks++;
    let [x,y]=interval(f,U),[z,w]=interval(g,U),[x0,y0]=interval(f,U,true),[z0,w0]=interval(g,U,true),lo=Math.max(x,z),hi=Math.min(y,w),lo0=Math.max(x0,z0),hi0=Math.min(y0,w0);let len=Math.max(0,hi-lo),len0=Math.max(0,hi0-lo0);ok(len<=len0+1e-7,"age nesting");
    let tail=rank(fullIds,f.tag.id)[1],birth=U.ages.get(f.tag.id).suf; // historical rank may include retired members
    let prefix=U.ages.get(g.tag.id).pre,pass=birth>=rho*q&&prefix>=rho*q;if(pass&&len>0){ok(U.C-f.tag.es[0].C>=4*(birth-1),'birth suffix root spacing');spacingChecks++;}old+=2*len0/q;newAge+=2*len/q;if(!pass)rankTrim+=2*len/q;if(pass)rankAllowed+=2*len/q;
    if(len0>len)youngChecks++;for(let a0 of [lo,hi])if(l<a0&&a0<e)endpoints.add(a0);ps.push({f,g,U,k1,k2,lo,hi,pass,sufPass:birth>=rho*q,prePass:prefix>=rho*q});
    for(let row of rows){let v0=2*row.P*count(row.P,lo0,hi0)/q,v1=2*row.P*count(row.P,lo,hi)/q;row.old+=v0;row.newAge+=v1;row.agePaid+=v0-v1;if(pass)row.rank+=v1;else row.rankPaid+=v1}
   }
   // For each older root the rank-cut partners occur in a nested historical tail set.
   let cut=new Map(),preCut=new Map();for(let p of ps)if(!p.pass){let map=p.sufPass?preCut:cut,id=p.sufPass?p.g.tag.id:p.f.tag.id,ar=map.get(id)||[];ar.push(p);map.set(id,ar)}
   for(let ar of cut.values()){ok(ar.length<=rho*q+1e-7,"suffix rank-cut distinct partners");rankChecks++}
   for(let ar of preCut.values()){ok(ar.length<=rho*q+1e-7,"prefix rank-cut distinct partners");prefixChecks++}
   rankBudget+=4*D*rho*q;for(let row of rows)row.rankCap+=4*row.P*count(row.P,l,e)*rho*q;
   // Direct branch-wise piecewise census, with no pair enumeration in the census itself.
   for(let [U,branches] of nodes){if(branches.size<2)continue;
    let cuts=new Set([l,e]),g=[];
    for(let [key0,ar] of branches){let v=[];for(let f of ar){let [lo,hi]=interval(f,U);if(lo>=hi)continue;cuts.add(lo);cuts.add(hi);v.push({id:f.tag.id,lo,hi,birth:U.ages.get(f.tag.id).suf,pre:U.ages.get(f.tag.id).pre})}g.push({key:key0,large:U.groups.get(key0).length>=large,v})}
    let xs=[...cuts].sort((a,b)=>a-b);
    for(let i=1;i<xs.length;i++){let x=xs[i-1],y=xs[i],K=(x+y)/2,groups=g.map(g0=>({...g0,v:g0.v.filter(z=>z.lo<=K&&K<z.hi)})),n=groups.reduce((v,g)=>v+g.v.length,0),small=groups.filter(g=>!g.large),sm=small.reduce((v,g)=>v+g.v.length,0),c=n*n-groups.reduce((v,g)=>v+g.v.length**2,0)-sm*sm+small.reduce((v,g)=>v+g.v.length**2,0);
     let cR=0;for(let g of groups)for(let v of g.v){if(v.birth<rho*q)continue;for(let other of groups)if(other.key!==g.key&&(other.large||g.large))cR+=2*other.v.filter(w=>w.id>v.id&&w.pre>=rho*q).length}
     ok(cR<=c&&c>=0,"branch census");branchSum+=(y-x)*c/q;rankSum+=(y-x)*cR/q;branchChecks++;
     for(let row of rows){let len=row.P*count(row.P,x,y);row.branch+=len*c/q;row.rankBranch+=len*cR/q}
    }
   }
  }
 }
 ok(eq(branchSum,newAge)&&eq(rankSum,rankAllowed)&&eq(newAge,rankAllowed+rankTrim)&&rankTrim<=rankBudget+1e-6,"aggregate branch identity");
 // Endpoint grid role capacity at each actual membership, no interior source tracking.
 for(let row of rows){row.ageCap=2*(largeAgeBudget+(row.P+1)*incidences);ok(eq(row.newAge,row.branch)&&eq(row.rank,row.rankBranch)&&eq(row.old,row.newAge+row.agePaid)&&row.rankPaid<=row.rankCap+1e-6&&row.agePaid<=row.ageCap+1e-6,"grid and payments");for(let k of Object.keys(row))row[k]=+row[k].toFixed(6)}
 return {X,focus,scale,gainFactor,B,T,H,N:tags.length,events,hit,b0,D,checks,strictAge,ageBudget:+ageBudget.toFixed(6),largeAgeBudget:+largeAgeBudget.toFixed(6),incidences,endpointGroups,endpointArea,pairChecks,branchChecks,rankChecks,prefixChecks,spacingChecks,youngChecks,old:+old.toFixed(6),newAge:+newAge.toFixed(6),rankTrim:+rankTrim.toFixed(6),rankAllowed:+rankAllowed.toFixed(6),rankBudget:+rankBudget.toFixed(6),rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2,true)));
console.log(JSON.stringify(audit(65536,false,1,2,true)));
