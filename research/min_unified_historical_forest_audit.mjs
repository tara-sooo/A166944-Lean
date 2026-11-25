// Historical component forest with retired membership, unique fresh attachments, and two-key cut.
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

 all.sort((a,b)=>a.t-b.t||a.C-b.C);
 const parent=Int32Array.from(tags.map(t=>t.id)),mass=new Int32Array(tags.length).fill(1),members=tags.map(t=>[t.id]),maturity=new Int32Array(tags.length).fill(-1);
 function find(i){while(parent[i]!==i){parent[i]=parent[parent[i]];i=parent[i]}return i}
 let founders=0,founderMass=0,mergeExcess=0,merges=0,attach=0,attachLive=0,distinctChecks=0,liveChecks=0,firstChecks=0,componentChecks=0;
 for(let U of all){let branches=[...U.groups.values()],ids=branches.map(a=>find(a[0].tag.id));ok(new Set(ids).size===ids.length,"one live branch per historical component");
  let ns=ids.map(i=>mass[i]),n=ns.reduce((a,b)=>a+b,0),h=ns.filter(x=>x>=large).length;
  U.history=new Map();U.histMass=n;U.histHeavy=h;U.fresh=0;
  for(let j=0;j<branches.length;j++){let a=branches[j];ok(a.every(f=>find(f.tag.id)===ids[j])&&a.length<=ns[j],"actual subset historical");U.history.set(branch(a[0],U.t),ns[j]);distinctChecks+=a.length;}
  if(n>=large){if(!h){founders++;founderMass+=n;}else if(h>=2){merges++;mergeExcess+=h-1}
    for(let j=0;j<ids.length;j++)if(ns[j]<large){let id=ids[j];for(let k of members[id]){ok(maturity[k]===-1,"unique historical crossing");maturity[k]=U.t;tags[k].histKey=U;U.fresh++}
      if(h){attach+=ns[j];for(let f of branches[j]){ok(!f.tag.histAttach,"one historical attachment");f.tag.histAttach=U;attachLive++;}}
    }
  }
  let root=ids[0];for(let j=1;j<ids.length;j++){let id=ids[j];parent[id]=root;members[root].push(...members[id]);members[id]=[]}
  mass[root]=n;
  ok(members[root].length===n,"historical mass");componentChecks++;
  for(let f of U.present){if(n>=large&&!f.tag.firstHist)f.tag.firstHist=U;if(f.tag.firstHist){ok(f.tag.histKey===f.tag.firstHist,"live first historical threshold");firstChecks++}}
 }
 ok(founderMass<=tags.length&&founders*large<=founderMass&&mergeExcess<=founders&&attach+founderMass<=tags.length&&attachLive<=attach,"global forest accounting");
 const cache=new Map();function meet(a,b){let k=key(a.tag.id,b.tag.id),q=cache.get(k);if(q)return a.tag.id<b.tag.id?q:[q[1],q[0],q[2]];let x=a.tag.es,y=b.tag.es,i=0,j=0;while(i<x.length&&j<y.length){let u=x[i],v=y[j];if(u.C<v.C){i++;continue}if(v.C<u.C){j++;continue}let t=Math.max(u.t,v.t);if(t<=Math.min(u.end,v.end)){q=[u,v,t];cache.set(k,a.tag.id<b.tag.id?q:[v,u,t]);return q}i++;j++}throw Error("missing birth")}
 const rows=Ps.map(P=>({P,raw:0,bothPhysicalSmall:0,histMerge:0,histAttach:0,physicalAttach:0,extraAttach:0,histCut:0,physCut:0,jointCut:0,attachLife:0,thinMerge:0,thinCap:0})),mergeLoads=new Map();let pairChecks=0,sourceChecks=0,attachPairs=0,mergePairs=0,extraPairs=0;
 for(let a of slots.values()){let b=a.length;if(b<large)continue;let e=a[0],gp=new Map(),gh=new Map(),gj=new Map();for(let f of a){let p=f.tag.firstBig,h=f.tag.firstHist;ok(p&&h&&h.t<=p.t,"historical maturity no later");for(let [m,k] of [[gp,p.key],[gh,h.key],[gj,p.key+"#"+h.key]])m.set(k,(m.get(k)||0)+1);liveChecks++}
  let sq=m=>[...m.values()].reduce((s,x)=>s+x*x,0);let joint=b*b-sq(gp)-sq(gh)+sq(gj);ok(joint>=0,"intersection cut");
  for(let z of rows){let P=z.P,nk=Math.ceil(e.J/P)-Math.ceil(e.C/P);z.histCut+=P*nk*(b*b-sq(gh))/b;z.physCut+=P*nk*(b*b-sq(gp))/b;z.jointCut+=P*nk*joint/b}
  for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let f=a[i],g=a[j],[u,v,t]=meet(f,g),U=verts.get(u.C+"|"+t),k1=branch(u,t),k2=branch(v,t),x=U.groups.get(k1).length,y=U.groups.get(k2).length,h1=U.history.get(k1),h2=U.history.get(k2);let type="bothPhysicalSmall",extra=false;
   if(Math.max(x,y)>=large){ok(f.tag.firstBig!==g.tag.firstBig&&f.tag.firstHist!==g.tag.firstHist,"distinct two maturity keys");
    if(Math.min(h1,h2)>=large){type="histMerge";ok(U.histHeavy>=2,"historical merge");mergePairs++}
    else{type="histAttach";let z=h1<large?f:g;ok(z.tag.histAttach===U&&z.tag.firstHist===U,"unique historical attachment source");attachPairs++;extra=Math.min(x,y)>=m;if(extra)extraPairs++}
   }
   for(let jj=0;jj<rows.length;jj++){let z=rows[jj],P=z.P,nk=Math.ceil(e.J/P)-Math.ceil(e.C/P),w=2*P*nk/b;z.raw+=w;z[type]+=w;if(type==="histAttach"){if(extra)z.extraAttach+=w;else z.physicalAttach+=w}if(type==="histMerge"){let ar=mergeLoads.get(U)||Ps.map(()=>0);ar[jj]+=w;mergeLoads.set(U,ar)}}
   pairChecks++;
  }sourceChecks++;
 }
 for(let j=0;j<rows.length;j++){let z=rows[j],P=z.P;for(let t of tags)if(t.histAttach)z.attachLife+=2*(Math.max(0,t.es.at(-1).C-t.histAttach.C)+P);
  for(let ar of mergeLoads.values())if(ar[j]<=.25*H*large)z.thinMerge+=ar[j];z.thinCap=.25*H*large*merges;
  ok(eq(z.raw,z.bothPhysicalSmall+z.histMerge+z.histAttach)&&eq(z.histAttach,z.extraAttach+z.physicalAttach)&&z.histMerge+z.histAttach<=z.jointCut+1e-6&&z.jointCut<=Math.min(z.histCut,z.physCut)+1e-6&&z.histAttach<=z.attachLife+1e-6&&z.thinMerge<=z.thinCap+1e-6,"global capacities");for(let k of Object.keys(z))z[k]=+z[k].toFixed(6)}
 return {X,focus,scale,gainFactor,B,T,H,N:tags.length,events,hit,m,large,edgeChecks,flowChecks,founders,founderMass,mergeExcess,merges,attach,attachLive,distinctChecks,componentChecks,firstChecks,liveChecks,pairChecks,sourceChecks,attachPairs,mergePairs,extraPairs,rows}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));
for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
console.log(JSON.stringify(audit(65536,false,.5,2)));
console.log(JSON.stringify(audit(65536,false,1,2)));
