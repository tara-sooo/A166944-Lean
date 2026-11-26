// Local paired witnesses, weighted phase-bin coupling and actual first-defect checks.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,near=(a,b)=>Math.abs(a-b)<=1e-6*Math.max(1,Math.abs(a),Math.abs(b));
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1),pr=[];for(let p=2;p<=lim;p++)if(!spf[p]){pr.push(p);for(let j=p;j<=lim;j+=p)spf[j]=p}
 let odd=pr.filter(p=>p>2),res=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),M=2*Math.max(8,Math.floor(B/8)),L=4*M,tags=[],slots=new Map(),events=0;
  for(let r=X|1;r<2*X;r+=2)if(spf[r]===r){let id=tags.length,C0=2*r-2,C=C0,t=r+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let z=mod((I?f+2:0)-t,2*f)||2*f;if(z<w||z===w&&f<p){p=f;w=z}}}if(!p)break;
    let g=p-1,J=C+g,n=t+w,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;
    if(!slots.has(key))slots.set(key,{key,C,p,n,ids:[],next:null});let s=slots.get(key);s.ids.push(id);ok(d>=0&&dp>=0&&w<=3*g,"MIN");path.push({C,J,p,w,g,d,dp,s});C=J;t=n;events++;
   }tags.push({id,F:C,path})
  }
  for(let t of tags)for(let j=0;j+1<t.path.length;j++){let a=t.path[j].s,b=t.path[j+1].s;ok(!a.next||a.next===b,"unique successor");a.next=b}
  let vmap=new Map(),variation=0;
  for(let s of slots.values())if(s.next){let b=s.next,ids=new Set(b.ids),r=s.ids.filter(i=>ids.has(i)).length,v=Math.log(s.ids.length/r)+Math.log(b.ids.length/r);vmap.set(s.key,v);variation+=r*v}
  ok(variation<=tags.length*(Math.log(tags.length)+2)+1e-6,"variation");
  for(let {S,R,V,A} of [{S:3,R:5,V:9,A:17},{S:5,R:7,V:25,A:37}]){
   let small=odd.filter(p=>p<=S),middle=odd.filter(p=>S<p&&p<=R),extra=odd.filter(p=>R<p&&p<=V),PS=small.reduce((a,b)=>a*b,1),P=middle.reduce((a,b)=>a*b,PS),lambda=Math.ceil(P**(4/11)),alpha=middle.reduce((a,p)=>a*(p-1)/(2*p),1/PS),Q=extra.reduce((a,p)=>a*(1-2/p),1),max=4*X+T+B+M+2*lambda;
   let raw=new Uint32Array(Math.ceil(max/2)+1);
   for(let j=0;j<raw.length-1;j++){let J=2*j;raw[j+1]=raw[j]+Number(j%PS===0&&middle.every(p=>mod(J,p)%2===0&&mod(J,p)<=p-3)&&extra.every(p=>mod(J,p)!==1&&mod(J,p)!==p-1))}
   const cnt=(a,b)=>raw[b/2]-raw[a/2],smooth=j=>(raw[j+lambda]-raw[j])/(alpha*lambda),mass=(a,b)=>2*cnt(a,b)/(alpha*Q);
   let sources=0,persistent=0,tiles=0,clockRich=0,large=0,short=0,unclassified=0,moderateRich=0,nonmoderateRich=0,innerOuter=0,localProducts=0,matchedProducts=0,phaseChecks=0,multiPhase=0,maxPhase=0,stable=0,unstable=0,sourceMass=0,transport=0,largeMass=0,shortMass=0,maxJointCap=0,maxCutCap=0,maxTickCap=0,offsetTwin=0,cheap=0,phaseMaps=new Map(),joint=new Map(),roles=new Map(),cutRoles=new Map(),tickRoles=new Map();
   const add=(m,k,v)=>{let z=(m.get(k)||0)+v;m.set(k,z);return z};
   function checkUnion(es){
    let G=es.reduce((a,e)=>a+e.g,0),m=es.length,K=es.reduce((a,e)=>a+mass(e.C,e.J),0),inner=new Set(),outer=new Set();
    for(let e of es){for(let j=e.C/2;j+lambda<=e.J/2;j++)inner.add(j);for(let j=e.C/2-lambda+1;j<e.J/2;j++)outer.add(j)}
    let s1=[...inner].reduce((a,j)=>a+smooth(j),0)*2/Q,s2=[...outer].reduce((a,j)=>a+smooth(j),0)*2/Q;
    let err=2/Q*[...new Set([...inner,...outer])].reduce((a,j)=>a+Math.abs(smooth(j)-Q),0);
    ok(s1<=K+1e-6&&K<=s2+1e-6,"inner outer");ok(K>=G-2*(lambda-1)*m-err-1e-6&&K<=G+2*(lambda-1)*m+err+1e-6,"two-sided bound");innerOuter++;
   }
   for(let s of slots.values()){
    if(s.ids.length<2)continue;let rows=s.ids.slice(0,5).map(id=>({id,i:tags[id].path.findIndex(e=>e.s===s)})).filter(r=>{let e=tags[r.id].path[r.i];return e.dp>e.d&&tags[r.id].F>=e.J+L});if(rows.length<2)continue;sources++;
    let t=tags[rows[0].id],first=t.path[rows[0].i],a=first.J,b=a+L,block=t.path.slice(rows[0].i+1).filter(e=>e.J<=b);
    if(!block.length||block.some(e=>e.d<first.dp||e.dp<first.dp))continue;
    let end=block.at(-1).J;rows=rows.filter(r=>tags[r.id].F>=end);if(rows.length<2)continue;persistent++;
    let prefix=new Map(),v=0,prev=s;for(let e of block){v+=vmap.get(prev.key);prefix.set(e.s.key,v);prev=e.s}
    let cand=[];
    for(let l=Math.ceil(a/M)*M;l+M<=end;l+=M){
     let es=block.filter(e=>l<=e.C&&e.J<=l+M);if(!es.length)continue;tiles++;let G=es.reduce((a,e)=>a+e.g,0),W=es.reduce((a,e)=>a+e.w,0);ok(G<=M,"tile gain");if(G<M/4||W<G/4)continue;clockRich++;
     let big=es.filter(e=>e.p>A),F=big.reduce((a,e)=>a+e.g,0);checkUnion(es);checkUnion(big);
     if(F*24>=23*G){let ex=big.filter(e=>16*e.w>=e.g),Wex=ex.reduce((a,e)=>a+e.w,0);ok(Wex>=G/16-1e-6,"large expensive");large++;cand.push({type:"h",l,ex,Wex});continue}
     let cut=[];for(let e of es.filter(e=>e.p<=A))for(let J=e.C;J<e.J;J+=2)if(cnt(J,J+2)){ok(e.p>R,"cut barrier");cut.push({J,e});if(e.p<=V){ok(J>e.C,"anchor");let rough=small.every(p=>mod(e.C,p)!==1&&mod(e.C,p)!==p-1);if(rough){let f=J-e.C;ok(spf[f-1]===f-1&&spf[f+1]===f+1&&f-1>S,"twins");offsetTwin++}else{ok(e.w<=2*S,"cheap");cheap++}}}
     let ex=es.filter(e=>8*e.w>=e.g),Wex=ex.reduce((a,e)=>a+e.w,0);ok(Wex>=G/8-1e-6,"short expensive");
     if(cut.length<alpha*Q*G/256||!cut.length){unclassified++;continue}
     let cm=cut.filter(z=>z.e.p<=V),type=2*cm.length>=cut.length?"m":"s";cut=type==="m"?cm:cut.filter(z=>z.e.p>V);ok(cut.length>0,"subtype");short++;if(type==="m")moderateRich++;else nonmoderateRich++;cand.push({type,l,ex,Wex,cut});
    }
    if(!cand.length)continue;
    for(let i of rows)for(let j of rows)if(i.id!==j.id){let weight=1/s.ids.length;sourceMass+=weight;
     for(let c of cand){let w0=weight/cand.length;
      if(c.type==="h"){largeMass+=w0;transport+=w0;continue}
      shortMass+=w0;
      for(let z of c.cut)for(let f of c.ex){let w=w0/c.cut.length*f.w/c.Wex;transport+=w;localProducts++;
       ok(z.e.s.ids.includes(i.id)&&z.e.s.ids.includes(j.id)&&f.s.ids.includes(i.id)&&f.s.ids.includes(j.id),"same pair");ok(c.l<=z.e.C&&z.e.J<=c.l+M&&c.l<=f.C&&f.J<=c.l+M,"same tile");
       if(Math.max(prefix.get(z.e.s.key),prefix.get(f.s.key))>.2){unstable+=w;continue}
       stable+=w;matchedProducts++;
       let E=z.e.C<=f.C?z.e.s:f.s,F=z.e.C<=f.C?f.s:z.e.s,inter=E.ids.filter(id=>F.ids.includes(id)).length;ok(inter>F.ids.length/2&&inter>E.ids.length/2,"majority");
       let key=z.J+"/"+z.e.C+"/"+z.e.p+"/"+f.C+"/"+f.p;let map=phaseMaps.get(key);if(!map){map={forward:new Map(),back:new Map(),weights:new Map()};phaseMaps.set(key,map)}
       ok(!map.forward.has(E.key)||map.forward.get(E.key)===F.key,"forward phase");ok(!map.back.has(F.key)||map.back.get(F.key)===E.key,"reverse phase");map.forward.set(E.key,F.key);map.back.set(F.key,E.key);add(map.weights,E.key,w);phaseChecks++;
       let phys=z.e.s.key+"/"+f.s.key+"/"+z.J,pk=key+"/"+i.id,cap=add(roles,pk,w);maxJointCap=Math.max(maxJointCap,cap*alpha*M/f.p);maxCutCap=Math.max(maxCutCap,add(cutRoles,z.J+"/"+i.id,w)*alpha);maxTickCap=Math.max(maxTickCap,add(tickRoles,f.s.key+"/"+i.id,w)/f.p);
       add(joint,key+"/"+phys,w)
      }
     }
    }
   }
   for(let m of phaseMaps.values()){ok(m.forward.size===m.back.size,"bijection");maxPhase=Math.max(maxPhase,m.forward.size);if(m.forward.size>1)multiPhase++}
   let phasePairs=0,actualDefects=0,persistentPairs=0,longGap=0,shortDefects=0,wheelDefects=0,binControls=0,binMass=0,smallPhaseMass=0,samePhaseMass=0,auxMass=0,auxDefectMass=0,auxChecks=0;
   let Delta=Math.max(4,Math.floor(M/2)),wheel=6;
   function strand(E,F){let e=slots.get(E),f=slots.get(F),id=e.ids.find(i=>f.ids.includes(i));ok(id!==undefined,"actual shared strand");let path=tags[id].path,a=path.findIndex(z=>z.s.key===E),b=path.findIndex(z=>z.s.key===F);ok(a>=0&&b>=a,"strand order");return {id,path:path.slice(a+1,b+1),E:e,F:f}}
   function compare(a,b){let lag=b.E.n-a.E.n,abs=Math.abs(lag),end=a.F.C+a.F.p-1,start=a.E.C+a.E.p-1,G=end-start;
    ok(lag!==0&&lag%(2*a.E.p)===0&&a.E.C===b.E.C&&a.F.C===b.F.C,"distinct projected phases");
    let i=0,def=null;
    while(i<a.path.length&&i<b.path.length){let x=a.path[i],y=b.path[i];ok(x.C===y.C,"shared prehorizon until defect");
     if(x.p!==y.p||x.w!==y.w){ok(lag%(2*x.p)!==0||lag%(2*y.p)!==0,"two-way MIN nonperiodic defect");let z=lag%(2*x.p)!==0?x:y;def={C:z.C,p:z.p};ok(z.C-start<abs,"first defect before lag length");break}
     ok(y.s.n-x.s.n===lag&&lag%(2*x.p)===0,"translated edge");
     let K=Math.ceil(x.C/abs)*abs;ok(K>=x.J,"strict lag barrier");i++;
    }
    if(!def){ok(i===a.path.length&&i===b.path.length,"complete shared projection");ok(G<abs,"persistent gain below lag");}
    return {lag,G,def}
   }
   for(let map of phaseMaps.values()){
    let es=[...map.forward.keys()],strands=new Map(es.map(E=>[E,strand(E,map.forward.get(E))])),comparisons=new Map();
    for(let i=0;i<es.length;i++)for(let j=i+1;j<es.length;j++){let a=es[i],b=es[j],v=compare(strands.get(a),strands.get(b));phasePairs++;comparisons.set(a+"|"+b,v);comparisons.set(b+"|"+a,v);
     if(v.def){actualDefects++;if(v.lag%wheel===0){ok(wheel%v.def.p!==0,"wheel exclusion");wheelDefects++}if(v.def.C-(strands.get(a).E.C+strands.get(a).E.p-1)<Math.abs(v.lag))shortDefects++}
     else persistentPairs++;
     if(v.G>=Math.abs(v.lag)){longGap++;ok(v.def,"forced defect")}
    }
    // Finite bins by departure time and wheel, with a deliberately relaxed small-phase threshold.
    let bins=new Map();for(let E of es){let a=strands.get(E),k=Math.floor(a.E.n/Delta)+"/"+mod(a.E.n,wheel);if(!bins.has(k))bins.set(k,[]);bins.get(k).push(E)}
    for(let bin of bins.values()){if(bin.length<2)continue;let total=bin.reduce((a,E)=>a+map.weights.get(E),0);binControls++;binMass+=total;
     let expectedAux=new Map();for(let E of bin){let w=map.weights.get(E);if(w>0.75*total)continue;smallPhaseMass+=w;
      for(let F of bin){let v=w*map.weights.get(F)/total;auxMass+=v;add(expectedAux,F,v);auxChecks++;if(E===F){samePhaseMass+=v;continue}
       let c=comparisons.get(E+"|"+F);ok(c&&Math.abs(c.lag)<Delta&&c.lag%wheel===0,"same-bin lag");if(c.G>=Delta){ok(c.def,"bin forced defect");auxDefectMass+=v}
      }
     }
     for(let [E,w] of expectedAux)ok(w<=map.weights.get(E)+1e-9,"auxiliary marginal domination")
    }
   }
   ok(near(auxMass,smallPhaseMass)&&samePhaseMass<=0.75*smallPhaseMass+1e-8,"coupling mass");
   ok(near(sourceMass,transport)&&near(transport,largeMass+shortMass)&&near(shortMass,stable+unstable),"partition");
   res.push({X,focus,B,T,M,L,N:tags.length,events,S,R,V,A,lambda,alpha,Q,sources,persistent,tiles,clockRich,large,short,unclassified,moderateRich,nonmoderateRich,innerOuter,localProducts,matchedProducts,phaseChecks,multiPhase,maxPhase,stable,unstable,sourceMass,transport,largeMass,shortMass,maxJointCap,maxCutCap,maxTickCap,offsetTwin,cheap,projectedPairs:phaseMaps.size,Delta,wheel,phasePairs,actualDefects,persistentPairs,longGap,shortDefects,wheelDefects,binControls,binMass,smallPhaseMass,samePhaseMass,auxMass,auxDefectMass,auxChecks})
  }
 }
 // Exact artificial phase cohort controls: distinct early sets and one later merged set
 // cannot BOTH occupy its strict majority. Two disjoint stable histories can match separately.
 const a=new Set([1,2,3,4]),b=new Set([5,6,7,8]),v=new Set([1,2,3,4,5,6,7,8]),x=new Set([1,2,3,4,9]),y=new Set([5,6,7,8,10]),inter=(p,q)=>[...p].filter(i=>q.has(i)).length;
 ok(inter(a,v)===v.size/2&&inter(b,v)===v.size/2,"merge equality excludes strict majority");ok(inter(a,x)>x.size/2&&inter(b,y)>y.size/2&&inter(a,y)===0,"two distinct matches");
 ok(res.some(r=>r.matchedProducts>0)&&res.some(r=>r.large>0)&&res.some(r=>r.moderateRich>0),"nonzero controls");
 return {results:res,synthetic:{mergeSize:v.size,eachEarlier:4,distinctMatches:2}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
