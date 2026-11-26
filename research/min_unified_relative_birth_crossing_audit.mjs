// Actual induced birth trees and local actual crossing-clock controls.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(v,m)=>(v%m+m)%m;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1),pr=[];for(let p=2;p<=lim;p++)if(!spf[p]){pr.push(p);for(let j=p;j<=lim;j+=p)spf[j]=p}
 const odd=pr.filter(p=>p>2),omega=x=>{let k=0;while(x>1){x/=spf[x];k++}return k};let res=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,paths=[],slots=new Map(),events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[],id=paths.length;
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let z=C-1+2*I;while(z>1){let f=spf[z];while(z%f===0)z/=f;if(f*f>C+1)continue;let v=mod((I?f+2:0)-t,2*f)||2*f;if(v<w||v===w&&f<p){p=f;w=v}}}if(!p)break;
    let n=t+w,J=C+p-1,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;ok(d>=0&&dp>=0&&w<=2*p,"MIN");
    if(!slots.has(key))slots.set(key,{C,J,p,n,ids:[]});let s=slots.get(key);s.ids.push(id);path.push({C,J,p,t,n,w,d,dp,g:p-1,s});C=J;t=n;events++;
   }
   let plate=path.map((e,j)=>({C:e.C,a:e.t,b:e.n-1,branch:j?"p"+path[j-1].p:"root"}));plate.push({C,a:t,b:t,branch:path.length?"p"+path.at(-1).p:"root"});paths.push({id,C0,F:C,path,plate})
  }
  function birth(A,B){let i=0,j=0;while(i<A.length&&j<B.length){let a=A[i],b=B[j];if(a.C<b.C){i++;continue}if(a.C>b.C){j++;continue}
   let t=Math.max(a.a,b.a);if(t<=Math.min(a.b,b.b))return {C:a.C,t,ba:a.a===t?a.branch:"wait",bb:b.a===t?b.branch:"wait"};i++;j++}throw Error("no true birth")}
  let cohorts=0,pairChecks=0,birthNodes=0,rootWait=0,jumpWait=0,jumpJump=0,reset=0,nonreset=0,productChecks=0,slackChecks=0,fringeNeeded=0,thresholdChecks=0,smallPairs=0,maxB=0,attachmentChecks=0,mergeChecks=0,forestChecks=0,largePhysical=0,skipped=0;
  let used=new Set();
  for(let s of slots.values()){let b=s.ids.length;if(b<2)continue;if(b>80){skipped++;continue}let key=s.ids.join(",")+"/"+Math.floor(s.J/B);if(used.has(key))continue;used.add(key);cohorts++;maxB=Math.max(maxB,b);if(b>=8)largePhysical++;
   let nodes=new Map(),pairs=[];
   for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){let a=paths[s.ids[i]],c=paths[s.ids[j]],v=birth(a.plate,c.plate);ok(v.ba!==v.bb,"distinct true incoming branches");let k=v.C+"/"+v.t;if(!nodes.has(k))nodes.set(k,{...v,groups:new Map(),members:new Set()});let z=nodes.get(k);
    for(let [id,branch] of [[a.id,v.ba],[c.id,v.bb]]){if(!z.groups.has(branch))z.groups.set(branch,new Set());z.groups.get(branch).add(id);z.members.add(id)}
    pairs.push({i:a.id,j:c.id,z,ba:v.ba,bb:v.bb});pairChecks++;
    let ps=[v.ba,v.bb].filter(x=>x[0]==="p").map(x=>+x.slice(1)),I=v.t%2,k0=(2*v.t-v.C-6*I)/2;
    if(ps.length){ok(Number.isInteger(k0)&&k0>=0,"adjusted deficit");if(k0===0)reset++;else nonreset++;let prod=1;for(let p of ps){ok((v.t-2*I)%p===0&&(v.C+2*I)%p===0&&k0%p===0,"inverse incoming label");prod*=p}ok(k0%prod===0&&(v.C+2*I)%prod===0,"inverse product");productChecks++}
    if(ps.length===2)jumpJump++;else if(ps.length===1)jumpWait++;else{rootWait++;ok([v.ba,v.bb].includes("root")&&[v.ba,v.bb].includes("wait"),"root/wait")}
   }
   let dmax=1;
   for(let z of nodes.values()){birthNodes++;dmax=Math.max(dmax,z.groups.size);let all=new Set();
    for(let [branch,ids] of z.groups)for(let id of ids){ok(!all.has(id),"disjoint branch");all.add(id);let a=paths[id],Cprev=branch[0]==="p"?z.C-(+branch.slice(1))+1:z.C,tprev=z.t-1;
     if(branch==="root"){ok(a.C0===z.C,"root origin");continue}
     let dp=2*tprev-Cprev,fringe=branch[0]==="p"?4*(+branch.slice(1)):4*B;
     if(dp>6+5*(Cprev-a.C0))fringeNeeded++;
     ok(a.C0<=Cprev&&dp<=6+5*(Cprev-a.C0)+fringe,"predecessor root envelope");ok(a.C0>=s.J-H&&s.J-Cprev+Math.max(0,dp-6-fringe)/5<=H+1e-7,"lifetime slack");slackChecks++;
    }
    ok(all.size===z.members.size,"branch union");
    for(let id of s.ids){let pl=paths[id].plate.find(e=>e.C===z.C&&e.a<=z.t&&z.t<=e.b);if(pl){let br=pl.a===z.t?pl.branch:"wait";ok(z.groups.get(br)?.has(id),"full induced birth membership")}}
   }
   for(let a of [1,2,3,Math.max(1,Math.floor(b/4)),Math.max(1,Math.floor(b/2)),b+1]){
    let small=0,per=new Map();for(let r of pairs)if(r.z.groups.get(r.ba).size<a&&r.z.groups.get(r.bb).size<a){small+=2;per.set(r.i,(per.get(r.i)||0)+1);per.set(r.j,(per.get(r.j)||0)+1)}
    ok(small<=dmax*a*b,"relative small-small bound");for(let n of per.values())ok(n<=dmax*a,"per tag small-small");thresholdChecks++;smallPairs+=small;
    let founders=0,merges=0,attach=0,founderMembers=new Set(),attached=new Set();
    for(let z of [...nodes.values()].sort((x,y)=>x.t-y.t||x.C-y.C)){let groups=[...z.groups.values()],k=groups.filter(g=>g.size>=a).length;
     if(k===0&&z.members.size>=a&&a>1){founders++;for(let id of z.members){ok(!founderMembers.has(id)&&!attached.has(id),"disjoint founders");founderMembers.add(id)}}
     if(k>=1){merges+=k-1;for(let g of groups)if(g.size<a)for(let id of g){ok(!attached.has(id)&&!founderMembers.has(id),"unique attachment");attached.add(id);attach++;attachmentChecks++}}
    }
    if(a===1)founders=b;ok(merges<=founders&&attach+a*merges<=b,"induced founder budget");mergeChecks+=merges;forestChecks++;
   }
  }
  let cfgs=[{S:3,R:5,V:9,A:17},{S:5,R:7,V:25,A:37}],tiles=0,rich=0,massChecks=0,clockChecks=0,small=0,large=0,unclassified=0,factorChecks=0,certCounts=[0,0,0,0],constantRuns=0,constantSupportChecks=0,maxSupport=0,exactCrossers=0,roughChecks=0;
  for(let {S,R,V,A} of cfgs){
   let sm=odd.filter(p=>p<=S),mid=odd.filter(p=>S<p&&p<=R),extra=odd.filter(p=>R<p&&p<=V),PS=sm.reduce((a,p)=>a*p,1),P=mid.reduce((a,p)=>a*p,PS),alpha=mid.reduce((a,p)=>a*(p-1)/(2*p),1/PS),Q=extra.reduce((a,p)=>a*(1-2/p),1),lam=Math.ceil(P**(4/11)),max=4*X+H+2*lam+20;
   let raw=new Uint32Array(Math.ceil(max/2)+1);for(let j=0;j<raw.length-1;j++){let J=2*j;raw[j+1]=raw[j]+Number(j%PS===0&&mid.every(p=>mod(J,p)%2===0&&mod(J,p)<=p-3)&&extra.every(p=>mod(J,p)!==1&&mod(J,p)!==p-1))}
   let cnt=(a,b)=>raw[b/2]-raw[a/2],mass=(a,b)=>2*cnt(a,b)/(alpha*Q),smth=j=>(raw[j+lam]-raw[j])/(alpha*lam),tile=2*Math.max(32,Math.floor(B/2));
   for(let a of paths){
    for(let l=Math.ceil(a.C0/tile)*tile;l+tile<=a.F;l+=tile){let es=a.path.filter(e=>l<=e.C&&e.J<=l+tile);if(!es.length)continue;tiles++;let G=es.reduce((s,e)=>s+e.g,0),W=es.reduce((s,e)=>s+e.w,0);if(W<G/4)continue;rich++;
     let Hc=es.filter(e=>e.p>=A&&cnt(e.C,e.J)>0),mh=Hc.reduce((s,e)=>s+mass(e.C,e.J),0),F=Hc.reduce((s,e)=>s+e.g,0),U=G-F,Msmall=es.reduce((s,e)=>s+(e.p<A?mass(e.C,e.J):0),0),Mtotal=mass(es[0].C,es.at(-1).J),outer=new Set();
     for(let e of Hc)for(let j=e.C/2-lam+1;j<e.J/2;j++)outer.add(j);
     let err=2/Q*[...outer].reduce((s,j)=>s+Math.abs(smth(j)-Q),0)+Math.abs(Mtotal-G);
     ok(mh<=F+2*(lam-1)*Hc.length+err+1e-6&&U<=Msmall+2*(lam-1)*Hc.length+err+1e-6,"crossing coverage");massChecks++;
     let ex=Hc.filter(e=>16*e.w>=e.g),Wex=ex.reduce((s,e)=>s+e.w,0);ok(Wex+1e-7>=W-3*U-F/16,"clock supply");clockChecks++;
     if(Msmall>=G/48)small++;else if(U<=G/24){ok(Wex>=G/16-1e-7,"large crossing alternative");large++}else unclassified++;
     for(let e of ex){exactCrossers++;let fmin=Math.min(spf[e.C-1],spf[e.C+1]);ok(fmin>=e.w/2,"roughness");roughChecks++;
      let sel=(e.C-1)%e.p===0?e.C-1:e.C+1,co=sel/e.p;ok(Number.isInteger(co)&&co>=e.p,"selected cofactor");
      for(let k=3;k<=6;k++)if(e.w/2>(e.C+1)**(1/k)){ok(omega(e.C-1)<k&&omega(e.C+1)<k&&omega(co)<=k-2,"factor certificate");factorChecks++;certCounts[k-3]++}
     }
    }
    for(let j=0;j<a.path.length;){let e=a.path[j];if(e.d!==e.dp){j++;continue}let k=j,d=e.d,ps=new Set();while(k<a.path.length&&a.path[k].d===d&&a.path[k].dp===d){let f=a.path[k],I=f.n%2;if(f.p>=A&&f.dp-6*I>0){ok((d-6*I)%(2*f.p)===0,"flat support");ps.add(f.p)}k++}
     constantRuns++;if(ps.size){let prod=[...ps].reduce((a,p)=>a*BigInt(p),1n);ok(BigInt(d/2)*BigInt((d-6)/2)%prod===0n,"flat product");constantSupportChecks++;maxSupport=Math.max(maxSupport,ps.size)}j=k;
    }
   }
  }
  res.push({X,focus,B,T,N:paths.length,events,cohorts,pairChecks,birthNodes,rootWait,jumpWait,jumpJump,reset,nonreset,productChecks,slackChecks,fringeNeeded,thresholdChecks,smallPairs,maxB,largePhysical,skipped,attachmentChecks,mergeChecks,forestChecks,tiles,rich,massChecks,clockChecks,small,large,unclassified,factorChecks,certCounts,constantRuns,constantSupportChecks,maxSupport,exactCrossers,roughChecks});
 }
 return res
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
