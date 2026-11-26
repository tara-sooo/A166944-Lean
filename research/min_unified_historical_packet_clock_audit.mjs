// True historical packets, eligible-only regularized multipartite graph, exact signed ledger.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},near=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(x,m)=>(x%m+m)%m;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),h=Math.max(2,Math.floor(B/16)),N=0,events=0,tags=[],edges=new Map(),plate=new Map(),W=0,G=0,Z=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let id=N++,C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,d=2*t-C,dp=2*n-J,key=C+"/"+t;if(!edges.has(key))edges.set(key,{C,t,J,n,d,dp,p,w,ids:[]});let e=edges.get(key);ok(e.J===J&&e.n===n,"determinism");e.ids.push(id);path.push(e);events++;W+=w;G+=p-1;C=J;t=n;
   }
   for(let j=0;j<=path.length;j++){let e=path[j],Cj=e?e.C:C,v={id,a:e?e.t:t,b:e?e.n-1:t};if(!plate.has(Cj))plate.set(Cj,[]);plate.get(Cj).push(v)}
   Z+=2*t-C;tags.push({id,C0,F:C,expiry:C-h,df:2*t-C,path})
  }
  ok(2*W===G+Z-6*N,"global clock");
  let ordered=[...edges.values()].sort((a,b)=>a.C-b.C||a.t-b.t),births=[];
  for(let [C,rows] of plate)for(let t of new Set(rows.map(r=>r.a))){let ids=rows.filter(r=>r.a<=t&&t<=r.b).map(r=>r.id);if(ids.length>=2)births.push({C,t,ids})}
  births.sort((a,b)=>a.t-b.t||a.C-b.C);
  for(let L0 of [3,Math.max(4,Math.floor(Math.sqrt(B)/2))]){
   let parent=Array.from({length:N},(_,i)=>i),members=parent.map(i=>[i]),color=new Int32Array(N).fill(-1),packetSizes=[],pairRule=new Map(),maxDegree=1,mergerCount=0,allowed=0,forbidden=0;
   let find=i=>parent[i]===i?i:parent[i]=find(parent[i]),pkey=(a,b)=>a<b?a+"/"+b:b+"/"+a;
   function packet(ids){let c=packetSizes.length;for(let id of ids){ok(color[id]===-1,"unique packet assignment");color[id]=c}packetSizes.push(ids.length)}
   for(let v of births){let roots=[...new Set(v.ids.map(find))];if(roots.length<2)continue;mergerCount++;maxDegree=Math.max(maxDegree,roots.length);
    let total=roots.reduce((s,r)=>s+members[r].length,0),small=roots.filter(r=>members[r].length<L0);
    for(let i=0;i<v.ids.length;i++)for(let j=i+1;j<v.ids.length;j++){let a=v.ids[i],b=v.ids[j],r=find(a),s=find(b);if(r===s)continue;let key=pkey(a,b);ok(!pairRule.has(key),"unique true pair birth");let yes=members[r].length>=L0||members[s].length>=L0;pairRule.set(key,yes);if(yes)allowed++;else forbidden++}
    if(total>=L0&&small.length)packet(small.flatMap(r=>members[r]));
    let big=roots.reduce((a,b)=>members[a].length>=members[b].length?a:b);for(let r of roots)if(r!==big){parent[r]=big;members[big].push(...members[r]);members[r]=[]}
   }
   for(let i=0;i<N;i++)if(find(i)===i&&members[i].length<L0)packet(members[i]);
   ok(color.every(c=>c>=0),"complete packet partition");let P=Math.max(...packetSizes);ok(P<=maxDegree*L0,"packet bound");
   for(let [key,yes] of pairRule){let [a,b]=key.split("/").map(Number);ok(yes===(color[a]!==color[b]),"packet exact true birth mask")}
   // Finite start: fixed first actual shared completed-arrival plus h for some tags, 
   // other tags deliberately have empty eligibility. This is not the old cumulative maturity mask.
   let first=new Float64Array(N).fill(Infinity);
   for(let e of ordered)if(e.ids.length>=2)for(let i of e.ids)first[i]=Math.min(first[i],e.C);
   for(let mode of [0,1]){
    let start=tags.map(a=>mode===0?a.C0+h:(a.id%7===0?Infinity:first[a.id]+h));
    let R=Math.max(2,P*2),d0=R*4,vertices=new Map(),U=0,V=0,Zelig=0,Znot=0,ret=0,retEx=0,retUp=0,Cadd=0,Cmerge=0,Cdense=0,retSteps=0,exSteps=0,addSteps=0,denseSteps=0,mergeSteps=0,activePairs=0,denChecks=0,origUpper=0,errBound=0,eligibleGain=0,packetLoss=0,eligible=0;
    for(let a of tags){if(start[a.id]<a.expiry)eligible++;else Znot+=a.df}
    const vert=(C,t)=>{let k=C+"/"+t;if(!vertices.has(k))vertices.set(k,{C,t,ins:[],out:null});return vertices.get(k)};
    const counts=ids=>{let c=new Map();for(let i of ids)c.set(color[i],(c.get(color[i])||0)+1);return c};
    const A=ids=>ids.length**2-[...counts(ids).values()].reduce((s,k)=>s+k*k,0),f=ids=>A(ids)/(ids.length+R);
    const D=(e,x)=>e.d+(x-e.C)*(e.dp-e.d)/(e.J-e.C);
    function insert(live,add,d){for(let id of add){let n=live.length,m=live.filter(i=>color[i]===color[id]).length,old=f(live);live.push(id);let delta=f(live)-old,low=(n-m)*(n-m+2*R)/((n+R)*(n+R+1)),low2=1-(R/(n+R))**2-(2*P+1)/(n+R+1);
     ok(delta>=-1e-9&&delta>=low-1e-9&&delta>=low2-1e-9,"monotone insertion");Cadd+=d*delta;addSteps++;if(n>=R*2){Cdense+=d*delta;denseSteps++}}
    }
    for(let e of ordered){
     let ids=e.ids.filter(i=>start[i]<tags[i].expiry&&start[i]<e.J&&tags[i].expiry>e.C);if(!ids.length)continue;
     let cuts=[e.C,e.J,...ids.flatMap(i=>[start[i],tags[i].expiry]).filter(x=>e.C<x&&x<e.J)];cuts=[...new Set(cuts)].sort((a,b)=>a-b);
     let live=ids.filter(i=>start[i]<e.C),v=vert(e.C,e.t);ok(!v.out,"unique out");v.out=live.slice();insert(live,ids.filter(i=>start[i]===e.C),e.d);
     // An eligible start at root is possible only for synthetic zero strip; here h>0.
     for(let k=0;k+1<cuts.length;k++){
      let x=cuts[k],y=cuts[k+1],n=live.length,a=A(live),wgt=a/(n+R),dx=y-x,omega=e.w/(e.J-e.C);
      for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let key=pkey(live[i],live[j]);ok(pairRule.has(key)&&pairRule.get(key)===(color[live[i]]!==color[live[j]]),"actual active pair mask");activePairs++}
      let old=a/Math.max(d0,e.ids.length),err=R*n/d0;ok(old<=wgt+err+1e-9,"denominator error");denChecks++;origUpper+=old*dx*omega;errBound+=err*dx*omega;
      U+=wgt*dx;V+=wgt*dx*omega;eligibleGain+=n*dx;packetLoss+=(n-wgt)*dx;
      let remaining=live.filter(i=>tags[i].expiry>y),kret=n-remaining.length;
      if(kret){let delta=wgt-f(remaining),d=D(e,y),s=remaining.length,ex=d*(delta-kret),bound=d*kret*P/(n+R);
       ok(delta>=-1e-9&&ex<=bound+1e-7,"retirement bound");ret+=d*delta;Zelig+=d*kret;retEx+=ex;retUp+=bound;retSteps++;if(ex>1e-8)exSteps++;
       for(let i of live)if(tags[i].expiry===y)ok(d<=tags[i].df+h+1e-7,"virtual terminal");
      }
      live=remaining;if(y<e.J)insert(live,ids.filter(i=>start[i]===y),D(e,y));
     }
     if(live.length)vert(e.J,e.n).ins.push(live.slice())
    }
    for(let v of vertices.values()){
     let flat=v.ins.flat(),out=v.out||[];ok(flat.length===out.length&&new Set(flat).size===flat.length&&flat.every(i=>out.includes(i)),"eligible edge conservation");
     let delta=f(out)-v.ins.reduce((s,a)=>s+f(a),0);ok(delta>=-1e-9,"merge superadditivity");Cmerge+=(2*v.t-v.C)*delta;if(delta>1e-8)mergeSteps++;
    }
    ok(near(2*V,U+ret-Cadd-Cmerge)&&near(ret,Zelig+retEx)&&near(eligibleGain,U+packetLoss),"graph identities");
    ok(retEx<=retUp+1e-7&&Zelig+Znot<=Z+N*h+1e-6&&origUpper<=V+errBound+1e-6,"global upper bounds");
    results.push({X,focus,L0,mode,N,events,mergerCount,packets:packetSizes.length,P,maxDegree,R,d0,allowed,forbidden,eligible,activePairs,denChecks,U,V,eligibleGain,packetLoss,Z,Zelig,Znot,ret,retEx,retUp,Cadd,Cmerge,Cdense,retSteps,exSteps,addSteps,denseSteps,mergeSteps,origUpper,errBound,objective:U-Cadd-Cmerge+retEx-Znot,relaxedObjective:U-Cadd-Cmerge+retUp-Znot});
   }
  }
 }
 // Artificial repeated colors: no disjoint-color assumption at merges.
 let groups=[[4,1,2],[2,5,0],[3,2,4]],R=7,A=v=>v.reduce((a,b)=>a+b,0)**2-v.reduce((a,b)=>a+b*b,0),f=v=>A(v)/(v.reduce((a,b)=>a+b,0)+R),v=[0,1,2].map(i=>groups.reduce((s,g)=>s+g[i],0));ok(f(v)>=groups.reduce((s,g)=>s+f(g),0),"overlapping-color merge");
 // Nonvacuous positive retirement surplus: twenty size-five packets and one singleton.
 const survivors=Array(20).fill(5),before=[...survivors,1],regularizer=10,P=5;
 const wgt=g=>A(g)/(g.reduce((s,x)=>s+x,0)+regularizer);
 const excess=wgt(before)-wgt(survivors)-1,bound=P/(101+regularizer);
 ok(excess>0&&excess<=bound+1e-12,"positive retirement surplus bound");
 return {results,synthetic:{merged:f(v),separate:groups.reduce((s,g)=>s+f(g),0),positiveRetirementExcess:excess,retirementBound:bound}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
