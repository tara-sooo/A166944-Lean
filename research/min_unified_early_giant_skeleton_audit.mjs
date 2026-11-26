// Actual physical hysteresis skeleton, prefix clock and localized cut corridors.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},near=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let out=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],plate=new Map(),verts=new Map(),edges=new Map(),slots=new Map(),events=0,G=0,W=0;
  function vertex(C,t){let k=C+"/"+t;if(!verts.has(k))verts.set(k,{k,C,t,ids:[],ins:[],out:null});return verts.get(k)}
  function edge(a,b,i,p=0){let k=a.k+">"+b.k;if(!edges.has(k)){let e={a,b,p,ids:[]};edges.set(k,e);a.out=e;b.ins.push(e)}let e=edges.get(k);ok(a.out===e&&e.p===p,"deterministic successor");e.ids.push(i);return e}
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let id=tags.length,C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,e={C,t,J,n,p,w,g:p-1,d:2*t-C,dp:2*n-J};path.push(e);let k=C+"/"+p+"/"+n;if(!slots.has(k))slots.set(k,[]);slots.get(k).push(e);let row={id,a:t,b:n-1,e};if(!plate.has(C))plate.set(C,[]);plate.get(C).push(row);events++;G+=p-1;W+=w;C=J;t=n;
   }
   let row={id,a:t,b:t,e:null};if(!plate.has(C))plate.set(C,[]);plate.get(C).push(row);tags.push({id,C0,F:C,tf:t,df:2*t-C,path,vertices:[],edges:[]})
  }
  let N=tags.length;
  for(let [C,rows] of plate){let times=[...new Set(rows.flatMap(r=>[r.a,r.b]))].sort((a,b)=>a-b),idx=new Map(times.map((x,j)=>[x,j]));
   for(let r of rows){let tag=tags[r.id],a=idx.get(r.a),b=idx.get(r.b);for(let j=a;j<=b;j++){let v=vertex(C,times[j]);v.ids.push(r.id);tag.vertices.push(v);if(j<b)tag.edges.push(edge(v,vertex(C,times[j+1]),r.id))}
    if(r.e){let e=r.e;tag.edges.push(edge(vertex(C,r.b),vertex(e.J,e.n),r.id,e.p));e.slot=slots.get(e.C+"/"+e.p+"/"+e.n);e.jump=tag.edges.at(-1)}
   }
  }
  for(let t of tags){t.vertices.sort((a,b)=>a.t-b.t||a.C-b.C);t.edges.sort((a,b)=>a.a.t-b.a.t||a.a.C-b.a.C);ok(t.vertices.length===t.edges.length+1,"path shape");for(let j=0;j<t.edges.length;j++)ok(t.edges[j].a===t.vertices[j]&&t.edges[j].b===t.vertices[j+1],"path adjacency")}
  let vs=[...verts.values()].sort((a,b)=>a.t-b.t||a.C-b.C),parent=Array.from({length:N},(_,i)=>i),mass=Array(N).fill(1),find=i=>parent[i]===i?i:parent[i]=find(parent[i]);
  for(let v of vs){for(let e of v.ins){let r=find(e.ids[0]);ok(e.ids.every(i=>find(i)===r),"history coherence");e.hist=mass[r]}let roots=[...new Set(v.ids.map(find))];if(roots.length){let a=roots[0];for(let b of roots.slice(1)){parent[b]=a;mass[a]+=mass[b]}}}
  for(let L of [4,Math.max(5,Math.floor(Math.sqrt(B)))]){
   let m=Math.max(2,Math.floor(L/2)),b0=2*L,theta=L/b0,first=tags.map(t=>t.vertices.find(v=>v.ids.length>=L)||null),firstIdx=tags.map((t,i)=>first[i]?t.vertices.indexOf(first[i]):-1),marked=new Set(),starts=[],stops=[],seedOn=new Map(),pathCount=0,merges=0,switches=0,retiredSets=new Set(),newStartMass=0,restartMass=0,stopFlow=0;
   let started=new Uint8Array(N),lastStop=new Int32Array(N).fill(-1);
   for(let v of vs){let incoming=v.ins.filter(e=>marked.has(e)),active=incoming.length>0,trigger=!active&&v.ids.length>=L;
    if(trigger){starts.push(v);for(let i of v.ids){if(started[i]){ok(lastStop[i]>=0,"restart consumes stop");lastStop[i]=-1;restartMass++}else newStartMass++;started[i]=1}}
    if(!active&&!trigger)continue;
    let pick=active?incoming.reduce((a,b)=>a.hist>=b.hist?a:b):null,pid=pick?seedOn.get(pick).pid:pathCount++,anchor=pick?seedOn.get(pick).anchor:v;
    if(v.ids.length>=L)anchor=v;
    if(incoming.length>1){merges+=incoming.length-1;for(let e of incoming)if(e!==pick){switches+=e.ids.length;ok(e.hist<=pick.hist,"history continuation")}}
    if(v.out&&v.out.ids.length>=m){marked.add(v.out);seedOn.set(v.out,{pid,anchor})}
    else{
     let continuing=v.out?v.out.ids:[],lost=anchor.ids.filter(i=>!continuing.includes(i));ok(lost.length>=L-m+1,"retirement witness size");for(let i of lost){let t=tags[i];ok(t.vertices.includes(anchor)&&t.tf<=v.t,"retired witness");ok(!retiredSets.has(i),"disjoint stop retirees");retiredSets.add(i)}
     stops.push(v);stopFlow+=continuing.length;for(let i of continuing)lastStop[i]=stops.length-1;
    }
   }
   ok(restartMass<=stopFlow&&newStartMass<=N&&starts.length*L<=newStartMass+restartMass,"start conservation");
   ok(stops.length*(L-m+1)<=N&&stopFlow<=(m-1)*stops.length,"stop conservation");
   ok(starts.length<=N/(L-m+1)+1e-8,"start bound");
   let markedGain=0,markedTagGain=0,chainG=new Map();
   for(let e of marked){ok(e.ids.length>=m,"marked flow");let g=e.b.C-e.a.C;markedGain+=g;markedTagGain+=g*e.ids.length;let pid=seedOn.get(e).pid;chainG.set(pid,(chainG.get(pid)||0)+g)}
   ok(markedGain*m<=G&&markedTagGain<=G,"marked gain capacity");
   let Mmiss=0,prefixWait=0,prefixGain=0,firstDef=0,never=0,bad=0,outside=0,postOutside=0,maxSwitch=0,tagSwitch=0,coveredGain=0,corridors=0,clean=0,witnessed=0,pend=0,corridorGain=0,lowGain=0,positiveOutside=0,initialDef=0,localDemand=0;
   for(let t of tags){let i=t.id,k=firstIdx[i],v=first[i],a=v?v.C-t.C0:t.F-t.C0,pw=v?v.t-(t.C0/2+3):t.tf-(t.C0/2+3),d=v?2*v.t-v.C:t.df;ok(2*pw===a+d-6,"prefix identity");prefixWait+=pw;prefixGain+=a;firstDef+=d;if(!v)never++;
    let miss=t.path.reduce((s,e)=>s+e.w*(1-Math.min(1,e.slot.length/b0)),0);Mmiss+=miss;ok((1-theta)*Math.max(0,pw-2*B)<=miss+1e-8,"prefix missing capacity");
    let isBad=k>=0&&t.edges.slice(k).some(e=>e.ids.length<m);if(isBad)bad++;
    let nsw=0,last=-1;
    for(let j=0;j<t.edges.length;j++){let e=t.edges[j],g=e.b.C-e.a.C;if(!marked.has(e)){outside+=g;if(k>=0&&j>=k)postOutside+=g}else{coveredGain+=g;if(k>=0&&j>=k&&!isBad){let pid=seedOn.get(e).pid;if(last>=0&&last!==pid)nsw++;last=pid}}if(k>=0&&j>=k&&!isBad)ok(marked.has(e),"good suffix in skeleton")}
    if(k>=0&&!isBad){ok(nsw<=Math.ceil(Math.log2(N)),"tag switch bound");tagSwitch+=nsw;maxSwitch=Math.max(maxSwitch,nsw)}
    if(k<0||isBad)continue;
    let path=t.path.filter(e=>e.t>=v.t&&e.C>=v.C);if(!path.length)continue;
    ok(path[0].d<=d+9*B,"prefix fringe");
    let S=5,V=14,K=30,cut=25,alpha=1-4*S/cut,used=new Set(),count=0,low=0;
    for(let j=0;j<path.length;j++){let e=path[j],J=K*(Math.floor(e.C/K)+1);if(!(e.C<J&&J<e.J&&e.p<=V))continue;
     let end=j;while(end<path.length&&path[end].J<J+V)end++;if(end===path.length){pend++;continue}
     let seg=path.slice(j,end+1);let rough=seg.some(f=>{let z=Math.abs(f.C-J);return z>=4&&spf[z-1]===z-1&&spf[z+1]===z+1&&z-1>S});corridors++;if(rough){witnessed++;continue}clean++;count++;let gain=0,gl=0;
     for(let f of seg){ok(!used.has(f)&&f.w<=2*S&&Math.abs(f.C-J)>0&&Math.abs(f.C-J)<=V,"clean corridor");used.add(f);gain+=f.g;if(f.p<=cut)gl+=f.g;else ok(f.d-f.dp>=alpha*f.g-1e-8,"high drop")}
     ok(gain>=V&&seg[0].d-seg.at(-1).dp>=alpha*V-(alpha+5)*gl-1e-8,"local corridor net drop");corridorGain+=gain;low+=gl;
    }
    let pos=path.reduce((s,e)=>s+(used.has(e)?0:Math.max(0,e.dp-e.d)),0);ok(alpha*V*count<=(alpha+5)*low+pos+path[0].d+1e-8,"corridor prefix budget");lowGain+=low;positiveOutside+=pos;initialDef+=path[0].d;localDemand+=alpha*V*count;
   }
   ok(bad<=stopFlow,"bad tag return cap");ok(postOutside<=bad*H,"outside suffix bound");ok(outside<=prefixGain+bad*H,"outside gain bound");ok(prefixWait<=Mmiss/(1-theta)+2*B*N+1e-7,"global prefix budget");ok(near(coveredGain+outside,G),"gain partition");
   ok(localDemand<=5.2*lowGain+positiveOutside+initialDef+1e-7,"global corridor budget");
   out.push({X,focus,N,events,L,m,b0,physicalVertices:vs.length,physicalEdges:edges.size,starts:starts.length,stops:stops.length,merges,pathCount,newStartMass,restartMass,stopFlow,retired:retiredSets.size,markedGain,markedTagGain,G,W,Mmiss,prefixWait,prefixGain,firstDef,never,bad,outside,postOutside,maxSwitch,tagSwitch,corridors,clean,witnessed,pend,corridorGain,lowGain,positiveOutside,initialDef,localDemand});
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
