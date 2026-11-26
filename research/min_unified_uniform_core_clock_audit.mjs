// Common-core uniform pinned-cut and signed clock resource audit.
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
   const D=Math.max(40,Math.floor(B/2)),S=5,Rc=7,Z=13,V=12,K=30,Lcut=25,ac=1-4*S/Lcut;
   let period=3*5*7*11*13,alphaCut=(1/15)*(3/7)*(1-2/11)*(1-2/13),kap=2/alphaCut;
   const cutOK=J=>J%K===0&&[0,2,4].includes(J%7)&&![1,10].includes(J%11)&&![1,12].includes(J%13);
   let residues=0;for(let j=0;j<period;j++)if(cutOK(2*j))residues++;ok(near(residues/period,alphaCut),"exact CRT density");
   let good=new Set(tags.filter(t=>firstIdx[t.id]>=0&&!t.edges.slice(firstIdx[t.id]).some(e=>e.ids.length<m)).map(t=>t.id));
   let eventMap=tags.map(t=>new Map(t.path.map(e=>[e.jump,e]))),chains=new Map(),blocks=[];
   for(let e of marked)if(e.p){let pid=seedOn.get(e).pid;if(!chains.has(pid))chains.set(pid,[]);chains.get(pid).push(e)}
   for(let [pid,es] of chains){es.sort((a,b)=>a.a.t-b.a.t);let cur=[],g=0;for(let e of es){cur.push(e);g+=e.p-1;if(g>=D){blocks.push({pid,es:cur,g});cur=[];g=0}}}
   let coreGain=0,coreBlocks=0,coreWeight=0,coreEvents=0,coreTags=0,coreUnweighted=0,rawCuts=0,anchor=0,launch=0,landing=0,bypass=0,pending=0,completed=0,cleanCore=0,witnessCore=0,cleanDemand=0,allDemand=0,weightedLow=0,bypassGain=0,bypassBound=0,anchorGain=0,physicalChecks=0,periodChecks=0,largeLaunch=0,largeLanding=0;
   // Pin-only controls, exact finite-period discrepancy in horizon units.
   let controls=[];
   for(let [SS,ZZ,PP] of [[3,7,105],[5,11,1155]]){let primes=[];for(let p=3;p<=ZZ;p+=2)if(spf[p]===p)primes.push(p);
    let arr=Array.from({length:PP},(_,j)=>primes.every(p=>p<=SS?2*j%p===0:![1,p-1].includes(2*j%p))?1:0),n=arr.reduce((a,b)=>a+b,0),kk=2*PP/n,prefix=[0];for(let a of arr)prefix.push(prefix.at(-1)+a);let dev=prefix.map((v,j)=>kk*v-2*j),disc=Math.max(...dev)-Math.min(...dev);
    let mass=(C,J)=>{let a=C/2,b=J/2,f=x=>Math.floor(x/PP)*n+prefix[x%PP];return kk*(f(b)-f(a))};
    for(let Y of [31,127,257])controls.push({SS,ZZ,PP,kk,disc,Y,mass,U:0,F:0,excess:0,lowMass:0,lowN:0,hiN:0,hiMass:0,fastG:0,fastDrop:0,positive:0,checks:0,rich:0,resource:0,lowGainAtCuts:0,bypassHigh:0,weightedBlocks:0});
   }
   let coreWait=0,coreSigned=0,terminal=tags.reduce((s,t)=>s+t.df,0);
   let tagCore=tags.map(()=>new Set()),tagClean=tags.map(()=>new Set()),tagDemand=new Float64Array(N),tagLow=new Float64Array(N);
   for(let blk of blocks){let a=blk.es[0],z=blk.es.at(-1),lastSet=new Set(z.ids),ids=a.ids.filter(i=>good.has(i)&&lastSet.has(i)&&tags[i].vertices.indexOf(a.a)>=firstIdx[i]);if(!ids.length)continue;
    let common=blk.es.slice(1).map(e=>eventMap[ids[0]].get(e));if(!common.length)continue;
    let b=ids.length,g=common.reduce((s,e)=>s+e.g,0);
    ok(blk.g>=D&&blk.g<D+B&&g>=D-B,"block gain");
    for(let i of ids)for(let j=0;j<common.length;j++){let e=eventMap[i].get(blk.es[j+1]),f=common[j];ok(e&&e.C===f.C&&e.t===f.t&&e.n===f.n&&e.p===f.p&&e.w===f.w,"whole actual common event");ok(!tagCore[i].has(e),"disjoint core events");tagCore[i].add(e);physicalChecks++}
    for(let j=1;j<common.length;j++)ok(common[j-1].J===common[j].C&&common[j-1].n===common[j].t,"common contiguous word");
    coreGain+=b*g;coreBlocks++;coreWeight+=b;coreEvents+=common.length;coreTags+=b*common.length;coreUnweighted+=g;
    let ww=common.reduce((s,e)=>s+e.w,0);coreWait+=b*ww;coreSigned+=b*(4*ww-g);
    for(let c of controls){let U=0,F=0,E=0,ML=0,MH=0,nl=0,nh=0,fg=0,fd=0,po=0,lg=0,by=0;
     for(let e of common){let M=c.mass(e.C,e.J);ok(Math.abs(M-e.g)<=c.disc+1e-7,"period discrepancy per event");
      if(M>0)ok(e.p>c.SS,"ordinary pin barrier");
      if(e.p<c.Y){U+=e.g;ML+=M;if(M>0){nl++;lg+=e.g;ok(M<=e.g+c.disc+1e-7,"low crosser cap")}}
      else{nh++;MH+=M;let q=Math.max(0,4*e.w-e.g);E+=q;if(4*e.w>=e.g){F+=e.g;ok(q<=(7+8/(c.Y-1))*e.g+1e-7,"high excess cap")}
       else{fg+=e.g;fd+=e.d-e.dp;ok(e.d-e.dp>e.g/2,"high fast drop")}
       if(M>0)by+=e.g;
      }po+=Math.max(0,e.dp-e.d);c.checks++;
     }
     let mTot=c.mass(common[0].C,common.at(-1).J);ok(near(ML+MH,mTot)&&Math.abs(mTot-g)<=c.disc+1e-7,"exact core cut mass");
     ok(U<=ML+c.disc*(nh+1)+1e-7,"low gain from cut mass");
     ok(4*ww-g<=11*U+E+1e-7,"signed clock upper");
     ok(4*ww-g<=11*(ML+c.disc*(nh+1))+E+1e-7,"signed resource upper");
     ok(po<=5*U+E/2+1e-7,"positive variation upper");
     ok(fd>=fg/2-1e-7,"fast drop sum");
     let resource=11*ML+E;if(resource>=g/4)c.rich+=b*g;c.resource+=b*resource;c.weightedBlocks+=b;
     for(let [k,v] of Object.entries({U,F,excess:E,lowMass:ML,lowN:nl,hiN:nh,hiMass:MH,fastG:fg,fastDrop:fd,positive:po,lowGainAtCuts:lg,bypassHigh:by}))c[k]+=b*v;
    }
    let cuts=0,used=new Set(),localLow=0,localDemand=0;
    for(let j=0;j<common.length;j++){let e=common[j],by=0;
     for(let J=K*Math.ceil(e.C/K);J<e.J;J+=K){if(!cutOK(J))continue;cuts++;if(J===e.C){ok(e.p>Z,"rough anchor");anchor+=b;anchorGain+=b*e.g;continue}
      let aa=J-e.C,bb=e.J-J;if(aa>V&&bb>V/2){bypass+=b;by++;continue}
      let isLaunch=aa<=V;if(isLaunch){launch+=b;if(e.p>V)largeLaunch+=b}else{landing+=b;if(e.p>V)largeLanding+=b}
      let k=isLaunch?j:j+1,end=k;while(end<common.length&&common[end].J<J+V)end++;if(end>=common.length){pending+=b;continue}
      completed+=b;let seg=common.slice(k,end+1),gain=seg.reduce((s,f)=>s+f.g,0),demand=isLaunch?Math.max(V,e.g):V/2;
      ok(gain>=demand,"endpoint corridor gain");allDemand+=b*demand;
      let rough=seg.some(f=>{let h=Math.abs(f.C-J);return h>=4&&h-1>S&&spf[h-1]===h-1&&spf[h+1]===h+1});
      for(let f of seg){ok(!used.has(f)&&Math.abs(f.C-J)>0&&Math.abs(f.C-J)<=V,"disjoint endpoint corridor");used.add(f)}
      if(rough){witnessCore+=b;continue}cleanCore+=b;let low=0;for(let f of seg){ok(f.w<=2*S,"clean fast clock");if(f.p<=Lcut)low+=f.g;else ok(f.d-f.dp>=ac*f.g-1e-8,"clean high decrease")}
      ok(seg[0].d-seg.at(-1).dp>=ac*demand-(ac+5)*low-1e-8,"net corridor decrease");
      localLow+=low;localDemand+=demand;
      for(let i of ids)for(let f of seg){let fe=eventMap[i].get(f.jump);ok(tagCore[i].has(fe)&&!tagClean[i].has(fe),"actual clean tag corridor");tagClean[i].add(fe)}
     }
     if(by){ok(by<=Math.ceil(Math.max(0,e.g-3*V/2)/K)&&e.g>3*V/2,"bypass erosion");bypassGain+=b*e.g;bypassBound+=b*Math.ceil(Math.max(0,e.g-3*V/2)/K)}
    }
    weightedLow+=b*localLow;cleanDemand+=b*localDemand;for(let i of ids){tagLow[i]+=localLow;tagDemand[i]+=localDemand}
    rawCuts+=b*cuts;ok(Math.abs(kap*cuts-g)<=2*period+1e-7,"fixed period mass");periodChecks++;
   }
   let coreRecount=0,corePositive=0,outsidePositive=0,suffixPositive=0,suffixDef=0,coreTagLoss=0;
   for(let t of tags){let i=t.id,gg=[...tagCore[i]].reduce((s,e)=>s+e.g,0);coreRecount+=gg;ok(gg<=t.F-t.C0,"core actual gain");
    let pos=0,pc=0,po=0,low=0;for(let e of t.path){if(tagClean[i].has(e)){if(e.p<=Lcut)low+=e.g;continue}let v=Math.max(0,e.dp-e.d);pos+=v;if(tagCore[i].has(e))pc+=v;else po+=v}
    ok(near(low,tagLow[i]),"weighted low recount");ok(ac*tagDemand[i]<=(ac+5)*low+pos+6+1e-7,"full actual root telescoping");corePositive+=pc;outsidePositive+=po;
    if(good.has(i)){let v=first[i],suf=t.path.filter(e=>e.t>=v.t&&e.C>=v.C);if(suf.length){let sg=suf.reduce((s,e)=>s+e.g,0),loss=sg-gg;ok(loss>=0,"core inside suffix");coreTagLoss+=loss;let runs=1,last=-1;for(let e of t.edges.slice(firstIdx[i]))if(marked.has(e)){let pid=seedOn.get(e).pid;if(last>=0&&pid!==last)runs++;last=pid}
      ok(loss<=2*(D+B)*runs+B*(H/D+1)+2*B+1e-7,"core fringe loss");let ds=suf[0].d;let ps=suf.reduce((s,e)=>s+(tagClean[i].has(e)?0:Math.max(0,e.dp-e.d)),0);ok(ac*tagDemand[i]<=(ac+5)*low+ps+ds+1e-7,"suffix net budget");suffixPositive+=ps;suffixDef+=ds;
    }}
   }
   ok(coreRecount===coreGain&&coreWeight*D<=G+1e-7,"core multiplicity capacity");
   ok(rawCuts===anchor+launch+landing+bypass&&launch+landing===pending+completed&&completed===cleanCore+witnessCore,"cut partition");
   ok(anchor*(Z-1)<=coreGain&&anchor*(Z-1)<=anchorGain&&bypass<=bypassBound,"anchor and bypass cap");
   ok(ac*cleanDemand<=(ac+5)*weightedLow+suffixPositive+suffixDef+1e-7,"aggregate suffix budget");
   ok(ac*cleanDemand<=(ac+5)*weightedLow+corePositive+outsidePositive+6*N+1e-7,"aggregate canonical budget");
   ok(outsidePositive<=5*(G-coreGain)+1e-7,"omitted positive variation");
   ok(Math.abs(kap*rawCuts-coreGain)<=2*period*coreWeight+1e-6,"weighted periodic mass");
   let omitWait=W-coreWait,omitGain=G-coreGain,omitSigned=4*omitWait-omitGain;
   ok(near(coreSigned+omitSigned,G+2*terminal-12*N),"canonical signed clock balance");
   ok(omitWait<=prefixWait+2*B*N+3*coreTagLoss+3*H*bad+1e-7,"omitted clock prefix and fringe");
   ok(coreSigned>=G+2*terminal-12*N-4*(prefixWait+2*B*N+3*coreTagLoss+3*H*bad)-1e-7,"prefix clock lower");
   for(let c of controls){ok(coreSigned<=11*c.lowMass+c.excess+11*c.disc*(c.hiN+coreWeight)+1e-6,"aggregate signed resource");
    ok(c.lowMass<=(c.Y-1+c.disc)*c.lowN+1e-7,"aggregate count upper");
    ok(c.fastDrop<=c.positive+6*N+5*omitGain+1e-7,"global fast recovery");
    delete c.mass;
   }
   out.push({X,focus,N,events,D,coreWait,coreSigned,terminal,omitWait,omitGain,omitSigned,controls,coreGain,coreBlocks,coreWeight,coreEvents,coreTags,coreUnweighted,coreTagLoss,physicalChecks,periodChecks,rawCuts,anchor,launch,landing,bypass,pending,completed,cleanCore,witnessCore,cleanDemand,allDemand,weightedLow,bypassGain,bypassBound,anchorGain,largeLaunch,largeLanding,corePositive,outsidePositive,suffixPositive,suffixDef,kap,period,L,m,b0,physicalVertices:vs.length,physicalEdges:edges.size,starts:starts.length,stops:stops.length,merges,pathCount,newStartMass,restartMass,stopFlow,retired:retiredSets.size,markedGain,markedTagGain,G,W,Mmiss,prefixWait,prefixGain,firstDef,never,bad,outside,postOutside,maxSwitch,tagSwitch,corridors,clean,witnessed,pend,corridorGain,lowGain,positiveOutside,initialDef,localDemand});
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
