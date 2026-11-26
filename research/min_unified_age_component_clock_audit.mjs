// Actual historical packets, first-large colors and delayed pair activation components.
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
   for(let j=0;j<=path.length;j++){let e=path[j],Cj=e?e.C:C,v={id,a:e?e.t:t,b:e?e.n-1:t,br:j?"p"+path[j-1].p:"root"};if(!plate.has(Cj))plate.set(Cj,[]);plate.get(Cj).push(v)}
   Z+=2*t-C;tags.push({id,C0,F:C,expiry:C-h,df:2*t-C,path})
  }
  ok(2*W===G+Z-6*N,"global clock");
  let ordered=[...edges.values()].sort((a,b)=>a.C-b.C||a.t-b.t),births=[];
  for(let [C,rows] of plate)for(let t of new Set(rows.map(r=>r.a))){let ids=rows.filter(r=>r.a<=t&&t<=r.b).map(r=>r.id);if(ids.length>=2){let rowsAt=rows.filter(r=>r.a<=t&&t<=r.b);births.push({C,t,ids,br:rowsAt.map(r=>r.a===t?r.br:"wait")})}}
  births.sort((a,b)=>a.t-b.t||a.C-b.C);
  for(let L0 of [3,Math.max(4,Math.floor(Math.sqrt(B)/2))]){
   let age=h, firstLarge=new Int32Array(N).fill(-1),firstLargeC=new Float64Array(N).fill(Infinity),freshSizes=[], pairStarts=new Map();
   for(let v of births)if(v.ids.length>=L0){let fresh=v.ids.filter(i=>firstLarge[i]<0);if(fresh.length){let c=freshSizes.length;for(let i of fresh){firstLarge[i]=c;firstLargeC[i]=v.C}freshSizes.push(fresh.length)}}
   for(let i=0;i<N;i++)if(firstLarge[i]<0){firstLarge[i]=freshSizes.length;freshSizes.push(1)}
   let parent=Array.from({length:N},(_,i)=>i),members=parent.map(i=>[i]),color=new Int32Array(N).fill(-1),packetSizes=[],pairRule=new Map(),maxDegree=1,mergerCount=0,allowed=0,forbidden=0;
   let find=i=>parent[i]===i?i:parent[i]=find(parent[i]),pkey=(a,b)=>a<b?a+"/"+b:b+"/"+a;
   function packet(ids){let c=packetSizes.length;for(let id of ids){ok(color[id]===-1,"unique packet assignment");color[id]=c}packetSizes.push(ids.length)}
   for(let v of births){let roots=[...new Set(v.ids.map(find))];if(roots.length<2)continue;mergerCount++;maxDegree=Math.max(maxDegree,roots.length);
    let total=roots.reduce((s,r)=>s+members[r].length,0),small=roots.filter(r=>members[r].length<L0);
    for(let i=0;i<v.ids.length;i++)for(let j=i+1;j<v.ids.length;j++){let a=v.ids[i],b=v.ids[j],r=find(a),s=find(b);if(r===s)continue;let key=pkey(a,b);ok(!pairRule.has(key),"unique true pair birth");let yes=members[r].length>=L0||members[s].length>=L0;pairRule.set(key,yes);let bi=v.br[i],bj=v.br[j],size=br=>v.br.filter(x=>x===br).length,actual= Math.max(size(bi),size(bj))>=L0; if(actual)ok(firstLarge[a]!==firstLarge[b]&&yes,"actual large implies both colors"); if(actual)pairStarts.set(key,v.C+Math.max(age,Math.ceil(age*Math.log2(total/Math.min(members[r].length,members[s].length)))));if(yes)allowed++;else forbidden++}
    if(total>=L0&&small.length)packet(small.flatMap(r=>members[r]));
    let big=roots.reduce((a,b)=>members[a].length>=members[b].length?a:b);for(let r of roots)if(r!==big){parent[r]=big;members[big].push(...members[r]);members[r]=[]}
   }
   for(let i=0;i<N;i++)if(find(i)===i&&members[i].length<L0)packet(members[i]);
   ok(color.every(c=>c>=0),"complete packet partition");let P=Math.max(...packetSizes);ok(P<=maxDegree*L0,"packet bound");
   for(let [key,yes] of pairRule){let [a,b]=key.split("/").map(Number);ok(yes===(color[a]!==color[b]),"packet exact true birth mask")}
   let freshP=Math.max(...freshSizes);ok(freshP<=maxDegree*L0,"first-large size");
   // Kruskal reconstruction forest of permitted static pair starts, finite age proxy.
   let par=Array.from({length:N},(_,i)=>i),up=Array(N).fill(-1),when=Array(N).fill(-Infinity),root=i=>par[i]===i?i:par[i]=root(par[i]),unions=0;
   for(let [key,x] of [...pairStarts].sort((a,b)=>a[1]-b[1])){let [i,j]=key.split("/").map(Number),a=root(i),b=root(j);if(a===b)continue;let k=up.length;up.push(-1);when.push(x);par.push(k);up[a]=up[b]=k;par[a]=par[b]=k;unions++}
   ok(unions<=N-1,"activation forest");
   const comp=(i,x,strict)=>{while(up[i]>=0&&(strict?when[up[i]]<x:when[up[i]]<=x))i=up[i];return i};
   for(let [key,x] of pairStarts){let [i,j]=key.split("/").map(Number);ok(comp(i,x,false)===comp(j,x,false),"activation coverage")}
   let starts=tags.map(a=>firstLargeC[a.id]+h),capP=Math.max(P,freshP),R=Math.max(2,2*capP),d0=4*R;
   for(let mode of [0,1]){
    let vertices=new Map(),U=0,V=0,baseU=0,baseV=0,exactU=0,exactV=0,eligibleGain=0,Zelig=0,Znot=0,Cstart=0,Cmerge=0,Cage=0,ret=0,Sret=0,retUp=0,err=0,retSteps=0,mergeSteps=0,ageSteps=0,addSteps=0,activePairs=0,checks=0,strictImprovements=0;
    let start=starts.map((x,i)=>mode===0?x:(i%7===0?Infinity:x+h));
    for(let a of tags)if(!(start[a.id]<a.expiry))Znot+=a.df;
    const vert=(C,t)=>{let k=C+"/"+t;if(!vertices.has(k))vertices.set(k,{C,t,ins:[],out:null});return vertices.get(k)};
    const mono=(ids,labels)=>{let n=ids.length,m=new Map();for(let i of ids)m.set(labels[i],(m.get(labels[i])||0)+1);return (n*n-[...m.values()].reduce((s,v)=>s+v*v,0))/(n+R)};
    const weight=(ids,x,strict)=>{let gr=new Map();for(let i of ids){let c=comp(i,x,strict);if(!gr.has(c))gr.set(c,[]);gr.get(c).push(i)}let a=0;for(let g of gr.values())a+=Math.min(mono(g,color),mono(g,firstLarge));return a};
    const D=(e,x)=>e.d+(x-e.C)*(e.dp-e.d)/(e.J-e.C);
    function change(live,x,d,add){let old=weight(live,x,true),after=weight(live,x,false);ok(after>=old-1e-9,"age monotone");Cage+=d*(after-old);if(after>old+1e-9)ageSteps++;
     for(let i of add){let before=weight(live,x,false);live.push(i);let delta=weight(live,x,false)-before;ok(delta>=-1e-9,"insert monotone");Cstart+=d*delta;addSteps++}}
    for(let e of ordered){
     let ids=e.ids.filter(i=>start[i]<tags[i].expiry&&start[i]<e.J&&tags[i].expiry>e.C);if(!ids.length)continue;
     let points=[e.C,e.J,...ids.flatMap(i=>[start[i],tags[i].expiry]).filter(x=>e.C<x&&x<e.J)];
     for(let i of ids){let j=i;while(up[j]>=0){j=up[j];let x=when[j];if(e.C<x&&x<e.J)points.push(x);if(x>=e.J)break}}
     let cuts=[...new Set(points)].sort((a,b)=>a-b),live=ids.filter(i=>start[i]<e.C),v=vert(e.C,e.t);ok(!v.out,"one out");v.out=live.slice();change(live,e.C,e.d,ids.filter(i=>start[i]===e.C));
     for(let k=0;k+1<cuts.length;k++){let x=cuts[k],y=cuts[k+1],dx=y-x,n=live.length,wgt=weight(live,x,false),base=mono(live,color),A=0;
      for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let a=live[i],b=live[j],z=pairStarts.get(pkey(a,b));if(z!==undefined&&z<=x){ok(comp(a,x,false)===comp(b,x,false)&&color[a]!==color[b]&&firstLarge[a]!==firstLarge[b],"retained pair coverage");A+=2;activePairs++}}
      let old=A/Math.max(d0,e.ids.length),omega=e.w/(e.J-e.C),epsilon=R*n/d0;ok(old<=wgt+epsilon+1e-8&&wgt<=base+1e-8,"envelope comparison");if(wgt<base-1e-8)strictImprovements++;
      U+=wgt*dx;V+=wgt*dx*omega;baseU+=base*dx;baseV+=base*dx*omega;exactU+=old*dx;exactV+=old*dx*omega;err+=epsilon*dx*omega;eligibleGain+=n*dx;checks++;
      let stay=live.filter(i=>tags[i].expiry>y),kr=n-stay.length;
      if(kr){let drop=weight(live,y,true)-weight(stay,y,true),d=D(e,y),ex=d*(drop-kr),bound=d*kr*capP/R;ok(drop>=-1e-8&&ex<=bound+1e-7,"retirement bound");ret+=d*drop;Zelig+=d*kr;Sret+=ex;retUp+=bound;retSteps++}
      live=stay;if(y<e.J)change(live,y,D(e,y),ids.filter(i=>start[i]===y))
     }
     if(live.length)vert(e.J,e.n).ins.push(live.slice())
    }
    for(let v of vertices.values()){let out=v.out||[],flat=v.ins.flat();ok(flat.length===out.length&&new Set(flat).size===flat.length&&flat.every(i=>out.includes(i)),"flow");
     let delta=weight(out,v.C,true)-v.ins.reduce((s,g)=>s+weight(g,v.C,true),0);ok(delta>=-1e-9,"physical merge");Cmerge+=(2*v.t-v.C)*delta;if(delta>1e-9)mergeSteps++}
    ok(near(2*V,U+ret-Cstart-Cmerge-Cage)&&near(ret,Zelig+Sret),"exact graph identity");
    ok(V<=baseV+1e-7&&exactV<=V+err+1e-7&&Sret<=retUp+1e-7&&Zelig+Znot<=Z+N*h+1e-6,"global inequalities");
    results.push({X,focus,L0,mode,N,events,packets:packetSizes.length,P,freshP,capP,R,d0,allowed,forbidden,staticPairs:pairStarts.size,unions,activePairs,checks,strictImprovements,retSteps,mergeSteps,ageSteps,addSteps,U,V,baseU,baseV,exactU,exactV,eligibleGain,Z,Zelig,Znot,Cstart,Cmerge,Cage,Sret,retUp,err,objective:U-Cstart-Cmerge-Cage+Sret-Znot});
   }
  }
 }
 // Synthetic min of two color diversities: arbitrary overlap of colors.
 const w=(ids,labels)=>{let m=new Map();for(let i of ids)m.set(labels[i],(m.get(labels[i])||0)+1);return (ids.length**2-[...m.values()].reduce((a,b)=>a+b*b,0))/(ids.length+2)};
 let colors=[[0,0,1,1,2,2],[0,1,0,1,0,1]],f=g=>Math.min(...colors.map(c=>w(g,c))),a=[0,1,2],b=[3,4,5];
 ok(f(a.concat(b))>=f(a)+f(b),"min superadditivity");return {results,synthetic:{separate:f(a)+f(b),union:f(a.concat(b))}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
