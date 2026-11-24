// Latest-origin capped representative transport in the retained physical forest.
function audit(X,y=7){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,Y=11,L=210,T=Math.max(53,Math.ceil(X/256)),cap=Math.max(2,Math.floor(B/4))*B,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 let W=2;for(let p=3;p<y;p++)if(spf[p]===p)W*=p;const w0=Math.floor(W/4)+1,H=Math.max(12,Math.floor(Math.sqrt(B))),Q=Math.max(11,Math.ceil(B/2)),J=7;
 const ck=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b,cell=(C,W)=>Math.floor((C-1)/W);
 const orig=i=>2*(X+2*i+1)-2,colour=i=>cell(orig(i),W);
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const traces=Array.from({length:N},()=>[]),term=new Uint8Array(N),times=new Int32Array(N),cuts=new Int32Array(N),head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),admit=new Map();
 function add(i,C,entry){next[i]=head[C/2];head[C/2]=i;if(entry){let b=cell(C,L);admit.set(b,(admit.get(b)||0)+1)}}
 for(let i=0;i<N;i++){let M=X+2*i+1;times[i]=M+2;cuts[i]=Math.floor((7*M-1)/4);add(i,orig(i),true)}
 let S=0,events=0,primeStops=0,cellStops=0;
 for(let b=cell(2*X,L);b<=cell(7*X-2,L);b++){
  if(!admit.has(b))continue;let stop=admit.get(b)>=T;
  for(let C=Math.max(2*X,b*L+2);C<=Math.min(7*X-2,(b+1)*L);C+=2){
   let i=head[C/2];head[C/2]=-1;let groups=new Map();
   while(i>=0){let j=next[i];if(stop){term[i]=1;S++;cellStops++}else{let [n,p]=hit(times[i],C,cuts[i]);if(!p){term[i]=3}else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}}i=j}
   for(let [p,a] of groups){let stopP=p>=Y&&a.length>=Math.ceil(cap/p);for(let [i,n] of a){traces[i].push({p,n,C,r:Math.min(spf[C-1],spf[C+1])});if(stopP){term[i]=2;S++;primeStops++}else{times[i]=n;let C1=C+p-1;events++;add(i,C1,cell(C1,L)!==b)}}}
  }
 }

 // Latest-origin representatives in the full retained physical forest.
 head.fill(-1);
 const ptr=new Int32Array(N),alive=new Uint8Array(N),badH=new Uint8Array(N),badP=new Uint8Array(N),depart=new Uint8Array(N),last=new Int32Array(N).fill(-1),gs=[];
 let kappa=8,repH=y>=17?7:H;
 let out={X,Y,y,W,w0,H:repH,kappa,N,S,events,primeStops,cellStops,vertices:0,repInc:0,discarded:0,repHigh:0,repLarge:0,repBadUnion:0,repExit:0,repExitBad:0,repExitHigh:0,repExitLarge:0,repExitOrdinary:0,exitGroups:0,exitMass:0,capExitMass:0,smallExitMass:0,largeExitMass:0,largeExitGroups:0,residentTerminal:0,foreignTerminal:0,capForeignTerminal:0,smallForeignTerminal:0,terminalGroups:0,terminalReps:0,capChecks:0,badExitChecks:0,forestChecks:0,exitSelectedGroups:0,maxGroup:0,allExitGroups:0,allExitMass:0,allExitCap:0};
 for(let i=0;i<N;i++)if(term[i]===1||term[i]===2){alive[i]=1;times[i]=X+2*i+3;add(i,orig(i),false)}
 const terminal=[];
 function inspect(a,C,t,isV,terminalFlag){
  out.vertices++;out.maxGroup=Math.max(out.maxGroup,a.length);
  let parents=new Map();for(let i of a)if(last[i]>=0)parents.set(last[i],(parents.get(last[i])||0)+1);
  for(let [g,m] of parents){ck(m===gs[g],"non-splitting");out.forestChecks++}
  let id=gs.length;gs.push(a.length);a.sort((i,j)=>j-i);
  // The attained height at V is tested also for incoming representatives discarded here.
  if(isV&&2*t-C>=repH)for(let i of a)if(alive[i]&&!badH[i]){badH[i]=1;out.repHigh++}
  let reps=a.slice(0,kappa),set=new Set(reps);
  for(let i of a){if(set.has(i)){ck(alive[i],"no resurrection");out.repInc++}else if(alive[i]){alive[i]=0;out.discarded++}last[i]=id}
  ck(reps.length===Math.min(kappa,a.length),"cap");out.capChecks++;
  if(terminalFlag){terminal.push({a:a.slice(),C});out.terminalReps+=reps.length;}
  return reps;
 }
 for(let C=2*X;C<=7*X-2;C+=2){
  let i=head[C/2];head[C/2]=-1;if(i<0)continue;let V=new Map(),A=new Map();
  while(i>=0){let j=next[i];if(!V.has(times[i]))V.set(times[i],[]);V.get(times[i]).push(i);i=j}
  for(let [t,a] of V){
   let ended=a.filter(i=>ptr[i]===traces[i].length);
   if(ended.length){ck(ended.length===a.length&&a.every(i=>term[i]===1),"terminal V");inspect(a,C,t,true,true);continue;}
   inspect(a,C,t,true,false);
   for(let i of a){let ev=traces[i][ptr[i]];ck(ev.C===C&&ev.n>t,"trace");let k=ev.n*B+ev.p;if(!A.has(k))A.set(k,{ev,a:[]});A.get(k).a.push(i)}
  }
  for(let {ev,a} of A.values()){
   let stopped=a.filter(i=>term[i]===2&&ptr[i]+1===traces[i].length);ck(!stopped.length||stopped.length===a.length,"terminal A");
   let reps=inspect(a,C,ev.n,false,stopped.length>0);if(stopped.length)continue;
   let C1=C+ev.p-1,from=cell(C,W),to=cell(C1,W);
   for(let i of reps)if(!badH[i]&&ev.p>2*repH+2&&!badP[i]){ck(2*times[i]-C<repH&&ev.r>ev.p/8,"rough representative");badP[i]=1;out.repLarge++}
   if(from!==to){
    ck(ev.p>=y,"barrier");out.allExitGroups++;out.allExitMass+=a.length;out.allExitCap+=reps.length;
    let local=a.filter(i=>colour(i)===from);
    if(local.length){
     let lr=reps.filter(i=>colour(i)===from);ck(lr.length===Math.min(kappa,local.length),"local top representatives");
     out.exitGroups++;out.exitMass+=local.length;out.capExitMass+=lr.length;
     if(local.length<=kappa)out.smallExitMass+=local.length;else{out.largeExitMass+=local.length;out.largeExitGroups++}
     for(let i of local){ck(!depart[i],"first exit once");depart[i]=1}
     for(let i of lr){out.repExit++;if(badH[i]||badP[i])out.repExitBad++;else out.repExitOrdinary++;out.repExitHigh+=badH[i];out.repExitLarge+=badP[i];
      if(y>2*repH+2){ck(badH[i]||badP[i],"large barrier exit certificate");out.badExitChecks++}}
    }
   }
   for(let i of a){times[i]=ev.n;ptr[i]++;add(i,C1,false)}
  }
 }
 for(let i=0;i<N;i++)if(term[i]===1||term[i]===2)out.repBadUnion+=!!(badH[i]||badP[i]);
 ck(out.repExitBad<=out.repBadUnion,"unique bad representatives");
 for(let {a,C} of terminal){out.terminalGroups++;let c=cell(C,W),counts=new Map();
  for(let i of a){if(colour(i)===c){ck(!depart[i],"resident");out.residentTerminal++}else{ck(depart[i],"foreign");out.foreignTerminal++;let k=colour(i);counts.set(k,(counts.get(k)||0)+1)}}
  for(let m of counts.values()){out.capForeignTerminal+=Math.min(kappa,m);if(m<=kappa)out.smallForeignTerminal+=m}
 }
 ck(out.exitMass===out.foreignTerminal&&out.residentTerminal+out.foreignTerminal===S,"exit conservation");
 ck(out.capForeignTerminal<=out.capExitMass&&out.smallForeignTerminal<=out.capExitMass&&out.smallExitMass<=out.capExitMass,"capped transport");
 ck(out.repExit===out.capExitMass&&out.discarded+out.terminalReps===S,"representative conservation");
 return out;
}
for(const x of process.argv.slice(2).map(Number))for(const y of [5,7,11,13,17])console.log(JSON.stringify(audit(x,y)));
