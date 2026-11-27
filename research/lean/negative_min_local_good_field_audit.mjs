// Reverse charge locality, history-only contact energy, and good-phase mask.
// Reproduce: node research/lean/negative_min_local_good_field_audit.mjs
function audit(){
 let checks=0,ticks=0,roots=0,windows=0,pairs=0,localTests=0,maskTests=0,prefixTests=0,supportTests=0,phaseTests=0;
 const ck=(b,s)=>{checks++;if(!b)throw Error(s)};
 function gcd(a,b){a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a}
 function lpf(n){if(n<2)return 0;for(let p=2;p*p<=n;p++)if(n%p===0)return p;return n}
 function win(x,n){return lpf(gcd(n%2===0?x+1:x-1,n%2===0?n:n-2))}
 function literal(x,n){for(let p=3;p<=x+1;p+=2)if(lpf(p)===p&&(n%2===0?((x+1)%p===0&&n%(2*p)===0):((x-1)%p===0&&(n%(2*p)+2*p)%(2*p)===p+2)))return p;return 0}
 function ledger(ps,c){
  let joint=0,low=0,broad=0,seen=new Set(),ns=new Set(),paid=false,J=[0],N=[0];
  for(let p of ps){
   if(p>=c.Ystar){broad=0;seen.clear();paid=false}
   else{
    if(c.z<p&&p<c.Yb)broad++;
    if(c.z<p&&p<c.Y0)seen.add(p);
    if(!paid&&broad>c.K&&seen.size>c.div){joint++;paid=true}
   }
   if(p>=c.Y0)ns.clear();else if(c.z<p){
    if(!ns.size)low++;ns.add(p);if(ns.size>c.div)ns.clear()
   }
   J.push(joint);N.push(low)
  }
  return {J,N,C:J.map((v,i)=>c.wS*v+c.wL*N[i])}
 }
 function blockScore(ps,c){
  let b=0,s=new Set();for(let p of ps){if(p>=c.Ystar)break;
   if(c.z<p&&p<c.Yb)b++;if(c.z<p&&p<c.Y0)s.add(p)
  }return {value:+(b>c.K&&s.size>c.div),b,s}
 }
 function classify(ps,c){
  let events=[];for(let i=0,prev=-1;i<ps.length;i++)if(ps[i]){events.push({i,p:ps[i],wait:i-prev});prev=i}
  let classes=[],targets=[];
  for(let j=0;j<events.length;j++){
   let {p,i}=events[j],type,target=-1;
   if(p<c.Y0)type="low";
   else if(p>=c.Pmax)type="near";
   else if(p>=c.Y1)type=blockScore(ps.slice(i+1),c).value?"highBad":"highGood";
   else {
    let used=new Set([p]),news=0;type="medTail";
    for(let k=j+1;k<events.length;k++){
     let e=events[k],q=e.p;target=k;
     if(q>=c.U*c.Y1){type="medBig";break}
     if(c.z<q&&q<c.Y0){type="medNarrow";break}
     if(q>=c.Y0&&!used.has(q)){
      used.add(q);if(e.wait**5<q**3){type="medFast";break}
      if(++news===c.h){type="medSlow";break}
     }
    }
    if(type==="medTail")target=events.length
   }
   classes[j]=type;targets[j]=target;
  }
  let phase=[],end=[],last=0;
  for(let j=0;j<events.length;j++){
   let e=events[j];ck(e.wait<=3*(e.p-1),"complete phase gain-time");
   for(let i=last;i<=e.i;i++){phase[i]=classes[j];end[i]=e.i}
   last=e.i+1
  }
  for(let i=last;i<ps.length;i++){phase[i]="terminal";end[i]=ps.length}
  return {phase,end,events,classes,targets}
 }
 const isGood=t=>["near","highGood","medFast","medSlow","terminal"].includes(t);
 function peak(fs){let h=0;return fs.map(v=>h=Math.max(h,v))}
 function trace(A,start,T,c,literalCheck){
  let n=3-A/2,x=A,ps=[],xs=[x];
  while(n<start+T){let p=win(x,n+1);if(literalCheck)ck(p===literal(x,n+1),"literal tick");
   ps.push(p);if(p)x-=p-1;xs.push(x);n++;ticks++;
  }
  let age=start-(3-A/2),C=ledger(ps,c),F=ps.map((_,i)=>ledger(ps.slice(i),c).C.at(-1));F.push(0);
  let H=ps.map((_,i)=>Math.max(0,i-age)-C.C[i]);H.push(T-C.C.at(-1));
  let f=H.map((_,i)=>Math.max(0,i-age)-(F[0]-F[i])),E=c.wS+c.wL;
  let g=peak(f),h=peak(H),cl=classify(ps,c),badHigh=0,lowTime=0,lowGain=0;
  for(let i=0;i<ps.length;i++){
   ck(Math.abs(f[i]-H[i])<=E&&Math.abs(g[i]-h[i])<=E,"prefix and peak defect");
   ck(Math.abs((g[i]-f[i])-(h[i]-H[i]))<=2*E,"debt defect");
   ck(F[i]>=F[i+1],"nonnegative potential");
   const p=ps[i],B=blockScore(ps.slice(i+1),c),BB=blockScore(ps.slice(i),c);
   let js=ledger(ps.slice(i),c).J.at(-1),jt=ledger(ps.slice(i+1),c).J.at(-1);
   ck(js-jt===(p>=c.Ystar?0:BB.value-B.value),"exact local joint decrement");
   if(js>jt){
    ck(p<c.Ystar&&((c.z<p&&p<c.Yb&&B.b===c.K)||(c.z<p&&p<c.Y0&&!B.s.has(p)&&B.s.size===c.div)),"reverse threshold cause");
    localTests++;
    let tail=ps.slice(i+1);let j=tail.findIndex(q=>q>=c.Ystar);if(j>=0)tail=tail.slice(0,j);
    let ev=tail.filter(q=>q>0),broad=ev.filter(q=>c.z<q&&q<c.Yb),med=ev.filter(q=>q>=c.Yb);
    if(broad.length===c.K){
     let reg=0,maxReg=0;
     for(let q of ev){if(c.z<q&&q<c.Yb){maxReg=Math.max(maxReg,reg);reg=0}else reg+=q-1}
     maxReg=Math.max(maxReg,reg);
     ck(ev.reduce((s,q)=>s+q-1,0)<=(broad.length+1)*maxReg+broad.reduce((s,q)=>s+q-1,0),"mixed support segmentation");
     supportTests++
    }
   }
   if(cl.phase[i]==="highBad")badHigh++;
   if(cl.phase[i]==="low")lowTime++;
   if(p&&p<c.Y0)lowGain+=p-1;
   ck(badHigh<=3*c.Pmax*(C.J[i+1]+2),"bad high prefix charged to block and at most two tails");
   ck(lowTime<=3*(lowGain+c.Y0),"low completed gain and partial tail");
   prefixTests++;
  }
  ck(Math.abs(f.at(-1)-H.at(-1))<=E,"final defect");
  return {A,age,ps,xs,C,F,H,f,g,h,cl};
 }
 function runWindow(rs,T,M,c){
  let E=c.wS+c.wL,N=rs.length,row={N,phaseCount:0,goodPhaseCount:0,clippedInteriorGood:0,clippedTerminal:0,clippedNear:0,goodRawEnergy:0,S:0,Q:0,Qlo:0,Qhi:0,Qraw:0,zeroPairs:0,excludedPairs:0,recordV:0,good:0,clippedGood:0,clippedAll:0,classes:{},contactPairs:0,maskDominatesActualCost:0};
  let cohorts=[],first=Array.from({length:N},()=>Array(N).fill(-1)),alive=new Set(),dead=new Set(),lastAge=Math.max(...rs.map(r=>r.age));
  // Process all absolute ticks, including births. Fixed ascending A priority.
  for(let u=-lastAge;u<T;u++){
   let by=new Map(),full=new Map();
   for(let i=0;i<N;i++){let r=rs[i],k=r.age+u;if(k<0)continue;
    if(k===0)alive.add(i);
    let x=r.xs[k];if(!full.has(x))full.set(x,[]);full.get(x).push(i);
    if(alive.has(i)){if(!by.has(x))by.set(x,[]);by.get(x).push(i)}
   }
   for(let [x,ids] of by){ids.sort((i,j)=>rs[i].A-rs[j].A);for(let i of ids.slice(M)){alive.delete(i);dead.add(i)}}
   for(let [x,ids] of full){
    let live=ids.filter(i=>alive.has(i)),m=Math.min(M,ids.length);
    ck(live.length===m,"simultaneous full-cap occupancy");if(u<0)continue;
    let types=ids.map(i=>rs[i].cl.phase[rs[i].age+u]);ck(types.every(t=>t===types[0]),"mask is shared physical-bin field");
    let type=types[0],good=isGood(type);
    row.classes[type]=(row.classes[type]||0)+ids.length;
    row.clippedAll+=m;if(good){row.good+=ids.length;row.clippedGood+=m;row.goodRawEnergy+=ids.length**2;if(type==="terminal")row.clippedTerminal+=m;else if(type==="near")row.clippedNear+=m;else row.clippedInteriorGood+=m}
    let gains=ids.map(i=>{let r=rs[i],k=r.age+u;return r.g[k+1]-r.g[k]});
    ck(gains.every(g=>g===0||g===1),"record increments binary at D=1");
    let mass=gains.reduce((a,b)=>a+b,0);row.S+=mass;row.Q+=mass*mass;row.Qraw+=ids.length**2;row.recordV+=Math.min(M,mass);
    for(let i of ids)for(let j of ids)if(first[i][j]<0)first[i][j]=u;
    maskTests++;
   }
   ck([...alive].every(i=>!dead.has(i)),"no resurrection");
  }
  // Independent phase integral: no tick-by-tick mass sum. A root enters
  // each stationary phase once, then remains until its common end.
  let phaseMap=new Map();
  for(let i=0;i<N;i++){
   let r=rs[i];
   for(let u=0;u<T;){
    let k=r.age+u,x=r.xs[k],end=Math.min(T-1,r.cl.end[k]-r.age),key=x+":"+end,type=r.cl.phase[k];
    ck(end>=u,"phase time order");
    if(!phaseMap.has(key))phaseMap.set(key,{end,type,entries:[]});
    let p=phaseMap.get(key);ck(p.type===type,"shared phase flag");p.entries.push({i,u});
    for(let t=u;t<=end;t++)ck(r.xs[r.age+t]===x&&r.cl.phase[r.age+t]===type,"constant stationary phase");
    u=end+1;
   }
  }
  let all=0,good=0,uncapped=0,energy=0,goodEnergy=0;
  for(let p of phaseMap.values()){
   p.entries.sort((a,b)=>a.u-b.u||a.i-b.i);
   ck(new Set(p.entries.map(a=>a.i)).size===p.entries.length,"one arrival per root per phase");
   let times=p.entries.map(a=>p.end-a.u+1);
   let v=times.slice(0,M).reduce((s,x)=>s+x,0),mass=times.reduce((s,x)=>s+x,0),q=0;
   for(let x of times)for(let y of times)q+=Math.min(x,y);
   all+=v;energy+=q;
   if(isGood(p.type)){good+=v;uncapped+=mass;goodEnergy+=q;row.goodPhaseCount++}
   row.phaseCount++;phaseTests++;
  }
  ck(all===row.clippedAll&&good===row.clippedGood&&uncapped===row.good&&energy===row.Qraw&&goodEnergy===row.goodRawEnergy,"phase integral equals tick integral");
  let q=0,lo=0,hi=0,suffixCache=new Map();
  for(let i=0;i<N;i++)for(let j=0;j<N;j++){
   let u=first[i][j];if(u<0)continue;let a=rs[i],b=rs[j],ka=a.age+u,kb=b.age+u;
   let ar=a.g.at(-1)-a.g[ka],br=b.g.at(-1)-b.g[kb],p=Math.min(ar,br),raw=T-u;
   let key=u+":"+a.xs[ka],H=suffixCache.get(key);
   if(H===undefined){
    let C=ledger(a.ps.slice(ka),c).C;H=Math.max(...C.map((x,k)=>k-x));suffixCache.set(key,H)
   }
   let debt=Math.max(a.h[ka]-a.H[ka],b.h[kb]-b.H[kb]),lower=Math.max(0,H-debt-3*E),upper=Math.min(raw,Math.max(0,H-debt+3*E));
   ck(lower<=p&&p<=upper,"local pair envelope");
   let exact=0;for(let t=u;t<T;t++){
    let x=a.age+t,y=b.age+t;ck(a.xs[x]===b.xs[y],"permanent contact");
    exact+=Math.min(a.g[x+1]-a.g[x],b.g[y+1]-b.g[y])
   }ck(exact===p,"pair min of cumulative peak increases");
   let hmin=Math.min(a.h.at(-1)-a.h[ka],b.h.at(-1)-b.h[kb]);
   ck(Math.abs(hmin-p)<=2*E,"history-only sharper peak-rise envelope");
   q+=p;lo+=Math.max(lower,hmin-2*E,0);hi+=Math.min(upper,hmin+2*E);pairs++;row.contactPairs++;
   if(!p)row.zeroPairs++;if(Math.min(upper,hmin+2*E)===0)row.excludedPairs++;
  }
  ck(q===row.Q,"pair energy exact");row.Qlo=lo;row.Qhi=hi;
  ck(lo<=q&&q<=hi&&hi<=row.Qraw,"global energy bounds");
  // Test arbitrary irreversible deadline policies under the cap.
  let rand=123;for(let it=0;it<24;it++){
   let d=rs.map(()=>{rand=(Math.imul(rand,1664525)+1013904223)>>>0;return rand%(T+1)}),alive=new Set(rs.map((_,i)=>i)),tot=0,bad=0,g=0;
   for(let u=0;u<T;u++){
    let map=new Map();for(let i of alive){if(u>=d[i]){alive.delete(i);continue}
     let x=rs[i].xs[rs[i].age+u];if(!map.has(x))map.set(x,[]);map.get(x).push(i)}
    for(let ids of map.values()){ids.sort((i,j)=>d[j]-d[i]||i-j);for(let i of ids.slice(M))alive.delete(i);
     let l=ids.slice(0,M);tot+=l.length;for(let i of l){if(isGood(rs[i].cl.phase[rs[i].age+u]))g++;else bad++}}
   }ck(g+bad===tot&&g<=row.clippedGood,"good mask optimal for arbitrary deadline clip");row.maskDominatesActualCost++;
  }
  return row
 }
 let results=[];
 for(let cfg of [{R:600,T:18,M:1,sample:34},{R:2400,T:36,M:2,sample:50},{R:12000,T:72,M:4,sample:40},{R:48000,T:144,M:8,sample:20},{R:192000,T:288,M:16,sample:15}]){
  let {R,T,M,sample}=cfg,W=T,c={z:3,Y0:13,Yb:23,Ystar:31,Y1:47,Pmax:Math.max(48,Math.floor(T*.75)),K:2,div:1,h:2,U:4,wS:2,wL:1},count=Math.ceil((R/6+1)/(W/6)),total={...cfg,N:0,phaseCount:0,goodPhaseCount:0,clippedInteriorGood:0,clippedTerminal:0,clippedNear:0,goodRawEnergy:0,S:0,Q:0,Qlo:0,Qhi:0,Qraw:0,zeroPairs:0,excludedPairs:0,recordV:0,good:0,clippedGood:0,clippedAll:0,contactPairs:0,maskDominatesActualCost:0,classes:{}};
  for(let j=0;j<Math.min(sample,count);j++){
   let base=R+Math.floor(j*count/Math.min(sample,count))*W,start=3-base/2,rs=[];
   for(let A=base;A<base+W&&A<=2*R;A+=6)rs.push(trace(A,start,T,c,R===600));
   if(!rs.length)continue;windows++;roots+=rs.length;
   let row=runWindow(rs,T,M,c);for(let [k,v] of Object.entries(row)){if(k==="classes"){for(let [t,n] of Object.entries(v))total.classes[t]=(total.classes[t]||0)+n}else total[k]+=v}
  }
  let NT=total.N*T;total.normalized={s:total.S/NT,e:total.Q/NT,elo:total.Qlo/NT,ehi:total.Qhi/NT,raw:total.Qraw/NT,v:total.recordV/NT,good:total.good/NT,clippedGood:total.clippedGood/NT,clippedAll:total.clippedAll/NT,clippedInteriorGood:total.clippedInteriorGood/NT,clippedTerminal:total.clippedTerminal/NT,clippedNear:total.clippedNear/NT,goodRawEnergy:total.goodRawEnergy/NT};
  results.push(total)
 }
 return {checks,ticks,roots,windows,pairs,localTests,maskTests,prefixTests,supportTests,phaseTests,results}
}
console.log(JSON.stringify(audit()));
