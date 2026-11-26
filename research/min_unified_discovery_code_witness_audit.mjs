// Finite discovery codes, weighted within-code first-defect pairs and deficit-coordinate arithmetic.
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
  let Ps=[6,30,210],L=Math.max(4,Math.floor(B/8)),classes=new Map(),slots=new Map(),Aall=0,Fall=0,Fraw=0,sourceClock=0,wordChecks=0,defectChecks=0,assignedEvents=0,minorChecks=0,zeroC=0,zeroExcluded=0,signChecks=0,smallResidueChecks=0,nearSquareChecks=0,highFloor=Math.max(5,Math.floor(B**.25)),Dwait=2,bins=4,codeChecks=0,bothNew=0,bothNewDifferent=0,bothNewSame=0,oneNew=0,neitherNew=0,sameCodeBoth=0,sameCodeOne=0,sameCodeNeither=0,maxCodeLen=0,maxCodes=0,coordPairs=0,coordUnique=0,coordCRT=0,coordKeys=0;
  for(let t of tags)for(let j=0;j<t.path.length;j++){let e=t.path[j],key=e.C+"/"+e.p+"/"+e.n,ck=e.C+"/"+e.p+"/"+mod(e.n,6);
   if(!slots.has(key)){let s={e,refs:[],stable:[],cls:null,word:null,alpha:0,phi:0,raw:0};slots.set(key,s);if(!classes.has(ck))classes.set(ck,{slots:[],n:0,words:new Map()});s.cls=classes.get(ck);s.cls.slots.push(s)}
   let s=slots.get(key),v={id:t.id,j,e};s.refs.push(v);s.cls.n++;if(t.F-e.J>=L)s.stable.push(v);e.exit=s;
  }
  const gcd=(a,b)=>{while(b){let t=a%b;a=b;b=t}return a},lcm=(a,b)=>a/gcd(a,b)*b,rcap=BigInt(4*(T+B));
  function factors(C){let out=[];for(let v of [C-1,C+1])while(v>1){let f=spf[v];if(f>=highFloor&&f*f<=C+1)out.push(f);while(v%f===0)v/=f}return [...new Set(out)].sort((a,b)=>a-b)}
  function code(v){let path=tags[v.id].path,j=v.j+1,R=lcm(6n,BigInt(2*v.e.p)),records=[];
   while(path[j-1].J-v.e.J<L&&R<=rcap){let e=path[j++],p=BigInt(e.p);if(e.p>=highFloor&&R%p!==0n){let fs=factors(e.C),rank=fs.indexOf(e.p);ok(rank>=0,"eligible rank");records.push({C:e.C,p:e.p,w:e.w,rank,gainBin:Math.floor(bins*(e.C-v.e.J)/L),waitBin:Math.floor(bins*e.w/e.p),residue:e.w%(Dwait+1)})}R=lcm(R,2n*p)}
   maxCodeLen=Math.max(maxCodeLen,records.length);return {records,key:JSON.stringify(records.map(z=>[z.rank,z.gainBin,z.waitBin,z.residue]))}
  }
  function word(v){let a=tags[v.id].path,j=v.j+1,z=[];while(a[j-1].J-v.e.J<L){let e=a[j++];ok(e,"future room");z.push(e.p+":"+e.w)}return z.join(",")}
  function defect(a,b){let u=tags[a.id].path,v=tags[b.id].path,i=a.j+1,j=b.j+1,lag=b.e.n-a.e.n,R=lcm(6n,BigInt(2*a.e.p)),idx=0;
   while(u[i-1].J-a.e.J<L){let x=u[i++],y=v[j++];ok(x&&y&&x.C===y.C&&y.t-x.t===lag,"translated prefix");if(x.p!==y.p||x.w!==y.w){ok(lag%(2*x.p)!==0||lag%(2*y.p)!==0,"actual defect");ok(BigInt(Math.abs(lag))%R===0n&&R<=rcap,"common prefix radical");let xn=x.p>=highFloor&&R%BigInt(x.p)!==0n,yn=y.p>=highFloor&&R%BigInt(y.p)!==0n,ca=a.e.exit.code,cb=b.e.exit.code,same=ca.key===cb.key;
    if(xn&&yn){bothNew++;if(x.p!==y.p)bothNewDifferent++;else bothNewSame++;ok(ca.records[idx].C===x.C&&cb.records[idx].C===y.C,"common discovery index");
     if(same){sameCodeBoth++;ok(x.p===y.p&&Math.abs(x.w-y.w)>Dwait&&Math.abs(x.w-y.w)<x.p/bins+1e-9,"same-code wait interval");ok(Math.abs(lag-Math.round(lag/(2*x.p))*2*x.p)<x.p/bins+1e-9,"near periodic lag")}
    }else if(xn||yn){oneNew++;if(same){sameCodeOne++;let later=(xn?cb:ca).records[idx];ok(later&&later.C>x.C&&later.C-x.C<L/bins+1e-9,"paired delayed discovery")}}
    else{neitherNew++;if(same){sameCodeNeither++;ok((x.p<highFloor&&lag%(2*x.p)!==0)||(y.p<highFloor&&lag%(2*y.p)!==0),"small nonperiodic label")}}
    codeChecks++;return {C:x.C,same,xn,yn}}
   if(x.p>=highFloor&&R%BigInt(x.p)!==0n)idx++;R=lcm(R,BigInt(2*x.p));}
   throw Error("distinct word without defect")
  }
  for(let c of classes.values()){let stable=0;for(let s of c.slots)if(s.stable.length){s.word=word(s.stable[0]);s.code=code(s.stable[0]);s.accepted=new Map();if(!c.codes)c.codes=new Map();c.codes.set(s.code.key,(c.codes.get(s.code.key)||0)+s.stable.length);for(let v of s.stable){ok(word(v)===s.word,"same slot word");wordChecks++}c.words.set(s.word,(c.words.get(s.word)||0)+s.stable.length);stable+=s.stable.length}
   maxCodes=Math.max(maxCodes,c.codes?.size||0);for(let s of c.slots)if(s.stable.length){s.alpha=c.words.get(s.word)/c.n;for(let q of c.slots)if(q.stable.length&&q.word!==s.word){let z=defect(s.stable[0],q.stable[0]);defectChecks++;s.raw+=q.stable.length/c.n;if(z.C%10===0){s.phi+=q.stable.length/c.n;s.accepted.set(q,true)}}
    ok(near(s.alpha+s.raw,stable/c.n)&&s.phi<=s.raw+1e-10,"source partition")}
  }
  for(let t of tags){for(let e of t.path){if(!e.coeff)e.coeff=new Map();e.coeff.set(t.id,{a:0,f:0,raw:0,assigned:0,refs:[]})}
   for(let pi=0;pi<Ps.length;pi++){let P=Ps[pi],pending=[];for(let e of t.path){pending.push(e);let k=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!k)continue;let s=e.exit;
    if(t.F-e.J>=L){let first=P*Math.ceil(e.C/P);for(let v of pending){let z=v.coeff.get(t.id);z.a+=s.alpha/Ps.length;z.f+=s.phi/Ps.length;z.raw+=s.raw/Ps.length;z.assigned+=1/Ps.length;z.refs.push({pi,P,k,first,s});Aall+=v.w*s.alpha/Ps.length;Fall+=v.w*s.phi/Ps.length;Fraw+=v.w*s.raw/Ps.length;sourceClock+=v.w/Ps.length;assignedEvents++}}
    pending=[]
   }}
   for(let Y of [17,31,47,71]){let selected=t.path.filter(e=>e.p>=Y&&e.dp-6*(e.n%2)>0&&(e.dp-6*(e.n%2))/2<Y*Y),seen=new Set();
    for(let j=1;j<selected.length;j++){let a=selected[j-1],b=selected[j],E=b.C-a.J,v=b.dp-a.dp;if(E>4||Math.abs(v)>10)continue;
     let I=a.n%2,J=b.n%2,x=(a.dp-6*I)/2,y=(b.dp-6*J)/2,c=y-x;ok(a.p!==b.p&&c!==0,"close distinct high labels");let f=z=>{let out=[];while(z>1){let p=spf[z];if(p>=Y)out.push(p);z/=p}return out};ok(f(x).length===1&&f(x)[0]===a.p&&f(y).length===1&&f(y)[0]===b.p,"unique high deficit factors");
     ok(mod(a.C-(1-2*I),a.p)===0&&mod(a.C+a.p-1+E-(1-2*J),b.p)===0,"horizon CRT");
     let key=[x,c,E,I,J,a.C].join("/");ok(!seen.has(key),"unique physical starting candidate");seen.add(key);coordPairs++;coordUnique+=2;coordCRT++;coordKeys++;
    }
   }
   let sel=t.path.filter(e=>e.p>=11&&e.dp-6*(e.n%2)>0);
   for(let i=1;i<sel.length;i++){let a=sel[i-1],b=sel[i],E=b.C-a.J,v=b.dp-a.dp;if(E>4||Math.abs(v)>10)continue;let I=a.n%2,J=b.n%2,ee=1-2*I,ff=1-2*J,q=(a.C-ee)/a.p,s=(b.C-ff)/b.p,h1=(a.dp-6*I)/(2*a.p),h2=(b.dp-6*J)/(2*b.p);
    if(spf[s]!==s||!Number.isInteger(h1)||!Number.isInteger(h2))continue;let aa=E+ee-1-ff,c=v/2-3*(J-I),j=h1*s-h2*(q+1),LL=a.p*(q+1),xx=h1*a.p;
    ok(b.p*j===aa*h1-c*(q+1)&&a.p*j===aa*h2-c*s&&a.p*b.p*j===aa*xx-c*LL,"minor identities");minorChecks++;
    if(3+2.5*(T+B)<2*X-2){ok(xx<LL&&j!==0,"short canonical zero minor exclusion");zeroExcluded++}
    if(c===0){zeroC++;ok(xx%(a.p*b.p)===0,"zero displacement product")}
    if(a.p*b.p>3+2.5*(T+B)){nearSquareChecks++;ok(c!==0,"large product exclusion")}
    if(Math.abs(aa)*xx<LL&&c!==0){ok(j*c<0,"minor sign");signChecks++}
    if(j!==0&&Math.abs(j)<s&&xx<LL){ok(h1<q+1,"unique small multiplier range");smallResidueChecks++}
   }
  }
  ok(Aall+Fall<=sourceClock+1e-6&&Aall+Fraw<=sourceClock+1e-6&&sourceClock<=W+1e-6,"whole source budgets");
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
    let vertices=new Map(),U=0,V=0,baseU=0,baseV=0,exactU=0,exactV=0,eligibleGain=0,Zelig=0,Znot=0,Cstart=0,Cmerge=0,Cage=0,ret=0,Sret=0,retUp=0,err=0,retSteps=0,mergeSteps=0,ageSteps=0,addSteps=0,activePairs=0,checks=0,strictImprovements=0,softV=0,softU=0,hardImproves=0,Cret=0,Zstart=0,missingWait=0,flowLength=0,flowSinkD=0,flowStartD=0,flowWait2=0,flowTokens=0,immediate=0,coveredRetire=0,uncoveredRetire=0,flowMerges=0,flowAges=0,flowEnds=0,coveredA=0,coveredF=0,coveredRaw=0,weightedBack=0,weightedErr=0,wordOverlapChecks=0; let queues=new Map(),missingPerEvent=new Map();
    let start=starts.map((x,i)=>mode===0?x:(i%7===0?Infinity:x+h));
    for(let a of tags)if(!(start[a.id]<a.expiry))Znot+=a.df;
    const vert=(C,t)=>{let k=C+"/"+t;if(!vertices.has(k))vertices.set(k,{C,t,ins:[],out:null});return vertices.get(k)};
    const mono=(ids,labels)=>{let n=ids.length,m=new Map();for(let i of ids)m.set(labels[i],(m.get(labels[i])||0)+1);return (n*n-[...m.values()].reduce((s,v)=>s+v*v,0))/(n+R)};
    const hard=(ids,labels)=>{let m=new Map();for(let i of ids)m.set(labels[i],(m.get(labels[i])||0)+1);return Math.max(0,ids.length-R-Math.max(0,...m.values()))};
    const weight=(ids,x,strict,soft=false)=>{let gr=new Map();for(let i of ids){let c=comp(i,x,strict);if(!gr.has(c))gr.set(c,[]);gr.get(c).push(i)}let a=0;for(let g of gr.values())a+=soft?Math.min(mono(g,color),mono(g,firstLarge)):Math.min(hard(g,color),hard(g,firstLarge));return a};
    const D=(e,x)=>e.d+(x-e.C)*(e.dp-e.d)/(e.J-e.C);
    function sink(queue,k,x,d,kind){ok(Number.isInteger(k)&&k>=0&&k<=queue.length,'uncovered sink capacity');for(let j=0;j<k;j++){let z=queue.pop();ok(x>=z.x&&d>=z.d-(x-z.x)-1e-7,'uncovered path cone');flowLength+=x-z.x;flowSinkD+=d;flowWait2+=x-z.x+d-z.d;flowEnds++;}if(kind==='merge')flowMerges+=k;if(kind==='age')flowAges+=k;}
    function change(live,x,d,add,queue){let old=weight(live,x,true),after=weight(live,x,false);ok(after>=old-1e-9,"age monotone");Cage+=d*(after-old);sink(queue,after-old,x,d,'age');if(after>old+1e-9)ageSteps++;
     for(let i of add){let before=weight(live,x,false);live.push(i);let delta=weight(live,x,false)-before;ok(delta===0||delta===1,"unit insertion");Cstart+=d*delta;Zstart+=d;flowStartD+=d;flowTokens++;if(delta){immediate++;flowSinkD+=d;flowEnds++}else queue.push({x,d});addSteps++}}
    for(let e of ordered){
     let ids=e.ids.filter(i=>start[i]<tags[i].expiry&&start[i]<e.J&&tags[i].expiry>e.C);if(!ids.length)continue;
     let points=[e.C,e.J,...ids.flatMap(i=>[start[i],tags[i].expiry]).filter(x=>e.C<x&&x<e.J)];
     for(let i of ids){let j=i;while(up[j]>=0){j=up[j];let x=when[j];if(e.C<x&&x<e.J)points.push(x);if(x>=e.J)break}}
     let cuts=[...new Set(points)].sort((a,b)=>a-b),live=ids.filter(i=>start[i]<e.C),v=vert(e.C,e.t);ok(!v.out,"one out");v.out=live.slice();let key=e.C+'/'+e.t,queue=queues.get(key)||[];queues.delete(key);let beforeMerge=v.ins.reduce((s,g)=>s+weight(g,e.C,true),0),mergeDelta=weight(live,e.C,true)-beforeMerge;ok(queue.length===live.length-beforeMerge,'incoming uncovered flow');sink(queue,mergeDelta,e.C,e.d,'merge');change(live,e.C,e.d,ids.filter(i=>start[i]===e.C),queue);
     for(let k=0;k+1<cuts.length;k++){let x=cuts[k],y=cuts[k+1],dx=y-x,n=live.length,wgt=weight(live,x,false),base=mono(live,color),A=0;
      for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let a=live[i],b=live[j],z=pairStarts.get(pkey(a,b));if(z!==undefined&&z<=x){ok(comp(a,x,false)===comp(b,x,false)&&color[a]!==color[b]&&firstLarge[a]!==firstLarge[b],"retained pair coverage");A+=2;activePairs++}}
      let old=A/Math.max(d0,e.ids.length),omega=e.w/(e.J-e.C),epsilon=(R+capP)*n/d0,soft=weight(live,x,false,true);ok(old<=wgt+epsilon+1e-8&&wgt<=soft+1e-8&&soft<=base+1e-8,"envelope comparison");ok(queue.length===n-wgt,'uncovered occupancy');softU+=soft*dx;softV+=soft*dx*omega;if(wgt<soft-1e-8)hardImproves++;missingWait+=(n-wgt)*dx*omega;if(wgt<base-1e-8)strictImprovements++;
      let gr=new Map();for(let i of live){let c=comp(i,x,false);if(!gr.has(c))gr.set(c,[]);gr.get(c).push(i)}
      let aSum=0,fSum=0;for(let g of gr.values()){let cv=Math.min(hard(g,color),hard(g,firstLarge))/g.length;for(let i of g){let z=e.coeff.get(i),deg=g.filter(j=>j!==i&&pairStarts.has(pkey(i,j))&&pairStarts.get(pkey(i,j))<=x).length;
       let ba=z.a*deg/Math.max(d0,e.exit.refs.length),er=z.a*(R+capP)/d0;ok(ba<=z.a*cv+er+1e-9,"word-weighted row upper");weightedBack+=ba*dx*omega;weightedErr+=er*dx*omega;coveredA+=z.a*cv*dx*omega;coveredF+=z.f*cv*dx*omega;coveredRaw+=z.raw*cv*dx*omega;aSum+=z.a*cv;fSum+=z.f*cv;
       let key=e.C+'/'+e.t+'/'+i;missingPerEvent.set(key,(missingPerEvent.get(key)||0)+cv*dx*omega);
      }}ok(aSum+fSum<=wgt+1e-8,"no double coverage");wordOverlapChecks++;
      U+=wgt*dx;V+=wgt*dx*omega;baseU+=base*dx;baseV+=base*dx*omega;exactU+=old*dx;exactV+=old*dx*omega;err+=epsilon*dx*omega;eligibleGain+=n*dx;checks++;
      let stay=live.filter(i=>tags[i].expiry>y),kr=n-stay.length;
      if(kr){let drop=weight(live,y,true)-weight(stay,y,true),d=D(e,y),ex=d*(drop-kr),bound=0;ok(Number.isInteger(drop)&&drop>=0&&drop<=kr,"exact retirement bound");ret+=d*drop;Zelig+=d*kr;Sret+=ex;Cret+=d*(kr-drop);coveredRetire+=drop;uncoveredRetire+=kr-drop;sink(queue,kr-drop,y,d,'retire');retUp+=bound;retSteps++}
      live=stay;if(y<e.J)change(live,y,D(e,y),ids.filter(i=>start[i]===y),queue)
     }
     if(live.length){vert(e.J,e.n).ins.push(live.slice());let k=e.J+'/'+e.n;if(!queues.has(k))queues.set(k,[]);queues.get(k).push(...queue)}else ok(queue.length===0,'no ghost flow')
    }
    for(let v of vertices.values()){let out=v.out||[],flat=v.ins.flat();ok(flat.length===out.length&&new Set(flat).size===flat.length&&flat.every(i=>out.includes(i)),"flow");
     let delta=weight(out,v.C,true)-v.ins.reduce((s,g)=>s+weight(g,v.C,true),0);ok(delta>=-1e-9,"physical merge");Cmerge+=(2*v.t-v.C)*delta;if(delta>1e-9)mergeSteps++}
    ok(near(2*V,U+ret-Cstart-Cmerge-Cage)&&near(ret,Zelig-Cret)&&near(Sret,-Cret),"exact graph identity");ok(queues.size===0&&flowTokens===flowEnds,"flow closure");ok(near(flowLength,eligibleGain-U)&&near(flowSinkD,Cstart+Cmerge+Cage+Cret)&&near(flowStartD,Zstart)&&near(flowWait2,2*missingWait),"path sum");ok(near(eligibleGain-U+Cstart+Cmerge+Cage+Cret,Zstart+2*missingWait),"missing clock identity");
    ok(V<=baseV+1e-7&&exactV<=V+err+1e-7&&Sret<=retUp+1e-7&&Zelig+Znot<=Z+N*h+1e-6,"global inequalities");
    let missingA=Aall-coveredA,missingF=Fall-coveredF,missingRaw=Fraw-coveredRaw,unused=W-Aall-Fall,coveredUnused=V-coveredA-coveredF,missingUnused=W-V-missingF,overlapGap=W-Fall-coveredA;
    ok(weightedBack<=coveredA+weightedErr+1e-6&&coveredA+coveredF<=V+1e-6,"weighted global upper");ok(near(overlapGap,unused+missingA)&&near(overlapGap,missingUnused+coveredUnused)&&missingUnused>=-1e-6,"exact overlap cancellation");
    let unassignedMissing=0,atomClasses=new Map(),assignedMissing=0,missingByWordA=0;
    for(let t of tags)for(let e of t.path){let z=e.coeff.get(t.id),miss=e.w-(missingPerEvent.get(e.C+'/'+e.t+'/'+t.id)||0);ok(miss>=-1e-7,"event missing");unassignedMissing+=miss*(1-z.assigned);
     for(let ref of z.refs){let s=ref.s,mass=miss/(Ps.length*ref.k);assignedMissing+=mass*ref.k;
      for(let k=0;k<ref.k;k++){let K=ref.first+k*ref.P,key=ref.pi+'/'+K+'/'+s.e.C+'/'+s.e.p+'/'+mod(s.e.n,6),a=atomClasses.get(key);if(!a){a={P:ref.P,n:s.cls.n,words:new Map(),k:s.cls.words.size,cls:s.cls,rows:new Map(),slotMass:new Map()};atomClasses.set(key,a)}
       let w=a.words.get(s.word)||{mass:0,alpha:s.alpha,stable:s.cls.words.get(s.word)};w.mass+=mass;a.words.set(s.word,w);missingByWordA+=mass*s.alpha;a.rows.set(t.id,(a.rows.get(t.id)||0)+mass);a.slotMass.set(s,(a.slotMass.get(s)||0)+mass);
      }
     }
    }
    let cappedSquare=0,lowWordMass=0,lowWordSquare=0,rawCap=0,wordAtoms=0;
    let cap=3;for(let a of atomClasses.values())for(let m of a.rows.values())cap=Math.max(cap,m*Ps.length/a.P);
    for(let a of atomClasses.values()){let total=0,den=cap*a.P*a.n/Ps.length;rawCap+=den;for(let w of a.words.values()){ok(w.mass<=cap*a.P*w.stable/Ps.length+1e-7,"word capacity");cappedSquare+=w.mass*w.mass/den;total+=w.mass;wordAtoms++}
     if(a.k<=3){lowWordMass+=total;lowWordSquare+=total*total/(3*den)}
    }
    ok(near(assignedMissing+unassignedMissing,W-V)&&near(missingByWordA,missingA),"assigned missing mass");ok(cappedSquare<=missingA+1e-6&&lowWordSquare<=cappedSquare+1e-6&&lowWordMass*lowWordMass<=3*rawCap*lowWordSquare+1e-5*Math.max(1,lowWordMass*lowWordMass),"collision bound");
    let codeSquare=0,codeCapacity=0,sameCodePartner=0,sameCodeAccepted=0,codeRejected=0,pairSampleMass=0,pairRejectMass=0,mutualPairs=0,mutualTriples=0,codeAtomCount=0,maxOccupied=0;
    for(let a of atomClasses.values()){let cm=new Map(),den=cap*a.P*a.n/Ps.length;for(let [s,m] of a.slotMass){if(!cm.has(s.code.key))cm.set(s.code.key,[]);cm.get(s.code.key).push([s,m])}
     maxOccupied=Math.max(maxOccupied,cm.size);codeCapacity+=den*cm.size;
     for(let [k,g] of cm){let total=g.reduce((z,[s,m])=>z+m,0),ncode=a.cls.codes.get(k),mass=total*total/den;ok(total<=cap*a.P*ncode/Ps.length+1e-7,"code row capacity");codeSquare+=mass;sameCodePartner+=total*ncode/a.n;pairSampleMass+=mass;codeAtomCount++;
      for(let [s,m] of g){for(let q of a.cls.slots)if(q.stable.length&&q.code.key===k){if(s.accepted.has(q))sameCodeAccepted+=m*q.stable.length/a.n;else codeRejected+=m*q.stable.length/a.n}
       for(let [q,v] of g)if(!s.accepted.has(q))pairRejectMass+=m*v/den;else if(q.accepted.has(s)&&s.e.n<q.e.n){mutualPairs++;for(let [z,zz] of g)if(z.e.n>q.e.n&&s.accepted.has(z)&&z.accepted.has(s)&&q.accepted.has(z)&&z.accepted.has(q))mutualTriples++}
      }
     }
    }
    ok(near(sameCodePartner,sameCodeAccepted+codeRejected)&&near(pairSampleMass,codeSquare),"code partition");ok(codeSquare<=sameCodePartner+1e-6&&pairRejectMass<=codeRejected+1e-6&&codeRejected<=missingUnused+1e-6,"weighted same-code rejection");ok(assignedMissing*assignedMissing<=codeCapacity*codeSquare+1e-5*Math.max(1,assignedMissing*assignedMissing),"global code collision");
    results.push({X,focus,L0,mode,N,events,highFloor,Dwait,bins,codeChecks,bothNew,bothNewDifferent,bothNewSame,oneNew,neitherNew,sameCodeBoth,sameCodeOne,sameCodeNeither,maxCodeLen,maxCodes,coordPairs,coordUnique,coordCRT,coordKeys,codeSquare,codeCapacity,sameCodePartner,sameCodeAccepted,codeRejected,pairSampleMass,pairRejectMass,mutualPairs,mutualTriples,codeAtomCount,maxOccupied,sourceClock,Aall,Fall,Fraw,wordChecks,defectChecks,assignedEvents,minorChecks,zeroC,zeroExcluded,nearSquareChecks,signChecks,smallResidueChecks,coveredA,coveredF,coveredRaw,weightedBack,weightedErr,missingA,missingF,missingRaw,unused,coveredUnused,missingUnused,overlapGap,wordOverlapChecks,assignedMissing,unassignedMissing,wordAtoms,cap,cappedSquare,lowWordMass,lowWordSquare,rawCap,packets:packetSizes.length,P,freshP,capP,R,d0,allowed,forbidden,staticPairs:pairStarts.size,unions,activePairs,checks,strictImprovements,retSteps,mergeSteps,ageSteps,addSteps,U,V,softU,softV,hardImproves,Cret,Zstart,missingWait,flowLength,flowSinkD,flowStartD,flowWait2,flowTokens,immediate,coveredRetire,uncoveredRetire,flowMerges,flowAges,flowEnds,baseU,baseV,exactU,exactV,eligibleGain,Z,Zelig,Znot,Cstart,Cmerge,Cage,Sret,retUp,err,objective:U-Cstart-Cmerge-Cage+Sret-Znot});
   }
  }
 }
 // Exhaustive small fixed-color configurations: overlapping colors and independent retirements.
 let tests=0,strict=0;const hard=(ids,c,R)=>{let m=new Map();for(let i of ids)m.set(c[i],(m.get(c[i])||0)+1);return Math.max(0,ids.length-R-Math.max(0,...m.values()))};
 let ids=[0,1,2,3,4,5];for(let mask=0;mask<729;mask++){let z=mask,c=[];for(let i=0;i<6;i++){c.push(z%3);z=Math.floor(z/3)}let P=Math.max(...[0,1,2].map(j=>c.filter(k=>j===k).length));for(let R of [1,2,3])for(let b=0;b<64;b++){let a=ids.filter(i=>b>>i&1),d=ids.filter(i=>!(b>>i&1)),f=hard(ids,c,R),fa=hard(a,c,R),fb=hard(d,c,R);ok(f>=fa+fb&&f-fa<=d.length,'synthetic superadditive and Lipschitz');let S2=[0,1,2].reduce((s,j)=>s+c.filter(k=>j===k).length**2,0),soft=(36-S2)/(6+R);ok(f<=soft+1e-9,'synthetic nested');for(let b0 of [2,4,8,16])ok((36-S2)/Math.max(b0,6)<=f+(R+P)*6/b0+1e-9,'synthetic error');tests++;if(f<soft-1e-8)strict++}}
 return {results,synthetic:{tests,strict}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
