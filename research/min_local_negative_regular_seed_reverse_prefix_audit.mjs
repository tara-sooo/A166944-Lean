// Selected zero-relay CRT seeds and actual growing-prefix reverse-word capacity.
// node research/min_local_negative_regular_seed_reverse_prefix_audit.mjs [R ...]
function audit(Rs){
 const mod=(a,b)=>(a%b+b)%b,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v);
 const primes=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113];
 const spf=new Int32Array(2*Math.max(...Rs)+5);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p;}return a}
 function nxt(x,n,ps=null){let p=Infinity,w=Infinity,e=0;
  for(let s of [-1,1])for(let r of ps||fs(x-s))if(mod(x-s,r)===0){
   let d=mod((s===-1?0:r+2)-n,2*r)||2*r;
   if(d<w||d===w&&r<p){p=r;w=d;e=s}
  }
  return {p,w,e};
 }
 function run(v,h,ps){
  let x=v,n=h-v/2,ev=[],Q=2*ps.reduce((a,b)=>a*b,1);
  for(;;){let e=nxt(x,n,ps);if(!Number.isFinite(e.p))break;
   ev.push({x,n,...e});x-=e.p-1;n+=e.w;
   ck(Math.floor(v/Q)===Math.floor(x/Q)&&n+x/2>=0,"restricted wall and height");
  }
  return {x,n,g:v-x,h:n+x/2,k:ev.length,ev};
 }
 let seeds=new Map();
 let ps=[3],F=12,keep=new Uint8Array(F/2).fill(1);
 function store(z){
  let a=new Uint32Array(F/2),gain=new Uint32Array(F/2),length=new Uint32Array(F/2),target=new Uint32Array(F/2);
  for(let v=0;v<F;v+=4)for(let hi=0;hi<2;hi++){
   let i=v/2+hi,o=run(v,3*hi,ps);gain[i]=o.g;length[i]=o.k;target[i]=o.x;if(keep[i])a[o.x/2]++;
  }
  seeds.set(z,{ps:[...ps],F,keep:keep.slice(),a,gain,length,target,K:[...a].reduce((s,x)=>s+x*x,0)/F});
 }
 store(3);
 for(let p of [5,7,11,13]){
  let newF=F*p,newKeep=new Uint8Array(newF/2),qs=[...ps,p];
  for(let v=0;v<F;v+=4)for(let hi=0;hi<2;hi++){
   let i=v/2+hi;if(!keep[i])continue;let o=run(v,3*hi,ps);
   for(let j=0;j<p;j++){
    let x=v+j*F,a=run(x,3*hi,qs),at=a.ev.findIndex(e=>e.p===p),good=at===-1;
    if(at===o.k&&o.h<=(p-3)/2){let e=a.ev[at],y=e.x-p+1;
     if(!Number.isFinite(nxt(y,e.n+e.w,ps).p)){ck(a.k===o.k+1&&a.x===y,"zero relay");good=true;}
    }
    if(good)newKeep[x/2+hi]=1;
   }
  }
  ps=qs;F=newF;keep=newKeep;store(p);
 }
 // Complete small CRT check of reverse-word second moment with repeated labels.
 function exactCRT(z,U,k){
  let ps=primes.filter(p=>p>z&&p<=U),Q=2*primes.filter(p=>p<=z).reduce((a,b)=>a*b,1),K=ps.reduce((a,p)=>a*p,1),words=[],all=0,checks=0;
  function go(j,offset,pins){
   words.push({pins:new Map(pins)});all++;
   if(j===k)return;
   for(let E=0;E<Q;E+=2)for(let p of ps)for(let c of [0,2]){
    let b=mod(c-offset-E,p);
    if(pins.has(p)&&pins.get(p)!==b)continue;
    let v=new Map(pins);v.set(p,b);go(j+1,offset+E+p-1,v);
   }
  }
  go(0,0,new Map());
  let sum=0,sum2=0;
  function w(x,j){if(!j)return 1;let n=0;for(let E=0;E<Q;E+=2)for(let p of ps)if(mod(x+E,p)===0||mod(x+E-2,p)===0)n+=w(x+E+p-1,j-1);return n;}
  for(let x=0;x<2*K;x+=2){
   let a=0;for(let j=0;j<=k;j++)a+=w(x,j);
   let b=words.filter(v=>[...v.pins].every(([p,r])=>mod(x,p)===r)).length;
   ck(a===b,"exact recursive CRT word count");sum+=a;sum2+=a*a;checks++;
  }
  let pair=0,first=0;
  for(let a of words){
   first+=K/[...a.pins.keys()].reduce((s,p)=>s*p,1);
   for(let b of words){
    let v=new Map(a.pins),ok=true;
    for(let [p,r] of b.pins){if(v.has(p)&&v.get(p)!==r){ok=false;break;}v.set(p,r);}
    if(ok)pair+=K/[...v.keys()].reduce((s,p)=>s*p,1);
   }
  }
  ck(sum===first&&sum2===pair,"pairwise CRT moment equality");
  return {z,U,k,Q,K,words:words.length,sum,sum2,checks,pairs:words.length**2};
 }
 const crt=[exactCRT(3,7,3),exactCRT(3,11,2),exactCRT(3,13,2)];
 let rows=[];
 for(let R of Rs){
  let S=Math.sqrt(2*R+1),T=Math.ceil(S),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let specs=[[5,3,31,2,4,16],[7,3,61,3,8,32],[11,5,97,3,12,64]].filter(s=>s[2]<T);
  let controls=[];
  for(let [z,zs,U,k,M0,M] of specs){
   let s=seeds.get(z),F=s.F,Q=2*primes.filter(p=>p<=zs).reduce((a,b)=>a*b,1),D=4*z;
   let eligible=0,early=0,stage=0,bad=0,done=0,heavy=0,kept=0,checks=0,events=0,rootEvents=0,longBad=0,nearBad=0,maxWord=0,maxMass=0,maxInitial=0,maxAge=0,initialTime=0,life=0,visited=0,roughSeeds=0;
   let records=[],m=new Map(),words=new Map(),m0=new Map();
   for(let A=12*Math.ceil(lo/12);A<=hi;A+=12){
    let v=mod(A,F),i=v/2+1;if(!s.keep[i]||s.gain[i]>D||s.a[s.target[i]/2]>M0)continue;
    eligible++;roughSeeds+=+(s.gain[i]===0);let o=run(v,3,s.ps),shift=A-v,y=o.x+shift,nt=o.n-shift/2;
    let a=A,n=3-A/2,birth=n,init=[],cut=false;
    for(let t=0;t<o.ev.length;t++){
     let e=nxt(a,n);
     if(e.p>z){ck(e.p<=6*o.g+7,"early interference bound");early++;cut=true;break;}
     ck(e.p===o.ev[t].p&&e.w===o.ev[t].w&&a===o.ev[t].x+shift,"actual low prefix equals static prefix");
     init.push({a,n,end:n+e.w,y});a-=e.p-1;n+=e.w;events++;
    }
    if(cut)continue;
    ck(a===y&&n===nt&&a>=A-D,"actual initial terminal");stage++;add(m0,y);
    let word=[],low=0,post=a,visits=[],nHigh=0,doneRoot=false,badRoot=false;
    function visit(){
     let code=word.map(e=>[e.p,e.c,e.E].join(",")).join(";"),g=0,cur=a;
     for(let j=word.length-1;j>=0;j--){
      let e=word[j],v=cur+e.E;ck(mod(v-e.c,e.p)===0&&e.E<Q&&e.E%2===0,"reverse pin");
      cur=v+e.p-1;g+=e.E+e.p-1;
     }
     ck(cur===y&&g===y-a,"reverse recovery of static terminal");
     add(m,a);visited++;visits.push(a);let v=words.get(a)||new Map();add(v,code);words.set(a,v);checks++;maxWord=Math.max(maxWord,word.length);
    }
    for(;;){
     visit();
     if(nHigh===k){done++;doneRoot=true;break;}
     let e=nxt(a,n),gain=A-a;
     ck(gain<=D+k*(U+Q)+Q,"prefix gain bound");
     if(e.p>U){
      bad++;badRoot=true;
      let H=n+a/2,cap=20*(D+(k+1)*(U+Q)+1);
      if(e.p<=cap)nearBad++;else{let q=Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
       ck(q>=U/8&&e.w>e.p/4,"far high label implies roughness");longBad++;}
      break;
     }
     let b=a-e.p+1;
     if(e.p>zs){word.push({p:e.p,c:e.e===-1?0:2,E:0});nHigh++;low=0;post=b;}
     else{
      ck(word.length>0,"initial terminal has no small labels");
      ck(Math.floor(a/Q)===Math.floor(b/Q),"low relay wall");low+=e.p-1;ck(low===post-b&&low<Q,"relay gain");word.at(-1).E=low;
     }
     a=b;n+=e.w;rootEvents++;ck(n+a/2>=0&&n-birth<=3*(A-a),"actual prefix age");
    }
    ck(doneRoot!==badRoot&&new Set(visits).size===visits.length,"prefix partition and no revisit");
    maxAge=Math.max(maxAge,n-birth);records.push({A,y,init,visits,stop:n,done:doneRoot});
   }
   for(let [x,v] of m0){ck(v<=M0,"light static terminal mass");maxInitial=Math.max(maxInitial,v);}
   let moment=0,wordMoment=0,heavyMass=0;
   for(let [x,v] of m){let w=words.get(x);for(let a of w.values())ck(a<=M0,"per-word initial terminal mass");
    ck(v<=M0*w.size,"reverse list mass");moment+=v*v;wordMoment+=w.size*w.size;maxMass=Math.max(maxMass,v);
    if(v>M)heavyMass+=v;checks++;
   }
   let intervalMap=new Map();
   for(let r of records){
    if(r.visits.some(x=>m.get(x)>M)){heavy++;continue;}
    kept++;let J=Math.floor((r.A-lo)/W),n0=3-(lo+J*W)/2,end=n0+T;
    life+=Math.max(0,Math.min(r.stop,end)-n0);
    for(let e of r.init){let v=intervalMap.get(e.a)||[];v.push(e);intervalMap.set(e.a,v);}
   }
   // Initial prefixes from different terminal fibers cannot occupy the same
   // physical state simultaneously. Sweep intervals, with end before start.
   for(let [x,es] of intervalMap){
    let ev=[];for(let e of es){ev.push({n:e.n,d:1,y:e.y},{n:e.end,d:-1,y:e.y});}
    ev.sort((a,b)=>a.n-b.n||a.d-b.d);let active=new Map(),total=0;
    for(let e of ev){add(active,e.y,e.d);if(!active.get(e.y))active.delete(e.y);total+=e.d;
     ck(total>=0&&total<=M0&&active.size<=1,"initial actual simultaneous cap");checks++;}
    ck(total===0,"closed intervals");
   }
   ck(stage===done+bad&&eligible===stage+early&&bad===nearBad+longBad&&heavy<=heavyMass&&heavyMass<=moment/M&&kept+heavy===stage,"actual prefix ledger");
   controls.push({z,zs,U,k,M0,M,F,Q,D,eligible,early,stage,bad,done,nearBad,longBad,heavy,kept,roughSeeds,checks,events,rootEvents,visited,maxMass,maxInitial,maxWord,maxAge,moment:moment/N,wordMoment:wordMoment/N,heavyBound:moment/(N*M),live:life/(N*T)});
  }
  rows.push({R,N,T,controls});
 }
 return {crt,rows};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000,1000000,2000000]),null,2));
