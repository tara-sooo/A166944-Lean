// Local first-high-successor direct recovery and multiplier-state capacity.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J;path.push({C,t,J,n,I,e:1-2*I,p,w,g:p-1,d,dp,j:path.length});events++;C=J;t=n;
   }
   // Exact last-up matching of unit height intervals, for all actual decreases above 6.
   let high=6,last=new Map(),matches=0;
   for(let e of path){e.up=[];e.exc=high;if(e.dp>e.d){for(let a=Math.max(6,e.d);a<e.dp;a++){ok(!last.has(a),"no repeated open height");last.set(a,e.j)}}
    if(e.dp<e.d){for(let a=Math.max(6,e.dp);a<e.d;a++){ok(last.has(a),"prior actual ascent");let j=last.get(a);ok(j<e.j&&path[j].d<=a&&path[j].dp>a&&path[j].exc===e.exc,"same excursion matched ascent");e.up.push(j);last.delete(a);matches++}}
    if(e.dp<=6){ok(last.size===0,"no open high level at reset");high=e.j+7}
   }
   ok(last.size===Math.max(0,2*t-C-6),"terminal unmatched heights");tags.push({M,C0,F:C,df:2*t-C,path,matches})
  }
  for(let Y of [9,17,31,61])for(let capMult of [2,8]){
   let k=Math.floor(Math.sqrt(Y)),alpha=1-2/k,L=Math.max(4*Y*Y,Math.floor(H/4)),cap=capMult*Y,R=Math.max(Y,2*cap+1),r={X,focus,N:tags.length,events,Y,k,L,cap,R,bins:0,fragments:0,nonempty:0,kept:0,wide:0,zeroEntry:0,boundaryEntry:0,selected:0,F:0,drop:0,old:0,local:0,entry:0,terminal:0,positive:0,low:0,mid:0,large:0,G:0,midLabels:0,primeChecks:0,roughChecks:0,matchChecks:0,resetChecks:0,wideGain:0,sumWidth:0,maxWidthSum:0,multiGuards:0,strictWidthSaving:0,matchedSources:0,sourceReusedUnits:0,localPairs:0,sameLabelPairs:0,shortPairs:0,shortMass:0,moment:0,tickMoment:0,area:0,tickArea:0,occupancyChecks:0,tupleChecks:0,crtCapacity:0,middleMass:0,returnPairs:0,returnChecks:0,returnShort:0,returnLong:0,returnFirst:0,returnLast:0,returnShortStart:0,returnLongStart:0,returnSpan:0,middleD:0,consumerSupport:0,collisionChecks:0,crossMass:0,oneMass:0,exceptionMass:0,extractMass:0,extractPairs:0,phaseChecks:0,bufferUnits:0,oneSources:0,depthReset:0,nearHeight:0,strongMass:0,shortBinMass:0,shortBins:0,shortLabels:0,spacingChecks:0,independentBuffers:0,independentUnits:0,transMass:0,transFirst:0,transLong:0,transSame:0,transDistinct:0,transCount:0,transSpan:0,transTuples:0,transEdges:0,transShiftCount:0,transMaxShifts:0,transRootChecks:0,transRoughChecks:0,transCapacity:0,transZero:0,transOne:0,transTwoPlus:0,transInside:0,transOutside:0,transSparse:0,transSupport:0,transBins:0,transMaxDegree:0,transPhase:0,wordCount:0,wordLow:0,wordMass:0,wordTail:0,wordSmall:0,wordSmallMass:0,wordRepeats:0,wordDistinct:0,wordFirstOffsets:0,wordRepeatOffsets:0,wordRepeatRelation:0,wordCRT:0,wordTuples:0,wordCap:0,wordRootChecks:0,wordClosed:0,wordOpen:0,wordTwo:0,wordMany:0,wordMaxHigh:0,wordMaxDistinct:0,wordLowNonreset:0,wordLowReset:0,alphabetBins:0,alphabetSize:0,sourceGain:0,targetGain:0,sourceN:0,targetN:0,extraGain:0,extraMass:0,extraEvents:0,extraNonreset:0,extraReset:0,alphabetClosedMass:0,alphabetClosedSmall:0,alphabetShiftChecks:0,alphabetShifts:0,alphabetBudgetChecks:0,deepWords:0,deepMass:0,deepStartMass:0,deepEvents:0,deepLowGain:0,deepExtraGain:0,deepExtraMass:0,deepExtraStartMass:0,deepUniformWords:0,deepUniformMass:0,deepUniformLow:0,deepUniformExtra:0,firstPairs:0,firstMass:0,firstLow:0,firstLowTail:0,firstExtended:0,firstFast:0,firstFastMass:0,firstActualDirect:0,firstGuaranteed:0,firstRetained:0,firstSameSource:0,firstOdd:0,firstFactor:0,firstPhase:0,firstTuple:0,firstTupleCap:0,firstStateChecks:0,firstRangeChecks:0,firstShallow:0,firstShallowMass:0,firstShallowTarget:0,firstReset:0,firstDeep:0,firstTargetState:0,firstTargetLabels:0,firstSourceState:0,firstSourceLabels:0,firstRough:0,firstFourRoots:0,firstDisjoint:0,firstLowReset:0};
   for(let t of tags){
    let bins=new Map();for(let e of t.path){let b=Math.floor((e.C-t.C0)/L);if(!bins.has(b))bins.set(b,[]);bins.get(b).push(e)}
    for(let [bi,es] of bins){
     r.bins++;let G=es.reduce((s,e)=>s+e.g,0);r.G+=G;ok(G<=L+B,"actual bin gain");let frags=[];
     for(let e of es){if(!frags.length||frags.at(-1)[0].exc!==e.exc)frags.push([]);frags.at(-1).push(e)}
     let entry=0,term=0,drop=0,F=0,positive=0,low=0,mid=0,large=0,old=0,local=0,sumWidth=0,maxWidth=0,guards=0,primeMap=new Map(),used=new Map(),pairMap=new Map(),sourceMap=new Map(),consumers=new Set();
     for(let fi=0;fi<frags.length;fi++){
      let fs=frags[fi];r.fragments++;if(fi>0)ok(fs[0].d<=6,"fresh fragment starts low");
      let sel=fs.filter(e=>e.p>=Y&&e.dp>6&&k*e.w<e.g);if(!sel.length)continue;r.nonempty++;
      let u=[];for(let e of sel.slice().sort((a,b)=>a.dp-b.dp)){let a=e.dp,b=a+e.g,last=u.at(-1);if(last&&a<=last[1])last[1]=Math.max(last[1],b);else u.push([a,b])}
      let width=u.reduce((s,[a,b])=>s+b-a,0),phi=d=>u.reduce((s,[a,b])=>s+Math.max(0,Math.min(b,d)-a),0);
      if(width>cap){r.wide++;r.wideGain+=sel.reduce((s,e)=>s+e.g,0);continue}
      r.kept++;guards++;sumWidth+=width;maxWidth=Math.max(maxWidth,width);
      let delta=new Int32Array(fs.length+1),localMoment=0,localTickMoment=0;
      let pi=phi(fs[0].d),pt=phi(fs.at(-1).dp),pp=0,nn=0,dd=0,fg=0,oo=0,ll=0;
      if(fs[0].d<=6){ok(pi===0,"zero entry");r.zeroEntry++}else{ok(fi===0,"only first fragment can inherit");r.boundaryEntry++}
      for(let e of fs){let z=phi(e.dp)-phi(e.d);pp+=Math.max(z,0);nn+=Math.max(-z,0);
       if(e.dp<=6){ok(z<=0,"low arrival not a source");r.resetChecks++}
       if(z>0){ok(z<=Math.min(width,3*e.p+1)&&2*e.w>e.g,"source overlap");
        if(e.p<Y)low+=z;else if(e.p>R)large+=z;else {mid+=z;let id=e.p+"/"+e.I,q=primeMap.get(id)||{p:e.p,I:e.I,n:0,first:e.C,last:e.C};ok(q.n===0||mod(e.C-q.last,e.p)===0,"source progression");q.n++;q.last=e.C;primeMap.set(id,q);for(let f=3;4*f<e.g;f+=2)if(spf[f]===f){ok((e.C-1)%f!==0&&(e.C+1)%f!==0,"source roughness");r.roughChecks++}}
       }
      }
      for(let e of sel){r.selected++;fg+=e.g;let v=e.d-e.dp;ok(v>alpha*e.g&&phi(e.d)-phi(e.dp)===v&&e.up.length===v,"full fast drop");dd+=v;
       for(let i=0;i<e.up.length;i++){let j=e.up[i],a=e.dp+i;ok(j<e.j&&t.path[j].exc===e.exc,"matched source chronology");let key=j+"/"+a;ok(!used.has(key),"no reused source height");used.set(key,1);
        if(j<fs[0].j)oo++;else{ll++;let s=t.path[j];ok(j<=fs.at(-1).j&&phi(s.dp)-phi(s.d)>0,"same fragment positive source");
         let E=e.C-s.J,U=e.t-s.n;ok(E>=0&&U>=0,"actual residence");
         localMoment+=E;localTickMoment+=U;delta[j+1-fs[0].j]++;delta[e.j-fs[0].j]--;
         let key=j+"/"+e.j,q=pairMap.get(key)||{s,e,n:0,E,U,width};q.n++;pairMap.set(key,q);
         if(s.p>=Y&&s.p<=R){let z=sourceMap.get(j)||{s,n:0};z.n++;sourceMap.set(j,z);consumers.add(e.p)}
        }
        r.matchChecks++;
       }
      }
      ok(pp-nn===pt-pi&&dd<=nn&&oo<=pi&&dd===oo+ll&&ll<=pp,"fragment exact transport");
      let open=0,area=0,tickArea=0,mo=0,mt=0;for(let j=0;j<fs.length;j++){let e=fs[j];open+=delta[j];ok(open>=0&&open<=phi(e.d),"active matched height inventory");mo+=open*e.g;mt+=open*e.w;area+=phi(e.d)*e.g;tickArea+=phi(e.d)*e.w;r.occupancyChecks++}
      ok(open+delta[fs.length]===0&&mo===localMoment&&mt===localTickMoment&&mo<=area&&mt<=tickArea,"exact residence area identities");r.moment+=mo;r.tickMoment+=mt;r.area+=area;r.tickArea+=tickArea;
      entry+=pi;term+=pt;drop+=dd;F+=fg;positive+=pp;old+=oo;local+=ll;
     }
     ok(entry<=cap&&old<=entry&&drop+term<=positive+entry&&positive===low+mid+large&&large<=cap*G/(R-1)+1e-7,"bin resource balance");
     ok(used.size===drop,"matched units distinct");
     let K=Math.floor(Y/3),tuples=new Map(),short=0,capCRT=0,ms=0;
     for(let q of pairMap.values()){let {s,e,n,E}=q;r.localPairs++;ok(n<=Math.min(q.width,3*s.p+1,e.g),"matched pair mass cap");
      if(s.p===e.p){ok(E>=s.p-1,"same-label matched relay");r.sameLabelPairs++}
      if(s.p<Y||s.p>R||E>K)continue;
      ok(s.p!==e.p&&mod(s.C-s.e,s.p)===0&&mod(s.C+s.p-1+E-e.e,e.p)===0,"matched joint CRT");
      let key=[s.p,e.p,E,s.I,e.I].join("/"),z=tuples.get(key)||{s,e,E,n:0,m:0,starts:new Set()};ok(!z.starts.has(s.C)&&mod(s.C-z.s.C,s.p*e.p)===0,"matched CRT unique source");z.starts.add(s.C);z.n++;z.m+=n;tuples.set(key,z);short+=n;r.shortPairs++;
     }
     for(let z of tuples.values()){let {s,e,E}=z,p=s.p,rr=e.p,step=p*rr,lo=t.C0+bi*L,hi=lo+L,cnt=0;
      for(let j=Math.ceil((lo-s.C)/step);s.C+j*step<hi;j++){let C=s.C+j*step,pass=true;for(let f=3;4*f<s.g;f+=2)if(spf[f]===f&&((C-1)%f===0||(C+1)%f===0)){pass=false;break}if(pass)cnt++}
      ok(z.n<=cnt&&z.m<=cnt*Math.min(cap,3*p+1,rr-1)&&cnt<=1+L/step+1e-7,"matched finite rough CRT cap");capCRT+=cnt*Math.min(cap,3*p+1,rr-1);r.tupleChecks++;
     }
     ok(short<=capCRT,"aggregate matched CRT capacity");r.shortMass+=short;r.crtCapacity+=capCRT;
     // Restrict to an actual bounded-residence middle population; choose one
     // of original cross or compulsory buffer for each source, never both.
     let near=new Map(),extracted=[],taken=new Map();
     for(let z of pairMap.values()){let {s,e,n,E,U}=z;if(s.p<Y||s.p>R||E>4*cap||U>4*cap)continue;
      let o=near.get(s.j)||{s,cross:[],one:[],exc:0,c:0,b:0,a:0};o.a+=n;
      if(s.p!==e.p){o.cross.push(z);o.c+=n;r.crossMass+=n}
      else{let h=(s.dp-6*s.I)/(2*s.p),k=(e.dp-6*e.I)/(2*e.p),d=h-k;ok(Number.isInteger(h)&&Number.isInteger(k)&&d>=0&&d<=2,"same-label strata");
       if(d===1){o.one.push(z);o.b+=n;r.oneMass+=n;ok(s.w>=s.p-1&&E>=3*s.p-1,"one-stratum clock and relay")}
       else{o.exc+=n;r.exceptionMass+=n}
      }near.set(s.j,o);
     }
     for(let o of near.values()){let s=o.s,p=s.p;ok(o.exc<=10&&o.b<=p+3,"per source stratum cap");
      let buf=[],bn=0;
      if(o.b){let h=(s.dp-6*s.I)/(2*p),hi=2*p*h,lo=hi-p+3,first=o.one.reduce((a,b)=>a.e.j<b.e.j?a:b).e;
       ok(s.d<=lo&&first.d<=lo&&s.dp>=hi,"buffer geometry");let map=new Map();
       for(let u=lo;u<hi;u++){let e=t.path.slice(s.j+1,first.j).find(e=>e.dp<=u);ok(e&&e.p!==p&&e.up[u-Math.max(6,e.dp)]===s.j,"actual causal forbidden buffer");map.set(e,(map.get(e)||0)+1);bn++}
       for(let [e,n] of map)buf.push({s,e,n,E:e.C-s.J,U:e.t-s.n});
       ok(bn===p-3,"full buffer");r.bufferUnits+=bn;r.oneSources++;
      }
      let chosen=o.cross,weight=o.c;if(Math.min(bn,o.b)>weight){chosen=buf;weight=Math.min(bn,o.b)}
      let left=weight;
      for(let z of chosen){let n=Math.min(z.n,left);left-=n;if(n)extracted.push({...z,n});}
      ok(left===0&&weight<=o.a&&2*(p+3)*weight>=(p-3)*(o.a-o.exc),"source-preserving cross extraction");
     }
     let nearS=new Map(),nearT=new Map(),shBins=new Map(),bySource=new Map();
     let ell=Math.ceil(Y*Math.log(Y)**2),beta=0.1;
     for(let z of extracted){let {s,e,n,E,U}=z,p=s.p,rr=e.p,hh=(s.dp-6*s.I)/(2*p),kk=(e.dp-6*e.I)/(2*rr),a=s.dp-e.dp;
      ok(p!==rr&&E<=4*cap&&U<=4*cap&&a>0&&a<=(3*p+1)+(rr-3),"extracted cross geometry");
      ok(Number.isInteger(hh)&&Number.isInteger(kk)&&mod(s.C-(s.e+p*(2*s.I-2*hh-1)),4*p)===0&&mod(e.C-(e.e+rr*(2*e.I-2*kk-1)),4*rr)===0,"exact endpoint phase");
      r.phaseChecks++;r.extractPairs++;r.extractMass+=n;
      if(e.dp<=6){ok(2*p*hh<=rr+3*p+4,"reset depth limit");r.depthReset++}
      if(a<=beta*p){nearS.set(s,(nearS.get(s)||0)+n);r.nearHeight+=n}
      if(a<=beta*rr)nearT.set(e,(nearT.get(e)||0)+n);
      if(s.dp-s.d>=beta*p&&e.d-e.dp>=beta*rr&&a>beta*Math.max(p,rr))r.strongMass+=n;
      let v=bySource.get(p)||new Set();v.add(s);bySource.set(p,v);
      let b1=Math.floor((s.C-t.C0)/ell),b2=Math.floor((e.C-t.C0)/ell);
      if(b1===b2&&rr<=R){let v=shBins.get(b1)||{mass:0,labels:new Set(),targets:new Map()};v.mass+=n;v.labels.add(p);v.targets.set(e,(v.targets.get(e)||0)+n);shBins.set(b1,v)}
     }
     for(let [s,n] of nearS)ok(n<=beta*s.p+1e-7,"small net descent source cap");
     for(let [e,n] of nearT)ok(n<=beta*e.p+1e-7,"small net descent target cap");
     for(let [p,v] of bySource){let a=[...v].sort((a,b)=>a.C-b.C);for(let j=1;j<a.length;j++){ok(a[j].C-a[j-1].C>=2*p-2,"extraction uses original occurrences");r.spacingChecks++}}
     for(let v of shBins.values()){let g=0;for(let [e,n] of v.targets){ok(n<=e.d-e.dp,"extracted target capacity");g+=e.g}ok(v.mass<=g&&g<=ell+R,"short-bin target gain");r.shortBinMass+=v.mass;r.shortBins++;r.shortLabels+=v.labels.size}
     // Aggregate actual cross weights once per source. Consecutive sources
     // may belong to distinct fragments, but all are in the same original bin.
     let agg=new Map();for(let z of extracted){let s=z.s,o=agg.get(s)||{s,n:0};o.n+=z.n;agg.set(s,o)}
     let aa=[...agg.values()].sort((a,b)=>a.s.C-b.s.C),A=16,pm=new Map(),em=new Map(),wm=new Map(),S=new Set(aa.map(z=>z.s.p));
     if(aa.length){
      let sources=new Set(aa.map(z=>z.s)),targets=new Set(extracted.map(z=>z.e)),alphabet=new Set([...sources,...targets].filter(e=>e.p>=Y).map(e=>e.p)),extras=new Set(),closedShifts=new Map(),localExtraMass=0,localDeepExtraMass=0,localDeepExtraStart=0;
      let sg=[...sources].reduce((v,e)=>v+e.g,0),tg=[...targets].reduce((v,e)=>v+e.g,0),M=aa.reduce((v,z)=>v+z.n,0),endCap=Math.max(...aa.map(z=>3*z.s.p+1));
      ok([...sources].every(e=>!targets.has(e)&&e.dp>e.d)&&[...targets].every(e=>e.dp<e.d),"disjoint actual rise and descent");
      ok(M<=3*sg+4*sources.size&&M<=tg,"transport endpoint gain budget");
      r.alphabetBins++;r.alphabetSize+=alphabet.size;r.sourceGain+=sg;r.targetGain+=tg;r.sourceN+=sources.size;r.targetN+=targets.size;
      // Independent re-pairing, not an extra credit to the original transport.
      // The first high successor exists by the earliest actual extracted target.
      let byEarliest=new Map();for(let z of extracted){let old=byEarliest.get(z.s);if(!old||z.e.j<old.j)byEarliest.set(z.s,z.e)}
      let bc=Math.max(1,Math.floor(Y/8)),wc=Math.max(1,Math.floor(Math.sqrt(Y))),qc=5*bc+2*wc+7,fast=[],ft=new Map(),fsource=new Map(),ftarget=new Map(),directUsed=new Set(),allLow=0,shallow=new Set(),shallowLabels=new Set(),fastW=0,shallowW=0,sourceCap=0,targetCap=0,sdlo=Infinity,sdhi=-Infinity,tdlo=Infinity,tdhi=-Infinity;
      const fac=n=>{ok(Number.isInteger(n)&&n>0&&n<=lim,"factor input");let a=[];while(n>1){let p=spf[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a};
      for(let z of aa){let s=z.s,end=byEarliest.get(s),b=t.path.slice(s.j+1,end.j+1).find(e=>e.p>=Y);
       // Finite extraction may contain a low buffer target, unlike asymptotic high-only population.
       if(!b)continue;
       let relay=t.path.slice(s.j+1,b.j),E=relay.reduce((v,e)=>v+e.g,0),V=relay.reduce((v,e)=>v+e.w,0);
       ok(b.j<=end.j&&b.C-s.J===E&&b.t-s.n===V&&relay.every(e=>e.p<Y)&&V<=3*E,"actual first-high relay");
       r.firstPairs++;r.firstMass+=z.n;r.firstLow+=E;allLow+=E;r.firstLowReset+=relay.filter(e=>e.dp===6*e.I).reduce((v,e)=>v+e.g,0);
       if(E>bc){r.firstLowTail+=z.n;continue}
       if(b.w>=wc){r.firstExtended+=z.n;
        let D=b.C-s.C;for(let f=5;2*f<Math.min(s.w,b.w);f+=2)if(spf[f]===f&&f<Y){ok([s.C-1,s.C+1,b.C-1,b.C+1].every(v=>v%f!==0),"two rough first horizons");r.firstRough++;let roots=new Set([1,f-1,mod(1-D,f),mod(-1-D,f)]);ok((roots.size<4)===[D,D-2,D+2].some(v=>mod(v,f)===0),"first four roots");r.firstFourRoots++}
        continue;
       }
       if(b.dp>=b.d)continue; // finite wc and Y need not make all short successors downward
       ok(s.p!==b.p&&E<s.p-1,"distinct short first labels");
       let up=s.dp-s.d,down=b.d-b.dp,variation=relay.reduce((v,e)=>v+Math.abs(e.dp-e.d),0),direct=b.up.filter(j=>j===s.j).length;
       // actual matching above 6; subtract any source portion <=6 from the full-axis lower bound.
       let lower=Math.max(0,Math.min(up,down)-2*variation-Math.max(0,6-s.d));
       ok(direct>=lower&&variation<=5*E&&direct<=Math.min(up,down),"actual direct causal lower");
       let kept=Math.min(z.n,direct);
       ok(!directUsed.has(s)&&!directUsed.has(b),"disjoint first high pairs");directUsed.add(s);directUsed.add(b);r.firstDisjoint++;
       r.firstFast++;r.firstFastMass+=z.n;r.firstActualDirect+=direct;r.firstGuaranteed+=lower;r.firstRetained+=kept;
       let p=s.p,rr=b.p,h=(s.dp-6*s.I)/(2*p),k1=(b.dp-6*b.I)/(2*rr),c=E-1-2*(V+b.w)+6*(b.I-s.I);
       ok(Number.isInteger(h)&&h>=1&&Number.isInteger(k1)&&k1>=0&&Math.abs(c)<=qc&&Math.abs(c)%2===1&&2*h*p-(2*k1+1)*rr===c,"odd shifted multiplier");
       let v1=2*h*p-c,v2=(2*k1+1)*rr+c;
       ok(fac(v1).includes(rr)&&fac(v2).includes(p),"two endpoint shifted divisors");r.firstOdd++;r.firstFactor+=2;
       let a0=s.e+p*(2*s.I-2*h-1),b0=b.e+rr*(2*b.I-2*k1-1);
       ok(mod(s.C-a0,4*p)===0&&mod(b.C-b0,4*rr)===0&&mod(b0-a0-(b.C-s.C),4)===0,"first pair exact phase");r.firstPhase++;
       let id=[p,h,c,E,s.I,b.I,rr].join("/"),v=ft.get(id)||{s,b,n:0,starts:new Set()};
       ok(!v.starts.has(s.C)&&mod(s.C-v.s.C,p*rr)===0,"first pair tuple CRT");v.starts.add(s.C);v.n+=z.n;ft.set(id,v);
       let f1=fsource.get(p)||new Set(),f2=ftarget.get(rr)||new Set();f1.add(h);f2.add(k1);fsource.set(p,f1);ftarget.set(rr,f2);
       sdlo=Math.min(sdlo,s.dp);sdhi=Math.max(sdhi,s.dp);tdlo=Math.min(tdlo,b.dp);tdhi=Math.max(tdhi,b.dp);
       fast.push({s,b,h,k1,c,E,n:z.n});fastW+=z.n;
       if(h<=Math.floor(Math.sqrt(Y))){r.firstShallow++;r.firstShallowMass+=z.n;shallowW+=z.n;shallow.add(p+"/"+h);shallowLabels.add(p);ok(v1<=2*p*Math.floor(Math.sqrt(Y))+qc,"shallow divisor bound")}
       else r.firstDeep++;
       if(k1<=Math.floor(Math.sqrt(Y))){r.firstShallowTarget++;ok(h<=( (2*Math.floor(Math.sqrt(Y))+1)*rr+qc)/(2*p),"reverse small multiplier cap")}
       if(!k1)r.firstReset++;
      }
      // All strict low relays are disjoint even before filtering fast successors.
      ok(allLow<=es.filter(e=>e.p<Y).reduce((v,e)=>v+e.g,0),"first low relay budget");
      if(fast.length){let P0=Math.max(...fast.flatMap(z=>[z.s.p,z.b.p])),wcap=3*P0+1,fh=[...fsource.values()].reduce((v,s)=>v+s.size,0),kh=[...ftarget.values()].reduce((v,s)=>v+s.size,0);
       let bf=Math.max(1,Math.floor(Math.log(6+5*H+qc+P0)/Math.log(Y))),bfsmall=Math.max(1,Math.floor(Math.log(2*P0*Math.floor(Math.sqrt(Y))+qc)/Math.log(Y)));
       let coef=4*(bc+1)*(2*qc+1)*wcap*(1+L/(Y*Y));
       ok(fastW<=coef*bf*fh+1e-7&&fastW<=coef*bf*kh+1e-7&&shallowW<=coef*bfsmall*shallow.size+1e-7,"two-sided actual multiplier-state capacity");r.firstStateChecks++;
       for(let [p,s] of fsource)ok(s.size<=2+(sdhi-sdlo+6)/(2*p),"source multiplier range");
       for(let [p,s] of ftarget)ok(s.size<=2+(tdhi-tdlo+6)/(2*p),"target multiplier range");r.firstRangeChecks+=2;
       r.firstSourceState+=fh;r.firstTargetState+=kh;r.firstSourceLabels+=fsource.size;r.firstTargetLabels+=ftarget.size;
       for(let v of ft.values()){let bound=(1+Math.floor(L/(v.s.p*v.b.p)))*wcap;ok(v.n<=bound&&v.starts.size<=1+Math.floor(L/(v.s.p*v.b.p)),"weighted first tuple capacity");r.firstTuple++;r.firstTupleCap+=bound}
      }
      r.transBins++;r.transSupport+=S.size;r.transFirst+=aa[0].n;let span=0,largeN=0,all=aa.reduce((a,z)=>a+z.n,0),tot=aa[0].n;
      r.transMass+=all;
      for(let j=1;j<aa.length;j++){let a=aa[j-1].s,b=aa[j].s,p=a.p,rr=b.p,D=b.C-a.C,n=aa[j].n;
       ok(D>=p-1&&n<=3*rr+1&&a.dp>a.d&&b.dp>b.d,"actual upward source pair");
       span+=D;tot+=n;r.transCount++;
       if(D>A*Y){largeN++;r.transLong+=n;continue}
       if(p===rr){r.transSame+=n;continue}
       r.transDistinct+=n;
       let relay=t.path.slice(a.j+1,b.j),E=relay.reduce((s,e)=>s+e.g,0);
       ok(E===D-(p-1),"actual relay sum");
       // Every physical event >=Y is retained in the high word, not only selected sources.
       let word=[a,...relay.filter(e=>e.p>=Y),b],low=relay.filter(e=>e.p<Y),lowG=low.reduce((v,e)=>v+e.g,0),cut=Math.min(Y-4,Math.ceil(Math.sqrt(Y)*Math.log(Y)));
       let outside=relay.filter(e=>e.p>=Y&&!alphabet.has(e.p)),outG=outside.reduce((v,e)=>v+e.g,0);
       if(outside.length){localExtraMass+=n;r.extraMass+=n;ok(n*(Y-1)<=endCap*outG,"actual outside alphabet charge");
        for(let e of outside){ok(!sources.has(e)&&!targets.has(e)&&!extras.has(e),"extra high gain disjoint from every endpoint and previous relay");extras.add(e);r.extraEvents++;if(e.dp===6*e.I)r.extraReset+=e.g;else r.extraNonreset+=e.g}
       }else{r.alphabetClosedMass+=n;if(lowG<=cut){r.alphabetClosedSmall+=n;let id=p+"/"+rr,z=closedShifts.get(id)||{D:new Set(),k:0};z.D.add(D);z.k=Math.max(z.k,word.length-2);closedShifts.set(id,z)}}
       if(a.dp>6+E){r.deepWords++;r.deepMass+=n;r.deepStartMass+=aa[j-1].n;r.deepLowGain+=lowG;
        let cum=0;for(let e of relay){cum+=e.g;ok(e.dp>=a.dp-cum&&e.dp>6&&e.dp!==6*e.I,"deep relay cannot reset");r.deepEvents++}
        ok(b.d>=a.dp-E&&b.d>6,"deep ending preheight");
        if(outside.length){r.deepExtraGain+=outG;localDeepExtraMass+=n;localDeepExtraStart+=aa[j-1].n;r.deepExtraMass+=n;r.deepExtraStartMass+=aa[j-1].n;ok(aa[j-1].n*(Y-1)<=endCap*outG,"deep starting-weight charge")}
        if(a.dp>6+A*Y){r.deepUniformWords++;r.deepUniformMass+=aa[j-1].n;r.deepUniformLow+=lowG;r.deepUniformExtra+=outG}
       }
       r.wordCount++;r.wordMass+=n;r.wordLow+=lowG;r.wordLowNonreset+=low.filter(e=>e.dp!==6*e.I).reduce((v,e)=>v+e.g,0);r.wordLowReset+=low.filter(e=>e.dp===6*e.I).reduce((v,e)=>v+e.g,0);
       let dset=new Set(word.map(e=>e.p));r.wordMaxHigh=Math.max(r.wordMaxHigh,word.length);r.wordMaxDistinct=Math.max(r.wordMaxDistinct,dset.size);
       ok(word.length<=1+Math.floor(A*Y/(Y-1))&&D===word.slice(0,-1).reduce((v,e)=>v+e.g,0)+lowG,"complete high word");
       if(word.length===2)r.wordTwo+=n;else r.wordMany+=n;
       if(lowG>cut)r.wordTail+=n;else{
        r.wordSmall++;r.wordSmallMass+=n;if(dset.size===word.length)r.wordDistinct++;else r.wordRepeats++;
        let off=[],g=0,first=new Map(),P=1n;
        for(let i=0;i<word.length;i++){let e=word[i],u=e.C-a.C-g;ok(u>=0&&u<=lowG&&(!i||u>=off[i-1]),"actual cumulative low gain");off.push(u);
         if(!first.has(e.p)){first.set(e.p,{i,u});P*=BigInt(e.p);r.wordFirstOffsets++}
         else{let z=first.get(e.p),prev=word[z.i],rhs=mod(e.e-(a.C+g),e.p);ok(u===rhs&&u<e.p,"unique repeat offset");r.wordRepeatOffsets++;
          let inner=word.slice(z.i+1,i),m=(e.C-prev.C-e.e+prev.e)/(2*e.p),lowDiff=u-z.u;
          ok(Number.isInteger(m)&&m>=1&&(2*m-1)*e.p-inner.reduce((s,v)=>s+v.p,0)===lowDiff-(i-z.i)-e.e+prev.e,"actual repeated-label relation");r.wordRepeatRelation++;
         }
         ok(mod(a.C+g+u-e.e,e.p)===0,"all high horizon congruences");g+=e.g;
        }
        ok(off[0]===0&&off.at(-1)===lowG,"word offset endpoints");
        let k=word.map(e=>e.p).join(",")+"/"+word.map(e=>e.I).join(",")+"/"+[...first.values()].map(z=>z.u).join(",");
        let q=wm.get(k)||{C:a.C,D,P,n:0,count:0,starts:new Set(),p,rr};
        ok(q.D===D&&q.P===P&&!q.starts.has(a.C)&&(BigInt(a.C-q.C)%P===0n),"first offsets determine word progression and end shift");q.n+=n;q.count++;q.starts.add(a.C);wm.set(k,q);r.wordCRT++;
        for(let f=5;4*f<Y-1;f+=2)if(spf[f]===f){ok([a.C-1,a.C+1,b.C-1,b.C+1].every(v=>mod(v,f)!==0),"both high word endpoints rough");r.wordRootChecks++}
        if(word.every(e=>S.has(e.p)))r.wordClosed+=n;else r.wordOpen+=n;
       }
       if(!relay.length)r.transZero+=n;else if(relay.length===1){ok(E+1===relay[0].p&&spf[E+1]===E+1,"one-event prime shift");r.transOne+=n}else r.transTwoPlus+=n;
       if(relay.every(e=>S.has(e.p))){ok(relay.length<=Math.floor(A*Y/(Y-1)),"inside alphabet length");r.transInside+=n}else r.transOutside+=n;
       let h=(a.dp-6*a.I)/(2*p),k=(b.dp-6*b.I)/(2*rr);
       let ca=a.e+p*(2*a.I-2*h-1),cb=b.e+rr*(2*b.I-2*k-1);
       ok(mod(a.C-ca,4*p)===0&&mod(b.C-cb,4*rr)===0&&mod(cb-ca-D,4)===0,"actual two-source endpoint phases");r.transPhase++;
       let id=[p,rr,D,a.I,b.I].join("/"),q=pm.get(id)||{a,b,p,rr,D,n:0,count:0,starts:new Set()};
       ok(!q.starts.has(a.C)&&mod(a.C-q.a.C,p*rr)===0,"actual distinct-source CRT");q.starts.add(a.C);q.n+=n;q.count++;pm.set(id,q);
       let eid=p+"/"+rr,z=em.get(eid)||{p,rr,shifts:new Set(),mass:0};z.shifts.add(D);z.mass+=n;em.set(eid,z);
       for(let f=5;4*f<Math.min(p,rr)-1;f+=2)if(spf[f]===f){
        ok([a.C-1,a.C+1,b.C-1,b.C+1].every(v=>v%f!==0),"two upward horizons rough");r.transRoughChecks++;
        let roots=new Set([1,f-1,mod(1-D,f),mod(-1-D,f)]);
        ok((roots.size<4)===[D,D-2,D+2].some(v=>v%f===0),"four roots collision");r.transRootChecks++;
       }
      }
      let eg=[...extras].reduce((v,e)=>v+e.g,0);
      ok(sg+tg+eg<=G&&localExtraMass*(Y-1)<=endCap*eg&&localDeepExtraMass<=localExtraMass&&localDeepExtraStart*(Y-1)<=endCap*eg,"disjoint endpoint plus extra relay cost");
      r.extraGain+=eg;r.alphabetBudgetChecks++;
      for(let z of closedShifts.values()){let choices=0n;for(let k=0;k<=z.k;k++)choices+=BigInt(alphabet.size)**BigInt(k);ok(BigInt(z.D.size)<=BigInt(Math.min(Y-4,Math.ceil(Math.sqrt(Y)*Math.log(Y)))+1)*choices,"closed alphabet actual shift set bound");r.alphabetShiftChecks++;r.alphabetShifts+=z.D.size}
      ok(tot===all&&span<=L&&largeN*A*Y<=span,"consecutive source gap ledger");r.transSpan+=span;
      let lo=t.C0+bi*L,hi=lo+L,cp=0,cm=0,degrees=new Map();
      for(let q of pm.values()){let {a,p,rr,D}=q,step=p*rr,cnt=0;
       for(let j=Math.ceil((lo-a.C)/step);a.C+j*step+D<hi;j++){let C=a.C+j*step,pass=true;for(let f=3;4*f<Math.min(p,rr)-1;f+=2)if(spf[f]===f&&[C-1,C+1,C+D-1,C+D+1].some(v=>v%f===0)){pass=false;break}if(pass)cnt++}
       ok(q.count<=cnt&&q.n<=cnt*(3*rr+1),"finite four-form CRT weighted capacity");cp+=cnt*(3*rr+1);cm+=q.n;r.transTuples++;
      }
      let wordCap=0,wordMass=0;for(let q of wm.values()){let cnt=0;let start=BigInt(q.C),lower=BigInt(lo),upper=BigInt(hi-q.D),step=q.P;
       // BigInt floor/ceil for possibly negative lower-start.
       let ceil=(a,b)=>a>=0n?(a+b-1n)/b:a/b;
       for(let k=ceil(lower-start,step);start+k*step<upper;k++){let C=Number(start+k*step),pass=true;for(let f=3;4*f<Y-1;f+=2)if(spf[f]===f&&[C-1,C+1,C+q.D-1,C+q.D+1].some(v=>mod(v,f)===0)){pass=false;break}if(pass)cnt++}
       ok(q.count<=cnt&&q.n<=cnt*(3*q.rr+1),"all high word finite rough capacity");wordCap+=cnt*(3*q.rr+1);wordMass+=q.n;r.wordTuples++;
      }ok(wordMass<=wordCap,"word aggregate capacity");r.wordCap+=wordCap;
      let edgeMass=0;for(let z of em.values()){let ds=degrees.get(z.p)||new Set();ds.add(z.rr);degrees.set(z.p,ds);edgeMass+=z.mass;r.transShiftCount+=z.shifts.size;r.transMaxShifts=Math.max(r.transMaxShifts,z.shifts.size);if(z.shifts.size<=2)r.transSparse+=z.mass}
      ok(edgeMass===cm&&cm<=cp,"edge shift partition");r.transCapacity+=cp;r.transEdges+=em.size;r.transMaxDegree=Math.max(r.transMaxDegree,...[...degrees.values()].map(z=>z.size));
     }
     let by=new Map();for(let z of sourceMap.values()){let s=z.s;ok(z.n<=Math.min(cap,3*s.p+1),"source total match capacity");ms+=z.n;if(!by.has(s.p))by.set(s.p,[]);by.get(s.p).push(z)}
     r.middleMass+=ms;r.consumerSupport+=consumers.size;let D=0;
     for(let [p,zs] of by){zs.sort((a,b)=>a.s.C-b.s.C);let weight=Math.min(cap,4*p),D0=Math.min(1,cap/p);D+=D0;
      let first=zs[0].n,last=zs.at(-1).n,sh=0,lg=0,shStart=0,lgStart=0,span=0,ln=0;
      for(let j=1;j<zs.length;j++){let a=zs[j-1],b=zs[j],q1=(a.s.C-a.s.e)/p,q2=(b.s.C-b.s.e)/p,m=(q2-q1)/2;ok(Number.isInteger(m)&&m>=1&&b.s.C-a.s.C===2*p*m+b.s.e-a.s.e,"actual source return gap");span+=m;r.returnPairs++;
       if(m<=4){sh+=b.n;shStart+=a.n}else{lg+=b.n;lgStart+=a.n;ln++}
       let disc=m*(p*m+b.s.e)*(p*m-a.s.e)*(p*m+b.s.e-a.s.e);
       // Avoid product precision by testing factors separately modulo f.
       for(let f=5;4*f<p-1;f+=2)if(spf[f]===f){let forms=x=>[x,x+2*m,p*x+2*a.s.e,p*(x+2*m)+2*b.s.e];ok(forms(q1).every(x=>mod(x,f)!==0),"actual repeated source roughness");let roots=Array.from({length:f},(_,x)=>x).filter(x=>forms(x).some(v=>mod(v,f)===0));let collision=[m,p*m+b.s.e,p*m-a.s.e,p*m+b.s.e-a.s.e].some(v=>mod(v,f)===0);ok((roots.length<4)===collision,"four-form collision");r.collisionChecks++}
      }
      ok(first+sh+lg===zs.reduce((a,b)=>a+b.n,0)&&last+shStart+lgStart===zs.reduce((a,b)=>a+b.n,0)&&span<=(L+2)/(2*p)+1e-7&&ln*5<=span&&lg<=weight*span/5+1e-7&&lgStart<=weight*span/5+1e-7,"two-sided matched return partition");r.returnChecks++;r.returnFirst+=first;r.returnLast+=last;r.returnShort+=sh;r.returnLong+=lg;r.returnShortStart+=shStart;r.returnLongStart+=lgStart;r.returnSpan+=span;
     }
     r.middleD+=D;
     r.matchedSources+=new Set([...used.keys()].map(x=>x.split("/")[0])).size;
     for(let q of primeMap.values()){ok(q.n<=1+L/q.p,"local prime count");r.primeChecks++}
     r.midLabels+=new Set([...primeMap.values()].map(q=>q.p)).size;
     for(let [key,v] of Object.entries({F,drop,old,local,entry,terminal:term,positive,low,mid,large,sumWidth,maxWidthSum:maxWidth}))r[key]+=v;
     if(guards>1)r.multiGuards++;if(sumWidth>cap)r.strictWidthSaving++;
    }
   }
   ok(r.drop+r.terminal<=r.positive+r.entry&&r.entry<=r.cap*r.bins&&r.old<=r.entry&&r.positive===r.low+r.mid+r.large,"global balance");
   ok(r.moment<=r.area&&r.tickMoment<=r.tickArea&&r.area<=r.cap*r.G&&r.returnFirst+r.returnShort+r.returnLong===r.middleMass&&r.returnLast+r.returnShortStart+r.returnLongStart===r.middleMass,"aggregate residence and return budgets");ok(r.extractMass*2*(Y+3)>=(Y-3)*(r.crossMass+r.oneMass)-1e-7,"aggregate cross lower");ok(r.transMass===r.extractMass&&r.transMass===r.transFirst+r.transLong+r.transSame+r.transDistinct&&r.transDistinct===r.transZero+r.transOne+r.transTwoPlus&&r.transDistinct===r.transInside+r.transOutside&&r.transDistinct<=r.transCapacity,"aggregate transition ledger");ok(r.wordMass===r.transDistinct&&r.wordMass===r.wordTail+r.wordSmallMass&&r.wordSmallMass===r.wordClosed+r.wordOpen&&r.wordMass===r.wordTwo+r.wordMany&&r.wordSmallMass<=r.wordCap&&r.wordLow===r.wordLowReset+r.wordLowNonreset&&r.wordLow<=r.G,"aggregate actual low word budgets");ok(r.sourceGain+r.targetGain+r.extraGain<=r.G&&r.extractMass<=3*r.sourceGain+4*r.sourceN&&r.extractMass<=r.targetGain&&r.extraGain===r.extraReset+r.extraNonreset&&r.extraMass+r.alphabetClosedMass===r.wordMass,"aggregate disjoint gain and alphabet ledger");ok(r.firstRetained<=r.firstFastMass&&r.firstGuaranteed<=r.firstActualDirect&&r.firstLow<=r.G&&r.firstFastMass<=r.firstMass,"global direct re-pairing budget");results.push(r)
  }
 }
 return results
}
function abstractBuffer(){let geometry=0,valid=0,units=0;for(let p of [11,17,31,61])for(let h of [2,3,7])for(let I of [0,1])for(let J of [0,1])for(let rise=2;rise<=3*p+1;rise+=2)for(let drop=2;drop<=p-3;drop+=2){geometry++;let a=2*p*h+6*I,b=2*p*(h-1)+6*J,lo=2*p*h-p+3,hi=2*p*h;if(Math.min(a,b+drop)<=Math.max(a-rise,b))continue;valid++;if(!(a-rise<lo&&b+drop<=lo&&a>=hi))throw Error("abstract buffer geometry");for(let u=lo;u<hi;u++){for(let j=h-2;j<=h+1;j++)for(let K of [0,1]){let d=2*p*j+6*K;if(d<=u&&u<d+p-3)throw Error("forbidden buffer")}units++}}return {geometry,valid,units}}
console.log(JSON.stringify({results:audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),abstract:abstractBuffer()},null,2));
