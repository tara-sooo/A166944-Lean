function audit(N=150000,steps=200,P=1100){
 const cap=Math.max(4*N+50000,8*P*P+50000),spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(x,p)=>(x%p+p)%p,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function next(t,H){let best=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}}return best}
 function literal(t,H){for(let w=1;w<=2*Math.floor(Math.sqrt(H+1));w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1&&spf[g]**2<=H+1)return {p:spf[g],e,w}}return null}
 function event(t,H,r){let {p,e,w}=r,n=t+w,q=(H-e)/p,D=2*n-H-p+1-(e===-1?6:0),d=2*t-H;return {p,e,w,n,H,q,D,d}}
 function excursion(t,H){let w=0,word=[];while(H%3){let a=next(t,H);if(!a)throw Error("3 absent");word.push(a.p);t+=a.w;w+=a.w;H+=a.p-1;if(w>12)throw Error("excursion");}return {w,word,endH:H,endT:t,d:2*t-H}}
 let s={N,steps,P,events:0,rangeTruncated:0,excursions:0,maxExcursion:[0,0,0],maxExcursionExamples:{},resetChecks:0,resetTypes:{},resetWitness:{},canonicalResetChecks:0,canonicalResetTypes:{},twoRelay:0,longTwoRelay:0,minimalLongTwoRelay:0,relayTwin:0,twinLabelLower:new Set(),twinPhysical:new Set(),relayNo3EvenOdd:0,relayNo3OddEven:0,allNo3OddEven:0,maxRelayPrime:0,relayExamples:[],resetNo3Checks:0,highScaleChecks:0,highScaleComposite:0,highScalePrime:0,abstractCandidates:0,abstractFirstHits:0,abstractTwoRelay:0,abstractHighComposite:0,abstractExamples:[],localCounterexample:null,literalChecks:0};
 function checkReset(t,H,canonical=false){
  let d=2*t-H,I=t%2;if(d!==6*I||H%3===0)throw Error("reset input");
  let a=excursion(t,H),word,wait,df;
  if(I===0&&H%3===1){if((t+2)%5===0&&H+1>=25){word=[5,3,3];wait=4;df=0}else{word=[3];wait=4;df=6}}
  if(I===0&&H%3===2){word=[3,3];wait=2;df=0}
  if(I===1&&H%3===1){word=[3];wait=1;df=6}
  if(I===1&&H%3===2){if(t%5===0&&H+1>=25){word=[5];wait=2;df=6}else if((t+3)%13===0&&H+1>=169){word=[13,3,3];wait=5;df=0}else{word=[3,3];wait=5;df=12}}
  if(a.word.join()!==word.join()||a.w!==wait||a.d!==df)throw Error("reset table "+JSON.stringify({t,H,a,word,wait,df}));
  let k=`${I}/${H%3}/${word.join()}`;s[canonical?"canonicalResetChecks":"resetChecks"]++;let types=canonical?s.canonicalResetTypes:s.resetTypes;types[k]=(types[k]||0)+1;if(!s.resetWitness[k])s.resetWitness[k]={t,H,...a};
 }
 function checkReturn(z,a,b,x,canonical){
  const p=z.p,m=(x.q-z.q)/2;
  if(x.p!==p||a.p===p||b.p===p||p<5)throw Error("return input");
  if(a.p===b.p&&a.p!==3)throw Error("consecutive relay");
  if(canonical)s.twoRelay++;
  if(z.H%3===0&&x.H%3===0&&m===1&&z.e===-1&&x.e===1&&a.p!==3&&b.p!==3){
   if(a.w+b.w>9||x.w<p-11||z.D===0||z.D<2*p)throw Error("general odd even no3");if(canonical)s.allNo3OddEven++;
  }
  if(z.w<=6||x.w<=6)return;
  if(canonical)s.longTwoRelay++;
  if(m!==1)return;
  if(canonical)s.minimalLongTwoRelay++;
  if(x.e===z.e||a.p+b.p!==p+3+x.e-z.e)throw Error("side");
  if(a.p===3||b.p===3){let other=a.p===3?b.p:a.p;if(other!==p+x.e-z.e)throw Error("relay twin");if(canonical){s.relayTwin++;s.twinLabelLower.add(Math.min(p,other));s.twinPhysical.add(`${z.n}:${z.H}:${p}:${x.n}:${x.H}`);if(p>s.maxRelayPrime){s.maxRelayPrime=p;s.relayExamples.push({z,a,b,x})}}return;}
  if(z.e===1){if(p%3!==1||a.p%3!==1||b.p%3!==1)throw Error("even odd class");if(canonical)s.relayNo3EvenOdd++}
  else{if(p%3!==2||a.p%3!==2||b.p%3!==2||z.D===0||a.w+b.w>9||x.w<p-11)throw Error("odd even class/time");if(canonical)s.relayNo3OddEven++}
  if(z.D===0&&x.D===0&&z.e===1){
    s.resetNo3Checks++;if(a.D!==0&&a.D!==2*a.p)throw Error("first relay D");
    if(a.D===2*a.p&&3*a.p>2*p-11)throw Error("relay bound");
    if(b.D>=4*b.p&&!(a.D===0&&b.p===7&&b.D===28))throw Error("last relay D");
    if(b.D===2*b.p&&2*x.w!==a.p-b.p+4-6*(b.e===-1?1:0))throw Error("resonance");
    let Y=x.H;
    if(p>=101&&p*p*p>64*(Y+1)){
      s.highScaleChecks++;
      if(spf[x.q]===x.q){s.highScalePrime++;return;}
      s.highScaleComposite++;if(!canonical)s.abstractHighComposite++;
      let r=spf[x.q],I=b.e===-1?1:0;if(b.D!==2*b.p||p%12!==7||a.p-b.p<10+6*I||a.p-b.p>4*r-6+6*I)throw Error("high scale obstruction");
    }
  }
 }
 for(let H=8;H<=N;H+=2)if(H%3){let t=H/2;if(t%2===0)checkReset(t,H);t=H/2+3;if(t%2===1)checkReset(t,H)}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,ev=[];for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+50>=cap){s.rangeTruncated++;break}if(H%3){let a=excursion(t,H);s.excursions++;if(a.w>s.maxExcursion[H%3]){s.maxExcursion[H%3]=a.w;s.maxExcursionExamples[H%3]={M,H,t,...a}}if(H%3===2&&a.w>7)throw Error("residue2");if(a.endH-H>2*t-H+2*a.w)throw Error("envelope");if(2*t-H===6*(t%2))checkReset(t,H,true)}
 let r=next(t,H);if(!r)break;let x=event(t,H,r),{p}=x;
 if(i>=3&&p>=5&&ev[i-3].p===p&&ev[i-2].p!==p&&ev[i-1].p!==p){checkReturn(ev[i-3],ev[i-2],ev[i-1],x,true)}
 ev.push(x);t=x.n;H+=p-1;s.events++;
 }}
 // Actual local segment with both non-3 relays, not claimed canonical.
 function replay(t,H,expected){let ev=[];for(let p of expected){let r=next(t,H),l=literal(t,H);if(!r||r.p!==p||JSON.stringify(r)!==JSON.stringify(l))throw Error("literal");let x=event(t,H,r);ev.push(x);t=x.n;H+=p-1;s.literalChecks++}return ev}
 let v=replay(201864,303078,[29,11,23,29]);checkReturn(...v,false);s.localCounterexample=v;
 // Exhaustive bounded abstract reset entries, not canonical reachability.
 for(let p=101;p<=P;p+=2)if(spf[p]===p&&p%3===1){
  for(let q=p+(11-p%12+12)%12;q<=Math.min(8*p,Math.floor(p*p/64)-3);q+=12){
   let H=p*q+1,n=p*(q+1)/2,t=n-7;s.abstractCandidates++;
   let r=next(t,H);if(r?.p!==p||r.w!==7||r.e!==1)continue;s.abstractFirstHits++;
   let z=event(t,H,r),ev=[z];t=n;H+=p-1;
   for(let i=0;i<3;i++){let a=next(t,H);if(!a)break;let x=event(t,H,a);ev.push(x);t=x.n;H+=x.p-1}
   if(ev.length!==4||ev[3].p!==p||ev[1].p===p||ev[2].p===p||ev[3].q!==q+2||ev[3].D!==0||ev[3].w<=6)continue;
   s.abstractTwoRelay++;checkReturn(...ev,false);
   if(ev[1].p!==3&&ev[2].p!==3&&s.abstractExamples.length<6){let re=replay(n-7,p*q+1,ev.map(x=>x.p));if(JSON.stringify(re)!==JSON.stringify(ev))throw Error("abstract replay");s.abstractExamples.push({ev,secondComposite:spf[q+2]!==q+2,firstPrime:spf[q]===q})}
  }
 }
 s.twinLabelLower=[...s.twinLabelLower].sort((a,b)=>a-b);s.twinPhysical=s.twinPhysical.size;return s
}

const r=audit(Number(process.argv[2]||150000),Number(process.argv[3]||200),Number(process.argv[4]||1100)); console.log(JSON.stringify(r,null,2));
