// Growing-order sieve smoothing: exact finite envelopes, zero-run and actual cut-free corridor audits.
function audit(N=30000){
 const lim=500000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const assert=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b,prod=a=>a.reduce((v,p)=>v*p,1),bigprod=a=>a.reduce((v,p)=>v*BigInt(p),1n);
 let seed=7219;const rand=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 const st={periodControls:0,truncationControls:0,intersectionPeriods:0,periodPositions:0,pointwiseEnvelopeChecks:0,localL2Controls:0,periodL2Checks:0,zeroCountChecks:0,zeroRunControls:0,longZeroRuns:0,zeroRunPositions:0,roots:0,events:0,unresolved:0,corridorControls:0,marks:0,pending:0,completed:0,resetBad:0,crossBad:0,cutFree:0,cutFreeHigh:0,extendedGood:0,extendedLow:0,extendedModerate:0,recordPartitionChecks:0,weightedRecordChecks:0,colorChecks:0,maxOverlap:0,cutCrossChecks:0,actualWitnessTicks:0,actualWitnessResidues:0,examples:[]};
 function setup(S,R,V){let small=pr.filter(f=>f<=R),extra=pr.filter(f=>f>R&&f<=V);return {S,R,V,small,extra,P:prod(small),Q:prod(extra),A:prod(small.map(f=>f<=S?1:(f-1)/2)),K:2*prod(small.filter(f=>f<=S))}}
 function base(j,c){return c.small.every(f=>{let z=mod(2*j,f);return f<=c.S?z===0:z%2===0&&z<=f-3})}
 for(let spec of [[3,5,7],[5,7,17],[7,7,13],[7,11,17],[11,13,17],[3,7,17]]){
  let c=setup(...spec),{P,Q,A,extra}=c,full=P*Q,qnum=prod(extra.map(f=>f-2));assert(full<=300000,"period");
  const sv=new Uint8Array(full);for(let j=0;j<full;j++)sv[j]=base(j,c)&&extra.every(f=>![1,f-1].includes(mod(2*j,f)))?1:0;
  assert(sv.reduce((a,b)=>a+b,0)===A*qnum,"density");
  function roll(arr,L){let n=0;for(let i=0;i<L;i++)n+=arr[i%arr.length];let a=new Int32Array(arr.length);for(let i=0;i<arr.length;i++){a[i]=n;n+=arr[(i+L)%arr.length]-arr[i]}return a}
  for(let L of [...new Set([1,3,Math.ceil(P**(4/11))])]){
   let all=[],Froll=roll(sv,L);for(let mask=0;mask<2**extra.length;mask++){
    let f=extra.filter((p,i)=>mask&(1<<i)),q=prod(f),period=P*q,k=f.length,weight=2**k*(Q/q),arr=new Uint8Array(period);
    for(let j=0;j<period;j++)arr[j]=base(j,c)&&f.every(p=>[1,p-1].includes(mod(2*j,p)))?1:0;
    assert(arr.reduce((a,b)=>a+b,0)===A*2**k,"intersection density");
    let a=roll(arr,L),z=new Int32Array(period),zBig=null,v=0n; // exact integer normalized deviations in common units; use BigInt when needed
    if(P*Q*L>2147483647)zBig=new Array(period);
    for(let j=0;j<period;j++){let d=BigInt(P)*BigInt(Q)*BigInt(a[j])-BigInt(A)*BigInt(L)*BigInt(weight);if(zBig)zBig[j]=d;else z[j]=Number(d);v+=d*d}
    all.push({k,weight,period,a,z,zBig,v});st.intersectionPeriods++;
   }
   let scale=BigInt(A)*BigInt(L),mean=scale*BigInt(qnum),zsv=new Array(full);
   for(let j=0;j<full;j++)zsv[j]=BigInt(P)*BigInt(Q)*BigInt(Froll[j])-mean;
   for(let even=0;even<=extra.length;even+=2){
    let odd=even+1,used=all.filter(f=>f.k<=odd),up=all.filter(f=>f.k<=even),qUp=up.reduce((a,f)=>a+(f.k%2?-1:1)*f.weight,0),qDown=used.reduce((a,f)=>a+(f.k%2?-1:1)*f.weight,0);
    assert(qDown<=qnum&&qnum<=qUp,"expectations");
    let gap=scale*BigInt(Math.max(qUp-qnum,qnum-qDown)),vsum=0n;
    const at=(f,j)=>f.zBig?f.zBig[mod(j,f.period)]:BigInt(f.z[mod(j,f.period)]);
    const abs=x=>x<0n?-x:x;
    for(let j=0;j<full;j++){
     let hi=scale*BigInt(qUp-qnum),lo=scale*BigInt(qDown-qnum),env=gap;
     for(let f of used){let x=at(f,j),y=f.k%2?-x:x;lo+=y;if(f.k<=even)hi+=y;env+=abs(x)}
     assert(lo<=zsv[j]&&zsv[j]<=hi&&abs(zsv[j])<=env,"pointwise envelope");
     vsum+=zsv[j]*zsv[j];st.pointwiseEnvelopeChecks++;
    }
    for(let j=0;j<35;j++){
     let start=rand(4*full)-2*full,n=1+rand(Math.min(full,5000)),actual=0n,zero=0;
     for(let t=start;t<start+n;t++){let v=zsv[mod(t,full)];actual+=v*v;if(Froll[mod(t,full)]===0)zero++}
     let sumNorm=Number(gap)*Math.sqrt(n);
     for(let f of used){let v=0n;for(let t=start;t<start+n;t++){let x=at(f,t);v+=x*x}assert(v<=BigInt(1+Math.floor(n/f.period))*f.v,"period L2");st.periodL2Checks++;sumNorm+=Math.sqrt(Number(v))}
     assert(Math.sqrt(Number(actual))<=sumNorm+1e-7*Math.max(1,sumNorm),"Minkowski");
     assert(BigInt(zero)*mean*mean<=actual,"zero count exact");st.zeroCountChecks++;st.localL2Controls++;
    }
    st.truncationControls++;
   }
   // Greedy disjoint intervals of empty cuts in an arbitrary translated window, exact zero-start budget.
   for(let q=0;q<20;q++){
    let a=rand(2*full)-full,n=50+rand(Math.min(2000,full)),b=a+n,long=0,starts=0,variance=0n;
    for(let j=a;j<b;j++){let v=zsv[mod(j,full)];variance+=v*v}
    for(let j=a;j<b;){if(sv[mod(j,full)]){j++;continue}let k=j+1;while(k<b&&!sv[mod(k,full)])k++;if(k-j>=2*L){long+=k-j;st.longZeroRuns++;for(let u=j;u+L<=k;u++){assert(Froll[mod(u,full)]===0,"zero start");starts++;st.zeroRunPositions++}}j=k}
    assert(long<=2*starts&&BigInt(starts)*mean*mean<=variance,"long zero-run gain");st.zeroRunControls++;
   }
   st.periodControls++;st.periodPositions+=full;
  }
 }
 const controls=[[5,13,25],[7,23,49],[11,47,121],[13,47,169],[7,47,49]].map(z=>({S:z[0],R:z[1],V:z[2],small:pr.filter(f=>f<=z[1]),extra:pr.filter(f=>f>z[1]&&f<=z[2]),K:2*prod(pr.filter(f=>f<=z[0]))}));
 function crossing(H,p,c){let K=BigInt(c.K),J=((H+K-1n)/K)*K;for(;J<H+BigInt(p-1);J+=K){if(c.small.every(f=>{let v=Number(J%BigInt(f));return f<=c.S?v===0:v%2===0&&v<=f-3})&&c.extra.every(f=>{let v=Number(J%BigInt(f));return v!==1&&v!==f-1}))return true}return false}
 const a1=z=>z.p>=47&&z.p>=5*(z.d+3)&&z.dp-6*z.I===2*z.p,reset=z=>z.p>=5&&z.dp===6*z.I;
 function inspect(rows,c,T0,kind){
  if(!rows.length)return;let x=[...rows.map(z=>z.d+3),rows.at(-1).dp+3],C=Math.max(...rows.map(z=>z.p)),cross=rows.map(z=>crossing(z.H,z.p,c)),good=[],badR=new Set,badCross=new Map;
  for(let T=T0,j=0;T<=C;T*=2,j++){
   let prev=-1,pend=0;
   for(let i=0;i<rows.length;i++)if(a1(rows[i])&&rows[i].p>c.V&&rows[i].p>=T&&rows[i].p<2*T){
    st.marks++;let b=i+1;while(b<x.length&&5*x[b]>2*T)b++;if(b===x.length){pend++;st.pending++;continue}
    assert(i>=prev,"cores");prev=b;st.completed++;
    let a=b-1;while(10*x[a]<19*T)a--;
    let rs=-1,cs=-1,bs=false,g=0,W=0;
    for(let h=a;h<b;h++){let z=rows[h];assert(!a1(z)&&5*x[h]>2*T&&10*x[h+1]<19*T,"corridor");if(reset(z)){assert(h===b-1,"reset last");rs=h}else{assert(20*x[h]<57*T,"pre bound");if(z.p>=5)assert(20*z.p<19*T,"label bound");if(cross[h]){assert(z.p>c.R,"cross label");if(cs<0)cs=h}}
     if(z.p>c.V||z.p>c.R&&z.w<=2*c.S)bs=true;g+=z.p-1;W+=z.w;
    }
    assert(g===x[a]-x[b]+2*W&&2*g>=3*T,"gain");
    if(rs>=0){st.resetBad++;badR.add(rs);continue}
    if(cs>=0){st.crossBad++;badCross.set(cs,(badCross.get(cs)||0)+1);continue}
    // Verify directly no surviving cut in the union, not just per-event flags.
    let end=rows[b-1].H+BigInt(rows[b-1].p-1),K=BigInt(c.K);
    for(let J=((rows[a].H+K-1n)/K)*K;J<end;J+=K){
     let allowed=c.small.every(f=>{let v=Number(J%BigInt(f));return f<=c.S?v===0:v%2===0&&v<=f-3})&&c.extra.every(f=>{let v=Number(J%BigInt(f));return v!==1&&v!==f-1});
     assert(!allowed,"union no cut");st.cutCrossChecks++;
    }
    st.cutFree++;if(rows.slice(a,b).some(z=>z.p>c.R)){st.cutFreeHigh++;if(st.examples.length<5)st.examples.push({kind,S:c.S,R:c.R,V:c.V,T,mark:rows[i].p,labels:rows.slice(a,b).map(z=>z.p)})}
    let rec=x[a],Dlo=0,Dhi=0,nlo=0,nhi=0,Dmid=0;
    for(let h=a;h<b;h++)if(x[h+1]<rec){let z=rows[h],delta=rec-x[h+1];assert(z.p>=5&&!reset(z)&&delta<=z.p-3,"record");
     if(z.p<=c.R){Dlo+=delta;nlo++;assert(15*x[h+1]>4*T,"multiplier scale")}else{Dhi+=delta;nhi++;assert(20*delta<19*T,"high record bound");if(!bs){assert(z.p<=c.V&&z.w>2*c.S&&delta<=c.V-3-4*c.S,"slow moderate");Dmid+=delta}}
     rec=x[h+1]
    }
    assert(rec===x[b]&&Dlo+Dhi===x[a]-x[b]&&20*(c.R-3)*nlo+19*T*nhi>=30*T,"record allocation");st.recordPartitionChecks++;
    if(!bs){st.extendedGood++;st.extendedLow+=nlo;st.extendedModerate+=nhi;assert(Dhi===Dmid&&(c.R-3)*nlo+Math.max(0,c.V-3-4*c.S)*nhi>=Dlo+Dhi,"extended weighted records");st.weightedRecordChecks++}
    good.push({a,b,j});
   }assert(pend<=1,"pending");
  }
  for(let v of badCross.values())assert(v<=3,"exception incidence");
  for(let j=0;j<3;j++){let a=good.filter(z=>z.j%3===j).sort((a,b)=>a.a-b.a);for(let i=1;i<a.length;i++){assert(a[i-1].b<=a[i].a,"color");st.colorChecks++}}
  let count=new Int32Array(rows.length);for(let z of good)for(let i=z.a;i<z.b;i++)count[i]++;
  for(let v of count){assert(v<=3,"overlap");st.maxOverlap=Math.max(st.maxOverlap,v)}st.corridorControls++;
 }
 function factors(x){let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;
  for(let k=0;k<180;k++){let best=null;for(let I=0;I<=1;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={H:BigInt(H),d:2*t-H,p,I,w,dp:2*t-H+2*w-p+1}}
   if(!best)break;rows.push(best);H+=best.p-1;t+=best.w;
  }if(rows.length===180)st.unresolved++;st.events+=rows.length;
  if(rows.some(a1))for(let c of controls)inspect(rows,c,47,"canonical")
 }
 // Reconstruct previously audited exact canonical CRT witness.
 const word=[7687,5233,3541,2389,1621,1093,733,7369],shifts=[0];for(let p of word)shifts.push(shifts.at(-1)+p-1);
 let H=0n,P=4n;for(let s of pr.filter(p=>p<=3*7687+6)){let at=word.indexOf(s),r=at>=0?mod(1-shifts[at],s):0,valid=x=>shifts.slice(0,-1).every((g,i)=>word[i]===s?mod(x+g,s)===1:![1,s-1].includes(mod(x+g,s)));while(at<0&&r<s&&!valid(r))r++;assert(r<s&&valid(r),"witness CRT");
  let a=Number(P%BigInt(s)),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}assert(a===1,"inverse");H+=P*BigInt(mod(u*mod(r-Number(H%BigInt(s)),s),s));P*=BigInt(s);st.actualWitnessResidues+=word.length}
 if(H<100000000n)H+=P;let t=H/2n+3n,rows=[];
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a};
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2;
  for(let j=1;j<=w;j++){let n=t+BigInt(j),I=n%2n;assert(gcd(n-2n*I,H-1n+2n*I)===BigInt(j===w?p:1),"literal witness");st.actualWitnessTicks++}
  rows.push({H,d,p,w,I:0,dp:2*p});H+=BigInt(p-1);t+=BigInt(w)
 }
 for(let [S,R,V] of [[3,5,7],[5,13,25],[7,47,49],[11,47,121],[13,47,169],[73,3600,5329],[79,5233,6241]]){
  let c={S,R,V,small:pr.filter(f=>f<=R),extra:pr.filter(f=>f>R&&f<=V),K:2n*bigprod(pr.filter(f=>f<=S))};inspect(rows,c,3500,"witness")
 }
 assert(st.longZeroRuns&&st.cutFree&&st.cutFreeHigh&&st.resetBad&&st.crossBad&&st.extendedGood&&st.extendedModerate&&st.localL2Controls,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||30000)),null,2));
