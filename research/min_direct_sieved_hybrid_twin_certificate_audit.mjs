// Primorial-offset twin certificates and Bonferroni-smoothed hybrid barrier diagnostics.
function audit(N=60000){
 const limit=1000000,spf=new Int32Array(limit),pr=[];
 for(let i=2;i<limit;i++)if(!spf[i]){spf[i]=i;if(i%2)pr.push(i);if(i*i<limit)for(let j=i*i;j<limit;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,assert=(x,m)=>{if(!x)throw Error(m)},prod=a=>a.reduce((v,p)=>v*p,1);
 const isprime=x=>x>=2&&x<limit&&spf[x]===x;
 const factors=x=>{assert(x>0&&x<limit,"sieve range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a};
 let seed=91751;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 const st={roots:0,events:0,capUnresolved:0,a1Events:0,a1LeastChecks:0,moderateCrossings:0,anchoredUnsieved:0,strictUnsievedTwin:0,sievedCrossings:0,sievedTwinWitnesses:0,sievedA1Witnesses:0,sievedFastDecreases:0,strictCertificates:0,fastClockChecks:0,hybridPeriodControls:0,intersectionPeriods:0,crtPositionChecks:0,variancePositionChecks:0,pointwiseBonferroniChecks:0,smoothedBonferroniChecks:0,unionControls:0,lowerMassChecks:0,upperMassChecks:0,cauchyChecks:0,witness:null,a1Witness:null,fastExample:null,periodSummaries:[]};
 function hbar(H,ps,S){return ps.every(f=>{let z=mod(H,f);return f<=S?z===0:z%2===0&&z<=f-3})}
 function setup(S,R,V){let ps=pr.filter(f=>f<=R),extra=pr.filter(f=>f>R&&f<=V);return {S,R,V,ps,extra,K:2*prod(ps.filter(f=>f<=S)),P:prod(ps)}}
 const controls=[[5,7,25],[7,7,49],[7,11,49],[7,13,49],[11,13,121],[11,17,121],[13,17,169]].map(z=>setup(...z));
 function next(H,t){let best=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,w,I}}return best}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2;st.roots++;
  let k=0;for(;k<180;k++){let z=next(H,t);if(!z)break;let {p,w,I}=z,d=2*t-H,dp=d+2*w-p+1,A1=p>=47&&p>=5*(d+3)&&dp-6*I===2*p;st.events++;
   let fmin=Math.min(spf[H-1],spf[H+1]);if(A1){assert(fmin===p,"A1 least factor");st.a1Events++;st.a1LeastChecks++}
   for(let c of controls){if(p<=c.R||p>c.V)continue;
    for(let J=Math.ceil(H/c.K)*c.K;J<H+p-1;J+=c.K){if(!hbar(J,c.ps,c.S))continue;st.moderateCrossings++;
     let u=J-H;assert(u%2===0&&u>=0&&u<=p-3&&u+1<c.S*c.S,"offset range");
     let rough=fmin>c.S,sv=c.extra.every(f=>![1,f-1].includes(J%f));
     if(u===0){st.anchoredUnsieved++;assert(!sv,"anchor excluded by chosen p")}
     if(rough&&u){assert(u>=4&&isprime(u-1)&&isprime(u+1)&&u-1>c.S,"strict twin");st.strictCertificates++;if(!sv)st.strictUnsievedTwin++}
     if(!sv)continue;
     st.sievedCrossings++;assert(u>0,"strict sieve");
     if(rough){st.sievedTwinWitnesses++;let ex={M,H,t,p,w,I,d,dp,S:c.S,R:c.R,V:c.V,J,u,twins:[u-1,u+1]};if(!st.witness)st.witness=ex;if(A1){st.sievedA1Witnesses++;if(!st.a1Witness)st.a1Witness=ex}}
     else{assert(w<=2*fmin&&fmin<=c.S&&d-dp>=p-1-4*c.S,"fast recovery");assert(!A1,"A1 cannot have small divisor");st.sievedFastDecreases++;st.fastClockChecks++;if(!st.fastExample)st.fastExample={M,H,t,p,w,d,dp,S:c.S,R:c.R,V:c.V,J,u,smallFactor:fmin}}
    }
   }
   H+=p-1;t+=w;
  }if(k===180&&next(H,t))st.capUnresolved++;
 }
 const tests=[[3,5,7],[5,7,17],[7,7,13],[7,11,17],[11,13,17],[3,7,17]];
 for(let [S,R,V] of tests){
  let c=setup(S,R,V),{P,ps,extra}=c,Q=prod(extra),L=Math.max(1,Math.ceil(P**(4/11))),full=P*Q,A=prod(ps.map(f=>f<=S?1:(f-1)/2));
  assert(full<=300000,"period cap");let allMask=(1<<extra.length)-1,sub=[];
  function base(j){return hbar(2*j,ps,S)}
  for(let mask=0;mask<=allMask;mask++){
   let ff=extra.filter((p,i)=>mask&(1<<i)),q=prod(ff),period=P*q,AA=A*2**ff.length,arr=new Uint8Array(period),cnt=0;
   for(let j=0;j<period;j++){let b=base(j)&&ff.every(f=>[1,f-1].includes(mod(2*j,f)));arr[j]=b?1:0;cnt+=arr[j];st.crtPositionChecks++}
   assert(cnt===AA,"intersection CRT count");
   let roll=new Int32Array(period),n=0;for(let i=0;i<L;i++)n+=arr[i%period];
   let Vnum=0n;for(let j=0;j<period;j++){roll[j]=n;let x=BigInt(period)*BigInt(n)-BigInt(AA*L);Vnum+=x*x;n+=arr[(j+L)%period]-arr[j];st.variancePositionChecks++}
   assert(n===roll[0],"periodic rolling");
   sub.push({mask,ff,q,period,AA,arr,roll,Vnum,k:ff.length,w:2**ff.length*(Q/q)});st.intersectionPeriods++;
  }
  let sv=new Uint8Array(full),svroll=new Int32Array(full),cnt=0;
  for(let j=0;j<full;j++){sv[j]=base(j)&&extra.every(f=>![1,f-1].includes(mod(2*j,f)))?1:0;cnt+=sv[j]}
  assert(cnt===A*prod(extra.map(f=>f-2)),"sieve CRT density");
  let n=0;for(let i=0;i<L;i++)n+=sv[i%full];
  for(let j=0;j<full;j++){svroll[j]=n;n+=sv[(j+L)%full]-sv[j]}
  for(let j=0;j<full;j++){
   let s=0,t=0;
   for(let k=0;k<=extra.length;k++){for(let f of sub)if(f.k===k){s+=(k%2?-1:1)*f.arr[j%f.period];t+=(k%2?-1:1)*f.roll[j%f.period]}
    assert(k%2?s<=sv[j]:s>=sv[j],"pointwise Bonferroni");assert(k%2?t<=svroll[j]:t>=svroll[j],"smoothed Bonferroni");st.pointwiseBonferroniChecks++;st.smoothedBonferroniChecks++}
   assert(s===sv[j]&&t===svroll[j],"full inclusion-exclusion")
  }
  for(let h=0;h<180;h++){
   let a=rand(4*full)-2*full,len=30+rand(800),b=a+len,nprime=len+L-1,inter=[],pos=a;
   while(pos<b){pos+=rand(12);if(pos>=b)break;let end=Math.min(b,pos+1+rand(30));inter.push([pos,end]);pos=end+rand(9)}
   let cover=new Set,Ucnt=0,Ulen=0;
   for(let [u,v] of inter){Ulen+=v-u;for(let j=u;j<v;j++)Ucnt+=sv[mod(j,full)];for(let j=u-L+1;j<v;j++)cover.add(j)}
   assert(cover.size<=Ulen+(L-1)*inter.length,"union expansion");
   let smooth=0,total=0;for(let j of cover)smooth+=svroll[mod(j,full)];for(let j=a;j<b;j++)total+=sv[mod(j,full)];
   assert(L*Ucnt<=smooth,"nonnegative smoothed union");
   for(let K=0;K<=extra.length;K++){
    let used=sub.filter(f=>f.k<=K),qK=used.reduce((z,f)=>z+(f.k%2?-1:1)*f.w,0);
    if(K%2){let err=used.reduce((z,f)=>z+BigInt(f.w)*BigInt(f.period),0n);
     assert(BigInt(P)*BigInt(Q)*BigInt(total)>=BigInt(A)*BigInt(qK)*BigInt(len)-BigInt(A)*err,"lower sieve mass");st.lowerMassChecks++;
    }else{
     let err=0n;for(let f of used){let diff=0n;for(let j=a-L+1;j<b;j++){let x=BigInt(f.period)*BigInt(f.roll[mod(j,f.period)])-BigInt(f.AA*L);diff+=x<0n?-x:x}
      assert(diff*diff*BigInt(f.period)<=BigInt(nprime)*BigInt(nprime+f.period)*f.Vnum,"exact Cauchy");
      err+=BigInt(Q/f.q)*diff;st.cauchyChecks++;
     }
     assert(BigInt(P)*BigInt(Q)*BigInt(smooth)<=BigInt(A*L)*BigInt(qK)*BigInt(cover.size)+err,"upper smoothed sieve mass");st.upperMassChecks++;
    }
   }st.unionControls++;
  }
  st.hybridPeriodControls++;st.periodSummaries.push({S,R,V,P,Q,L,full,baseCount:A,sievedCount:cnt,extra})
 }
 assert(st.sievedA1Witnesses&&st.sievedFastDecreases&&st.anchoredUnsieved&&st.strictCertificates&&st.cauchyChecks,"coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
