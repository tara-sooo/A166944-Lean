// Standalone exact tick-mass / deficit packing and sparse-interval audit. Diagnostic thresholds are deliberately finite and non-asymptotic.
function deficitPackingAudit(X,mode="diagnostic"){
 const B=Math.ceil(Math.sqrt(7*X)),u=Math.log(B),ell=1+Math.log(u),T=mode==="analytic"?Math.floor(X/Math.pow(u,.25)):Math.min(8*B,Math.floor(X/2)),H=T+B,dh=6+5*H;
 const Q=mode==="analytic"?Math.ceil(B/u):Math.max(5,Math.ceil(B/10)),R=mode==="analytic"?B/(2*Math.pow(u,1.5)):Q/2;
 const mh=mode==="analytic"?u*u/(ell*ell):1.5,Lh=mode==="analytic"?u*u*u/(ell*ell):8;
 const S=mode==="analytic"?Math.max(1,Math.floor(H/(4*u*ell*ell))):2*B,minLen=mode==="analytic"?Math.ceil(Math.pow(B,1.5)):Math.max(4,Math.floor(B/2)),eta=mode==="analytic"?Math.pow(u,-.25):.2;
 const limit=7*X+10,spf=new Int32Array(limit),mod=(a,m)=>((a%m)+m)%m,fail=(b,s)=>{if(!b)throw Error(`${X} ${mode}: ${s}`)};
 for(let p=2;p<limit;p++)if(!spf[p]){spf[p]=p;if(p*p<limit)for(let j=p*p;j<limit;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];fail(p>0,"factor");if(p<=B&&p!==2)a.push(p);while(n%p===0)n/=p}return a}
 function eventAt(t,C){let r=Infinity,p=0,v=Infinity;for(let s of [-1,1])for(let q of factors(C+s)){r=Math.min(r,q);let phase=s===-1?0:q+2,j=t+1+mod(phase-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q}}return {r,p,v}}
 const high=e=>e.p>=Q&&(mode==="analytic"?e.r>e.p/Math.sqrt(Math.log(e.p)):2*e.r>e.p);
 const f=d=>Math.max(1,Math.sqrt(H/(d+1)),H/(u*(d+1)));
 const mr=r=>mode==="analytic"?Math.pow(Math.log(2+r),2)/(u*ell*ell):.1*Math.pow(Math.log(2+r)/u,2);
 const lr=r=>mode==="analytic"?Math.pow(Math.log(2+r)/ell,2):2*Math.pow(Math.log(2+r)/u,2);
 let fs=0;for(let d=0;d<=dh;d++)fs+=f(d);
 let buckets=new Map(),rByC=new Map(),highHorizons=0;for(let C=2*X-2;C<=7*X;C+=2){let q=Math.min(...factors(C-1),...factors(C+1));if(!Number.isFinite(q))continue;rByC.set(C,q);buckets.set(q,(buckets.get(q)||0)+1);if(q>=R)highHorizons++;}
 let paths=[],states=new Map(),events=0,raw=0,rawHigh=0,literal=0,resetEvents=0,resetTicks=0;
 function gcd(a,b){while(b){let x=a%b;a=b;b=x}return a}
 const key=(t,C)=>t*limit+C;
 for(let M=X;M<2*X;M++)if(spf[M]===M){let s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),t=s,C=C0,es=[],ticks=[];
   while(C-C0<T){let {r,p,v}=eventAt(t,C);
     if(X<=1024&&literal<4000){let pp=0,vv=Infinity;for(let j=t+1;j<=Math.min(K,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1),q=factors(g)[0];if(q){pp=q;vv=j;break}}fail((!p||v>K)?vv===Infinity:pp===p&&vv===v,"literal MIN");literal++}
     if(!p||v>K)break;
     let J=C+p-1,w=v-t,d0=2*t-C,d1=2*v-J,s1=v%2,phase=d1-6*s1,e={t,C,v,p,r,J,w,phase,live:0};
     fail(r===rByC.get(C)&&w>=1&&w<=2*r&&w<=3*(p-1)&&d0>=0&&d1>=0&&d1<=dh,"event geometry");
     fail(phase%(2*p)===0,"adjusted phase divisibility");if(phase===0)resetEvents++;
     events++;raw+=w;if(high(e)){rawHigh+=w;fail(r>=R,"high support");}
     for(let j=t;j<v;j++){let d=2*j-C;fail(d>=0&&d<=dh,"tick deficit");if(phase===0){fail(d<=B+6,"RESET wait lies in low deficit");resetTicks++}
       let k=key(j,C),a=states.get(k);if(!a){a={n:0,C,j,d,p,r,v,flag:0};states.set(k,a)}
       fail(a.p===p&&a.r===r&&a.v===v,"common tick deterministic exit");a.n++;ticks.push(a)
     }
     es.push(e);t=v;C=J;
   }
   paths.push({M,s,C0,es,ticks,end:t,endC:C});
 }
 const N=paths.length,paid=[0,0,0,0,0],paidHigh=[0,0,0,0,0],observedByR=new Map(),maxByR=new Map();let maxN=0,allRet=0,highRet=0,resetHighRet=0,lowBHighRet=0,peakNeed=0,minLiveMass=Infinity,lowBMinMass=Infinity,liveStates=0;
 for(let a of states.values()){let {r,d,n}=a;maxN=Math.max(maxN,n);let bh=r>=R;
   let flag=n<=mr(r)*f(d)?1:d+1<=lr(r)?2:bh&&n<=mh*f(d)?3:bh&&d+1<=Lh?4:0;a.flag=flag;
   paid[flag]+=n;let e={p:a.p,r};if(high(e))paidHigh[flag]+=n;
   let v=observedByR.get(r)||[0,0,0,0,0];v[flag]+=n;observedByR.set(r,v);maxByR.set(r,Math.max(maxByR.get(r)||0,n));
   if(!flag){allRet+=n;liveStates++;fail(n>mr(r)*f(d)&&d+1>lr(r),"general retained inequalities");fail(d+1+1e-8>=H*Math.pow(mr(r)/n,2)&&d+1+1e-8>=H*mr(r)/(u*n),"general inverse deficit bound");
     if(bh)fail(n>mh*f(d)&&d+1>Lh,"large-factor retained inequalities");
     if(high(e)){highRet+=n;minLiveMass=Math.min(minLiveMass,n);if(d<=B){lowBHighRet+=n;lowBMinMass=Math.min(lowBMinMass,n);peakNeed=Math.max(peakNeed,mh*f(d))}}
   }
 }
 let budgetGeneralMass=0,budgetGeneralLow=0,budgetHighMass=0,budgetHighLow=0;
 for(let [r,c] of buckets){let mmax=maxByR.get(r)||0,b=observedByR.get(r)||[0,0,0,0,0];
   let bm=c*mr(r)*fs,bl=c*mmax*lr(r),hm=r>=R?c*mh*fs:0,hl=r>=R?c*mmax*Lh:0;
   fail(b[1]<=bm+1e-6&&b[2]<=bl+1e-6&&b[3]<=hm+1e-6&&b[4]<=hl+1e-6,"finite factorwise packing");
   budgetGeneralMass+=bm;budgetGeneralLow+=bl;budgetHighMass+=hm;budgetHighLow+=hl;
 }
 fail(paid.reduce((a,b)=>a+b,0)===raw&&paidHigh.reduce((a,b)=>a+b,0)===rawHigh&&paid[0]===allRet&&paidHigh[0]===highRet,"exact tick partition");
 let sparsePaid=0,retainedHigh=0,intervalChecks=0,witnessChecks=0,blocks=0,nonempty=0,nearLowChecks=0,resetHighChecks=0,minWitnessLabels=Infinity,minWitnessPhases=Infinity,maxPhaseDivisors=0;
 for(let path of paths){
   let {es,ticks}=path,lastLow=path.C0,nextLow=null,at=0,nexts=new Array(ticks.length);
   if(2*path.end-path.endC<=6)nextLow=path.endC;
   for(let i=ticks.length-1;i>=0;i--){nexts[i]=nextLow;if(ticks[i].d<=6)nextLow=ticks[i].C;}
   for(let e of es){for(let j=e.t;j<e.v;j++){let a=ticks[at];fail(a.j===j&&a.C===e.C,"path tick index");if(a.d<=6)lastLow=a.C;
       if(!a.flag&&high(e)){e.live++;fail(a.d-6<=5*(a.C-lastLow)+4*B,"previous low-deficit separation");if(nexts[at]!==null)fail(nexts[at]-a.C>=a.d-6,"future low-deficit separation");nearLowChecks++;
         if(e.phase===0){fail(a.d<=B+6&&a.n>mh*f(a.d),"retained RESET threshold");resetHighRet++;resetHighChecks++}
       }at++;
     }
     if(high(e)&&e.phase!==0){let x=Math.abs(e.phase),k=0;for(let p=2;p*p<=x;p++)if(x%p===0){if(p>=Q)k++;while(x%p===0)x/=p}if(x>=Q)k++;
       maxPhaseDivisors=Math.max(maxPhaseDivisors,k);
     }
   }
   // Blocks of consecutive original gain intervals, aligned by prehorizon.
   for(let a=0;a<es.length;){let K=S*Math.floor((es[a].C-1)/S),b=a+1;while(b<es.length&&S*Math.floor((es[b].C-1)/S)===K)b++;
     blocks++;let E=es.slice(a,b),k=E.length,xx=E.map(e=>e.C);xx.push(E[k-1].J);let pref=[0],diff=new Int32Array(k+1);
     for(let e of E)pref.push(pref[pref.length-1]+e.live);
     if(pref[k])nonempty++;
     for(let i=0;i<k;i++)for(let j=i+1;j<=k;j++){let L=xx[j]-xx[i],w=pref[j]-pref[i];if(L<minLen)continue;intervalChecks++;if(w<=eta*L+1e-9){diff[i]++;diff[j]--;}}
     let covered=0,bpaid=0,keptPrefix=[0];for(let i=0;i<k;i++){covered+=diff[i];let v=covered?0:E[i].live;bpaid+=E[i].live-v;keptPrefix.push(keptPrefix[i]+v);}
     fail(bpaid<=2*eta*(xx[k]-xx[0])+1e-7,"sparse union linear bound");sparsePaid+=bpaid;retainedHigh+=keptPrefix[k];
     for(let i=0;i<k;i++)for(let j=i+1;j<=k;j++){if(xx[j]-xx[i]<minLen||keptPrefix[j]===keptPrefix[i])continue;
       fail(pref[j]-pref[i]>eta*(xx[j]-xx[i])-1e-9,"every interval containing retained wait dense");witnessChecks++;
       let P=new Set(),A=new Set(),hasReset=false;for(let l=i;l<j;l++)if(E[l].live){P.add(E[l].p);if(E[l].phase===0)hasReset=true;else A.add(E[l].phase)}
       minWitnessLabels=Math.min(minWitnessLabels,P.size);if(!hasReset)minWitnessPhases=Math.min(minWitnessPhases,A.size);
     }
     a=b;
   }
 }
 fail(sparsePaid+retainedHigh===highRet,"sparse retained partition");
 return {X,mode,B,T,H,Q,R,mh,Lh,S,minLen,eta,N,events,literal,states:states.size,raw,rawHigh,highHorizons,maxN,paid,paidHigh,allRet,highRet,liveStates,minLiveMass:Number.isFinite(minLiveMass)?minLiveMass:null,lowBHighRet,lowBMinMass:Number.isFinite(lowBMinMass)?lowBMinMass:null,peakNeed,resetEvents,resetTicks,resetHighRet,nearLowChecks,resetHighChecks,blocks,nonempty,intervalChecks,witnessChecks,sparsePaid,retainedHigh,minWitnessLabels:Number.isFinite(minWitnessLabels)?minWitnessLabels:null,minWitnessPhases:Number.isFinite(minWitnessPhases)?minWitnessPhases:null,maxPhaseDivisors,packingBudget:[budgetGeneralMass,budgetGeneralLow,budgetHighMass,budgetHighLow].map(Math.floor)};
}
const args=process.argv.slice(2);const mode=args[0]||'diagnostic';for(const X of (args.length>1?args.slice(1).map(Number):[256,1024,4096,16384])) console.log(JSON.stringify(deficitPackingAudit(X,mode)));
