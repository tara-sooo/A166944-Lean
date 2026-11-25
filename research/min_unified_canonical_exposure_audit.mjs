// Primorial lower exposure for canonical-gap gain targets. Finite diagnostic parameters.
function barrierAudit(X,P,a){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),lim=7*X+B+20,spf=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(`${X} ${P} ${s}`)},mod=(a,m)=>((a%m)+m)%m;
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,reached=0,events=0,crossings=0,crossingEvents=0,crossGain=0,longGap=0,targetCount=0,actualGain=0,fullyInsideCrossings=0,reachedChecks=0,reachedExposure=0,reachedBound=0,distinctChecks=0;
 for(let M=X;M<2*X;M++)if(spf[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),can=[0],marked=[],localCross=0,localGain=0,localActual=0;
  while(C-C0<T){let p=0,v=Infinity;for(let s of [-1,1])for(let q of factors(C+s)){let alpha=s===-1?0:q+2,j=t+1+mod(alpha-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q}}
   if(!p||v>cut)break;
   let J=C+p-1,ct=C/2+3;
   if(C%4===0&&ct>=t&&ct<v&&C-C0>can[can.length-1])can.push(C-C0);
   let n=Math.ceil(J/P)-Math.ceil(C/P);
   let brute=0;for(let k=P*Math.ceil(C/P);k<J;k+=P){brute++;fail(P%p!==0&&p-1>=a,"primorial strict crossing");}
   fail(n===brute&&n<= (p-1)*(1/a+1/P)+1e-9,"crossing packing");distinctChecks++;crossings+=n;events++;
   if(n){crossingEvents++;if(J-C0<=T){marked.push([C-C0,J-C0]);localGain+=p-1;localCross+=n;}}
   C=J;t=v;localActual+=p-1;
   if(C%4===0&&2*t-C===6&&C-C0>can[can.length-1])can.push(C-C0);
  }
  const gaps=can.filter(g=>g<T);gaps.push(T);let lg=0,nsel=0;
  for(let i=1;i<gaps.length;i++){let l=gaps[i]-gaps[i-1];if(l>=a){lg+=l;nsel+=Math.ceil(l/2)}}
  let idx=0;for(let [l,h] of marked){while(gaps[idx+1]<=l)idx++;fail(gaps[idx]<=l&&h<=gaps[idx+1]&&gaps[idx+1]-gaps[idx]>=a,"crossing gain inside long gap")}
  fail(localGain<=lg&&nsel>=lg/2&&localCross<=localGain*(1/a+1/P)+1e-9,"local exposure");
  if(C-C0>=T){reached++;let need=Math.max(0,T-B-P)*a/(P+a);fail(localGain+1e-9>=need&&nsel+1e-9>=need/2,"reached exposure bound");reachedChecks++;reachedExposure+=nsel;reachedBound+=need/2}
  crossGain+=localGain;fullyInsideCrossings+=localCross;longGap+=lg;targetCount+=nsel;actualGain+=localActual;
 }
 return {X,P,a,B,T,N,reached,events,crossings,crossingEvents,fullyInsideCrossings,crossGain,longGap,targetCount,actualGain,reachedChecks,reachedExposure,reachedBound:+reachedBound.toFixed(6),distinctChecks};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))for(const [P,a] of [[6,3],[30,5],[210,7]]) console.log(JSON.stringify(barrierAudit(X,P,a)));
