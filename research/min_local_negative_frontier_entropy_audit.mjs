// Actual near-square-root low-gain frontier: Shannon entropy versus collision energy.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let x=p*p;x<=N;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let v=mod((s===-1?0:q+2)-n,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v}}return {p,w}}
 let out={roots:0,events:0,roughChecks:0,entropyChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),S=Math.sqrt(2*R+1),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,counts=new Map(),all=0,selected=0,selectedTw=0,badCount=0,twinCount=0;
  for(let a=2*Math.ceil((lo-2*T-6)/2);a<=hi;a+=2){let p=spf[a-1]||a-1,q=spf[a+1]||a+1;if(p>K&&q>K){if(p===a-1&&q===a+1)twinCount++;else badCount++}}
  for(let A=lo;A<=hi;A+=6){let a=A,n=3-A/2,end=n+T,W=0;
   for(;;){let e=next(a,n);if(n+e.w>end)break;a-=e.p-1;n+=e.w;W+=e.w;out.events++}
   let G=A-a;all+=G;out.roots++;
   if(G<=J){ck(T-W>2*K&&W<=9*G/4+8,"idle");ck((spf[a-1]||a-1)>K&&(spf[a+1]||a+1)>K,"rough");out.roughChecks++;selected++;counts.set(a,(counts.get(a)||0)+1);if(!spf[a-1]&&!spf[a+1])selectedTw++}
  }
  let E=0,H=0,max=0,badSel=0,goodSel=0,twMass=0;
  for(let [a,m] of counts){E+=m*m;H+=m*Math.log(m);max=Math.max(max,m);if(!spf[a-1]&&!spf[a+1]){goodSel++;twMass+=m}else badSel++}
  ck(selectedTw===twMass&&goodSel<=twinCount&&badSel<=badCount,"counts");H/=selected;let eff=selected*Math.exp(-H);ck(eff<=counts.size+1e-8&&eff+1e-8>=selected**2/E,"entropy supports");out.entropyChecks++;
  let x=twMass/selected,h=x===0||x===1?0:-x*Math.log(x)-(1-x)*Math.log(1-x);let rhs=h+(1-x)*Math.log(Math.max(1,badCount))+x*Math.log(Math.max(1,twinCount));ck(Math.log(selected)-H<=rhs+1e-10,"binary entropy split");out.entropyChecks++;
  out.rows.push({R,K,T,J,nr,selected,selectionRate:selected/nr,meanGain:all/nr/T,distinct:counts.size,badCount,twinCount,badSel,goodSel,twMass,entropy:H,entropyEffectiveSupport:eff,renyi2:Math.log(E/selected),collisionEffectiveSupport:selected**2/E,max,margin:Math.log(eff/Math.max(1,badCount)),effectiveVsBad:eff/Math.max(1,badCount),entropyOverLogLog:H/Math.log(Math.log(R))})
 }return out;
}
console.log(JSON.stringify(audit(),null,2));
