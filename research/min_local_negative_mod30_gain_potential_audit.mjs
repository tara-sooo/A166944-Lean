// Finite mod-30 priority potential: universal W <= 9G/4 + 8.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const N=300000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function wait(v,p,e){return mod((e===-1?0:p+2)-v,2*p)||2*p}
 function next(a,v,P=null){let p=Infinity,w=Infinity,e=0;for(let [d,f] of [[a+1,-1],[a-1,1]])for(let q of (P||fs(d))){if(P&&mod(d,q)!==0)continue;let t=wait(v,q,f);if(t<w||t===w&&q<p){p=q;w=t;e=f}}return {p,w,e}}
 const state=(a,v)=>mod(a,30)/2*30+mod(v,30),pr=[];for(let p=7;p<=151;p+=2)if(!spf[p])pr.push(p);
 let E=[],smallEdges=0,largeEdges=0;
 for(let a=0;a<30;a+=2)for(let v=0;v<30;v++){
  // Use direct residue tests, including formal negative/zero states.
  let p=Infinity,w=Infinity;for(let q of [3,5])for(let e of [-1,1])if(mod(a-e,q)===0){let t=wait(v,q,e);if(t<w||t===w&&q<p){p=q;w=t}}
  let i=state(a,v);if(isFinite(p)){E.push([i,state(a-p+1,v+w),p,w]);smallEdges++}
  for(let q of pr){let W=Math.min(2*q,w-1);for(let t=1;t<=Math.min(30,W);t++){let t0=t+30*Math.floor((W-t)/30);E.push([i,state(a-q+1,v+t0),q,t0]);largeEdges++}}
 }
 let F=new Int32Array(450),iterations=0;
 while(true){let changed=false;for(let [i,j,p,w] of E){let b=F[i]+4*w-9*(p-1);if(b>F[j]){F[j]=b;changed=true}}iterations++;if(!changed)break;ck(iterations<450,"positive cycle")}
 let min=Math.min(...F),max=Math.max(...F),span=max-min;
 ck(span===32&&9-153<=-span,"tail bound");
 for(let [i,j,p,w] of E)ck(4*w-9*(p-1)<=F[j]-F[i],"compressed edge inequality");
 let allWaits=0;
 // Independent noncompressed exhaustive transition verification on
 // finite labels through 151. All later labels use 9-p<=-span.
 for(let a=0;a<30;a+=2)for(let v=0;v<30;v++){
  let p=Infinity,w=Infinity;for(let q of [3,5])for(let e of [-1,1])if(mod(a-e,q)===0){let t=wait(v,q,e);if(t<w||t===w&&q<p){p=q;w=t}}
  if(isFinite(p))ck(4*w-9*(p-1)<=F[state(a-p+1,v+w)]-F[state(a,v)],"small winner");
  for(let q of pr)for(let t=1;t<=2*q&&t<w;t++){ck(4*t-9*(q-1)<=F[state(a-q+1,v+t)]-F[state(a,v)],"all waits");allWaits++}
 }
 let s={states:450,smallEdges,largeEdges,compressedEdges:E.length,iterations,min,max,span,allWaits,roots:0,events:0,tailEvents:0,prefixChecks:0,halfStops:0,timeStops:0,twinFree:0,twinFreeGainChecks:0,smallGainWitnesses:0,linearHorizonChecks:0,linearHorizonWitnesses:0,maxRatio:0,potential:Array.from(F)};
 for(let A=12;A<=300000;A+=6){
  let a=A,v=3-A/2,v0=v,W=0,G=0,seen=false,reason,H=Math.floor(A/8),hchecked=false;
  function horizon(){if(hchecked)return;hchecked=true;s.linearHorizonChecks++;
   // This records the last completed event at or before H.
   if(G<(4/9)*(H-2*Math.sqrt(A+1)-8)){ck(seen,"early witness");s.linearHorizonWitnesses++}
  }
  while(true){if(a<=A/2){reason="half";break}let x=next(a,v);let q=Math.min(...fs(a-1),...fs(a+1));if(q>Math.sqrt(a+1))seen=true;
   if(W+x.w>H)horizon();
   if(v+x.w>-1){reason="time";break}
   ck(4*x.w-9*(x.p-1)<=F[state(a-x.p+1,v+x.w)]-F[state(a,v)],{A,a,v,x});
   if(x.p>151)s.tailEvents++;
   a-=x.p-1;v+=x.w;W+=x.w;G+=x.p-1;s.events++;
   ck(4*W<=9*G+F[state(a,v)]-F[state(A,v0)]&&W<=9*G/4+8,"telescope");s.prefixChecks++;
  }
  s.roots++;s[reason+"Stops"]++;
  let B=Math.min(A/2,(4/9)*(A/2-4-2*Math.sqrt(A+1)-8));
  if(!seen){s.twinFree++;ck(G>=B-1e-8,"gain lower");s.twinFreeGainChecks++}
  if(G<B-1e-8){ck(seen,"gain witness");s.smallGainWitnesses++}
  if(G)s.maxRatio=Math.max(s.maxRatio,W/G)
 }
 return s
}
console.log(JSON.stringify(audit(),null,2));
