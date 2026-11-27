// Actual first-exit collision bound: exact pair parametrization, height pins and reset replay.
// Run with node. Analytic sieve estimates are separate from this finite audit.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const MAX=1600002,sp=new Int32Array(MAX+2);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let n=p*p;n<sp.length;n+=p)if(!sp[n])sp[n]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"range");a.push(p);while(n%p===0)n/=p}return a}
 function next(x,n){let w=Infinity,p=0,s=0;
  for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||(t===w&&q<p)){w=t;p=q;s=e}}
  return {w,p,s}
 }
 function literal(x,n,T){const a=fac(x-1),b=fac(x+1);for(let i=1;i<=T;i++){let nn=n+i,qs=nn%2===0?b:a;for(let p of qs)if(mod(nn,2*p)===(nn%2===0?0:p+2))return {w:i,p,s:nn%2===0?1:-1}}return null}
 let rows=[],detChecks=0,pairChecks=0,clockChecks=0,exitChecks=0,rootChecks=0,phaseChecks=0;
 for(let R of [12000,48000,192000,768000]){
  let z=Math.max(11,Math.floor(R**.198)),m=new Map(),all=new Map(),clock=new Map(),primeM=new Map(),N=0,primeN=0,twinN=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let q0=Math.min(sp[A-1],sp[A+1]);if(q0<z)continue;rootChecks++;
   if(sp[A-1]===A-1&&sp[A+1]===A+1){twinN++;continue}
   let n=3-A/2,e=next(A,n),l=literal(A,n,e.w);ok(l.p===e.p&&l.w===e.w&&l.s===e.s,"literal first event");
   ok(e.p>=z&&e.p<=4*q0+7&&e.w<=2*q0,"bounds");
   let x=A-e.p+1,h=x/2+n+e.w,s=e.s,p=e.p,c=1-s;
   ok((x-c)%p===0&&h%p===(s===1?0:3%p),"incoming pins");
   let v={A,x,h,p,s,n:n+e.w};N++;exitChecks++;
   const add=(map,key,v)=>{if(!map.has(key))map.set(key,[]);map.get(key).push(v)};
   add(m,x+","+s,v);add(all,x,v);add(clock,x+","+v.n,v);
   if(sp[A-1]===A-1){ok(s===1,"prime-minus family plus winner");primeN++;add(primeM,x,v)}
  }
  let samePairs=0,allPairs=0,primePairs=0,clockPairs=0;
  const pc=map=>[...map.values()].reduce((s,a)=>s+a.length*(a.length-1)/2,0);
  for(let arr of m.values())for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length;j++){
   let a=arr[i],b=arr[j],p=a.p,q=b.p,s=a.s,c=1-s;
   ok(p!==q&&a.x===b.x&&a.s===b.s,"distinct same-sign parents");let t=(a.x-c)/(p*q);ok(Number.isInteger(t)&&t>=1,"common product");
   const forms=[[1,0],[t,1],[q*t+1,-2*s],[q*t,q-2*s]];
   const vals=forms.map(([u,v])=>u*p+v);
   ok(vals[2]===a.A-s&&vals[3]===b.A-s&&vals[1]===(b.A+s)/q&&q*t+1===(a.A+s)/p,"four form identities");
   ok(vals.every(x=>sp[x]>=z)&&sp[q*t+1]>=z,"all rough");
   for(let k=0;k<4;k++)for(let v=k+1;v<4;v++){ok(forms[k][0]*forms[v][1]!==forms[v][0]*forms[k][1],"nonzero determinant");detChecks++}
   samePairs++;pairChecks++;
  }
  allPairs=pc(all);primePairs=pc(primeM);clockPairs=pc(clock);
  for(let arr of clock.values())for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length;j++){
   let a=arr[i],b=arr[j];ok(a.s===b.s,"simultaneous sign");clockChecks++;
   ok((a.h-(a.s===1?0:3))%(a.p*b.p)===0,"height product");
  }
  ok(clockPairs<=samePairs&&primePairs<=samePairs,"pair subsets");
  ok(m.size>=N-samePairs&&all.size>=(N-samePairs)/2&&primeM.size>=primeN-primePairs,"distinct lower");
  rows.push({R,z,N,primeN,twinN,sites:all.size,signedSites:m.size,primeSites:primeM.size,states:clock.size,samePairs,allPairs,primePairs,clockPairs})
 }
 // Nonvacuous fixed-scale reset proxies. Use p=1 mod12 and pin x' rough at 11
 // by testing actual v residues and factors rather than forcing the asymptotic
 // modulus 420 (too restrictive at these finite sizes).
 let resetExamples=0,resetEventTicks=0,postExitEvents=0,resetSites=new Set(),maxWait=0,forcedProgress=0;
 for(let p=13;p<=181;p++)if(sp[p]===p&&p%12===1){
  for(let v=p+1;v<=Math.floor((MAX-1)/p);v++)if(sp[v]===v&&v%12===1&&sp[p*v-2]>=p){
   const A=p*v-1,x=p*(v-1);
   if(Math.min(sp[x-1],sp[x+1])<11)continue;
   const n=3-A/2,w=(p-7)/2,l=literal(A,n,w);
   ok(l&&l.w===w&&l.p===p&&l.s===1,"prescribed first event");
   ok(n+w===-x/2&&literal(x,n+w,3)===null,"exact birth reset");
   ok(sp[A+1]===p&&p*v!==p,"source composite");
   resetExamples++;resetEventTicks+=w+3;maxWait=Math.max(maxWait,w);resetSites.add(x);
   // Exercise the deterministic neighborhood-crossing conclusion at fixed proxy.
   const J=20,K=31;
   if(x>J+2&&Array.from({length:J/2+1},(_,i)=>x-2*i).every(y=>Math.min(sp[y-1],sp[y+1])<K)){
    let y=x,nn=3-x/2,t=0;
    while(x-y<=J){let e=next(y,nn);ok(e.w<2*K,"short neighborhood");y-=e.p-1;nn+=e.w;t+=e.w;postExitEvents++}
    ok(t<=2*K*(J/2+1),"crossing time");forcedProgress++;
   }
  }
 }
 return {rows,rootChecks,exitChecks,pairChecks,detChecks,clockChecks,resetExamples,resetEventTicks,resetSites:resetSites.size,maxWait,forcedProgress,postExitEvents};
}
console.log(JSON.stringify(audit(),null,2));
