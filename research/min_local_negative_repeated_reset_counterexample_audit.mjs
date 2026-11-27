// Canonical repeated reset blocks: explicit CRT certificates for unbounded p=5 same-height descent counts.
function audit(){
 const mod=(a,p)=>(a%p+p)%p,ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))};
 function prime(n){if(n<2||n%2===0)return n===2;for(let q=3;q*q<=n;q+=2)if(n%q===0)return false;return true}
 function plist(N){let a=[];for(let q=3;q<=N;q+=2)if(prime(q))a.push(q);return a}
 function smallBlock(A){let a=A,n=-A/2,h=0,t=0,ev=[],tick=[];
  while(t<10){let b=h+1; n++;t++;let side=mod(n,2)?1:-1,f=Math.abs(side===-1?2*b+1:2*b-5),p=1;
   for(let q=3;q<=f;q+=2)if(prime(q)&&f%q===0&&mod(a-side,q)===0){p=q;break}
   let before=a;a-=p-1;h=b-(p-1)/2;tick.push({t,b,side,f,p,offset:A-before,post:h});if(p>1)ev.push({p,b,h})
  }ck(A-a===14&&h===3&&a%30===0&&ev.filter(e=>e.p===5).map(e=>e.b).join(",")==="2,5","small block");ck(tick.every(x=>[1,3,5,9].includes(x.f)),"all clock factors");return {ev,tick}
 }
 let block=smallBlock(164),out={block,controls:0,selectedPrimeChecks:0,absorberPinChecks:0,smallPrimeChecks:0,freePrimeChecks:0,fullCRTControls:0,fullRootEventChecks:0,rows:[]};
 for(let m of [1,2,3,4,6,8,10,12]){
  let L=2*(m+1),small=plist(L).filter(q=>q>=7),Q=60*small.reduce((a,b)=>a*b,1);
  function progression(i){let x=47,M=60;for(let q of small){let r=q===13?(i%2?2:q-2):mod(-13,q);let k=0;while(mod(x+k*M,q)!==r)k++;x+=k*M;M*=q}ck(M===Q,"progression");return x}
  let Y=Math.max(101,4*Q),P=[],S=[0],trials=0;
  // For a fixed m, Dirichlet/PNT in progressions ensures a
  // sufficiently large fixed-ratio band. Finite examples search
  // bands directly; no uniform bound on the required Y is assumed.
  for(let tries=0;tries<12;tries++){
   P=[];S=[0];
   for(let i=0;i<m;i++){
    let r=progression(i),found=false;
    for(let p=r+Q*Math.ceil((Y-r)/Q);p<2*Y;p+=Q){
     if(P.includes(p)||!prime(p))continue;trials++;
     if(S.slice(0,i).some(d=>mod(S[i]-d,p)===0||mod(S[i]-d-2,p)===0))continue;
     let t=S[i]+p+13;
     if(P.some((q,j)=>mod(t-S[j],q)===0||mod(t-S[j]+2,q)===0))continue;
     ck(mod(t-S[i],p)===13&&mod(t-S[i]+2,p)!==0,"self");P.push(p);S.push(t);found=true;break;
    }if(!found)break;
   }if(P.length===m)break;Y*=2;
  }
  ck(P.length===m,"finite prime search");
  const K=Math.max(...P),b0res=new Map([[3,0],[5,0]]);
  for(let q of small)b0res.set(q,0);
  for(let i=0;i<m;i++){let p=P[i];ck(prime(p)&&p>=Y&&p<2*Y&&p%60===47,"selected prime");out.selectedPrimeChecks++;b0res.set(p,mod(S[i]-1,p));
   for(let j=0;j<=m;j++){let r=mod(b0res.get(p)-S[j],p);ck(j===i?r===p-1:r!==1&&r!==p-1,"selected absorber pin");out.absorberPinChecks++}}
  for(let q of small)for(let j=0;j<=m;j++){let r=mod(-S[j],q);ck(r===(q===13&&j%2?2:0)&&r!==1&&r!==q-1,"small absorber");out.smallPrimeChecks++}
  let cutoff=Math.min(K,10000),others=plist(cutoff).filter(q=>!b0res.has(q));
  for(let q of others){ck(q>L,"free q");let denied=new Set(S.flatMap(s=>[mod(s-1,q),mod(s+1,q)]));ck(denied.size<=2*(m+1)&&denied.size<q,"free CRT coordinate");
   let r=0;while(denied.has(r))r++;b0res.set(q,r);out.freePrimeChecks++}
  // Complete physical CRT construction only for K<=10000.
  // Otherwise the missing q>L are handled by the cardinality proof.
  let digits=null,actualEvents=null;
  if(K<=10000){
   let A=30n,M=60n;
   for(let q of plist(K))if(q>=7){let p=BigInt(q),r=b0res.get(q);ck(r!==undefined,"all coordinates");let k=0n;while(Number((A+M*k)%p)!==r)k++;A+=M*k;M*=p}
   A+=M;digits=A.toString().length;ck(A%60n===30n,"canonical");
   let a=A,n=3n-A/2n,h=3,events=[],Pall=plist(K);
   for(;;){let p0=0,w0=Infinity;for(let q of Pall){let p=BigInt(q),r=Number(a%p);if(r!==1&&r!==q-1)continue;let c=r===1?q+2:0,w=mod(c-Number(n%BigInt(2*q)),2*q)||2*q;if(w<w0||w===w0&&q<p0){p0=q;w0=w}}
    if(!p0)break;let b=h+w0;events.push({p:p0,b,h:b-(p0-1)/2});a-=BigInt(p0-1);n+=BigInt(w0);h=b-(p0-1)/2;ck(h>=0&&a>0n,"domain");out.fullRootEventChecks++;
   }
   let expected=P.flatMap(p=>[{p,b:(p-1)/2,h:0},...block.ev]);
   ck(JSON.stringify(events)===JSON.stringify(expected)&&A-a===BigInt(S[m])&&h===3,"full CRT event replay");actualEvents=events.length;out.fullCRTControls++;
  }
  out.rows.push({m,L,Q,Y,K,primes:P,totalGain:S[m],totalElapsed:S[m]/2,descentAt1:m,descentAt4:m,primeSearchTests:trials,checkedFreePrimesThrough:cutoff,fullCRT:K<=10000,digits,actualEvents});out.controls++;
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
