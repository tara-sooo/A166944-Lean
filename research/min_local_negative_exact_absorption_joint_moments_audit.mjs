// Exact restricted ancestor and joint omitted-clock survival moments on complete periods.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,cap=g=>Math.floor(9*g/4+8);
 const Z=2*cap(18)+7,pr=[],fac=Array.from({length:Z+1},()=>[]);
 for(let p=3;p<=Z;p+=2)if(!fac[p].length){pr.push(p);for(let n=p;n<=Z;n+=p)fac[n].push(p)}
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 function rat(n,d){let g=gcd(n,d);return `${n/g}/${d/g}`}
 let out={periods:0,lowClasses:0,offsetControls:0,restrictedHits:0,jointTuples:0,jointHazardChecks:0,probabilityCacheEntries:0,rootEnumerations:0,rootMassChecks:0,exactMomentChecks:0,rows:[]};
 const known={
  6:["6028126/3660525","3587776/1220175"],
  12:["701632591/343823130","6588081083/1383678450"],
  18:["5106396847732215463/2097086682985544250","193920225430694299891/27262126878812075250"]
 };
 for(let L of [6,12,18]){
  let y=L+1,Z=2*cap(L)+7,P=pr.filter(p=>p<=y),hi=pr.filter(p=>p>y&&p<=Z),M=2*P.filter(p=>p>=5).reduce((a,b)=>a*b,1),den=hi.reduce((a,p)=>a*BigInt(p-2),1n),pc=new Map([["",den]]),classes=0,restricted=0,restricted2=0,S=0n,S2=0n,minPi=1,nontrivial=0,jointNontrivial=0;
  function numerator(B){if(!B||B.size===0)return den;let sig=[...B].map(([p,v])=>[p,v.size]).sort((a,b)=>a[0]-b[0]).map(([p,n])=>p+":"+n).join(",");if(pc.has(sig))return pc.get(sig);
   let ct=den;for(let [p,v] of B){ck(v.size<=L/2+1&&v.size/(p-2)<=2/3+1e-10,"hazard");ct=ct/BigInt(p-2)*BigInt(p-2-v.size)}pc.set(sig,ct);return ct
  }
  function test(j,g){
   let d=g,h=3,par=mod(3*j,2),B=null;
   if(d===0)return new Map();
   for(let t=0;t<cap(g);t++){
    let b=h+1,np=mod(b-par-d/2,2),list=fac[Math.abs(np?2*b-5:2*b+1)],p=1,large=0;
    for(let q of list){if(q>y){large=q;break}if(mod(6*j+d+(np?-1:1),q)===0){p=q;break}}
    if(p===1&&large){let r=mod(-d+(np?1:-1),large);if(r!==1&&r!==large-1){B??=new Map();let v=B.get(large)||new Set();v.add(r);B.set(large,v)}}
    d-=p-1;h=b-(p-1)/2;if(d===0)return B||new Map();if(d<0)return null;
   }return null
  }
  function union(A,B){if(A.size===0)return B;if(B.size===0)return A;let C=new Map();for(let [p,v] of A)C.set(p,new Set(v));for(let [p,v] of B){let w=C.get(p)||new Set();for(let x of v)w.add(x);C.set(p,w)}return C}
  for(let j=0;j<M;j++){
   if(P.some(p=>p>=5&&(mod(6*j,p)===1||mod(6*j,p)===p-1)))continue;
   classes++;out.lowClasses++;
   let ar=[];
   for(let g=0;g<=L;g+=6){let B=test(j,g);out.offsetControls++;if(B!==null){let n=numerator(B);ar.push({B,n});restricted++;S+=n;out.restrictedHits++;if(B.size){nontrivial++;minPi=Math.min(minPi,Number(n)/Number(den))}}}
   restricted2+=ar.length**2;
   for(let a of ar)for(let b of ar){let U=union(a.B,b.B),n=numerator(U);ck(n<=a.n&&n<=b.n,"joint subset");out.jointHazardChecks++;if(U.size)jointNontrivial++;S2+=n;out.jointTuples++}
  }
  ck(classes===2*P.filter(p=>p>=5).reduce((a,p)=>a*(p-2),1),"period classes");
  let D=BigInt(classes)*den,mu1=rat(S,D),mu2=rat(S2,D);
  ck(mu1===known[L][0]&&mu2===known[L][1],{L,mu1,mu2});out.exactMomentChecks+=2;
  if(L<=12){
   let roots=0;
   for(let j=0;j<M;j++){
    let G=0,h=3,t=0,par=mod(3*j,2);
    while(G<=L){
     if(P.every(p=>mod(6*j-G-1,p)!==0&&mod(6*j-G+1,p)!==0)){roots++;break}
     if(t>=cap(L))break;
     let b=h+1,np=mod(3+t+1-par,2),p=1;
     for(let q of fac[Math.abs(np?2*b-5:2*b+1)])if(q<=y&&mod(6*j-G+(np?-1:1),q)===0){p=q;break}
     G+=p-1;h=b-(p-1)/2;t++;
    }
    out.rootEnumerations++;
   }
   ck(roots===restricted,"root mass transport");out.rootMassChecks++;
  }
  out.probabilityCacheEntries+=pc.size;
  out.periods++;out.rows.push({L,y,M,classes,restricted,restricted2,restrictedFraction:restricted/M,nu1:restricted/classes,nu2:restricted2/classes,mu1,mu2,meanSurvival:Number(S)/(Number(den)*restricted),nontrivial,jointNontrivial,minPi});
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
