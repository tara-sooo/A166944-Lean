// Exact conditional CRT history law over small complete residue rectangles.
function historyAudit(Y){
 const ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const L=2*ps.reduce((a,b)=>a*b,1),mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 if(L>210)throw Error("exact history limit");
 const rows=[];
 for(let T of [4,10,25])for(let w of [8,16,32]){
  const groups=new Map();
  function trace(C,t){
   let g=0,word=[],before=[];
   for(let s=1;s<=T+w;s++){let q=0;for(let p of ps){
    let cc=mod(C+g,p),even=(t+s)%2===0;
    if(cc===(even?1:p-1)&&mod(t+s-(even?0:p+2),p)===0){q=p;break}
   }
   if(s<=T){before.push(g);word.push(q);}
   if(q)g+=q-1;
   if(s===T)var gT=g;
   if(s>T&&q)var next=true;
   }
   return {word,before,gT,quiet:!next};
  }
  for(let C=0;C<L;C+=2)for(let t=0;t<L;t++){
   let a=trace(C,t),key=(t%2)+":"+a.word.join(","),g=groups.get(key);
   if(!g){g={...a,parity:t%2,n:0,nQuiet:0};groups.set(key,g)}
   g.n++;g.nQuiet+=a.quiet;
  }
  let checked=0,quietCount=0,unusedChecks=0,selectedChecks=0,minAllowedRatio=1,highChecks=0,highQuietMin=1;
  for(let g of groups.values()){
   let product=1,quietProduct=1,highProduct=1,highBound=1,highSelectedQuiet=true,baseHigh=1,z=Math.max(5,Math.ceil(Math.sqrt(2*T)));
   for(let p of ps){
    let allowed=new Uint8Array(p*p).fill(1),used=false;
    for(let s=1;s<=T;s++){
     let even=(g.parity+s)%2===0,cp=mod((even?1:-1)-g.before[s-1],p),tp=mod((even?0:p+2)-s,p),id=cp*p+tp,q=g.word[s-1];
     if(!q||p<q)allowed[id]=0;
     else if(p===q){used=true;let v=allowed[id];allowed.fill(0);allowed[id]=v}
    }
    let n=allowed.reduce((a,b)=>a+b,0);ck(n>0,"nonempty");
    if(used){ck(n===1,"selected fixed");selectedChecks++}
    else{ck(n>=p*p-T,"unused loss");unusedChecks++;minAllowedRatio=Math.min(minAllowedRatio,n/(p*p))}
    let future=new Set();
    for(let s=T+1;s<=T+w;s++){let even=(g.parity+s)%2===0;future.add(mod((even?1:-1)-g.gT,p)*p+mod((even?0:p+2)-s,p))}
    ck(future.size===Math.min(w,2*p),"fixed horizon future pair count");
    let bad=[...future].reduce((a,b)=>a+allowed[b],0);
    product*=n;quietProduct*=n-bad;
    if(p>=z){
     highProduct*=(n-bad)/n;
     if(used){if(bad)highSelectedQuiet=false}
     else highBound*=Math.max(0,1-Math.min(w,2*p)/(p*p-T));
     baseHigh*=1-Math.min(w,2*p)/(p*p);
    }
   }
   ck(product===g.n&&quietProduct===g.nQuiet,"factorized exact history law");
   if(highSelectedQuiet){ck(highProduct>=highBound-1e-12,"conditional unused tail lower bound");highChecks++;highQuietMin=Math.min(highQuietMin,highProduct)}
   checked++;quietCount+=g.nQuiet;
  }
  rows.push({T,w,z:Math.max(5,Math.ceil(Math.sqrt(2*T))),groups:groups.size,checked,quietCount,unusedChecks,selectedChecks,minAllowedRatio,highChecks,highQuietMin});
 }
 return {Y,L,states:L*L/2,rows}
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(historyAudit(y)));
