// Finite independent controls of compressed support signatures,
// first-use CRT relay reconstruction and combined saturation chunks.
function audit(Rs=[12000,48000,192000]){
 const mod=(x,p)=>(x%p+p)%p;
 const gcd=(a,b)=>{a=Math.abs(a);while(b){let t=a%b;a=b;b=t}return a};
 const ck=(b,msg)=>{if(!b)throw Error(JSON.stringify(msg));checks++};
 let checks=0;
 const spf=new Int32Array(2*Math.max(...Rs)+64);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n;
 const primes=[];for(let p=3;p<=211;p+=2)if(lpf(p)===p)primes.push(p);
 function relaxedMax(ps){
  let Q=ps.reduce((a,b)=>a*b,1);
  const dp=new Int32Array(Q+1),win=new Int32Array(Q+1);
  let best=0,arg=0;
  for(let j=1;j<=Q;j++){
   let x=2*j;
   for(let p of ps)if(x%p===1||x%p===p-1){
    let v=j-(p-1)/2;
    ck(v>=0,'relaxed wall');if(1+dp[v]>dp[j]){dp[j]=1+dp[v];win[j]=p}
   }
   if(dp[j]>best){best=dp[j];arg=j}
  }
  let es=[];for(let j=arg;win[j];){let p=win[j];es.push({x:2*j,p});j-=(p-1)/2}
  return {best,es};
 }
 function signatureCheck(es,ps,B){
  let last=new Map(),seen=new Map(),x=es[0]?.x??0;
  for(let i=0;i<=es.length;i++){
   const sig=JSON.stringify(ps.map(p=>{
    if(!last.has(p))return [0];let j=last.get(p);
    if(i-j>B)return [1];
    return [2,es[j].x%p===1?0:1,...ps.map(q=>es.slice(j,i).filter(e=>e.p===q).length)];
   }));
   ck(!seen.has(sig),['signature collision',es,ps,B,i,seen.get(sig)]);
   seen.set(sig,i);
   if(i===es.length)break;
   let {p,x}=es[i];if(last.has(p))ck(i-last.get(p)<=B,'repeat recency');last.set(p,i);
  }
 }
 const small=primes.filter(p=>p<=31),cache=new Map();
 function bound(ps){let key=ps.join(',');if(!cache.has(key))cache.set(key,relaxedMax(ps).best);return cache.get(key)}
 let supports=0,maxima=[0,0,0,0],signatureStates=0;
 function visit(ps,at,k){
  if(ps.length===k){let r=relaxedMax(ps),B=1+Math.max(0,...ps.map((p,i)=>bound(ps.filter(q=>q!==p))));
   signatureCheck(r.es,ps,B);supports++;maxima[k]=Math.max(maxima[k],r.best);signatureStates+=r.es.length+1;return}
  for(let i=at;i<small.length;i++)visit([...ps,small[i]],i+1,k)
 }
 for(let k=1;k<=3;k++)visit([],0,k);
 for(let ps of [[3,5,7,11],[3,5,7,17],[3,11,13,17],[5,7,11,13]]){
  let r=relaxedMax(ps),B=1+Math.max(...ps.map(p=>bound(ps.filter(q=>q!==p))));
  signatureCheck(r.es,ps,B);supports++;maxima[4]=Math.max(maxima[4]??0,r.best);signatureStates+=r.es.length+1;
 }
 function nextRestricted(x,n,ps){let w=Infinity,p=0,e=0;for(let q of ps)for(let f of [-1,1])if(mod(x-f,q)===0){
   let u=mod((f===-1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q;e=f}
  }return {p,w,e}}
 function reconstruct(x,n,ps,m){
  let out=[];for(let i=0;i<m;i++){let a=nextRestricted(x,n,ps);if(!a.p)return null;
   n+=a.w;out.push({p:a.p,x,n,e:a.e});x-=a.p-1;
  }return {out,x,n};
 }
 let rows=[];
 for(let R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  const z=5,Y0=31,Y1=97,k=4,D=2,Qz=30;
  let ticks=0,events=0,relays=0,compressed=0,longCompressed=0,repeatCompressed=0,maxRel=0,words=0,
      narrow=0,sat=0,nonempty=0,lowGain=0,medium=0,clean=0,badGaps=0,late=0,bigBad=0,highBad=0;
  for(let l=lo;l<=hi;l+=W){
   const end=3-l/2+T;
   for(let A=l;A<=Math.min(hi,l+W-6);A+=6){
    let es=[],x=A;
    for(let n=3-A/2+1;n<=end;n++){
     let g=n%2===0?gcd(n,x+1):gcd(n-2,x-1),p=g>1?lpf(g):0;ticks++;
     if(p){es.push({p,x,n,e:n%2===0?-1:1,q:Math.min(lpf(x-1),lpf(x+1))});events++;x-=p-1}
    }
    let highs=[],K=0,J=0,C=0,G=0,lc=0,seen=new Set(),nk=0,nlow=0;
    function flush(saturated){
     if(nk){C++;if(saturated){ck(nk>k&&seen.size>D,'saturation');J++}else ck(nk<=k||seen.size<=D,'unsaturated final');}
     else if(nlow)ck(lc<Qz,'low wall');
     nk=0;nlow=0;lc=0;seen=new Set();
    }
    for(let j=0;j<es.length;j++){let a=es[j];G+=a.p-1;
     if(a.p>=Y0){flush(false);highs.push(j);continue}
     nlow++;lc+=a.p-1;
     if(a.p>z){K++;nk++;seen.add(a.p)}
     if(nk>k&&seen.size>D)flush(true);
    }
    flush(false);ck((k+1)*J<=K&&C<=K,'chunk count domination');narrow+=K;sat+=J;nonempty+=C;
    for(let h=0;h+1<highs.length;h++){
     let i=highs[h],j=highs[h+1],a=es[i],b=es[j],mid=es.slice(i+1,j),
         qs=[...new Set(mid.filter(e=>e.p>z).map(e=>e.p))].sort((a,b)=>a-b);
     if(a.p<Y1)continue;relays++;let narrowLen=mid.filter(e=>e.p>z).length;
     if(narrowLen>k&&qs.length>D)highBad++;
     if(qs.length>D)continue;
     compressed++;if(narrowLen>k)longCompressed++;if(narrowLen>qs.length)repeatCompressed++;maxRel=Math.max(maxRel,mid.length);
     const post=a.x-a.p+1,ps=[3,5,...qs];let E=0,counts=new Map(),pins=new Map();
     for(let e of mid){
      if(e.p>z&&!pins.has(e.p)){
       let gain=E+qs.reduce((s,q)=>s+(counts.get(q)||0)*(q-1),0);
       ck(post-gain===e.x,'prefix counts reconstruct source');
       pins.set(e.p,mod(a.p-1+gain+e.e,e.p));
       ck(mod(a.x,e.p)===pins.get(e.p),'first-use CRT pin');
      }
      if(e.p<=z)E+=e.p-1;else counts.set(e.p,(counts.get(e.p)||0)+1);
     }
     ck(pins.size===qs.length,'all first use pins');
     const r=reconstruct(post,a.n,ps,mid.length);
     ck(r!==null,'restricted path too short');
     ck(r.x===b.x&&r.n===(mid.length?mid.at(-1).n:a.n),'restricted relay endpoints');
     for(let h=0;h<mid.length;h++){let v=r.out[h],w=mid[h];ck(v.x===w.x&&v.n===w.n&&v.p===w.p&&v.e===w.e,'exact restricted relay');words++}
     let modulus=2*Qz*qs.reduce((s,q)=>s*q,1);
     let t=reconstruct(post+modulus,a.n-modulus/2,ps,mid.length);
     ck(t&&t.x===r.x+modulus&&t.n===r.n-modulus/2,'periodic reconstruction');
     for(let h=0;h<mid.length;h++)ck(t.out[h].p===r.out[h].p&&t.out[h].n===r.out[h].n-modulus/2,'periodic event');
    }
    // Refined forward medium ledger charges contaminated GAPS, not occurrences.
    const U=4,Ym=Math.max(Y0+1,Math.floor(T/2));
    let F=0,Q=0,Bg=0,tail=0,big=0,bad=0,gaps=[];
    for(let h=0;h+1<highs.length;h++)gaps.push(es.slice(highs[h]+1,highs[h+1]).some(a=>a.p>z));
    Bg=gaps.filter(Boolean).length;
    for(let h=0;h<highs.length;h++){
     let a=es[highs[h]],p=a.p;if(!(Y0<=p&&p<Ym&&BigInt(p)**3n<=(2n*BigInt(a.q))**5n))continue;
     let w=2*a.q;Q+=w;
     if(h+2>=highs.length){tail+=w;continue}
     if(gaps[h]||gaps[h+1]){bad+=w;continue}
     if(es[highs[h+1]].p>=U*Ym||es[highs[h+2]].p>=U*Ym){big+=w;continue}
     F+=w;
    }
    ck(Q===F+tail+bad+big&&tail<=4*Ym&&bad<=4*Ym*Bg&&U*big<=6*G,'gap medium ledger');
    ck(Bg<=C,'gap counts <= nonempty chunks');medium+=Q;clean+=F;badGaps+=Bg;late+=tail;bigBad+=big;
   }
  }
  rows.push({R,N,T,z,Y0,Y1,k,D,ticks,events,relays,compressed,longCompressed,repeatCompressed,maxRel,words,narrow,sat,nonempty,medium,clean,badGaps,late,bigBad,highBad});
 }
 return {checks,supports,signatureStates,maxima,rows}
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
