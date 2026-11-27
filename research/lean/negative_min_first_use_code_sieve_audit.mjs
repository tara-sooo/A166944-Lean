// Audit of bidirectional first-use spatial codes and elementary Selberg weights.
// Run: node research/lean/negative_min_first_use_code_sieve_audit.mjs
// Finite proxy Q,Y,T are not asymptotic parameters. Counts of encoded bits include all split tests.
function audit(){
 const ok=(h,m)=>{if(!h)throw Error(m)};
 const mod=(a,q)=>((a%q)+q)%q;
 const log2ceil=n=>n<=1?0:Math.ceil(Math.log2(n));
 function table(N){const sp=new Int32Array(N+1),ps=[];for(let p=2;p<=N;p++)if(!sp[p]){sp[p]=p;ps.push(p);if(p*p<=N)for(let n=p*p;n<=N;n+=p)if(!sp[n])sp[n]=p}return {sp,ps}}
 const runs=[];
 for(const mode of ['cell','base'])for(const [R,T,Q,Y] of [[12000,96,6,30],[48000,192,30,60],[96000,288,210,90]]){
  const {sp}=table(2*R+1);
  const fac=n=>{let f=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");f.push(p);while(n%p===0)n/=p}return f};
  const cell=x=>Math.floor(x/Q),q=log2ceil(Q);
  const cand=(x,dir,high)=>[...new Set((dir===1?[...fac(x-1),...fac(x+1)]:[...fac(x),...fac(x-2)]).filter(p=>p>2&&(high?p>=Y:p<Y)))].sort((a,b)=>a-b);
  const D=x=>1+fac(x-2).length+fac(x-1).length+fac(x).length+fac(x+1).length;
  let K=2;for(let x=R-3*T-6;x<=2*R;x+=2)K=Math.max(K,D(x));
  const w=log2ceil(K);
  const type=e=>(mode==='cell'?cell(e.x)===cell(e.y):Q%e.p===0)?0:e.p>=Y?2:1;
  let codeChecks=0,splitChecks=0,ticks=0,events=0,repeatBlocks=0,highBlocks=0,encodedBits=0,phases=0,freeChecks=0,freeCuts=0;
  function encode(word,start,dir,cuts=new Set()){
   let arr=dir===1?word:word.slice().reverse(),pos=start,bits="",formula=0,lo=0,nh=0,nm=0,blocks=0,nfree=0; const marks=dir===1?cuts:new Set([...cuts].map(j=>word.length-j));
   function put(n,b){ok(Number.isInteger(n)&&n>=0&&n<2**b,"code field");if(b)bits+=n.toString(2).padStart(b,"0")}
   function unary(n){bits+="1".repeat(n)+"0"}
   for(;;){
    let end=lo;while(end<arr.length&&type(arr[end])!==2&&!(end>lo&&marks.has(end)))end++;
    const a=arr.slice(lo,end),m=a.filter(e=>type(e)===1).length,k=new Set(a.filter(e=>type(e)===1).map(e=>e.p)).size,b=log2ceil(m+1);
    const flag=end===arr.length?0:type(arr[end])===2?1:2;put(flag,2);unary(k);unary(b);
    formula+=4+k+b+(k+1)*(b+q)+b*k*(k+1)/2+k*w+(flag===1?2:0);
    const seen=[],counts=[];let base=0;nm+=m;blocks++;
    if(m>k)repeatBlocks++;
    function chunk(){for(const n of counts)put(n,b);put(base,b+q);counts.fill(0);base=0}
    for(const e of a){
     ok(pos===(dir===1?e.x:e.y),"event continuity");
     let t=type(e);
     if(!t){base+=e.p-1;ok(e.p<=Q+1&&cell(e.x)===cell(e.y),"base run stays in cell")}
     else{let j=seen.indexOf(e.p);
      if(j>=0)counts[j]++;
      else{chunk();let choices=cand(pos,dir,false);ok(choices.length<=K,"medium degree");put(choices.indexOf(e.p),w);seen.push(e.p);counts.push(0)}
     }
     pos+=dir===1?-(e.p-1):e.p-1;
    }
    chunk();ok(seen.length===k,"all distinct");
    if(flag===0)break;if(flag===2){nfree++;lo=end;continue}
    const e=arr[end];ok(pos===(dir===1?e.x:e.y),"high continuity");
    const choices=cand(pos,dir,true);ok(choices.length<=4,"high degree");put(choices.indexOf(e.p),2);
    pos+=dir===1?-(e.p-1):e.p-1;nh++;highBlocks++;lo=end+1;
   }
   ok(bits.length===formula,"exact code length");encodedBits+=formula;
   ok(blocks===nh+nfree+1,"blocks");
   return {bits,pos,formula,nh,nm,nfree}
  }
  function decode(bits,start,dir){
   let i=0,x=start;
   function read(n){ok(i+n<=bits.length,"truncated");let r=n?parseInt(bits.slice(i,i+n),2):0;i+=n;return r}
   function unary(){let n=0;while(read(1))n++;return n}
   function move(g){x+=dir===1?-g:g}
   for(;;){
    const flag=read(2),k=unary(),b=unary(),seen=[];ok(flag<=2,'flag');
    for(let j=0;j<=k;j++){
     let g=0;for(const p of seen)g+=read(b)*(p-1);
     g+=read(b+q);move(g);
     if(j<k){let ps=cand(x,dir,false),p=ps[read(w)];ok(p!==undefined&&!seen.includes(p),"valid first medium");let y=x+(dir===1?-(p-1):p-1);ok(type({x,y,p})===1,"medium class");seen.push(p);move(p-1)}
    }
    if(flag===0)break;if(flag===2)continue;
    const p=cand(x,dir,true)[read(2)];ok(p!==undefined,"high pin");ok(type({x,y:x+(dir===1?-(p-1):p-1),p})===2,"high class");move(p-1)
   }
   ok(i===bits.length,"complete code");return x
  }
  let rootCount=0;const endpointCodes=new Map();let maxMultiplicity=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   rootCount++;let x=A,n=3-A/2,word=[];
   for(let i=0;i<Math.floor(T/2);i++){
    n++;let p=0;const even=n%2===0;
    for(const v of fac(even?x+1:x-1))if(v>2&&mod(n,2*v)===(even?0:v+2)){p=v;break}
    if(p){const y=x-p+1;word.push({x,y,p});x=y;events++;ok(x>=R-3*T-6,"slab")}
    ticks++;
   }
   const f=encode(word,A,1),r=encode(word,x,-1);
   ok(f.pos===x&&r.pos===A&&f.formula===r.formula,"symmetric code length");
   ok(decode(f.bits,A,1)===x&&decode(r.bits,x,-1)===A,"two directional reconstruction");codeChecks+=2;
   ok(word.length+1<=(Q/2)*(1+f.nh+f.nm),"phase count");phases+=word.length+1;
   if(mode==="base"){const cuts=new Set(),used=new Set();for(let i=0;i<word.length;i++){const e=word[i];if(type(e)===2)used.clear();else if(type(e)===1){used.add(e.p);if(used.size===3){if(i+1<word.length)cuts.add(i+1);used.clear()}}}const g=encode(word,A,1,cuts),h=encode(word,x,-1,cuts);ok(decode(g.bits,A,1)===x&&decode(h.bits,x,-1)===A,"free-cut reconstruction");freeChecks+=2;freeCuts+=cuts.size;}
   let map=endpointCodes.get(x);if(!map){map=new Map();endpointCodes.set(x,map)}
   ok(!map.has(r.bits)||map.get(r.bits)===A,"reverse code injectivity");map.set(r.bits,A);maxMultiplicity=Math.max(maxMultiplicity,map.size);
   for(const j of new Set([0,Math.floor(word.length/2),word.length])){
    let v=j===0?A:word[j-1].y;
    const a=encode(word.slice(0,j),A,1),b=encode(word.slice(j),x,-1);
    ok(a.formula<=f.formula&&b.formula<=f.formula,"contiguous subpath monotonicity");ok(decode(a.bits,A,1)===v&&decode(b.bits,x,-1)===v,"split reconstruction");splitChecks++;
   }
  }
  runs.push({mode,R,T,Q,Y,K,roots:rootCount,ticks,events,phases,codeChecks,splitChecks,repeatBlocks,highBlocks,encodedBits,maxMultiplicity,freeChecks,freeCuts});
 }
 // Independent small Selberg weight audit: direct Mobius inversion, then quadratic form and pointwise majorant.
 const sieve=[];const {ps}=table(400);
 function divisors(n){const d=[];for(let j=1;j<=n;j++)if(n%j===0)d.push(j);return d}
 function mu(n){let s=1;for(const p of ps){if(p*p>n)break;if(n%p===0){n/=p;s=-s;if(n%p===0)return 0}}return n>1?-s:s}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return a}
 for(const Z of [8,12,20,30,48]){
  const ds=Array.from({length:Z},(_,i)=>i+1).filter(d=>d%2&&mu(d)!==0);
  const g=d=>ps.filter(p=>d%p===0).reduce((a,p)=>a*2/p,1),h=d=>ps.filter(p=>d%p===0).reduce((a,p)=>a*2/(p-2),1);
  const G=ds.reduce((a,d)=>a+h(d),0),lam=new Map();
  for(const d of ds){let l=0;for(const r of ds)if(r%d===0)l+=mu(r/d)*mu(r)*h(r)/G;lam.set(d,l/g(d));ok(Math.abs(l/g(d))<=d+1e-9,"weight bound")}
  ok(Math.abs(lam.get(1)-1)<1e-10,"lambda one");
  let form=0;for(const d of ds)for(const e of ds)form+=lam.get(d)*lam.get(e)*g(d*e/gcd(d,e));
  ok(Math.abs(form-1/G)<1e-9,"Selberg minimum");
  for(const a of [0,101,127]){
   let live=0,major=0;const N=6000;
   for(let n=1;n<=N;n++){
    const f=a===0?(n-1)*(n+1):n*(a*n+2);
    let weight=0;for(const d of ds)if(f%d===0)weight+=lam.get(d);
    if(ps.filter(p=>p>2&&p<=Z).every(p=>f%p!==0)){live++;ok(Math.abs(weight-1)<1e-9,"pointwise sifting majorant")}
    major+=weight*weight;
   }
   ok(major+1e-8>=live,"summed majorant");
   sieve.push({Z,form:a===0?"x+-1":"r,"+a+"r+2",sifted:live,majorant:major,diagonal:form,divisors:ds.length});
  }
 }
 return {runs,sieve};
}
console.log(JSON.stringify(audit(),null,2));
