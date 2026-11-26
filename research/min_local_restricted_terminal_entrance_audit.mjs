// Exact restricted-terminal partition and first-high entrance factorization audit.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const ps=[3,5,7,11,13,17,19],lim=4000005,spf=new Uint32Array(lim);
 for(let p=2;p*p<lim;p++)if(!spf[p])for(let n=p*p;n<lim;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){ck(n>0&&n<lim,"domain "+n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 function next(x,v,A){let p=Infinity,w=Infinity,e=0;
  for(let r of A){let s=x%r===1?1:x%r===r-1?-1:0;if(!s)continue;let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){p=r;w=z;e=s}}
  return {p,w,e}
 }
 function full(x,v){return next(x,v,[...fs(x-1),...fs(x+1)])}
 function add(m,k,n=1){m.set(k,(m.get(k)||0)+n)}
 function stats(m){let E=0,max=0,n=0;for(let a of m.values()){E+=a*a;max=Math.max(max,a);n+=a}return {classes:m.size,E,max,n}}
 let periods=[],slabs=[];
 for(let T of [3,5,7,11,13,17]){
  let A=ps.filter(p=>p<=T),Q=2*A.reduce((a,b)=>a*b,1),P=2*Q,base=P,term=new Map(),exact=new Map(),memo=new Map(),steps=0,control=0,maxGain=0,waitSum=0,roots=0;
  function terminal(x,v){
   let path=[],k;
   for(;;){k=x+":"+v;if(memo.has(k)){k=memo.get(k);break}
    let z=next(x,v,A);if(!isFinite(z.p)){k=x+":"+v;break}
    path.push(k);let U=x+z.p-1;ck(U<=Q*(Math.floor(x/Q)+1),"wall");x=U;v+=z.w;steps++;
   }
   for(let a of path)memo.set(a,k);return k
  }
  for(let X=base;X<base+P;X+=6){
   roots++;let v=X/2+3,k=terminal(X,v),[u,t]=k.split(":").map(Number);add(term,u);add(exact,k);
   ck(u>=X&&u<=Q*(Math.floor(X/Q)+1),"terminal range");ck(A.every(p=>u%p!==1&&u%p!==p-1),"terminal rough");
   maxGain=Math.max(maxGain,u-X);waitSum+=t-v;
   if(X<base+120){
    let x=X,n=v;
    while(x<u){let z=next(x,n,A);for(let i=1;i<=z.w;i++){let tick=n+i,g=gcd(tick%2?tick-2:tick,tick%2?x+1:x-1),p=A.find(r=>g%r===0);ck(i===z.w?p===z.p:p===undefined,"literal");control++}x+=z.p-1;n+=z.w}
    ck(x===u&&n===t,"memo replay")
   }
  }
  // Two cells [base,base+Q),[base+Q,base+2Q), each can end at its right wall.
  // The boundary at base+Q also has a fresh canonical root in the next cell.
  // For periodic energy, fold terminal offsets modulo 2Q, and likewise phase.
  let folded=new Map(),foldedExact=new Map();for(let [u,n] of term)add(folded,mod(u,P),n);
  for(let [k,n] of exact){let [u,v]=k.split(":").map(Number),shift=Math.floor(u/P);add(foldedExact,mod(u,P)+":"+(v-shift*Q),n)}
  let rough=2*A.reduce((a,p)=>a*(p-2),1);
  let z=stats(folded),zz=stats(foldedExact);ck(z.classes<=rough&&z.E*rough>=roots*roots,"rough CS");ck(z.n===roots&&zz.n===roots,"mass");
  periods.push({T,Q,P,roots,rough,terminal:z,exactTerminal:zz,steps,control,maxGain,waitSum,meanSize:z.E/roots,maxNormalized:z.max/(Math.log(T)**2)})
 }
 for(let [R,len,T] of [[10000,10000,13],[100000,30000,31],[100000,30000,127],[1000000,60000,251],[1000000,60000,503],[1000000,60000,997]]){
  let J=R+len,A=Array.from({length:T-2},(_,i)=>i+2).filter(p=>p>2&&!spf[p]),memo=new Map(),terminal=new Map(),offsetTerminal=new Map(),entr=new Map(),entrOff=new Map(),map=new Map(),mapOff=new Map();
  let s={R,len,T,roots:0,lowEvents:0,firstHigh:0,noHigh:0,preempt:0,terminalHigh:0,terminalMemoSteps:0,literalTicks:0,replayChecks:0,distinctHighWithMultipleTerminalOffsets:0,example:null};
  function low(x,v){return next(x,v,fs(x-1).concat(fs(x+1)).filter(p=>p<T))}
  function term(x,v){
   let path=[],k;
   for(;;){
    k=x+":"+v;if(memo.has(k)){k=memo.get(k);break}
    if(x>=J){k="exit:"+x+":"+v;break}
    let z=low(x,v);if(!isFinite(z.p)){k="rough:"+x;break}
    path.push(k);x+=z.p-1;v+=z.w;s.terminalMemoSteps++;
   }
   for(let a of path)memo.set(a,k);return k
  }
  for(let X=Math.ceil(R/6)*6;X<J;X+=6){
   s.roots++;let x=X,v=X/2+3,k=term(x,v);add(terminal,k);let off=k.split(":")[1];add(offsetTerminal,off);
   while(x<J){
    let z=full(x,v);
    if(z.p>=T){
     s.firstHigh++;let n=v+z.w,U=x+z.p-1,mark=U+":"+n+":"+z.p+":"+z.e,lo=low(x,v),kk;
     if(isFinite(lo.p)){s.preempt++;ck(lo.w>z.w,"strict low preemption");kk=term(x,n)}else{s.terminalHigh++;kk="rough:"+x}
     ck(kk===k,"terminal factorization");s.replayChecks++;
     add(entr,mark);add(entrOff,x);
     if(map.has(mark))ck(map.get(mark)===k,"same mark different terminal");else map.set(mark,k);
     if(!mapOff.has(x))mapOff.set(x,new Set());mapOff.get(x).add(k);
     if(!s.example&&isFinite(lo.p)&&x>X)s.example={X,x,v,p:z.p,n,k,lowerWait:lo.w};
     break
    }
    let zz=low(x,v);ck(z.p===zz.p&&z.w===zz.w&&z.e===zz.e,"prefix");
    if(X<R+60)for(let i=1;i<=z.w;i++){let n=v+i,g=gcd(n%2?n-2:n,n%2?x+1:x-1);ck(i===z.w?(spf[g]||g)===z.p:g===1,"literal full");s.literalTicks++}
    x+=z.p-1;v+=z.w;s.lowEvents++;
   }
   if(x>=J){s.noHigh++;ck(k==="exit:"+x+":"+v,"exit")}
  }
  s.terminal=stats(terminal);s.offsetTerminal=stats(offsetTerminal);s.entrance=stats(entr);s.entranceOffsets=stats(entrOff);
  ck(s.entrance.E<=s.terminal.E&&s.entrance.max<=s.terminal.max,"energy");ck(s.firstHigh+s.noHigh===s.roots,"partition");
  for(let m of mapOff.values())if(m.size>1)s.distinctHighWithMultipleTerminalOffsets++;
  slabs.push(s)
 }
 return {periods,slabs}
}
console.log(JSON.stringify(audit(),null,2));
