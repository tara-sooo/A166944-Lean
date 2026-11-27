// Actual low-gain cohorts: compatible used-p return capacity, large plus-to-three bridge, and short p-q-p relays.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,s=0;for(let e of [-1,1])for(let q of fs(a-e)){let d=mod((e===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;s=e}}return {p,w,s}}
 const f=x=>x?x*Math.log(x):0,phi=(a,b)=>f(a+b)-f(a)-f(b);
 let out={roots:0,events:0,selected:0,compatibleChecks:0,largeChecks:0,relayChecks:0,bridgeMixChecks:0,macroBoundChecks:0,entropySplitChecks:0,relayUnionChecks:0,rows:[]};
 for(let R of [12000,48000,192000,480000,1000000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),H=Math.floor(3+T-J/2),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),ns=0,blocks=new Map(),Y=Math.max(5,Math.ceil(J/8)),ds=[0,4,8,16],sets=ds.map(D=>({D,roots:0,motifs:0,keys:new Set(),pairs:new Set(),bad:new Map()}));
  let ends=new Map(),macroUsed=0,macroMass=0,macroRepeatMass=0,macroUsedBound=0,macroPhi=0;
  let r={R,K,T,J,Y,ns:0,meanEvents:0,usedLower:0,usedLowerCap:0,usedAll:0,usedAllCap:0,largeFirst:0,largeUsedLower:0,largeBridges:0,largeBridgeMix:0,largeBridgeEntropy:0,largeBridgeKeys:0,macroRepeat:0,oneRelay:0,shortRepeat:0,otherRepeat:0};
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,end=n+T,G=0,path=[];
   for(;;){let e=next(a,n);if(n+e.w>end)break;path.push({a,n:n+e.w,G,p:e.p,s:e.s});a-=e.p-1;G+=e.p-1;n+=e.w;out.events++}
   out.roots++;if(G>J)continue;ns++;out.selected++;r.meanEvents+=path.length;ends.set(a,(ends.get(a)||0)+1);macroMass+=path.filter(e=>e.p>=Y).length;
   let seen=new Map(),macro=path.map((e,i)=>e.p>=Y?i:-1).filter(i=>i>=0),used=new Map();
   for(let i=0;i<path.length;i++){let e=path[i],p=e.p,b=e.a-p+1,u=i+1<path.length?path[i+1].n-1:H-b/2,key=b+":"+u;
    let v=blocks.get(key)||{a:b,u,first:new Map(),bridges:new Map(),entries:[]};blocks.set(key,v);v.entries.push({p,seen:[...seen.keys()]});
    if(p>=5&&!seen.has(p)){
     seen.set(p,i);if(p>J/3+1){r.largeFirst++;let t=v.first.get(p)||{m:0,n:e.n,s:e.s};t.m++;v.first.set(p,t);ck(e.s===t.s,"first sign")}
    }
    for(let [q,j] of seen)if(j<i&&[0,2].includes(mod(b,q))){
     let t=used.get(q)||{all:0,low:0,repeat:0};t.all++;if(p<q)t.low++;if(p===q)t.repeat++;used.set(q,t);
     if(q>J/3+1&&p<q){ck(p===3&&i===j+1&&path[j].s===1&&e.G-path[j].G===q-1&&mod(b,q)===0,"bridge");r.largeBridges++;r.largeUsedLower++;out.largeChecks++;let x=v.bridges.get(q)||{m:0,n:e.n,firstN:path[j].n};x.m++;v.bridges.set(q,x)}
    }
   }
   for(let [p,j] of seen){let e=path[j],D=G-e.G-(p-1),rem=D%(2*p),C=2*Math.floor(D/(2*p))+(rem>=(e.s===1?2:2*p-2)?1:0),x=used.get(p)||{all:0,low:0,repeat:0};ck(x.all<=C&&x.low<=C-x.repeat,"compatible cap");out.compatibleChecks++;if(p>=Y){macroUsed+=x.low;macroRepeatMass+=x.repeat;macroUsedBound+=C-x.repeat;}r.usedAll+=x.all;r.usedAllCap+=C;r.usedLower+=x.low;r.usedLowerCap+=C-x.repeat}
   let last=new Map(),hit=sets.map(()=>false);
   for(let k=0;k<macro.length;k++){let i=macro[k],e=path[i],p=e.p;if(last.has(p)){r.macroRepeat++;let k0=last.get(p);if(k===k0+2){r.oneRelay++;let j=macro[k0],m=macro[k0+1],x=path[j],q=path[m].p,d1=path[m].G-x.G-(p-1),d2=e.G-path[m].G-(q-1),D=d1+d2,c=x.s+1-e.s;ck(q!==p&&mod(q-1+D-c,p)===0&&(q-1+D-c)/p%2===1,"relay congruence");out.relayChecks++;
      if(D<=16)r.shortRepeat++;for(let l=0;l<sets.length;l++)if(D<=sets[l].D){let st=sets[l];st.motifs++;st.keys.add([x.a,p,q,d1,d2,x.s,path[m].s,e.s].join(":"));st.pairs.add(p+":"+q);hit[l]=true}
     }else r.otherRepeat++}last.set(p,k)}
   for(let l=0;l<sets.length;l++){sets[l].roots+=+hit[l];if(hit[l]){let b=sets[l].bad;b.set(a,(b.get(a)||0)+1)}}
  }
  for(let v of blocks.values())for(let [p,b] of v.bridges){let a=v.first.get(p);if(!a)continue;ck(a.s===-1&&mod(a.n,2*p)===0&&mod(b.firstN,2*p)===p+2&&b.n-b.firstN<=6&&Math.abs(a.n-b.n)>=p-8,"bridge clock separation");
   let q=Math.min(fs(v.a-1)[0],fs(v.a+1)[0]);ck(2*q>Math.abs(a.n-b.n),"stationary length");
   out.bridgeMixChecks++;r.largeBridgeMix+=b.m;r.largeBridgeEntropy+=phi(a.m,b.m);r.largeBridgeKeys++;
  }
  for(let v of blocks.values()){let marks=new Set(v.entries.filter(e=>e.p>=Y).map(e=>e.p));for(let p of marks){let a=v.entries.filter(e=>e.p===p).length,b=v.entries.filter(e=>e.p<p&&e.seen.includes(p)).length;macroPhi+=phi(a,b)}}
  ck(macroPhi<=phi(macroMass,macroUsed)+1e-7&&macroUsed<=macroUsedBound&&macroMass<=ns*J/(Y-1)+1e-8&&macroUsedBound<=macroMass*(1+J/Y)+1e-8,'macro bound');out.macroBoundChecks++;
  r.ns=ns;for(let k of Object.keys(r))if(!["R","K","T","J","Y","ns","largeBridgeKeys"].includes(k))r[k]/=ns;
  r.macroUsed=macroUsed/ns;r.macroMass=macroMass/ns;r.macroUsedBound=macroUsedBound/ns;r.macroMix=macroPhi/ns;r.macroMixUpper=phi(macroMass,macroUsed)/ns;r.macroRepeatMass=macroRepeatMass/ns;
  r.relays=sets.map(s=>{let F=0,F0=0,F1=0,binary=0;for(let [a,m] of ends){let b=s.bad.get(a)||0;F+=f(m);F0+=f(m-b);F1+=f(b);binary+=phi(m-b,b)}ck(Math.abs(F-F0-F1-binary)<1e-6,'entropy split');let e=s.roots/ns,h=e===0||e===1?0:-e*Math.log(e)-(1-e)*Math.log(1-e),loss=(binary+F1)/ns;ck(loss<=h+e*Math.log(Math.floor(J/6)+1)+1e-8,'discard bound');out.entropySplitChecks++;
   let upper=0,keys=0;const primes=[];for(let p=Y;p<=J+1;p++)if(p%2&&p>=5&&!spf[p])primes.push(p);
   for(let p of primes)for(let d1=0;d1<=s.D;d1+=2)for(let d2=0;d1+d2<=s.D;d2+=2)for(let e1 of [-1,1])for(let e2 of [-1,1])for(let e3 of [-1,1]){let cc=e1+1-e3;for(let k=1;k*p+cc+1-d1-d2<=J+1;k+=2){let q=k*p+cc+1-d1-d2;if(q<Y||q<5||q===p||q%2===0||spf[q])continue;let budget=J-2*(p-1)-(q-1)-d1-d2;if(budget<0)continue;let a=mod(e1,2*p);if(a%2)a+=p;a=mod(a,2*p);while(mod(a-(p-1)-d1-e2,q))a+=2*p;let step=2*p*q;let L=lo-budget,U=hi;a+=step*Math.ceil((L-a)/step);for(;a<=U;a+=step){let l=Math.max(lo,6*Math.ceil(a/6)),u=Math.min(hi,6*Math.floor((a+budget)/6));if(u>=l){upper+=(u-l)/6+1;keys++}}}}
   ck(s.roots<=upper&&s.keys.size<=keys,'CRT relay count');out.relayUnionChecks++;
   return {D:s.D,roots:s.roots,motifs:s.motifs,keys:s.keys.size,pairs:s.pairs.size,rate:e,entropyDiscardCost:loss,entropyDiscardUpper:h+e*Math.log(Math.floor(J/6)+1),crtUnionBound:upper,crtCandidateKeys:keys};});out.rows.push(r)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
