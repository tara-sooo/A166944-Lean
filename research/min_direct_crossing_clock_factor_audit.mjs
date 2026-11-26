// Exact crossing coverage/clock bounds, complete-excursion deficit charge and factor certificates.
function audit(N=30000){
 const lim=4500000,spf=new Int32Array(lim),ps=[];
 for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i%2)ps.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b,prod=a=>a.reduce((v,p)=>v*p,1);
 const factors=x=>{ok(x>0&&x<lim,"factor range "+x);let a=[];while(x>1){let p=spf[x];a.push(p);x/=p}return a};
 const next=(H,t)=>{let z=null;for(let I=0;I<2;I++)for(let p of new Set(factors(H-1+2*I))){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p)z={H,t,p,w,I,d:2*t-H,dp:2*t-H+2*w-p+1}}return z};
 const reset=z=>z.p>=5&&z.dp===6*z.I,fast=z=>4*z.w<z.p-1;
 const st={roots:0,events:0,unresolved:0,periods:0,periodPositions:0,windowControls:0,coverageChecks:0,clockChecks:0,combinedChecks:0,crossingEvents:0,largeCrossingEvents:0,longCrossingEvents:0,roughnessChecks:0,factorBounds:{3:0,4:0,5:0,6:0},canonicalSegments:0,selectedSegments:0,fastEvents:0,fastResets:0,fastNonresets:0,upwardCrossers:0,excursionChecks:0,boundaryChecks:0,certificateSearch:0,certifiedRoots:0,primeCofactorChecks:0,independentTicks:0,examples:[],resetExample:null};
 function setup(S,R,V,L){
  let small=ps.filter(p=>p<=R),extra=ps.filter(p=>p>R&&p<=V),PS=prod(small.filter(p=>p<=S)),P=prod(small)*prod(extra);
  ok(P<=300000,"period cap");
  let pref=new Int32Array(P+1);
  for(let j=0;j<P;j++){let hit=small.every(p=>{let a=mod(2*j,p);return p<=S?a===0:a%2===0&&a<=p-3})&&extra.every(p=>![1,p-1].includes(mod(2*j,p)));pref[j+1]=pref[j]+Number(hit)}
  let A=pref[P];ok(A===prod(small.map(p=>p<=S?1:(p-1)/2))*prod(extra.map(p=>p-2)),"density");
  function pre(j){let q=Math.floor(j/P);return q*A+pref[j-q*P]}
  let mass=(a,b)=>pre(b)-pre(a),unit=BigInt(A*L),p=BigInt(P),errs=[0n];
  for(let j=0;j<P;j++){let v=p*BigInt(mass(j,j+L))-unit;errs.push(errs.at(-1)+(v>0n?v:0n))}
  function ep(j){let q=Math.floor(j/P);return BigInt(q)*errs[P]+errs[j-q*P]}
  st.periods++;st.periodPositions+=P;
  return {S,R,V,L,P,PS,A,unit,p,mass,err:(a,b)=>ep(b)-ep(a),D:2*PS+1}
 }
 let cs=[setup(3,5,7,3),setup(5,7,17,6),setup(7,11,17,13)];
 function certify(z){
  if(z.p<5||fast(z))return;
  let fs=[factors(z.H-1),factors(z.H+1)],f=Math.min(fs[0][0],fs[1][0]),q=(z.H-(1-2*z.I))/z.p;
  ok(q>=z.p&&Number.isInteger(q)&&2*f>=z.w&&8*f>=z.p-1,"roughness");st.roughnessChecks++;
  for(let k of [3,4,5,6])if(BigInt(z.p-1)**BigInt(k)>8n**BigInt(k)*BigInt(z.H+1)){
   ok(fs.every(a=>a.length<=k-1)&&factors(q).length<=k-2,"factor certificate "+k);st.factorBounds[k]++;
   if(k===3){ok(spf[q]===q,"prime cofactor");st.primeCofactorChecks++}
  }
 }
 function inspect(rows,c,T){
  if(!rows.length)return;
  let {unit,p,L,mass,err,D,PS}=c,a=rows[0].H/2,z=rows.at(-1),b=(z.H+z.p-1)/2,G=2*(b-a),W=z.t+z.w-rows[0].t;
  let cut=rows.map(z=>mass(z.H/2,(z.H+z.p-1)/2)),large=rows.map((z,i)=>cut[i]>0&&z.p>=T),U=0,F=0,mH=0,nSmall=0,mMid=0,Gmid=0,Lup=0;
  for(let i=0;i<rows.length;i++){let z=rows[i],g=z.p-1,B=cut[i];ok(B<=Math.ceil(g/(2*PS)),"lattice");if(B){ok(z.p>c.R,"barrier");st.crossingEvents++}
   if(large[i]){mH++;st.largeCrossingEvents++;if(!fast(z)){F+=g;st.longCrossingEvents++}if(!reset(z)&&2*z.w>g)Lup+=g}
   else{U+=g;if(B){if(z.p<=D){ok(B===1,"small one");nSmall++}else{mMid++;Gmid+=g}}}
  }
  let whole=2n*p*BigInt(L)*BigInt(mass(a,b)),E=2n*err(a-L+1,b)+(BigInt(G)*unit>whole?BigInt(G)*unit-whole:0n);
  let lowBound=2n*p*BigInt(L*nSmall)+unit*BigInt(Gmid+2*(L-1)*mMid);
  ok(BigInt(U)*unit<=lowBound+unit*BigInt(2*(L-1)*mH)+E,"coverage");st.coverageChecks++;
  let den=BigInt(T-1),clock=BigInt(11*U)*den+BigInt(7*(T-1)+8)*BigInt(F);
  ok(BigInt(4*W-G)*den<=clock&&BigInt(G-2*rows[0].d)*den<=clock,"clock");st.clockChecks++;
  ok(BigInt(G-2*rows[0].d)*den*unit<=11n*(lowBound+E)*den+22n*BigInt((L-1)*G)*unit+BigInt(7*(T-1)+8)*BigInt(F)*unit,"combined");st.combinedChecks++;
  let visits=[];
  for(let i=0;i<rows.length;i++){let z=rows[i],ct=z.H/2+3;if(z.H%4===0&&ct>=z.t&&ct<z.t+z.w)visits.push({time:ct,H:z.H,idx:i})}
  let endH=z.H+z.p-1,endT=z.t+z.w;if(endH%4===0&&2*endT-endH===6)visits.push({time:endT,H:endH,idx:rows.length});
  let contained=new Set,fastGain=0,segU=0,segUp=0,quiet=0,resetUp=0,nSeg=0;
  for(let v=1;v<visits.length;v++){
   let l=visits[v-1],r=visits[v];ok(l.idx<r.idx&&2*(r.time-l.time)===r.H-l.H,"canonical balance");st.canonicalSegments++;
   let marked=[];for(let i=l.idx;i<r.idx;i++){contained.add(i);let z=rows[i];if(z.p>=T&&fast(z))marked.push(i)}
   if(!marked.length)continue;
   nSeg++;st.selectedSegments++;
   let Pinc=0,Ndec=0,curD=6,Gf=0,localU=0,localUp=0,localR=0,fastResets=[];
   for(let i=l.idx;i<r.idx;i++){let z=rows[i],g=z.p-1,tw=i===l.idx?z.t+z.w-l.time:z.w,dd=2*tw-g;ok(tw>=1&&tw<=z.w&&curD+dd===z.dp,"segment clock");curD=z.dp;
    if(dd>0)Pinc+=dd;else Ndec-=dd;
    if(!large[i]){localU+=g;if(dd>0)ok(dd<=5*g,"small increase")}
    else if(dd>0&&reset(z)){ok(dd<=6,"reset increase");localR+=dd}
    else if(dd>0){ok(2*z.w>g&&(T-1)*dd<=(3*(T-1)+4)*g,"large increase");localUp+=g;st.upwardCrossers++}
    if(marked.includes(i)){ok(2*(-dd)>g,"fast decrease");Gf+=g;st.fastEvents++;if(reset(z)){st.fastResets++;fastResets.push(i)}else st.fastNonresets++}
   }
   let q=6-curD;ok(q>=0&&q<=6&&Pinc+q===Ndec,"quiet tail balance");
   ok(BigInt(Gf)*den<=10n*BigInt(localU)*den+2n*BigInt(3*(T-1)+4)*BigInt(localUp)+2n*BigInt(localR+q)*den,"excursion transfer");
   if(fastResets.length){ok(fastResets.length===1,"one fast reset");let i=fastResets[0];for(let h=l.idx;h<i;h++)ok(!(rows[h].p>=T&&reset(rows[h])),"no earlier large reset");if(localUp&&!st.resetExample)st.resetExample={H:l.H,T,S:c.S,R:c.R,V:c.V,labels:rows.slice(l.idx,r.idx).map(z=>z.p),fastReset:rows[i].p,priorLargeUpGain:localUp}}
   fastGain+=Gf;segU+=localU;segUp+=localUp;quiet+=q;resetUp+=localR;st.excursionChecks++;
  }
  let pending=rows.filter((z,i)=>z.p>=T&&fast(z)&&reset(z)&&!contained.has(i));
  ok(pending.length<=2,"boundary reset count");st.boundaryChecks++;
  ok(segU<=U&&segUp<=Lup&&quiet<=6*nSeg&&resetUp<=6*G/(T-1),"aggregate");ok(BigInt(fastGain)*den<=10n*BigInt(U)*den+2n*BigInt(3*(T-1)+4)*BigInt(Lup)+24n*BigInt(G),"aggregate excursion");
  st.windowControls++;
 }
 function run(M,max=180){let H=2*M-2,t=M+2,rows=[];for(let j=0;j<max;j++){let z=next(H,t);if(!z)break;ok(z.d>=0&&z.dp>=0,"envelope");rows.push(z);H+=z.p-1;t+=z.w;if(H+1>=lim)break}return rows}
 for(let M=5;M<=N;M+=2){let rows=run(M);st.roots++;st.events+=rows.length;if(rows.length===180)st.unresolved++;for(let z of rows)certify(z);if(!rows.length)continue;
  inspect(rows,cs[M%3],M%5===0?17:M%7===0?47:7);
  if(rows.length>=4){let a=Math.floor(rows.length/4),b=Math.max(a+1,Math.floor(3*rows.length/4));inspect(rows.slice(a,b),cs[(M+1)%3],13)}
 }
 // Find canonical starts at large enough H for the cube certificate to be nonvacuous.
 const primes=ps.filter(p=>p>=1050&&p<=2100);
 outer:for(let p of primes)for(let q of primes){if(q<p||p*q+3>=lim)continue;let H=p*q+(mod(p*q,4)===1?-1:1),M=H/2+1,t=M+2,z=next(H,t);st.certificateSearch++;
  if(!z||fast(z)||BigInt(z.p-1)**3n<=512n*BigInt(H+1))continue;
  certify(z);st.certifiedRoots++;let rows=run(M,100);for(let c of cs)inspect(rows,c,Math.max(47,Math.floor(z.p/2)));
  let found=null;for(let w=1;w<=z.w;w++){let n=t+w,I=n%2,e=1-2*I;let a=n-2*I,b=H-e;while(b)[a,b]=[b,a%b];let f=factors(a).filter(p=>p%2&&p*p<=H+1).sort((a,b)=>a-b)[0];if(f){found={w,p:f,I};break}st.independentTicks++}
  ok(found&&found.w===z.w&&found.p===z.p&&found.I===z.I,"literal clock");st.independentTicks++;
  if(st.examples.length<4)st.examples.push({M,H,p:z.p,q:(H-(1-2*z.I))/z.p,w:z.w,neighbors:[factors(H-1),factors(H+1)],d:z.d,dp:z.dp});
  if(st.certifiedRoots>=24)break outer
 }
 ok(st.certifiedRoots&&st.factorBounds[3]&&st.fastResets&&st.fastNonresets&&st.upwardCrossers&&st.excursionChecks&&st.combinedChecks,"coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||30000)),null,2));
