// Causal transport exposure, short physical words and disjoint packing.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim);
 for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"factor range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g,h:(dp-6*I)/(2*p)}}}return z}
 function union(a){let out=[];for(let [l,r] of a.sort((a,b)=>a[0]-b[0])){if(out.length&&l<=out.at(-1)[1])out.at(-1)[1]=Math.max(r,out.at(-1)[1]);else out.push([l,r])}return out}
 const st={roots:0,events:0,cap:0,bins:0,guards:0,matched:0,middle:0,originalCross:0,originalOne:0,originalException:0,expandedCross:0,expandedMidCross:0,bufferCovered:0,bufferCompleted:0,bufferUnits:0,bufferForbiddenChecks:0,actualOneSources:0,actualOneBufferUnits:0,geometry:0,crt:0,capacity:0,sourceNonreuse:0,targetNonreuse:0,tailChecks:0,shallowChecks:0,syntheticPairs:0,syntheticCompleted:0,syntheticUnits:0,exposure:0,clockExposure:0,lowExposure:0,lowClockExposure:0,exposureChecks:0,wordChecks:0,shortPairs:0,shortWeight:0,lowRelayWeight:0,packingChecks:0,packedWeight:0,packedWords:0,maxDepth:0,multiRelay:0,shortExamples:[],examples:[]};
 function check(v,T,R,L){
  st.bins++;let k=Math.floor(Math.sqrt(T)),sel=v.filter(z=>z.p>=T&&z.p<=R&&z.dp>6&&k*z.w<z.g);
  // Actual completed excursions through a source's forbidden buffer, independently of chosen targets.
  for(let i=0;i<v.length;i++){let a=v[i],p=a.p;if(p<T||a.dp<=a.d||a.h<1)continue;let hi=2*p*a.h,lo=hi-p+3;if(a.d>lo||a.dp<hi)continue;st.bufferCovered++;
   let j=i+1;while(j<v.length&&v[j].dp>lo)j++;if(j===v.length)continue;st.bufferCompleted++;
   let floor=hi;
   for(let s=i+1;s<=j;s++){let z=v[s];if(z.dp>=floor)continue;let end=Math.max(lo,z.dp);if(end>=floor)continue;ok(z.d>=floor&&z.p!==p,"actual forbidden buffer first descent");st.bufferForbiddenChecks++;st.bufferUnits+=floor-end;floor=end}
   ok(floor===lo,"full buffer");if(st.examples.length<3)st.examples.push({T,L,p,H:a.H,sourcePre:a.d,sourcePost:a.dp,lo,hi,exitH:v[j].H,labels:v.slice(i+1,j+1).map(z=>z.p)})
  }
  if(!sel.length)return;st.guards++;
  let E=union(sel.map(z=>[z.dp,z.dp+z.g])),M=E.reduce((s,[a,b])=>s+b-a,0),E2=union(E.map(([a,b])=>[a,b+2*R])),M2=E2.reduce((s,[a,b])=>s+b-a,0);
  ok(E.length*(T-1)<=M&&M2<=M+2*R*E.length,"guard dilation");st.geometry++;
  let B1=Math.max(T,2*M+1),B2=Math.max(T,2*M2+1),ids=new Set(sel),last=new Map,used=new Map,targets=new Map,one=new Map,crossBySource=new Map,seenPairs=new Set;
  let O=0,S=0,C=0,X=0,Z=0,low=0,tail=0,shallow=0,total=0,orig=0;
  let idx=new Map(v.map((z,i)=>[z,i])),P=[0],W=[0],Q=[0],B=[0];for(let z of v){P.push(P.at(-1)+(z.p<T?z.g:0));W.push(W.at(-1)+z.w);Q.push(Q.at(-1)+(z.p<T?z.w:0));B.push(B.at(-1)+(z.p>=T?1:0))}
  let ex=0,wx=0,lx=0,qx=0,allPairs=new Map;
  let cut=6*T;
  for(let z of v){let up=z.dp>z.d,down=z.dp<z.d;if(!up&&!down)continue;
   for(let [a,b] of E2)for(let u=Math.max(a,Math.min(z.d,z.dp));u<Math.min(b,Math.max(z.d,z.dp));u+=2){
    if(up){ok(!last.has(u),"alternation");last.set(u,z);continue}
    let s=last.get(u);last.delete(u);if(!s)continue;
    let us=(used.get(s)||0)+2,ut=(targets.get(z)||0)+2;used.set(s,us);targets.set(z,ut);
    ok(us<=s.dp-s.d&&ut<=z.d-z.dp&&s.H<z.H&&z.H-s.H<L,"nonreuse");st.sourceNonreuse++;st.targetNonreuse++;
    let sourceMid=s.p>=T&&s.p<=B1;
    if(ids.has(z)){total+=2;if(sourceMid){orig+=2;if(s.p!==z.p)O+=2;else if(s.h-z.h===1){S+=2;let o=one.get(s)||{w:0,first:z};o.w+=2;one.set(s,o)}else X+=2}}
    let i=idx.get(s),j=idx.get(z),delta=z.H-s.H,dt=W[j+1]-W[i+1],Elo=P[j]-P[i+1],Wlo=Q[j]-Q[i+1];ex+=2*delta;wx+=2*dt;lx+=2*Elo;qx+=2*Wlo;
    if(!sourceMid||s.p===z.p)continue;
    if(z.p>=T&&z.p<=B2&&10*(z.d-z.dp)>=z.g&&10*(s.dp-s.d)>=s.g){
      let key=i+","+j,o=allPairs.get(key)||{i,j,weight:0,delta,Elo,Wlo};o.weight+=2;allPairs.set(key,o)
    }
    C+=2;let levels=crossBySource.get(s)||new Map;levels.set(u,z);crossBySource.set(s,levels);
    if(z.p<T)low+=2;else if(z.p>B2)tail+=2;else {Z+=2;if(10*(z.d-z.dp)<z.g||10*(s.dp-s.d)<s.g)shallow+=2}
    if(z.p>=T){let key=s.H+","+z.H;if(!seenPairs.has(key)){seenPairs.add(key);let p=s.p,r=z.p,A=s.e+p*(2*s.I-2*s.h-1),D=z.e+r*(2*z.I-2*z.h-1),delta=z.H-s.H;ok(mod(s.H-A,4*p)===0&&mod(z.H-D,4*r)===0,"phase");
      ok(mod(D-delta-A,4)===0,"compatibility");let H0=A+4*p*mod((D-delta-A)/4*inv(p,r),r);ok(mod(s.H-H0,4*p*r)===0&&mod(H0+delta-D,4*r)===0,"CRT");st.crt++}}
   }
  }
  for(let [s,o] of one){let p=s.p,hi=2*p*s.h,lo=hi-p+3,levels=crossBySource.get(s);ok(s.d<=lo&&o.first.d<=lo&&o.w<=p+3,"buffer endpoints");
    for(let u=lo;u<hi;u+=2){let z=levels?.get(u);ok(z&&z.H<o.first.H&&z.p!==p,"forced earlier cross");st.actualOneBufferUnits+=2}st.actualOneSources++}
  let G=v.reduce((s,z)=>s+z.g,0),Glo=v.filter(z=>z.p<T).reduce((s,z)=>s+z.g,0),nhi=v.filter(z=>z.p>B2).length;
  ok(C>=O&&(T+3)*C>=(T-3)*S&&orig===O+S+X&&X<=10*v.filter(z=>z.p>=T&&z.dp>z.d).length,"branch reduction");st.capacity++;
  ok(low<=Glo&&tail<=M2*nhi&&nhi<=1+Math.floor((v.at(-1).H-v[0].H)/(B2-1))&&C===Z+low+tail,"tail budget");st.tailChecks++;
  ok(10*shallow<=G,"shallow budget");st.shallowChecks++;
  ok(ex<=M2*(v.at(-1).H-v[0].H)&&wx<=M2*(W.at(-1)-W[1])&&lx<=M2*P.at(-1)&&qx<=M2*Q.at(-1),"integrated exposure");
  st.exposure+=ex;st.clockExposure+=wx;st.lowExposure+=lx;st.lowClockExposure+=qx;st.exposureChecks++;
  let short=[],shortWeight=0,longWeight=0,loBad=0,loCut=Math.max(1,Math.floor(T/4)),weight=0;
  for(let o of allPairs.values()){let {i,j,delta,Elo,Wlo}=o;weight+=o.weight;if(delta>cut){longWeight+=o.weight;continue}
   let hi=v.slice(i,j+1).filter(z=>z.p>=T),relay=hi.slice(0,-1).reduce((s,z)=>s+z.g,0);
   ok(delta===relay+Elo&&hi.length<=1+Math.floor(cut/(T-1))&&hi.slice(0,-1).every(z=>z.g<=cut)&&Wlo<=3*Elo,"short word");
   let n1=(v[i].H+v[i].g+v[i].dp)/2,n2=(v[j].H+v[j].g+v[j].dp)/2;ok(n2-n1===W[j+1]-W[i+1]&&2*(n2-n1)===delta+v[j].g-v[i].g+v[j].dp-v[i].dp,"clock identity");st.wordChecks++;st.shortPairs++;shortWeight+=o.weight;
   if(hi.length>2)st.multiRelay++;
   if(Elo>loCut){loBad+=o.weight;continue}
   short.push(o);if(st.shortExamples.length<3&&hi.length>2)st.shortExamples.push({T,L,labels:hi.map(z=>z.p),delta,Elo,Wlo,weight:o.weight,H:v[i].H,H2:v[j].H})
  }
  ok(cut*longWeight<=ex&&loCut*loBad<=lx&&weight===shortWeight+longWeight,"tail exposure");st.shortWeight+=shortWeight;st.lowRelayWeight+=shortWeight-loBad;
  // Color the whole-event spans. At a physical point source starts are separated by T-1,
  // and each source has at most 1+floor(cut/(T-1)) high targets in its forward span.
  let cap=(2+Math.floor((cut+B2)/(T-1)))*(1+Math.floor(cut/(T-1))),colors=[];
  short.sort((a,b)=>a.i-b.i||a.j-b.j);let totalWeight=0;
  for(let o of short){let c=colors.find(x=>x.end<o.i);if(!c){c={end:-1,weight:0,n:0};colors.push(c)}
   ok(c.end<o.i,"disjoint word");c.end=o.j;c.weight+=o.weight;c.n++;totalWeight+=o.weight}
  ok(colors.length<=cap&&totalWeight===shortWeight-loBad,"bounded depth");
  if(colors.length){let best=colors.reduce((a,b)=>a.weight>=b.weight?a:b);ok(best.weight*cap>=totalWeight,"packing");st.packedWeight+=best.weight;st.packedWords+=best.n;st.maxDepth=Math.max(st.maxDepth,colors.length)}
  st.packingChecks++;
  st.matched+=total;st.middle+=orig;st.originalCross+=O;st.originalOne+=S;st.originalException+=X;st.expandedCross+=C;st.expandedMidCross+=Z;
 }
 for(let n=5;n<=N;n+=2){let H=2*n-2,t=n+2,v=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;v.push(z);H+=z.g;t+=z.w}st.events+=v.length;if(v.length===180)st.cap++;
  for(let T of [11,17,31,61]){let R=4*T,L=Math.ceil(T*Math.log(T)**2),a=[],key=-1;for(let z of v){let j=Math.floor(z.H/L);if(j!==key){if(a.length)check(a,T,R,L);a=[];key=j}a.push(z)}if(a.length)check(a,T,R,L)}
 }
 // Independent interval/phase controls; these are not claimed to be actual MIN trajectories.
 for(let p of [11,17,31,61])for(let h=2;h<=8;h++)for(let I of [0,1])for(let J of [0,1])for(let rise=2;rise<=3*p+1;rise+=2)for(let drop=2;drop<=p-3;drop+=2){
   let a=2*p*h+6*I,b=2*p*(h-1)+6*J,lo=2*p*h-p+3,hi=2*p*h,ov=Math.max(0,Math.min(a,b+drop)-Math.max(a-rise,b));st.syntheticPairs++;
   if(!ov)continue;ok(a-rise< b+drop&&b+drop<=lo&&a>=hi&&ov<=p+3,"synthetic endpoints");let count=0;
   for(let u=lo;u<hi;u+=2){for(let m=h-2;m<=h+1;m++)for(let s of [0,1]){let d=2*p*m+6*s;ok(!(d<=u&&u<d+p-3),"forbidden same label cell")}count+=2}
   ok(count===p-3,"buffer length");st.syntheticUnits+=count;st.syntheticCompleted++;
 }
 ok(st.wordChecks&&st.packedWords&&st.multiRelay&&st.lowExposure&&st.bufferCompleted&&st.expandedCross&&st.crt&&st.syntheticCompleted,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
