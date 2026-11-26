// Causal level-by-level matching at logarithmic recycling scale and same-label overlap.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim);for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,d,dp,g,h:(dp-6*I)/(2*p)}}}return z}
 const st={roots:0,events:0,cap:0,bins:0,guardBins:0,selected:0,selectedDrop:0,matched:0,unmatched:0,low:0,mid:0,tail:0,weakSame:0,strongSame:0,crossLabel:0,sourceChecks:0,matchingChecks:0,weakChecks:0,tailChecks:0,binChecks:0,distinctMid:0,multisourceBins:0,examples:[],synthetic:0};
 function check(v,T,R,L){
  let k=Math.floor(Math.sqrt(T)),sel=v.filter(z=>z.p>=T&&z.p<=R&&z.dp>6&&k*z.w<z.g);st.bins++;if(!sel.length)return;st.guardBins++;st.selected+=sel.length;
  let guard=new Set;for(let z of sel)for(let u=z.dp;u<z.dp+z.g;u+=2)guard.add(u);
  let M=2*guard.size,B=Math.max(T,2*M+1),source=new Map,used=new Map,weak=new Map,tailN=0,tailFlux=0,first=v[0].H,last=v.at(-1).H,ids=new Set(sel),mid=new Set;
  let F=sel.reduce((s,z)=>s+z.g,0),drops=0,unmatched=0,matched=0,low=0,tail=0,middle=0,weakSame=0,strongSame=0,cross=0;
  for(let z of v){
   if(z.dp>z.d){if(z.p>B)tailN++;for(let u=z.d;u<z.dp;u+=2)if(guard.has(u)){ok(!source.has(u),"alternating up");source.set(u,z);if(z.p>B)tailFlux+=2}}
   if(z.dp<z.d)for(let u=z.dp;u<z.d;u+=2)if(guard.has(u)){
    let a=source.get(u);source.delete(u);if(!ids.has(z))continue;drops+=2;
    if(!a){unmatched+=2;continue}
    matched+=2;ok(a.H<z.H&&z.H-a.H<L&&a.d<=u&&u<a.dp&&z.dp<=u&&u<z.d,"causal");st.matchingChecks++;
    let n=(used.get(a)||0)+2;used.set(a,n);ok(n<=Math.min(M,a.dp-a.d),"no double use");st.sourceChecks++;
    if(a.p<T)low+=2;else if(a.p>B)tail+=2;else{middle+=2;mid.add(a.p)}
    if(a.p!==z.p)cross+=2;else if(a.dp-a.d<=a.p-3){weakSame+=2;let n=(weak.get(a)||0)+2;weak.set(a,n);ok(a.dp-6<=u&&n<=6,"weak same label overlap");st.weakChecks++}else strongSame+=2;
   }
  }
  let G=v.reduce((s,z)=>s+z.g,0),Glo=v.filter(z=>z.p<T).reduce((s,z)=>s+z.g,0);
  ok(k*drops>(k-2)*F&&unmatched<=M&&drops===unmatched+matched&&matched===low+middle+tail&&matched===weakSame+strongSame+cross,"partition");
  ok(tailN<=1+Math.floor((last-first)/(B-1))&&tail<=tailFlux&&tailFlux<=M*tailN&&low<=5*Glo,"tail");st.tailChecks++;
  ok(F<=L+R&& (k-2)*F<=k*(M+low+middle+tail),"budget");st.binChecks++;
  st.selectedDrop+=drops;st.matched+=matched;st.unmatched+=unmatched;st.low+=low;st.mid+=middle;st.tail+=tail;st.weakSame+=weakSame;st.strongSame+=strongSame;st.crossLabel+=cross;st.distinctMid+=mid.size;if(mid.size>1)st.multisourceBins++;
  if(st.examples.length<3&&middle&&strongSame)st.examples.push({T,R,L,M,B,F,drops,matched,unmatched,low,middle,tail,strongSame,weakSame,cross,mid:[...mid]});
 }
 for(let n=5;n<=N;n+=2){let H=2*n-2,t=n+2,v=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;v.push(z);H+=z.g;t+=z.w}st.events+=v.length;if(v.length===180)st.cap++;
 for(let T of [9,17,31,61]){let R=4*T,L=Math.ceil(T*Math.log(T)**2),a=[];let key=-1;for(let z of v){let j=Math.floor(z.H/L);if(j!==key){if(a.length)check(a,T,R,L);a=[];key=j}a.push(z)}if(a.length)check(a,T,R,L)}}
 for(let p of [11,17,31,61])for(let h=1;h<=8;h++)for(let I of [0,1])for(let J of [0,1])for(let k=0;k<=12;k++){let a=2*p*h+6*I,b=2*p*k+6*J;for(let u=2;u<=p-3;u+=2){let ov=Math.max(0,Math.min(a,b+p-3)-Math.max(a-u,b));ok(ov<=6&&(!ov||Math.max(a-u,b)>=a-6),"abstract weak overlap");st.synthetic++}}
 ok(st.matched&&st.mid&&st.crossLabel&&st.synthetic&&st.tailChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
