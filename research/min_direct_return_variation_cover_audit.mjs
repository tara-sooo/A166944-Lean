// Variation-charged short returns and bounded-overlap interval covers on actual MIN paths.
function audit(N=60000){
 const lim=1200000,spf=new Int32Array(lim);for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const st={roots:0,events:0,cap:0,blockChecks:0,selectedEvents:0,labels:0,returns:0,twinReturns:0,deficientReturns:0,deficientByM:{2:0,3:0,4:0},ordinaryVariationChecks:0,trimmedVariationChecks:0,coverChecks:0,coverIntervals:0,coverMaxOverlap:0,unionGainChecks:0,spacingChecks:0,capacityChecks:0,randomCoverChecks:0,randomCoverOverlap:0,positiveCoverBlocks:0,positiveTwinBlocks:0,generalGapControls:0,generalGapPairs:0,generalGapByK:{4:0,8:0,32:0},generalCoverChecks:0,generalVertexChecks:0,generalTrimChecks:0,partitionControls:0,partitionBlocks:0,partitionGainChecks:0,examples:[]};
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<=1;I++)for(let p of factors(H-1+2*I)){if(p===2||p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let e=1-2*I,q=(H-e)/p,d=2*t-H,dp=d+2*w-p+1;z={H,t,p,w,I,e,q,d,dp,D:dp-6*I,g:p-1}}}return z}
 // Minimum-cardinality cover is unnecessary: greedily advance the right edge
 // with the interval reaching furthest. Selected intervals have depth <=2.
 function cover(intervals){
  let a=intervals.slice().sort((u,v)=>u.a-v.a||v.b-u.b),out=[],i=0;
  while(i<a.length){let start=a[i].a,edge=start;
   while(true){let best=null;while(i<a.length&&a[i].a<=edge){if(a[i].b>edge&&(!best||a[i].b>best.b))best=a[i];i++}if(!best)break;out.push(best);edge=best.b}
  }
  return out
 }
 function unionLen(a){let s=a.slice().sort((x,y)=>x.a-y.a||x.b-y.b),z=0,end=-Infinity;for(let v of s){z+=Math.max(0,v.b-Math.max(end,v.a));end=Math.max(end,v.b)}return z}
 function depth(a){let ev=a.flatMap(z=>[[z.a,1],[z.b,-1]]).sort((x,y)=>x[0]-y[0]||x[1]-y[1]),n=0,m=0;for(let [_,v] of ev){n+=v;m=Math.max(m,n)}return m}
 function inspect(rows,T,select){
  if(!rows.length)return {G:0,F:0,b:0,B:0,V:0,W:0,Wt:0};let G=rows.at(-1).H+rows.at(-1).g-rows[0].H,groups=new Map,F=0,V=0,Vbig=0,vs=[0],vb=[0],intervals=[],W=0,Wt=0,B=0;
  for(let i=0;i<rows.length;i++){let z=rows[i],v=Math.abs(z.dp-z.d);V+=v;if(8*v>z.g)Vbig+=v;vs.push(V);vb.push(Vbig);if(z.p>=T&&z.w>6&&4*z.w>=z.g&&spf[z.q]===z.q&&select(z)){if(!groups.has(z.p))groups.set(z.p,[]);groups.get(z.p).push({...z,i});F+=z.g;st.selectedEvents++}}
  for(let [p,list] of groups){let n=list.length,h=0,r=0;
   for(let i=1;i<n;i++){let a=list[i-1],b=list[i],m=(b.q-a.q)/2,s1=mod(a.e*p,3)===1?1:-1,s2=mod(b.e*p,3)===1?1:-1,base=6+(s1-s2)/2;
    ok(a.H%3===0&&b.H%3===0&&Number.isInteger(m)&&m>=1&&b.H-a.H===2*m*p+b.e-a.e,"return coordinates");
    let eta=Number(m===1),chi=Number(!eta&&m<base);ok(m>=base-3*chi-6*eta,"spacing correction");if(eta){r++;st.twinReturns++}
    if(chi){ok([2,3,4].includes(m)&&m===base-3&&a.D!==b.D&&Math.abs(a.D-b.D)>=2*p,"deficient classification");h++;st.deficientReturns++;st.deficientByM[m]++;
     let left=a.H+a.g,right=b.H+b.g,L=right-left,v=vs[b.i+1]-vs[a.i+1],vbig=vb[b.i+1]-vb[a.i+1];
     ok(L===2*m*p+b.e-a.e&&L<=8*p+2&&v>=Math.abs(b.dp-a.dp)&&v>=2*p-6,"variation");
     ok(8*vbig>=8*(2*p-6)-L,"trimmed variation");
     intervals.push({a:left,b:right,p,i:a.i+1,j:b.i+1,v,vbig});st.ordinaryVariationChecks++;st.trimmedVariationChecks++;
     if(st.examples.length<5&&p>=17)st.examples.push({p,m,q:[a.q,b.q],H:[a.H,b.H],D:[a.D,b.D],d:[a.dp,b.dp],intervalGain:L,variation:v,largeVariation:vbig,relay:rows.slice(a.i+1,b.i).map(z=>z.p)})
    }
    st.returns++
   }
   ok(12*p*n<=G+14*p+2+6*p*h+12*p*r,"label capacity");W+=p*h;Wt+=p*r;B+=14*p+2;st.spacingChecks++;st.labels++
  }
  let cv=cover(intervals),u=unionLen(intervals),u2=unionLen(cv),dep=depth(cv);
  ok(u===u2&&dep<=2,"cover");st.coverMaxOverlap=Math.max(st.coverMaxOverlap,dep);st.coverIntervals+=cv.length;st.coverChecks++;
  let cg=intervals.reduce((s,z)=>s+z.p-1,0),cvV=cv.reduce((s,z)=>s+z.v,0),cvB=cv.reduce((s,z)=>s+z.vbig,0);
  ok(cg<=u&&cvV<=2*V&&cvB<=2*Vbig,"cover charges");st.unionGainChecks++;
  ok((T-1)*(2*T-6)*W<=2*T*(8*T+2)*V,"full variation bound");
  ok((T-1)*(4*T-25)*W<=8*T*(8*T+2)*Vbig,"trimmed variation bound");
  ok(12*F<=groups.size*G+B+6*W+12*Wt,"aggregate capacity");st.capacityChecks++;st.blockChecks++;
  if(W)st.positiveCoverBlocks++;if(Wt)st.positiveTwinBlocks++;
  if(T===17)for(let K of [4,8,32]){
   let pref=[0],all=[],W=0,vertices=new Set;for(let z of rows){let v=Math.abs(z.dp-z.d);pref.push(pref.at(-1)+(2*K*v>z.g?v:0))}
   for(let [p,l] of groups)for(let j=1;j<l.length;j++){
    let a=l[j-1],b=l[j],m=(b.q-a.q)/2;if(m>K||a.D===b.D)continue;
    let u=a.H+a.g,v=b.H+b.g,V=vs[b.i+1]-vs[a.i+1],Vb=pref[b.i+1]-pref[a.i+1];ok(v-u<=2*K*p+2&&V>=2*p-6,"general interval");ok(2*K*Vb>=2*K*(2*p-6)-(v-u),"general trimmed");
    all.push({a:u,b:v,p,V,Vb});W+=p;vertices.add(a.i);vertices.add(b.i);st.generalGapPairs++;st.generalGapByK[K]++;
   }
   let c=cover(all),len=unionLen(all),dep=depth(c),sum=c.reduce((x,z)=>x+z.V,0),sumb=c.reduce((x,z)=>x+z.Vb,0),vert=[...vertices].reduce((x,j)=>x+rows[j].g,0);
   ok(unionLen(c)===len&&dep<=2&&sum<=2*V&&sumb<=2*pref.at(-1),"general cover");
   ok(all.reduce((x,z)=>x+z.p-1,0)<=len&&vert<=2*W,"general vertex");
   ok((T-1)*(2*T-6)*W<=2*T*(2*K*T+2)*V,"general variation");
   ok((T-1)*(K*(T-6)-1)*W<=2*K*T*(2*K*T+2)*pref.at(-1),"general trimmed variation");
   st.generalGapControls++;st.generalCoverChecks++;st.generalVertexChecks++;st.generalTrimChecks++;
  }
  return {G,F,b:groups.size,B,V,W,Wt};
 }
 let seed=913;const rand=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
 for(let k=0;k<10000;k++){let a=[];for(let j=0,n=1+rand(70);j<n;j++){let x=rand(100);a.push({a:x,b:x+1+rand(40)})}let c=cover(a);ok(unionLen(a)===unionLen(c)&&depth(c)<=2,"random cover");st.randomCoverOverlap=Math.max(st.randomCoverOverlap,depth(c));st.randomCoverChecks++}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let T of [11,17,47])inspect(rows,T,()=>true);
  if(rows.length>=4&&M%3===2){
   let k=4,tot={G:0,F:0,weighted:0,B:0,V:0,W:0,Wt:0};for(let a=0;a<rows.length;){let b=a,s=new Set;
    while(b<rows.length){let z=rows[b],q=z.p>=11&&z.w>6&&4*z.w>=z.g&&spf[z.q]===z.q;if(q&&!s.has(z.p)&&s.size===k)break;if(q)s.add(z.p);b++}
    ok(b>a,"partition");let v=inspect(rows.slice(a,b),11,()=>true);ok(v.b<=k,"partition support");tot.G+=v.G;tot.F+=v.F;tot.weighted+=v.b*v.G;tot.B+=v.B;tot.V+=v.V;tot.W+=v.W;tot.Wt+=v.Wt;st.partitionBlocks++;a=b
   }
   let G=rows.reduce((a,z)=>a+z.g,0),V=rows.reduce((a,z)=>a+Math.abs(z.dp-z.d),0);ok(G===tot.G&&V===tot.V&&12*tot.F<=tot.weighted+tot.B+6*tot.W+12*tot.Wt,"partition aggregate");st.partitionControls++;st.partitionGainChecks++;
  }
  if(rows.length>=4){let a=rand(rows.length-2),b=a+2+rand(rows.length-a-1),labels=[...new Set(rows.slice(a,b).map(z=>z.p))].sort((a,b)=>b-a).slice(0,4);inspect(rows.slice(a,b),11,z=>labels.includes(z.p))}
 }
 ok(st.deficientReturns&&st.deficientByM[2]&&st.deficientByM[3]&&st.deficientByM[4]&&st.twinReturns&&st.coverMaxOverlap===2&&st.positiveCoverBlocks&&st.generalGapPairs&&st.partitionControls,"coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
