// First-preheight cuts, nested partitions and height-capped absorption launch profiles.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=400010,spf=new Uint32Array(N+1),pr=[];
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 for(let p=3;p<=N;p+=2)if(!spf[p])pr.push(p);
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n,cut=Infinity,P=null){let p=Infinity,w=Infinity,q=Infinity;
  for(let s of [-1,1])for(let r of P?P:fs(a-s)){
   if(r>cut||P&&mod(a-s,r)!==0)continue;q=Math.min(q,r);let t=mod((s===-1?0:r+2)-n,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}
  }return {p,w,q}
 }
 function restrict(A,H,P=null){let a=A,n=3-A/2,h=3,k=0;
  while(true){let e=next(a,n,2*H+1,P);
   if(!Number.isFinite(e.p)||h+e.w>H)return {a,G:A-a,k,absorb:!Number.isFinite(e.p),t:H-2+(A-a)/2};
   a-=e.p-1;n+=e.w;h+=e.w-(e.p-1)/2;k++;ck(h>=0&&h===n+a/2,"height");
  }
 }
 let z={periodRoots:0,periodEvents:0,periodMassChecks:0,periodNestingChecks:0,periodLiftChecks:0,physicalRoots:0,physicalEvents:0,cutChecks:0,absorptionChecks:0,largeLaunchChecks:0,launchListChecks:0,physicalNestingChecks:0,pairScans:0,pairCutChecks:0,recordIntervalChecks:0,period:[],physical:[]};
 let prev=null;
 for(let H of [3,4,5,6,7,8]){let P=pr.filter(p=>p<=2*H+1),M=2*P.filter(p=>p>=5).reduce((s,p)=>s*p,1),Q=3*M/2,cut=new Map(),abs=new Map(),gain=new Int32Array(M),key=new Int32Array(M),sum=0,max=0,energy=0,ae=0,as=0,V=P.filter(p=>p>=5).reduce((s,p)=>s*(1-2/p),1);
  for(let j=0;j<M;j++){let A=6*j,x=restrict(A,H,P),b=mod(x.a,6*M);ck(x.G<=2*(Q-1),"wall");gain[j]=x.G;key[j]=b;cut.set(b,(cut.get(b)||0)+1);sum+=x.G;max=Math.max(max,x.G);if(x.absorb){ck(b%6===0,"absorber");abs.set(b,(abs.get(b)||0)+1);as++}z.periodRoots++;z.periodEvents+=x.k}
  let total=0,mm=0;for(let m of cut.values()){total+=m;energy+=m*m;mm=Math.max(mm,m)}for(let m of abs.values())ae+=m*m;
  ck(total===M,"mass");z.periodMassChecks++;
  if(prev){let map=new Map();for(let j=0;j<M;j++){let x=mod(6*j-prev.gain[j%prev.M],6*M),y=key[j];if(map.has(x))ck(map.get(x)===y,"nested");else map.set(x,y);z.periodNestingChecks++}ck(energy/M>=prev.energy/prev.M-1e-10,"monotone energy");z.periodLiftChecks++}
  prev={M,gain,energy};z.period.push({H,M,cutStates:cut.size,meanGain:sum/M,maxGain:max,maxMass:mm,kappa2:energy/M,absorbFraction:as/M,nu1:as/(M*V),nu2:ae/(M*V)});
 }
 for(let R of [3000,12000,48000,192000]){
  let T=Math.ceil(8*Math.sqrt(2*R+1)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,Hs=[6,12,24,48,96],rows=Hs.map(H=>({H,cuts:0,cutGain:0,cutEnergy:0,absorb:0,large:0,largeTimed:0,largeEnergy:0,maxGain:0,stopGain:0,cut:new Map(),actual:new Map(),expected:new Map(),keys:new Int32Array(nr).fill(-1)})),paths=[];
  for(let i=0;i<nr;i++){let A=lo+6*i,a=A,n=3-A/2,h=3,end=n+T,idx=0,path=[],maxPre=3;
   while(true){let e=next(a,n),f=n+e.w,pre=h+e.w;
    if(R===3000)path.push({a,s:n,e:Math.min(end,f-1),h,maxPre});
    while(idx<Hs.length&&pre>Hs[idx]){let H=Hs[idx],row=rows[idx],ct=n+H+1-h,G=A-a;ck(ct-(3-A/2)===H-2+G/2,"cut time");
     if(ct<=end){row.cuts++;row.cutGain+=G;row.maxGain=Math.max(row.maxGain,G);row.keys[i]=a;row.cut.set(a,(row.cut.get(a)||0)+1);z.cutChecks++;
      if(e.p>=64*(H+1)){ck(e.q>=e.p/8&&e.q>2*H+1&&a%6===0,"large rough");let st=next(a,3-a/2);ck(st.p===e.p&&3+st.w===pre,"stationary");let x=row.actual.get(a)||[];x.push(A);row.actual.set(a,x);row.large++;if(f<=end)row.largeTimed++;z.largeLaunchChecks++}
     }row.stopGain+=f<=end?G+e.p-1:G;idx++}
    if(f>end){while(idx<Hs.length)rows[idx++].stopGain+=A-a;break}
    maxPre=Math.max(maxPre,pre);a-=e.p-1;n=f;h=pre-(e.p-1)/2;z.physicalEvents++;
   }
   if(R===3000)paths.push(path);
   for(let j=0;j<Hs.length;j++){let H=Hs[j],x=restrict(A,H),row=rows[j];ck((x.t<=T)===(row.keys[i]>=0),"cut reach");if(x.t<=T)ck(x.a===row.keys[i],"cut position");if(x.absorb&&x.t<=T){row.absorb++;z.absorptionChecks++;let e=next(x.a,3-x.a/2);if(e.p>=64*(H+1)){let ar=row.expected.get(x.a)||[];ar.push(A);row.expected.set(x.a,ar)}}}
   z.physicalRoots++;
  }
  for(let row of rows){ck(row.actual.size===row.expected.size,"launch maps");for(let [a,x] of row.actual){ck(JSON.stringify(x)===JSON.stringify(row.expected.get(a)),"root list");row.largeEnergy+=x.length**2;z.launchListChecks++}for(let m of row.cut.values())row.cutEnergy+=m*m}
  for(let j=0;j+1<rows.length;j++){let map=new Map(),r=rows[j],s=rows[j+1];for(let i=0;i<nr;i++)if(s.keys[i]>=0){ck(r.keys[i]>=0,"lower attained");let b=r.keys[i],c=s.keys[i];if(map.has(b))ck(map.get(b)===c,"physical nesting");else map.set(b,c);z.physicalNestingChecks++}}
  if(R===3000)for(let i=0;i<nr;i++)for(let j=i+1;j<nr;j++){let a=paths[i],b=paths[j],u=0,v=0,past=Infinity,future=-Infinity;
   while(u<a.length&&v<b.length){let x=a[u],y=b[v];if(x.a===y.a&&Math.max(x.s,y.s)<=Math.min(x.e,y.e)){let n=Math.max(x.s,y.s);past=Math.max(x.maxPre,y.maxPre,x.h+n-x.s,y.h+n-y.s);let end=3-(lo+6*j)/2+T;for(let k=u;k<a.length&&a[k].s<end;k++){let X=a[k],t=Math.min(X.e+1,end);future=Math.max(future,X.h+t-X.s)}break}
    if(x.e<y.e)u++;else v++}
   z.pairScans++;for(let row of rows){let H=row.H+1,shared=row.keys[i]>=0&&row.keys[i]===row.keys[j];ck(shared===(past<H&&H<=future),{i,j,H,past,future,shared});z.pairCutChecks++;z.recordIntervalChecks+=+shared}
  }
  z.physical.push({R,T,nr,rows:rows.map(({cut,actual,expected,keys,...r})=>r)});
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
