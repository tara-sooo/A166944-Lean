// All-height actual cut energy ledger separating each fresh prime's entire effect from old-label transport.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=1000010,spf=new Uint32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let e of [-1,1])for(let q of fs(a-e)){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}return {p,w}}
 let z={roots:0,survivors:0,events:0,intervals:0,corrections:0,freshLevels:0,energyChecks:0,massChecks:0,independentChecks:0,rows:[]};
 for(let R of [48000,192000,480000]){
  let Hmax=R===48000?256:512,T=Math.ceil(8*Math.sqrt(2*R+1)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),Nroots=(hi-lo)/6+1,sites=new Map(),corr=new Map(),mass=new Float64Array(Hmax+2),energy=new Float64Array(Hmax+2),oldDelta=new Float64Array(Hmax+2),freshMass=new Float64Array(Hmax+2),selected=new Map(),nKeep=0;
  function put(a,l,h){let s=sites.get(a)||[];s.push(l,h);sites.set(a,s);z.intervals++}
  function change(a,h,d){let m=corr.get(a)||[];m.push(h,d);corr.set(a,m)}
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,h=3,record=3,ar=[],first=new Map(),end=n+T,ok=false;
   for(;;){let e=next(a,n),pre=h+e.w,f=n+e.w;
    let maxCut=Math.min(pre,Hmax+1);
    if(maxCut>record){let t=n+maxCut-h;if(t>end)break;ar.push(a,record+1,maxCut);record=maxCut;if(record===Hmax+1){ok=true;break}}
    if(f>end)break;
    if(e.p===2*pre+1&&pre===record&&pre<=Hmax&&!first.has(pre))first.set(pre,a);
    a-=e.p-1;n=f;h=pre-(e.p-1)/2;z.events++;ck(a>0,"physical domain");
   }
   z.roots++;if(!ok)continue;nKeep++;z.survivors++;
   for(let i=0;i<ar.length;i+=3)put(ar[i],ar[i+1],ar[i+2]);
   for(let [b,x] of first){let y=null;for(let i=0;i<ar.length;i+=3)if(ar[i+1]<=b+1&&b+1<=ar[i+2]){y=ar[i];break}
    ck(y!==null&&y<x,"fresh shift");change(x,b+1,1);change(y,b+1,-1);freshMass[b]++;z.corrections++;
   }
   if((A-lo)/6%997===0){let arr=[];for(let b=4;b<=Hmax;b++)if(!spf[2*b+1])arr.push(b);selected.set(A,{ar,first,bands:arr.filter((b,i)=>i%11===0)})}
  }
  // At a site, sweep cut-height intervals and signed changes to
  // replace full first-(b+1) masses by the old-only masses.
  let diff=new Int32Array(Hmax+3),cd=new Int32Array(Hmax+3);
  for(let a of new Set([...sites.keys(),...corr.keys()])){
   diff.fill(0);cd.fill(0);let ints=sites.get(a)||[],ds=corr.get(a)||[];
   for(let i=0;i<ints.length;i+=2){diff[ints[i]]++;diff[ints[i+1]+1]--}
   for(let i=0;i<ds.length;i+=2)cd[ds[i]]+=ds[i+1];
   let m=0;for(let b=4;b<=Hmax+1;b++){m+=diff[b];ck(m>=0&&m+cd[b]>=0,"mass");energy[b]+=m*m;mass[b]+=m;if(cd[b])oldDelta[b]+=(m+cd[b])**2-m*m}
  }
  let sumFresh=0,sumOld=0,levels=[];
  for(let b=4;b<=Hmax+1;b++){ck(mass[b]===nKeep,"conservation");z.massChecks++;if(b===Hmax+1)break;
   let e=energy[b],v=energy[b+1],old=v+oldDelta[b+1],df=v-old,do_=old-e;
   ck(df>=0&&do_>=0,{R,b,e,v,old});if(spf[2*b+1])ck(df===0,"nonfresh");else z.freshLevels++;sumFresh+=df;sumOld+=do_;z.energyChecks++;
   if([8,16,32,64,128,256,512].includes(b))levels.push({b,energy:v/nKeep,ratio:v/nKeep/Math.log(b+1)**2,cumulativeFresh:sumFresh/nKeep,cumulativeOld:sumOld/nKeep,freshFraction:sumFresh/(sumFresh+sumOld)});
  }
  // Independent restricted replays for selected roots/heights.
  function oldCut(A,b){let a=A,n=3-A/2,h=3,limit=2*b-1;
   for(;;){let p=Infinity,w=Infinity;for(let e of [-1,1])for(let q of fs(a-e))if(q<=limit){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t}}
    if(h+w>=b+1)return a;a-=p-1;n+=w;h+=w-(p-1)/2;
   }
  }
  for(let [A,v] of selected)for(let b of v.bands){let expected=v.first.get(b);if(expected===undefined){for(let i=0;i<v.ar.length;i+=3)if(v.ar[i+1]<=b+1&&b+1<=v.ar[i+2]){expected=v.ar[i];break}}ck(oldCut(A,b)===expected,{R,A,b,expected});z.independentChecks++}
  ck(sumFresh+sumOld===energy[Hmax+1]-energy[4],"global ledger");
  z.rows.push({R,T,Hmax,Nroots,nKeep,initial:energy[4]/nKeep,final:energy[Hmax+1]/nKeep,meanFresh:sumFresh/nKeep,meanOld:sumOld/nKeep,freshFraction:sumFresh/(sumFresh+sumOld),levels});
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
