// Event-driven coherent rough-endpoint local profile sampling and cutoff comparisons.
function audit(){
 const ck=(b,m)=>{if(!b)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const MAX=98304,Z=2*Math.floor(9*MAX/4+8)+7,spf=new Uint32Array(Z+1),pr=[];
 for(let p=2;p*p<=Z;p++)if(!spf[p])for(let x=p*p;x<=Z;x+=p)if(!spf[x])spf[x]=p;
 for(let p=3;p<=Z;p+=2)if(!spf[p])pr.push(p);
 const levels=[6,12,24,48,96,192,384,768,1536,3072,6144,12288,24576,49152,98304];
 let seed=0x124a79df;
 function u32(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0}
 function uniform(n){let bound=Math.floor(4294967296/n)*n,x;do{x=u32()}while(x>=bound);return x%n}
 let z={sampleEnvironments:0,smallTickCrossChecks:0,restrictedCutoffChecks:0,eventKeys:0,eventMemoHits:0,eventCalls:0,hitTimeChecks:0,nonmonotoneLosses:0,nonmonotoneGains:0,rows:[],comparisons:[]};
 function environment(maxL){
  let lim=2*Math.floor(9*maxL/4+8)+7,N=maxL/2+1,par=uniform(2),res=new Int32Array(lim+1),clock=new Int32Array(lim+1),heads=new Int32Array(N).fill(-1),edgeP=[],edgeC=[],edgeNext=[];
  function add(i,p,c){edgeNext.push(heads[i]);edgeP.push(p);edgeC.push(c);heads[i]=edgeP.length-1}
  for(let p of pr){if(p>lim)break;let n=uniform(p-2),r=n===0?0:n+1;res[p]=r;
   let x=mod(r*((p+1)/2),p);if(mod(x,2)!==par)x+=p;clock[p]=x;
   for(let e of [-1,1]){
    let i0=mod((e-r)*((p+1)/2),p);
    for(let i=i0;i<N;i+=p)add(i,p,e===-1?0:p+2);
   }
  }
  function simulate(cut){
   let memo=new Map(),ans=new Uint8Array(maxL/6+1),stepSize=3*maxL+50;
   ans[0]=1;
   for(let g=6;g<=maxL;g+=6){
    let i=g/2,n=3-i,stack=[],result=-1;
    while(i>0){
     z.eventCalls++;let p0=0,w0=Infinity;
     for(let e=heads[i];e>=0;e=edgeNext[e]){let p=edgeP[e];if(p>cut)continue;let w=mod(clock[p]+edgeC[e]-n,2*p)||2*p;
      if(w<w0||w===w0&&p<p0){p0=p;w0=w}}
     if(!p0||p0-1>2*i){result=-1;break}
     let time=n+w0,key=i*stepSize+time+maxL/2;
     ck(Number.isSafeInteger(key)&&time+maxL/2>=0&&time+maxL/2<stepSize,"key encoding");
     if(memo.has(key)){result=memo.get(key);z.eventMemoHits++;break}
     stack.push(key);i-=(p0-1)/2;n=time;
     if(i===0){result=n;break}
    }
    for(let k of stack){memo.set(k,result);z.eventKeys++}
    if(result>=0){ans[g/6]=1;ck(result-(3-g/2)<=Math.floor(9*g/4+8),"arrival potential");z.hitTimeChecks++}
   }
   return ans
  }
  function tickCheck(g,cut){
   let d=g,h=3;for(let t=0;t<Math.floor(9*g/4+8)&&d>0;t++){
    let b=h+1,np=mod(b-par-d/2,2),f=Math.abs(np?2*b-5:2*b+1),p=1;
    while(f>1){let q=spf[f]||f;if(q<=cut&&mod(res[q]+d+(np?-1:1),q)===0){p=q;break}while(f%q===0)f/=q}
    d-=p-1;h=b-(p-1)/2;
   }return d===0
  }
  return {lim,simulate,tickCheck};
 }
 function count(A,L){let n=0;for(let i=0;i<=L/6;i++)n+=A[i];return n}
 const config=[{maxL:6144,samples:256},{maxL:24576,samples:128},{maxL:98304,samples:48}];
 for(let {maxL,samples} of config){
  let stat=levels.filter(L=>L<=maxL).map(L=>({L,n:0,sum:0,sq:0,max:0,zeroExtra:0})),cuts=[Math.floor(Math.log(maxL)*2),Math.floor(Math.sqrt(maxL)),Math.floor(maxL/4),maxL+1],compare=cuts.map(cut=>({cut,total:0,short:0,both:0,lost:0,gained:0,all:0,shortBoth:0,theory:1}));
  for(let C of compare){for(let p of pr){if(p>C.cut)break;if(p>=5)C.theory/=1-2/p}}
  for(let s=0;s<samples;s++){
   let env=environment(maxL),full=env.simulate(env.lim);z.sampleEnvironments++;
   if(s<8)for(let g=0;g<=384;g+=6){ck(Boolean(full[g/6])===env.tickCheck(g,env.lim),"independent tick");z.smallTickCrossChecks++}
   let m=0,j=0;for(let g=0;g<=maxL;g+=6){m+=full[g/6];if(g===stat[j].L){let x=stat[j++];x.n++;x.sum+=m;x.sq+=m*m;x.max=Math.max(x.max,m);if(m===1)x.zeroExtra++;if(j===stat.length)break}}
   for(let C of compare){
    let r=env.simulate(C.cut),m=0,short=0,both=0,lost=0,gained=0,shortBoth=0;
    for(let i=0;i<r.length;i++){
     if(r[i]){m++;if(6*i<=C.cut/4){short++;if(full[i])shortBoth++}}
     if(r[i]&&full[i])both++;
     else if(r[i])lost++;
     else if(full[i])gained++;
    }
    ck(m===both+lost&&count(full,maxL)===both+gained,"paired mass");z.restrictedCutoffChecks++;
    if(s<4)for(let g=0;g<=384;g+=6){ck(Boolean(r[g/6])===env.tickCheck(g,C.cut),"restricted independent tick");z.smallTickCrossChecks++}
    C.total+=m;C.short+=short;C.both+=both;C.lost+=lost;C.gained+=gained;C.shortBoth+=shortBoth;C.all+=count(full,maxL);
    z.nonmonotoneLosses+=lost;z.nonmonotoneGains+=gained;
   }
  }
  z.rows.push({maxL,samples,stats:stat.map(x=>({...x,mean:x.sum/x.n,meanSq:x.sq/x.n,ratio:x.sum/x.n/Math.log(x.L)**2}))});
  z.comparisons.push({maxL,samples,stats:compare.map(x=>({...x,meanRestricted:x.total/samples,meanFull:x.all/samples,meanCommon:x.both/samples,meanLost:x.lost/samples,meanGained:x.gained/samples,meanShort:x.short/samples}))});
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
