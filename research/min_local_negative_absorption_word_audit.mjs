// Restricted low-alphabet absorption and complete high-word CRT reconstruction.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2100000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v,P=null){let p=Infinity,w=Infinity,c=0;for(let [d,s] of [[a+1,0],[a-1,2]])for(let r of (P||fs(d))){if(P&&mod(d,r)!==0)continue;let t=mod((s===0?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;c=s}}return {p,w,c}}
 function twin(a){return !spf[a-1]&&!spf[a+1]}
 function wall(P){let Q=P.reduce((a,b)=>a*b,1),W=[];for(let x=0;x<Q;x++)if(P.every(p=>mod(-x,p)<=(p-3)/2))W.push(x);let M=1;for(let i=0;i<W.length;i++)M=Math.max(M,(W[i+1]??Q+W[0])-W[i]);return {Q,M}}
 function setup(P){let Q=2*P.filter(p=>p!==3).reduce((a,b)=>a*b,1),w=wall(P);return {P,Q,...{wall:w.M}}}
 function absorb(a,v,pdata){let A=a,V=v,events=0;while(true){let e=next(a,v,pdata.P);if(e.p===Infinity)break;a-=e.p-1;v+=e.w;events++;ck(A-a<=2*(pdata.wall-1),"wall");}return {a,v,events,g:A-a,t:v-V}}
 function decode(j0,word,data,L=Infinity){
  let A=6*j0,a=A,v=3-A/2,G=0,T=0,pins=new Map(),marks=[],steps=0,lowEvents=0;
  for(let j=0;j<=word.length;j++){
   let l=absorb(a,v,data);G+=l.g;T+=l.t;steps++;lowEvents+=l.events;a=l.a;v=l.v;
   if(G>L)return null;if(j===word.length)break;
   let [p,c]=word[j],r=mod(G+(c===0?-1:1),p);
   if(pins.has(p)&&pins.get(p)!==r)return null;pins.set(p,r);
   let x=mod(r*((p+1)/2),p);if(mod(x,2)!==mod(A/2,2))x+=p;
   let n=3-x+T,w=mod((c===0?0:p+2)-n,2*p)||2*p;
   marks.push({G,T,p,c,w,r});G+=p-1;T+=w;a-=p-1;v+=w;if(G>L)return null;
  }
  return {G,T,pins:[...pins],marks,steps,lowEvents,endpointResidue:mod(a,6*data.Q)}
 }
 let z={periodControls:0,periodRoots:0,periodTranslationChecks:0,periodMassChecks:0,periods:[],roots:0,events:0,successes:0,badSuccesses:0,classificationChecks:0,coveredRoots:0,coveredBadRoots:0,decodeChecks:0,markChecks:0,pinChecks:0,absorbingSourceChecks:0,lowGainChecks:0,repeatWordChecks:0,freeGapChecks:0,rows:[]};
 let PD=[[3],[3,5],[3,5,7],[3,5,7,11],[3,5,7,11,13]].map(setup);
 for(let data of PD){let {P,Q}=data,m=new Map(),maxG=0,maxT=0,events=0;
  for(let j=0;j<Q;j++){
   let a=6*j,v=3-a/2,e=absorb(a,v,data),shift=6*Q,e2=absorb(a+shift,v-shift/2,data);
   ck(e2.a===e.a+shift&&e2.v===e.v-shift/2&&e.events===e2.events,"period equivariance");z.periodTranslationChecks++;
   ck(P.every(p=>mod(e.a-1,p)!==0&&mod(e.a+1,p)!==0)&&e.a%6===0,"absorbing endpoint");
   let r=mod(e.a/6,Q);m.set(r,(m.get(r)||0)+1);maxG=Math.max(maxG,e.g);maxT=Math.max(maxT,e.t);events+=e.events;z.periodRoots++;
  }
  let rough=0;for(let j=0;j<Q;j++)if(P.every(p=>mod(6*j-1,p)!==0&&mod(6*j+1,p)!==0)){rough++;ck(m.has(j),"rough birth");}
  let count=[...m.values()].reduce((a,b)=>a+b,0),theory=2*P.filter(p=>p!==3).reduce((a,p)=>a*(p-2),1);
  ck(count===Q&&rough===theory&&rough===m.size,"period mass");z.periodMassChecks++;
  z.periodControls++;z.periods.push({P,Q,wall:data.wall,rough,mean:Q/rough,meanSq:[...m.values()].reduce((a,b)=>a+b*b,0)/rough,maxMass:Math.max(...m.values()),maxG,maxT,events})
 }
 for(let R of [3000,12000,48000,192000,480000,1000000]){
  const H=4*Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),L=Math.floor(H/4),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),row={R,H,L,roots:0,success:0,bad:0,classes:PD.map(data=>({P:data.P,covered:0,bad:0,byK:{},maxLowGap:0,maxHigh:0,fastAtRough:0,repeat:0}))};
  for(let A=lo;A<=hi;A+=6){let a=A,v=3-A/2,h=3,path=[];
   while(true){let e=next(a,v);if(h+e.w>H){row.success++;z.successes++;let bad=!twin(a);if(bad){row.bad++;z.badSuccesses++}
    for(let [idx,data] of PD.entries()){
     let c=row.classes[idx],word=[],marks=[],valid=true,loG=0,largestGap=0;
     for(let f of path){if(data.P.includes(f.p)){loG+=f.p-1;continue}
      let rough=data.P.every(p=>mod(f.a-1,p)!==0&&mod(f.a+1,p)!==0);
      if(f.w>=f.p/4&&f.p>8*Math.max(...data.P)){ck(rough,"slow beyond low cutoff");z.absorbingSourceChecks++}
      if(!rough){valid=false;break}
      word.push([f.p,f.c]);marks.push(f);largestGap=Math.max(largestGap,loG);loG=0;
     }
     z.classificationChecks++;if(!valid)continue;
     largestGap=Math.max(largestGap,loG);ck(largestGap<=2*(data.wall-1),"arbitrary gap wall");z.freeGapChecks++;
     let j0=mod(A/6,data.Q),d=decode(j0,word,data,L);ck(d&&d.G===A-a&&d.T===v-(3-A/2)&&d.endpointResidue===mod(a,6*data.Q),"exact word replay");z.decodeChecks++;
     for(let i=0;i<marks.length;i++){let f=marks[i],m=d.marks[i];ck(m.G===A-f.a&&m.T===f.v-(3-A/2)&&m.p===f.p&&m.c===f.c&&m.w===f.w,"mark timing");z.markChecks++;if(f.w<f.p/4)c.fastAtRough++}
     for(let [p,r] of d.pins){ck(mod(A,p)===r,"CRT pin");z.pinChecks++;}
     if(new Set(word.map(w=>w[0])).size<word.length){c.repeat++;z.repeatWordChecks++}
     c.covered++;if(bad)c.bad++;z.coveredRoots++;if(bad)z.coveredBadRoots++;c.maxLowGap=Math.max(c.maxLowGap,largestGap);c.maxHigh=Math.max(c.maxHigh,word.length);
     let k=c.byK[word.length]||[0,0];k[bad?1:0]++;c.byK[word.length]=k;
    }break}
    if(A-a+e.p-1>L)break;path.push({a,v,p:e.p,w:e.w,c:e.c});a-=e.p-1;v+=e.w;h+=e.w-(e.p-1)/2;z.events++;
   }row.roots++;z.roots++;
  }z.rows.push(row)
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
