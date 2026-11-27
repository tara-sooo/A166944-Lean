// Reverse spatial coding and Kraft support certificates on actual selected rough frontiers.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=4000005,spf=new Int32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let x=p*p;x<=N;x+=p)if(!spf[x])spf[x]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let v=mod((s===-1?0:q+2)-n,2*q)||2*q;if(v<w||v===w&&q<p){p=q;w=v}}return {p,w}}
 const f=x=>x?x*Math.log(x):0;
 let z={roots:0,events:0,selected:0,reverseChecks:0,pinChecks:0,kraftChecks:0,entropyChecks:0,rows:[]};
 for(let R of [48000,192000,480000,2000000]){
  let K=Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))),T=4*K,J=Math.floor(T/5),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),nr=(hi-lo)/6+1,paths=[],endpoints=new Map(),badCount=0,logfact=[0];
  for(let i=1;i<=J+2;i++)logfact.push(logfact.at(-1)+Math.log(i));
  for(let a=2*Math.ceil((lo-2*T-6)/2);a<=hi;a+=2){let p=spf[a-1]||a-1,q=spf[a+1]||a+1;if(p>K&&q>K&&(p!==a-1||q!==a+1))badCount++}
  for(let A=lo;A<=hi;A+=6){let a=A,n=3-A/2,end=n+T,labels=[];
   for(;;){let e=next(a,n);if(n+e.w>end)break;labels.push(e.p);a-=e.p-1;n+=e.w;z.events++}
   z.roots++;if(A-a>J)continue;
   paths.push({A,a,labels});endpoints.set(a,(endpoints.get(a)||0)+1);z.selected++;
  }
  let ns=paths.length,L=[...endpoints.values()].reduce((s,m)=>s+f(m),0)/ns,rows=[];
  for(let Y of [...new Set([3,5,7,11,19,31,Math.floor(Math.sqrt(J)),Math.floor(J/4),Math.floor(J/2),J+1])].sort((a,b)=>a-b)){
   let counts=new Map(),comps=new Map(),groups=new Map(),pinfo=[],totalRank=0,ks=0,ls=0,zeroK=0,maxD=0;
   let minP=Y+1;while(minP<=J+1&&(minP%2===0||spf[minP]))minP++;
   for(let {A,a,labels} of paths){
    let gaps=[0],high=[];
    for(let i=labels.length-1;i>=0;i--){let p=labels[i];if(p<=Y)gaps[gaps.length-1]+=(p-1)/2;else {high.push(p);gaps.push(0)}}
    let k=high.length,l=gaps.reduce((s,v)=>s+v,0),x=a,used=0,rank=0,rankAll=0;
    for(let i=0;i<k;i++){
     x+=2*gaps[i];let p=high[i],qmax=J-2*l-used-(k-i-1)*(minP-1)+1;
     let ps=[...new Set([...fs(x),...fs(x-2)])].filter(q=>q>Y&&q<=qmax).sort((a,b)=>a-b);
     ck(ps.includes(p),"reverse factor pin");z.pinChecks++;maxD=Math.max(maxD,ps.length);rank+=Math.log(ps.length);used+=p-1;x+=p-1;
    }
    x+=2*gaps[k];ck(x===A,"reverse root");z.reverseChecks++;
    let key=gaps.join(","),kl=k+":"+l,cls=mod(a,210),gkey=cls+":"+key;
    counts.set(key,(counts.get(key)||0)+1);comps.set(kl,(comps.get(kl)||0)+1);
    let grp=groups.get(cls)||{n:0,c:new Map()};grp.n++;grp.c.set(key,(grp.c.get(key)||0)+1);groups.set(cls,grp);
    let lc=logfact[l+k]-logfact[l]-logfact[k];pinfo.push({a,key,kl,cls,rank,lc});totalRank+=rank;ks+=k;ls+=l;zeroK+=+(k===0);
   }
   let Evec=0,Ecomp=0,Egroup=0,Wvec=0,Wcomp=0,Wgroup=0,weights=new Map(),bestFixed={gain:0,n:0,bound:0}; 
   for(let {a,key,kl,cls,rank,lc} of pinfo){
    let p=counts.get(key)/ns,q=comps.get(kl)/ns,grp=groups.get(cls),s=grp.c.get(key)/grp.n;
    let e1=-Math.log(p)+rank,e2=-Math.log(q)+lc+rank,e3=-Math.log(s)+rank,w1=Math.exp(-e1),w2=Math.exp(-e2),w3=Math.exp(-e3);
    Evec+=e1;Ecomp+=e2;Egroup+=e3;Wvec+=w1;Wcomp+=w2;Wgroup+=w3;let v=weights.get(a)||[0,0,0];v[0]+=w1;v[1]+=w2;v[2]+=w3;weights.set(a,v);
   }
   for(let v of weights.values()){ck(v.every(x=>x<=1+1e-9),"Kraft per endpoint");z.kraftChecks++}
   ck([Evec,Ecomp,Egroup].every(x=>x/ns>=L-1e-8),"entropy");ck(Wvec<=endpoints.size+1e-7&&Wcomp<=endpoints.size+1e-7&&Wgroup<=endpoints.size+1e-7,"support");z.entropyChecks++;
   rows.push({Y,meanHigh:ks/ns,meanLowGain:2*ls/ns,zeroHigh:zeroK/ns,maxCandidates:maxD,rankCost:totalRank/ns,vecCost:Evec/ns,compCost:Ecomp/ns,groupCost:Egroup/ns,vecWeight:Wvec,compWeight:Wcomp,groupWeight:Wgroup,gapVectors:counts.size,klClasses:comps.size})
  }
  z.rows.push({R,K,T,J,nr,ns,L,distinct:endpoints.size,badCount,rows})
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
