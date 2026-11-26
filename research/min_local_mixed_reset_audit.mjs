// Mixed path reset-only gain certificate, with exact finite sufficient condition.
function mixedResetAudit(limit=1000000){
 const a=new Uint32Array(2*limit+3);
 for(let p=3;p*p<a.length;p+=2)if(!a[p])for(let n=p*p;n<a.length;n+=2*p)if(!a[n])a[n]=p;
 function fs(n){let out=[];while(n>1){let p=a[n]||n;out.push(p);while(n%p===0)n/=p}return out}
 const mod=(x,m)=>(x%m+m)%m;
 function require(ok,m){if(!ok)throw Error(m)}
 function event(u,v){let f=fs(u-1),g=fs(u+1),w=Infinity,p=Infinity;for(let [ar,s] of [[f,0],[g,1]])for(let q of ar){let k=mod((s?q+2:0)-v,2*q)||2*q;if(k<w||k===w&&q<p){w=k;p=q}}return {w,p,twin:f[0]===u-1&&g[0]===u+1}}
 let stats=[];
 for(let c of [4,8,12]){
   let s={c,roots:0,events:0,noTwin:0,twinStart:0,twinLater:0,qualified:0,qualifiedNonTwinStart:0,qualifiedTwinFree:0,mixedQualifiedNonTwinStart:0,finiteBoundChecks:0,repeatedResetChecks:0,maxResetGainFractionTwinFree:0,example:null,exampleMixed:null,minOtherFractionTwinFreeByK:{}};
   for(let X=12;X<=limit;X+=12){
    const D=Math.ceil(c*Math.sqrt(X));let u=X,v=X/2+3,resetG=0,otherG=0,k=0,first=-1,ps=new Map(),steps=[];
    while(u<X+D){
     if(u+1>=a.length)throw Error("domain");
     let {p,w,twin}=event(u,v);if(twin&&first<0)first=k;
     let reset=u%12===0&&2*v-u===6&&p%12===1&&2*w===p-1;
     if(reset){
       let prev=ps.get(p);if(prev!==undefined){require((u-prev)%(12*p)===0,"repeat");s.repeatedResetChecks++}
       ps.set(p,u);resetG+=p-1;
       if(!twin)require(p*p<=u+1,"non-twin cap");
     }else otherG+=p-1;
     steps.push({u,v,p,w,reset,twin});u+=p-1;v+=w;k++;
     require(2*v>=u&&v<=u+1,"envelope");
    }
    const K=ps.size,G=u-X;require(G===resetG+otherG,"gain");
    s.roots++;s.events+=k;
    if(first===0)s.twinStart++;else if(first>0)s.twinLater++;else{
      s.noTwin++;
      require(12*resetG<=K*D+12*K*Math.sqrt(X+D+1)+1e-7,"reset cap");
      s.finiteBoundChecks++;
      s.maxResetGainFractionTwinFree=Math.max(s.maxResetGainFractionTwinFree,resetG/G);
      let key=String(K),f=otherG/D;
      s.minOtherFractionTwinFreeByK[key]=Math.min(s.minOtherFractionTwinFreeByK[key]??Infinity,f);
    }
    // Exact sufficient condition: (12-K)D-12*otherG > 12*K*sqrt(X+D+1).
    const left=(12-K)*D-12*otherG,right2=144*K*K*(X+D+1);
    const qualified=K<=11&&left>0&&left*left>right2;
    if(qualified){
      s.qualified++;
      if(first<0){s.qualifiedTwinFree++;throw Error("conditional contradiction")}
      if(first>0){s.qualifiedNonTwinStart++;if(!s.example)s.example={X,D,K,resetG,otherG,first,steps};if(otherG>0){s.mixedQualifiedNonTwinStart++;if(!s.exampleMixed)s.exampleMixed={X,D,K,resetG,otherG,first,steps}}}
    }
   }
   stats.push(s);
 }
 return {limit,stats};
}
console.log(JSON.stringify(mixedResetAudit(Number(process.argv[2]||1000000)),null,2));
