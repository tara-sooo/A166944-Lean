// Actual old-prime first-use retention, earlier preemption and short plus-clock lower bound.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=400010,spf=new Uint32Array(N+1);
 for(let p=2;p*p<=N;p++)if(!spf[p])for(let a=p*p;a<=N;a+=p)if(!spf[a])spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function run(A,b,omit,target){let a=A,n=3-A/2,h=3,first=null,record=3;
  for(;;){ck(a>=2,"physical domain");let p=Infinity,w=Infinity,side=0;
   for(let e of [-1,1])for(let q of fs(a-e))if(q!==omit){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t;side=e}}
   let B=h+w;if(B>b)return {a,G:A-a,first};
   if(p===target&&!first)first={a,side,b:B,record:B>=record};record=Math.max(record,B);a-=p-1;n+=w;h=B-(p-1)/2;
  }
 }
 let z={rootControls:0,activated:0,retained:0,lost:0,shortPlusChecks:0,sourceChecks:0,repeatClockChecks:0,oldMomentChecks:0,counterexamples:[],rows:[]};
 for(let R of [48000,192000])for(let p of [11,23,47,97])for(let k of [1,3,5])for(let side of [-1,1]){
  let b=(k*p+(side===-1?-1:5))/2,lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),activated=new Map(),retained=new Map(),row={R,p,k,side,b,roots:0,activated:0,retained:0,lost:0,shortPlus:0,lostSmall:0,lostSameSource:0,oldE:0,newE:0};
  // Deterministic full root subsample on the larger slab.
  let step=R===48000?1:7;
  for(let A=lo;A<=hi;A+=6*step){let old=run(A,b,p,0),full=run(A,b,0,p),act=mod(old.a,p)===mod(side,p)&&mod(b-old.a/2,2)===(side===-1?0:1),ret=full.first&&full.first.b===b&&full.first.record;
   if(ret){ck(act&&old.a===full.first.a,"deletion source");retained.set(old.a,(retained.get(old.a)||0)+1);row.retained++;z.retained++;z.sourceChecks++}
   if(act){row.activated++;z.activated++;activated.set(old.a,(activated.get(old.a)||0)+1);
    if(side===1&&k<=3&&old.G<2*p-2){ck(ret,"short plus retention");row.shortPlus++;z.shortPlusChecks++}
    if(!ret){ck(full.first&&full.first.b<=b,"earlier p");row.lost++;z.lost++;if(old.G<2*p-2)row.lostSmall++;
     if(full.first.a===old.a){ck(full.first.side===side&&b-full.first.b>=2*p&&(b-full.first.b)%(2*p)===0,"stationary prior clock");row.lostSameSource++;z.repeatClockChecks++}
     if(z.counterexamples.length<12&&((side===1&&k<=3)||old.G<2*p-2))z.counterexamples.push({R,A,p,k,side,b,old,first:full.first})
    }
   }
   row.roots++;z.rootControls++;
  }
  for(let [a,m] of activated){let n=retained.get(a)||0;ck(n<=m,"pointwise");row.oldE+=m*m;row.newE+=n*n;z.oldMomentChecks++}
  ck(row.retained+row.lost===row.activated,"partition");z.rows.push(row);
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
