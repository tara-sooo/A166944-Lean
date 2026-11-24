// Hybrid normalized cap with a sqrt(B) floor; exact audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const out=[];
 for(let W of [2,4,8]){
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),q0=new Int32Array(N),D0=new Int32Array(N),n0=new Int32Array(N),h0=new Int32Array(N),mass0=new Int32Array(N),gain=new Int32Array(N),time=new Int32Array(N);
  const put=(i,C)=>{next[i]=head[C/2];head[C/2]=i};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);put(i,2*M-2)}
  const floor=Math.ceil(Math.sqrt(B)),cap=p=>W*Math.max(floor,p);let s={W,floor,R:0,events:0,high:0,S:0,sinks:0,twin:0,bad:0,literal:0,relations:0,growth:0,equal:0,decline:0,initial:0,oneDonor:0,singleDonorTags:0,smallLabelStops:0,examples:[],modes:[[Math.ceil(B**.75),2,31,2],[Math.ceil(B**.75),4,7,1],[Math.ceil(B/3),2,31,2]].map(([Q,F,z,H])=>({Q,F,z,H,all:0,cheap:0,cheapLow:0,cheapHigh:0,small:0,smallCheapLow:0,comparableCheapLow:0,priorResetCheapLow:0,initialCheapLow:0,comparableCheapLowValid:0,comparableCheapLowBad:0,allComparableInc:0,allComparableValid:0,stopKeys:0,smallBound:0,maxSmallFrac:0,tuples:new Map()}))};
  for(let C=2*X;C<7*X;C+=2){let i=head[C/2];if(i<0)continue;const groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,a=0;for(let k=t[i]+1;k<=K[i];k++){let v=gcd(k%2?k-2:k,C+(k%2?1:-1));if(v>1&&spf[v]<=B){nn=k;a=spf[v];break}}ck(nn===n&&a===p,"literal");s.literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)s.twin++;else s.bad++}
    else if(p<=7){ck(n-t[i]<=2*r);s.R+=r;s.events++;gain[i]+=p-1;time[i]+=n-t[i];ck(gain[i]<L&&time[i]<3*L);t[i]=n;put(i,C+p-1)}
    else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j
   }
   for(let [p,a] of groups){let m=a.length,stop=m>=cap(p),parents=new Map();
    for(let [i,n] of a){let q=q0[i],D=D0[i],g=gain[i],h=2*n-(C+p-1),b=n%2?6:0,k=(h-b)/(2*p),e=0,A=0;ck(k>=0&&Number.isInteger(k));
     if(q){let b0=n0[i]%2?6:0,k0=(h0[i]-b0)/(2*q);e=b-b0-2*(n-n0[i])+g-1;A=(2*k+1)*p+e;ck(A===2*k0*q&&k0>=0&&Number.isInteger(k0)&&Math.abs(e)<=7*L+4*r+7);ck(C===D+q-1+g&&time[i]===t[i]-n0[i]&&mass0[i]<cap(q));s.relations++;let key=D*B+q;if(!parents.has(key))parents.set(key,{q,D,g,m:mass0[i],count:0});let par=parents.get(key);par.count++;ck(par.count<=par.m);
      if(stop){if(m>mass0[i])s.growth++;else{if(m===mass0[i])s.equal++;else s.decline++;ck(q>p,"normalized threshold without mass increase");}}
     }else if(stop)s.initial++;
     for(let v of s.modes)if(p>=v.Q){
       let cheap=r<=v.z,low=h<=p*v.H,small=q>0&&q<p/v.F,comp=q>0&&!small,valid=comp&&q!==p&&A>0;
       if(comp&&cheap&&low){v.allComparableInc++;if(valid){v.allComparableValid++;let key=D*B+q+":"+C+":"+p;if(!v.tuples.has(key))v.tuples.set(key,{count:0,cap:mass0[i]});let z=v.tuples.get(key);z.count++;ck(z.count<=z.cap&&z.cap<cap(q))}}
       if(stop){v.all++;if(cheap){v.cheap++;if(low){v.cheapLow++;if(small)v.smallCheapLow++;else if(comp){v.comparableCheapLow++;if(valid)v.comparableCheapLowValid++;else v.comparableCheapLowBad++;if(A===0)v.priorResetCheapLow++}else v.initialCheapLow++}else v.cheapHigh++}if(small)v.small++}
     }
     if(!stop){s.R+=r;s.events++;s.high++;q0[i]=p;D0[i]=C;n0[i]=n;h0[i]=h;mass0[i]=m;gain[i]=0;time[i]=0;t[i]=n;put(i,C+p-1)}
    }
    if(stop){s.S+=m;s.sinks++;if(p<Math.sqrt(B))s.smallLabelStops+=m;if(parents.size===1&&a.every(([i])=>q0[i])){s.oneDonor++;s.singleDonorTags+=m;let v=[...parents.values()][0];ck(v.q>p);if(s.examples.length<3)s.examples.push({p,C,m,q:v.q,D:v.D,previous:v.m})}
     for(let v of s.modes)if(p>=v.Q){v.stopKeys++;let a0=0,bound=0;for(let par of parents.values())if(par.q<p/v.F){a0+=par.count;bound+=cap(par.q);ck((C-par.g)%par.q===0||(C-par.g+2)%par.q===0)}ck(a0<=bound);v.smallBound+=bound;v.maxSmallFrac=Math.max(v.maxSmallFrac,a0/m)}
    }
   }
  }
  ck(s.S+s.twin+s.bad===N&&s.growth+s.equal+s.decline+s.initial===s.S);
  for(let v of s.modes){ck(v.cheap===v.cheapLow+v.cheapHigh&&v.cheapLow===v.smallCheapLow+v.comparableCheapLow+v.initialCheapLow&&v.comparableCheapLow===v.comparableCheapLowValid+v.comparableCheapLowBad&&v.small<=v.smallBound);v.distinctTuples=v.tuples.size;v.tupleCap=Array.from(v.tuples.values()).reduce((a,b)=>a+b.cap,0);ck(v.allComparableValid<=v.tupleCap);delete v.tuples}
  out.push(s)
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
