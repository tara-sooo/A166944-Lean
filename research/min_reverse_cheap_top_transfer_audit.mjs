// Source-preserving reverse high-to-high clock relation audit.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,L=210,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 const out=[];
 for(let T of [Math.max(2,Math.floor(B/4)),B]){
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),q0=new Int32Array(N),D0=new Int32Array(N),n0=new Int32Array(N),h0=new Int32Array(N),mass0=new Int32Array(N),lowTime=new Int32Array(N),lowGain=new Int32Array(N);
  function push(i,C){next[i]=head[C/2];head[C/2]=i}
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);push(i,2*M-2)}
  const modes=[[Math.ceil(B/2),2*B,31,Math.max(11,Math.ceil(Math.sqrt(B))),2],[Math.ceil(B/3),4*B,31,11,2],[Math.ceil(B/2),B,7,11,1],[Math.max(11,Math.ceil(B/Math.log(B)**(1/8))),Math.ceil(B*Math.log(B)**(1/8)),Math.ceil(Math.log(B)**(1/8)),Math.max(11,Math.ceil(Math.exp(Math.log(B)**.75))),Math.log(B)**(1/8)]].map(([Q,H,z,Y,W])=>({Q,H,z,Y,W,seen:new Uint8Array(N),seenNorm:new Uint8Array(N),tuples:new Map(),normTuples:new Map(),tags:0,incidences:0,stopped:0,stopHere:0,allTop:0,topLow:0,cheapTop:0,fromReset:0,toReset:0,nonreset:0,same:0,largeHeight:0,normTags:0,normInc:0,normStop:0,normSmallQ:0,normNoPrior:0,normUncovered:0,normReset:0,examples:[]}));
  let R=0,stopped=0,twin=0,bad=0,events=0,literal=0,relations=0;
  for(let C=2*X;C<7*X;C+=2){let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
   while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let u=K[i]+1,a=0;for(let k=t[i]+1;k<=K[i];k++){let v=gcd(k%2?k-2:k,C+(k%2?1:-1));if(v>1&&spf[v]<=B){u=k;a=spf[v];break}}ck(u===n&&p===a,"literal");literal++}
    if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
    else if(p<=7){ck(n-t[i]<=2*r);R+=r;events++;lowGain[i]+=p-1;lowTime[i]+=n-t[i];ck(lowGain[i]<L&&lowTime[i]<3*L,"low");t[i]=n;push(i,C+p-1)}
    else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j
   }
   for(let [p,a] of groups){let stop=a.length>=T;
    for(let [i,n] of a){let q=q0[i],D=D0[i],g=lowGain[i],h=2*n-(C+p-1),b=n%2?6:0,k=(h-b)/(2*p);ck(k>=0&&Number.isInteger(k),"current height");if(q){let b0=n0[i]%2?6:0,k0=(h0[i]-b0)/(2*q);ck(k0>=0&&Number.isInteger(k0));ck(C===D+q-1+g&&t[i]-n0[i]===lowTime[i]&&n-t[i]<=2*r&&mass0[i]<T);
      let e=2*k0*q-(2*k+1)*p;ck(e===b-b0-2*(n-n0[i])+g-1,"height relation");ck(Math.abs(e)<=7*L+4*r+7);
      let A=(2*k+1)*p+e;ck(A===2*k0*q&&A%q===0);relations++;
      if(q===p)ck(p<=L+3);
      for(let m of modes){
       if(q>=m.Q&&p>=m.Q){m.allTop++;if(Math.max(h0[i],h)>m.H)m.largeHeight++;else m.topLow++;if(r<=m.z)m.cheapTop++;if(r<=m.z&&Math.max(h0[i],h)<=m.H){m.incidences++;if(!m.seen[i]){m.seen[i]=1;m.tags++}if(stop)m.stopHere++;if(k0===0)m.fromReset++;if(k===0)m.toReset++;else m.nonreset++;if(q===p)m.same++;let key=D*B+q+":"+C+":"+p;if(!m.tuples.has(key))m.tuples.set(key,{count:0,cap:mass0[i]});let z=m.tuples.get(key);z.count++;ck(z.cap===mass0[i]&&z.count<=z.cap);if(m.examples.length<3)m.examples.push({q,p,D,C,g,h0:h0[i],h,k0,k,r,e,stop})}}
       if(p>=m.Q&&h<=m.H&&r<=m.z&&q>=m.Y){
        if(A>0&&q!==p&&mass0[i]<=q*m.W){m.normInc++;if(!m.seenNorm[i]){m.seenNorm[i]=1;m.normTags++}if(q<m.Q)m.normSmallQ++;let key=D*B+q+":"+C+":"+p;if(!m.normTuples.has(key))m.normTuples.set(key,{count:0,cap:mass0[i]});let z=m.normTuples.get(key);z.count++;ck(z.cap===mass0[i]&&z.count<=z.cap&&z.cap<=q*m.W)}
        else{m.normUncovered++;if(A===0)m.normReset++}
       }
      }
     }else{for(let m of modes)if(p>=m.Q&&h<=m.H&&r<=m.z)m.normNoPrior++}
     if(stop){for(let m of modes){if(m.seen[i])m.stopped++;if(m.seenNorm[i])m.normStop++}continue}
     R+=r;events++;q0[i]=p;D0[i]=C;n0[i]=n;h0[i]=h;mass0[i]=a.length;lowGain[i]=0;lowTime[i]=0;t[i]=n;push(i,C+p-1)
    }
    if(stop)stopped+=a.length
   }
  }
  ck(stopped+twin+bad===N);
  for(let m of modes){m.candidateTuples=m.tuples.size;m.capSum=Array.from(m.tuples.values()).reduce((s,v)=>s+v.cap,0);m.normCandidateTuples=m.normTuples.size;m.normCapSum=Array.from(m.normTuples.values()).reduce((s,v)=>s+v.cap,0);ck(m.incidences<=m.capSum&&m.tags<=m.incidences&&m.stopped<=stopped&&m.normInc<=m.normCapSum&&m.normTags<=m.normInc&&m.normStop<=stopped);delete m.tuples;delete m.normTuples;delete m.seen;delete m.seenNorm}
  out.push({T,R,stopped,twin,bad,events,literal,relations,modes})
 }
 return {X,B,N,runs:out}
}
for(const a of process.argv.slice(2)) console.log(JSON.stringify(audit(Number(a))));
