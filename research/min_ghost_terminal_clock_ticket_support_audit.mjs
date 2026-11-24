// Restricted terminal support from clock tickets and subset sums.
function audit(Y,N=256){
 const V=8*Y,T=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(T**.8),ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const k=ps.findIndex(p=>p>=z),v=Math.floor(z/4),P=Math.max(5,Math.ceil(Math.sqrt(v))),ks=[0,1,2,3,4],mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x4c179d25^Y)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let l=4294967296-4294967296%p,x;do{x=u32()}while(x>=l);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 const rows=ks.map(K=>({K,actualDone:0,actualGainBeyondV:0,supportSum:0,maxSupport:0,capSum:0,candidates:0,weight:0,badWeight:0}));
 let fresh=0,repeat=0,finished=0,tests=0,maxA=0,meanA=0,maxFullSupport=0,meanFullSupport=0;
 function choose(n,j){if(j>n)return 0;let r=1;for(let i=1;i<=j;i++)r*= (n-i+1)/i;return r}
 for(let j=0;j<N;j++){
  let parity=uni(2);for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let a=uni(p);t[i]=a%2===parity?a:a+p}
  function next(e,g,limit){let w=Infinity,b=-1;for(let i=0;i<limit;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[b])){w=f;b=i}}return {w,b}}
  function low(e,g){let u=e,h=g,n=0,sg=0;for(;;){let a=next(u,h,k);if(a.b<0)return {done:true,d:h-g,n,sg};if(u+a.w-e>v)return {done:false,d:h-g,n,sg};u+=a.w;let p=ps[a.b];h+=p-1;if(p>=P)n++;else sg+=p-1}}
  function elig(i,g){let cc=mod(c[i]+g,ps[i]);return cc===1||cc===ps[i]-1}
  let e=0,g=0,seen=new Set();
  for(;;){let a=next(e,g,ps.length);if(a.b<0||e+a.w>T)break;let i=a.b,p=ps[i],oldg=g;e+=a.w;g+=p-1;
   if(i>=k){if(seen.has(i))repeat++;else{
    fresh++;let A=0,smallGain=0;
    for(let x=0;x<k;x++){let q=ps[x];for(let ph of [0,q+2]){let f=2*q-mod(t[x]+e-ph,2*q);if(f<=v){let n=1+Math.floor((v-f)/(2*q));if(q<P)smallGain+=n*(q-1);else A+=n}}}
    let smax=Math.min(v*(P-1),smallGain),l=low(e,g);ck(l.n<=A&&l.sg<=smax,"actual tickets");
    if(l.done){finished++;for(let x of rows)if(l.n<=x.K){x.actualDone++;x.actualGainBeyondV+=l.d>v}}
    if(tests<32){tests++;meanA+=A;maxA=Math.max(maxA,A);let all=new Set(),DD=ks.map(K=>({K,set:new Set(),n:0,wt:0,bad:0})),known=[...seen].filter(x=>x>=k);
     for(let x=k;x<ps.length;x++){if(seen.has(x))continue;let q=ps[x],l=low(e,oldg+q-1);ck(l.n<=A&&l.sg<=smax,"candidate tickets");if(!l.done)continue;all.add(l.d);let bad=known.some(i=>elig(i,oldg+q-1+l.d))||(l.d-1)%q===0||(l.d+1)%q===0||(l.d-3)%q===0;
      for(let d of DD)if(l.n<=d.K){d.set.add(l.d);d.n++;d.wt+=1/q**2;if(bad)d.bad+=1/q**2}
     }
     meanFullSupport+=all.size;maxFullSupport=Math.max(maxFullSupport,all.size);
     for(let d of DD){let cap=(Math.floor(smax/2)+1)*ks.filter(j=>j<=d.K).reduce((s,j)=>s+choose(A,j),0);ck(d.set.size<=cap,"support cap");let x=rows[d.K];x.supportSum+=d.set.size;x.maxSupport=Math.max(x.maxSupport,d.set.size);x.capSum+=Math.min(cap,Math.floor(v*(z-1)/2)+1);x.candidates+=d.n;x.weight+=d.wt;x.badWeight+=d.bad}
    }
   }}
   seen.add(i)
  }
 }
 return {Y,V,T,z,v,P,N,fresh,repeat,finished,tests,maxA,meanA:meanA/tests,maxFullSupport,meanFullSupport:meanFullSupport/tests,rows}
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
