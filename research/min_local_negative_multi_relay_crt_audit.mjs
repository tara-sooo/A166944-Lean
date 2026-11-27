// Multi-intermediate periodic relay reconstruction with repeated-prime CRT consistency.
// node research/min_local_negative_multi_relay_crt_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,e=0;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;e=s}}return {p,w,e}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const qmin=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 const specs=[{z:3,ps:[3],Q:6,Y:11,P:47,k:3},{z:5,ps:[3,5],Q:30,Y:23,P:97,k:3},{z:7,ps:[3,5,7],Q:210,Y:47,P:193,k:3},{z:5,ps:[3,5],Q:30,Y:47,P:193,k:3}];
 function low(a,n,c,limit){
  let x=a,t=n,j=0;
  for(;;){
   if(j===limit)break;
   let p=Infinity,w=Infinity;
   for(let r of c.ps)for(let e of [-1,1])if(mod(x-e,r)===0){
    let d=mod((e===-1?0:r+2)-t,2*r)||2*r;
    if(d<w||d===w&&r<p){p=r;w=d}
   }
   if(!Number.isFinite(p))break;
   let y=x-p+1;ck(Math.floor(x/c.Q)===Math.floor(y/c.Q),"restricted barrier");
   x=y;t+=w;j++;ck(a-x<c.Q&&j<=c.Q/2,"restricted termination");
  }
  return {g:a-x,t:t-n,j};
 }
 // Keep exact BigInt CRT residues. Small restricted clocks can use reduced
 // representatives; their offsets and elapsed times are invariant mod 2Q.
 function extend(res,m,b,q){
  let Q=BigInt(q),B=BigInt(b);
  if(m%Q===0n)return res%Q===B?{res,m,repeated:true}:null;
  let a=Number(m%Q),v=1;while((a*v)%q!==1)v++;
  let t=BigInt(mod((b-Number(res%Q))*v,q));
  return {res:res+m*t,m:m*Q,repeated:false};
 }
 function reconstruct(x,h,p,word,tail,c,actual){
  let res=BigInt(mod(x,2*c.Q)),m=BigInt(2*c.Q),gain=p-1,t=0,repeated=0,fast=0;
  function prefix(j){
   let x0=Number(res%BigInt(2*c.Q))-gain;
   let n0=h-(Number(res%BigInt(2*c.Q))-p+1)/2+t;
   let v=low(x0,n0,c,j);
   if(j!==Infinity)ck(v.j===j,"prefix exists");
   gain+=v.g;t+=v.t;return v;
  }
  for(let w of word){
   let v=prefix(w.j);
   // Source congruence of the next intermediate event.
   let b=mod(gain+w.e,w.p),ex=extend(res,m,b,w.p);ck(ex!==null,"CRT consistency");
   res=ex.res;m=ex.m;repeated+=+ex.repeated;
   ck(BigInt(x)%m===res,"actual CRT residue");
   // m divisible by 4*w.p; n=h-(x-p+1)/2+t.
   let x0=Number(res%BigInt(4*w.p));
   let n0=h-(x0-p+1)/2+t;
   let dt=mod((w.e===-1?0:w.p+2)-n0,2*w.p)||2*w.p;
   ck(x-gain===w.a&&dt===w.w&&t===w.n-actual.n,"middle offset clock");
   fast+=+(dt<=2*c.z);gain+=w.p-1;t+=dt;
  }
  let v=prefix(tail.j);
  ck(x-gain===tail.a&&t===tail.n-actual.n,"target prefix");
  if(tail.j===Infinity)ck(v.j===tail.count,"terminal count");
  let b=h+t-(gain-(p-1))/2; // postheight at target prestate clock
  let H=2*(b+tail.w)+(tail.e===-1?1:-5);
  ck(H>=tail.p-6&&H>0&&H%tail.p===0,"positive target factor");
  ck(gain-(p-1)<=word.length*c.Y+(word.length+1)*c.Q,"relay gain cap");
  return {res,m,gain,t,repeated,fast,H};
 }
 let rows=[];
 for(let R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let controls=specs.filter(c=>c.P<=T).map(c=>({...c,pairs:0,short:0,slow:0,fast:0,repeated:0,middleFast:0,words:0,roughChecks:0,sourceRough:0,targetRough:0,crtChecks:0,distinctHigh:0,long:0,weightedLong:0,weightedShort:0,bandCount:0,weightedFast:0,maxWord:0,smallGain:0,sample:null}));
  let events=0,checks=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,j=Math.floor((A-lo)/W),n0=3-(lo+j*W)/2,end=n0+T,trace=[];
   for(;;){let e=next(a,n),fire=n+e.w;if(fire>end)break;trace.push({a,n,fire,dt:Math.max(0,fire-Math.max(n,n0)),...e});a-=e.p-1;n=fire;events++}
   for(let c of controls){
    let high=trace.map((e,i)=>e.p>=c.Y?i:-1).filter(i=>i>=0),charge=0;
    let K=trace.filter(e=>e.p>c.z&&e.p<c.Y).length;c.bandCount+=K;
    for(let k=0;k+1<high.length;k++){
     let i=high[k],j=high[k+1],s=trace[i],r=trace[j];if(s.p<c.P)continue;
     let middle=trace.slice(i+1,j),word=[],cnt=0;
     for(let e of middle){if(e.p<=c.z)cnt++;else{word.push({...e,j:cnt});cnt=0}}
     c.pairs++;c.maxWord=Math.max(c.maxWord,word.length);
     if(word.length>c.k){c.long++;c.weightedLong+=s.dt/T;charge+=c.k+1;continue}
     c.short++;c.weightedShort+=s.dt/T;c.words+=word.length;
     let h=s.fire+(s.a-s.p+1)/2;
     let slow=r.w>2*c.z,tail={...r,j:slow?Infinity:cnt,count:cnt};
     let x=reconstruct(s.a,h,s.p,word,tail,c,{n:s.fire});
     ck(x.gain===s.a-r.a&&x.t===r.n-s.fire,"full reconstructed offsets");
     ck(x.m===BigInt(2*c.Q)*[...new Set(word.map(v=>v.p))].reduce((a,p)=>a*BigInt(p),1n),"exact distinct modulus");
     c.crtChecks++;checks++;c.repeated+=+(x.repeated>0);c.middleFast+=+(x.fast>0);
     if(slow)c.slow++;else{c.fast++;c.weightedFast+=s.dt/T;}
     let E=x.gain-(s.p-1);if(E+3<s.p){ck(s.p!==r.p,"distinct high labels");c.distinctHigh++}
     if(s.dt>=s.p**.8&&r.w>=r.p**.8&&slow){
      ck(qmin(s.a)>=s.p**.8/2&&qmin(r.a)>=r.p**.8/2,"both rough");
      for(let l of [5,7,11,13,17,19,23,29,31])if(l>c.z&&l<Math.min(s.p**.8/2,r.p**.8/2)){
       ck([s.a-1,s.a+1,r.a-1,r.a+1].every(v=>mod(v,l)!==0),"four forms");c.roughChecks++;
      }
     }
     if(c.sample===null&&word.length>=2&&x.repeated&&x.fast)c.sample={A,source:s.p,target:r.p,word:word.map(e=>[e.p,e.j,e.w]),E,modulus:x.m.toString(),H:x.H};
    }
    ck(charge<=K,"disjoint many-middle charge");checks++;
   }
  }
  for(let c of controls)ck(c.short+c.long===c.pairs&&c.slow+c.fast===c.short,"partition");
  rows.push({R,N,T,events,checks,controls:controls.map(c=>({...c,weightedLong:c.weightedLong/N,weightedShort:c.weightedShort/N,weightedFast:c.weightedFast/N,bandCount:c.bandCount/N}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000,480000]),null,2));
