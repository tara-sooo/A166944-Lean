// Independent same-clock-slot comparable anchor transfer audit.
function auditSlots(X, stress){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,u=Math.log(B),D=Math.max(1,Math.floor(stress?B/4:B/u**2)),rough=Math.max(3,Math.ceil(D/4)),L=stress?30:2,y=stress?5:2,ratio=stress?2:u**(1/16),cap=stress?12:u**(11/4);
 const assert=(x,m)=>{if(!x)throw Error(m)},sp=new Int32Array(8*X+100);
 for(let i=2;i<sp.length;i++)if(!sp[i])for(let j=i;j<sp.length;j+=i)if(!sp[j])sp[j]=i;
 function gcd(a,b){while(b){let c=a%b;a=b;b=c}return a}
 function r(C){let p=Math.min(sp[C-1]||Infinity,sp[C+1]||Infinity);return p<=B?p:0}
 function factors(n){let a=[];while(n>1){let p=sp[n];a.push(p);while(n%p===0)n/=p}return a}
 const anchors=new Map(),groups=[new Map(),new Map()],target=new Map();
 for(let M=X+1;M<2*X;M+=2){
   let s=M+2,t=s,C=2*M-2,b=null;
   assert(s+H+2*B<=Math.floor((7*M-1)/4),"cutoff");
   while(t<s+H){
     const rr=r(C);if(!rr)break;
     let lo=t,p=0;
     while(!p){t++;const k=t%2;p=sp[gcd(t-2*k,C+2*k-1)]||0;if(p>B)p=0}
     if(b&&rr>=rough&&rr>y&&b.q*ratio>=rr){
       assert(C-b.J<L&&lo-b.t<=3*(C-b.J),"low-tail");
       const key=`${C},${t}`;
       assert(!target.has(b.key)||target.get(b.key)===key,"unique target slot");target.set(b.key,key);
       for(let mode=0;mode<2;mode++){
         const w=(mode===0?(p>Math.ceil(B**.25)?Math.max(0,Math.min(t,s+H)-Math.max(lo,s+a)):0):(2*(t-lo)>p-1?t-lo:0))/(2*rr);
         if(!w)continue;
         if(!groups[mode].has(key))groups[mode].set(key,{C,v:t,rr,weights:new Map()});
         const ww=groups[mode].get(key).weights;ww.set(b.key,(ww.get(b.key)||0)+w);
       }
     }
     C+=p-1;
     if(p>y&&t<s+H){let key=`${C},${t},${p}`;if(!anchors.has(key))anchors.set(key,{key,J:C,t,q:p,n:0});b=anchors.get(key);b.n++}
   }
 }
 const out=[];
 for(let mode=0;mode<2;mode++){
   let E=0,same=0,cross=0,transport=0,actualTransport=0,rawGain=0,maxActual=0,maxEnvelope=0,nontrivial=0,slots=0;
   for(const [key,h] of groups[mode]){
     let {C,v,rr,weights}=h,ret=[...weights].filter(([a,w])=>anchors.get(a).n>cap);
     if(!ret.length)continue;
     const low=v-2*rr-3*L,hi=v-1;
     let K=0;
     for(let e=0;e<L;e+=2){
       const J=C-e;
       for(let side=0;side<2;side++)for(const q of factors(J+2*side)){
         if(q<=y||q>B||q*ratio<rr)continue;
         const residue=side?q+2:0;
         K+=Math.max(0,Math.floor((hi-residue)/(2*q))-Math.ceil((low-residue)/(2*q))+1);
       }
     }
     assert(ret.length<=K,"arithmetic slot anchor envelope");
     let W=0,S=0,G=0;
     for(const [a,w] of ret){
       let z=anchors.get(a);assert(z.t>=low&&z.t<=hi&&w<=z.n+1e-7,"anchor window and weight");W+=w;S+=rr*w*w;G+=z.q*z.n*z.n;
     }
     assert(rr*W*W<=K*ratio*G+1e-6&&rr*W*W<=ret.length*ratio*G+1e-6,"all comparable slot transfer");
     E+=rr*W*W;same+=S;cross+=rr*W*W-S;transport+=K*ratio*G;actualTransport+=ret.length*ratio*G;rawGain+=G;maxActual=Math.max(maxActual,ret.length);maxEnvelope=Math.max(maxEnvelope,K);nontrivial+=ret.length>1?1:0;slots++;
   }
   out.push({mode:mode?"full-positive":"late-high",E,same,cross,transport,actualTransport,rawGain,maxActual,maxEnvelope,nontrivial,slots});
 }
 return {X,stress,B,L,y,rough,ratio,cap,out};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[4096,16384,65536]))for(const stress of [false,true])console.log(JSON.stringify(auditSlots(X,stress)));
