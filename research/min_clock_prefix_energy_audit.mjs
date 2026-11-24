// Relative-clock occupation with fractional waits, canonical MIN wheel.
// Run: node research/min_clock_prefix_energy_audit.mjs 256 1024 4096 16384 65536 262144
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)), N=X/2, minK=Math.floor((7*(X+1)-1)/4)-(X+3);
 const spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
   spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 const check=(x,m)=>{if(!x)throw Error(m)};
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
 const len=7*X/2+1;
 const r=new Int32Array(len);
 let S0=0;
 for(let C=2*X;C<7*X;C+=2){let q=Math.min(spf[C-1],spf[C+1]);if(q<=B){r[C/2]=q;S0+=q}}
 const hs=[...new Set([Math.min(B,minK),Math.min(2*B,minK),Math.min(4*B,minK),Math.min(8*B,minK),Math.min(Math.floor(B*Math.log(B)),minK)])].sort((a,b)=>a-b);
 const configs=hs.flatMap(H=>[{a:0,H},{a:Math.floor(H/2),H}]).map(({a,H})=>{
   const d=Math.max(1,Math.floor(H*Math.log(B)/B));
   return {a,H,h:H-a,d,W:new Float64Array(len),win:new Float64Array(len),near:0,total:0,live:0,finished:0,largestGain:0};
 });
 let events=0, literal=0, noTwin=0;
 function hit(t,C,K){
   let T=K+1,P=0;
   for(const s of [-1,1]){
     let v=C+s;while(v>1){const p=spf[v];if(p>B)break;
       const m=2*p,res=s===-1?0:p+2,u=t+1+((res-(t+1)%m+m)%m);
       if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
       while(v%p===0)v/=p;
     }
   }return [T,P];
 }
 function traverse(M,cb,verify=false){
   const s=M+2,K=Math.floor((7*M-1)/4),C0=2*M-2;
   let t=s,C=C0;
   for(;;){
     const [u,p]=hit(t,C,K);
     if(verify&&X<=1024){let a=K+1,b=0;for(let j=t+1;j<=K;j++){
       const g=gcd(j%2?j-2:j,j%2?C+1:C-1);
       if(g>1&&spf[g]<=B){a=j;b=spf[g];break}
     }check(a===u&&b===p,'literal MIN');literal++;}
     const q=r[C/2];
     check(C<=2*t&&C>=C0,'horizon invariant');
     if(!q){check(!p&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin at r=0');return {elapsed:t-s,twin:true};}
     const end=p?u:K;
     check(end-t<=2*q,'wait including clipped terminal tail');
     cb(C,t-s,end-s,C0);
     if(!p)return {elapsed:K-s,twin:false};
     if(verify)events++;
     t=u;C+=p-1;
   }
 }
 for(let M=X+1;M<2*X;M+=2){
   for(const c of configs){
     const gap=2*Math.floor(c.d/2), old=M-gap-2;
     if(old>=X+1)traverse(old,(C,l,u)=>{
       const w=Math.max(0,Math.min(u,c.H)-Math.max(l,c.a))/(2*r[C/2]);
       if(w)c.win[C/2]-=w;
     });
   }
   const totals=configs.map(()=>0);
   const result=traverse(M,(C,l,u,C0)=>{
     for(let j=0;j<configs.length;j++){
       const c=configs[j],duration=Math.max(0,Math.min(u,c.H)-Math.max(l,c.a));
       if(!duration)continue;
       const i=C/2,q=r[i],w=duration/(2*q);
       check(w<=1+1e-12&&C-C0<=2*c.H+6,'fractional/support bound');
       c.W[i]+=w;c.near+=q*(w*w+2*w*c.win[i]);c.win[i]+=w;
       c.total+=duration;totals[j]+=duration;
       c.largestGain=Math.max(c.largestGain,C-C0);
     }
   },true);
   if(!result.twin)noTwin++;
   for(let j=0;j<configs.length;j++){
     const c=configs[j],expected=Math.max(0,Math.min(result.elapsed,c.H)-c.a);
     check(totals[j]===expected,'exact slab live time');
     if(result.elapsed>=c.H)c.live++;else c.finished++;
   }
 }
 const results=[];
 for(const c of configs){
   let R=0,E=0,maxW=0;
   for(let C=2*X;C<7*X;C+=2){const i=C/2;R+=r[i]*c.W[i];E+=r[i]*c.W[i]**2;maxW=Math.max(maxW,c.W[i]);}
   check(Math.abs(2*R-c.total)<=1e-7*Math.max(1,c.total),'linear clock identity');
   check(R<=N*c.h/2+1e-7*Math.max(1,R),'linear cap');
   check(c.near<=(2*Math.floor(c.d/2)+1)*R+1e-7*Math.max(1,c.near),'near pair bound');
   check(E<=(2*Math.floor((c.H+3)/2)+1)*R+1e-7*Math.max(1,E),'support pair bound');
   check(R*R<=S0*E+1e-7*Math.max(1,S0*E),'Cauchy');
   const ratio=4*S0*E/(N*c.h)**2,far=Math.max(0,E-c.near);
   if(ratio<1-1e-9)check(c.finished>0,'finite twin certificate');
   results.push({a:c.a,H:c.H,h:c.h,d:c.d,R,E,near:c.near,far,ratio,maxW,live:c.live,finished:c.finished,largestGain:c.largestGain,midScale:far/(X*c.H*c.h*Math.log(B)**2/B)});
 }
 return {X,B,N,S0,events,literal,noTwin,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[256,1024,4096,16384,65536,262144])console.log(JSON.stringify(audit(X)));
