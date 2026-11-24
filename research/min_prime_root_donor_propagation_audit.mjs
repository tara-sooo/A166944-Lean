// Reproduce: node research/min_prime_root_donor_propagation_audit.mjs
function audit(X,mode="analytic"){
 const B=Math.ceil(Math.sqrt(7*X)), l=Math.max(1,Math.log(Math.log(B))),analytic=mode==="analytic",K=analytic?Math.max(2,Math.floor(Math.pow(Math.max(1,Math.log(l)),.25))):6,D=analytic?K:3,Q=mode==="wide"?7:Math.max(5,Math.ceil(B/Math.log(B))),H=analytic?Math.ceil(B/Math.sqrt(Math.log(B))):16,F=analytic?Math.ceil(l*l):4,k=analytic?Math.max(1,Math.floor(Math.sqrt(Math.log(B)))):1,A=analytic?Math.floor(B*B/(l*l)):0;
 const z=analytic?Math.ceil(Math.sqrt(B)):7,Kd=analytic?Math.max(2,Math.floor(Math.pow(l,.25))):6,Jd=analytic?Math.floor(Math.pow(l,.25)):2,J=analytic?Math.floor(Math.pow(Math.log(B),.25)):12;
 const topOverlap=(4*K+1)*(3+Math.ceil(Math.log2(B/Q))),compOverlap=(4*K+1)*(3+Math.ceil(Math.log2(K*D))),Gamma=K*topOverlap,Lambda=D*compOverlap;
 const tf=analytic?Math.floor(l/(8*Math.log(1+Gamma))):3,ts=analytic?Math.floor(Math.log(l)/(4*Math.log(1+Lambda))):3;
 const lim=7*X+5,spf=new Int32Array(lim+1),ps=[];
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)ps.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const factors=n=>{let a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;},ok=(b,msg)=>{if(!b)throw Error(msg);};
 const rc=new Int32Array(lim+1);function least(C){if(rc[C])return rc[C]-1;let r=0;for(let n of [C-1,C+1])for(let p of factors(n))if(!r||p<r)r=p;rc[C]=r+1;return r;}
 const W=new Map(),Wlate=new Map();let N=0,R=0,G=0,events=0,literal=0,nontwin=0,fastSeed=0,fastLong=0,localLong=0,fastAfter=0,slowSeed=0,slowAfter=0,fastClock=0,slowClock=0,remaining=0,medium=0,high=0,low=0,Zmid=0,shortCount=0,shortRemain=0,shortHighRemain=0,compRemain=0,maxTopOverlap=0,maxCompOverlap=0,maxDepth=0,light=0,dense=0,fastNew=Array(tf).fill(0),slowNew=Array(ts).fill(0),fastCounts=Array(tf).fill(0),slowCounts=Array(ts).fill(0),localLongNew=0;
 for(let M=X+1;M<2*X;M+=2)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,cut=Math.floor((7*M-1)/4);const a=[],last=new Map(),counts=new Map();
   while(true){let tt=Infinity,p=Infinity,sg=0;for(const sigma of [-1,1])for(const q of factors(C+sigma)){let n=t+1+mod((sigma===-1?0:q+2)-(t+1),2*q);if(n<tt||(n===tt&&q<p)){tt=n;p=q;sg=sigma;}}
     if(X<=1024){let lt=Infinity,lp=Infinity;for(let n=t+1;n<=cut;n++){let fs=factors(gcd(n%2?n-2:n,C+(n%2?1:-1)));if(fs.length){lt=n;lp=fs[0];break;}}ok((tt>cut&&lt===Infinity)||(tt===lt&&p===lp),"literal gcd");literal++;}
     if(tt>cut)break;const r=least(C),j=last.get(p)??-1,n=(counts.get(p)||0)+1;ok(r>0&&r<=p&&tt-t<=2*r,"clock");if(j>=0&&p>=5){const S=C-a[j].C;ok(S>=2*p-2&&mod(S+sg-a[j].sg,p)===0,"recharge");}
     last.set(p,a.length);counts.set(p,n);a.push({p,C,r,j,n,sg});R+=r;events++;t=tt;C+=p-1;ok(C<=2*t,"bound");
   }
   if(spf[C-1]!==C-1||spf[C+1]!==C+1)nontwin++;
   const gain=C-(2*M-2);G+=gain;const n=a.length,mark=new Uint8Array(n),long=new Uint8Array(n),local=new Uint8Array(n),short=[],topDeg=new Uint32Array(n),compDeg=new Uint32Array(n),compW=new Float64Array(n),spanSum=new Map();
   const weight=m=>a.reduce((s,e,i)=>s+(m[i]?e.p:0),0),clock=m=>a.reduce((s,e,i)=>s+(m[i]?e.r:0),0);
   for(let i=0;i<n;i++){const e=a[i];if(e.n<=k)mark[i]=1;if(e.j<0)continue;const S=e.C-a[e.j].C;spanSum.set(e.p,(spanSum.get(e.p)||0)+S);
     if(S>H*e.p){long[i]=1;mark[i]=1;fastLong+=e.p;}
     if(S>F*e.p*e.p){local[i]=1;localLong+=e.p;}
     if(e.p>=Q){let mx=0;for(let j=e.j+1;j<i;j++)mx=Math.max(mx,a[j].p-1);if(mx&&S-(e.p-1)-mx<=J){mark[i]=1;light++;}}
     if(e.p>=5&&S<=K*e.p){short.push(i);shortCount++;for(let j=e.j+1;j<i;j++){const q=a[j].p;ok(q<=K*e.p,"donor upper comparability");if(e.p>=Q)topDeg[j]++;if(e.p<=D*q){compDeg[j]++;compW[j]+=e.p;}}}
   }
   for(const s of spanSum.values())ok(s<=gain,"disjoint same-label spans");
   ok(weight(long)<=gain*ps.length/H+1e-7,"global long weight");
   ok(weight(local)<=gain*ps.reduce((s,p)=>s+1/p,0)/F+1e-7,"local long weight");
   const ids=[];for(let i=0;i<n;i++)if(a[i].p>=z)ids.push(i);
   for(let u=0;u<ids.length;u++){let mn=Infinity;const cnt=new Map();for(let v=u;v<ids.length&&v-u<=2*Kd;v++){const e=a[ids[v]];mn=Math.min(mn,e.p);if(v>u&&e.C-a[ids[v-1]].C-(a[ids[v-1]].p-1)>Jd)break;if(e.C-a[ids[u]].C>Kd*mn)break;cnt.set(e.p,(cnt.get(e.p)||0)+1);if(cnt.size>=2&&[...cnt.values()].every(x=>x>=2)){dense++;for(let j=ids[u];j<=ids[v];j++)mark[j]=1;}}}
   for(let j=0;j<n;j++){ok(topDeg[j]<=topOverlap&&compDeg[j]<=compOverlap&&compW[j]<=Lambda*a[j].p,"all-child overlap");maxTopOverlap=Math.max(maxTopOverlap,topDeg[j]);maxCompOverlap=Math.max(maxCompOverlap,compDeg[j]);}
   fastSeed+=weight(mark);
   let prevFastPrefix=null;for(let h=0;h<tf;h++){const old=weight(mark),prefix=[0],fresh=[];for(let i=0;i<n;i++)prefix.push(prefix[i]+(mark[i]?a[i].p-1:0));prevFastPrefix=prefix;for(const i of short){const e=a[i];if(!mark[i]&&e.p>=Q&&K*(prefix[i]-prefix[e.j+1])>=e.p)fresh.push(i);}
     let inc=0;for(const i of fresh){mark[i]=1;inc+=a[i].p;fastClock+=a[i].r;}ok(inc<=Gamma*old,"fast growth");fastNew[h]+=inc;fastCounts[h]+=fresh.length;
   }
   if(prevFastPrefix)for(const i of short)if(!mark[i]&&a[i].p>=Q)ok(K*(prevFastPrefix[i]-prevFastPrefix[a[i].j+1])<a[i].p,"fast residual marked donor gain");fastAfter+=weight(mark);
   for(let i=0;i<n;i++){const e=a[i];if(local[i]&&!mark[i])localLongNew+=e.p;if(local[i]||e.n<=k+Math.floor(A/(e.p*e.p)))mark[i]=1;}
   slowSeed+=weight(mark);
   const depth=new Int32Array(n);for(let i=0;i<n;i++)if(mark[i])depth[i]=1;
   for(let h=0;h<ts;h++){const old=weight(mark),fresh=[];for(const i of short){const e=a[i];if(mark[i])continue;for(let j=e.j+1;j<i;j++)if(mark[j]&&e.p<=D*a[j].p){fresh.push(i);break;}}
     let inc=0;for(let i of fresh){mark[i]=1;inc+=a[i].p;slowClock+=a[i].r;depth[i]=h+2;maxDepth=Math.max(maxDepth,h+1);}ok(inc<=Lambda*old,"comparable growth");slowNew[h]+=inc;slowCounts[h]+=fresh.length;
   }
   slowAfter+=weight(mark);const mc=new Map();for(let i=0;i<n;i++){const e=a[i];if(mark[i])continue;ok(e.n>k+Math.floor(A/(e.p*e.p)),"base residual");if(e.j>=0)ok(e.C-a[e.j].C<=Math.min(H*e.p,F*e.p*e.p),"long residual");remaining+=e.r;if(e.p===3)low+=e.r;else if(e.p<Q){medium+=e.r;mc.set(e.p,(mc.get(e.p)||0)+1);}else{high+=e.r;W.set(e.C,(W.get(e.C)||0)+1);if(e.C-(2*M-2)>B)Wlate.set(e.C,(Wlate.get(e.C)||0)+1);}}
   for(let v of mc.values())Zmid+=v*v;
   for(const i of short)if(!mark[i]){shortRemain++;if(a[i].p>=Q)shortHighRemain++;let found=false;for(let j=a[i].j+1;j<i;j++)if(a[i].p<=D*a[j].p){found=true;ok(!mark[j]||depth[j]===ts+1,"residual comparable predecessor only in last layer");}if(found)compRemain++;}
 }
 const energy=m=>[...m].reduce((s,[C,n])=>s+BigInt(least(C))*BigInt(n)**2n,0n).toString();
 ok(remaining===low+medium+high,"residual partition");
 return {mode,X,B,Q,K,D,H,F,N,R,G,events,literal,nontwin,tf,ts,fastSeed,fastLong,localLong,localLongNew,fastAfter,slowSeed,slowAfter,fastClock,slowClock,fastNew,fastCounts,slowNew,slowCounts,remaining,low,medium,high,Zmid,E:energy(W),Elate:energy(Wlate),shortCount,shortRemain,shortHighRemain,compRemain,maxTopOverlap,maxCompOverlap,maxDepth,light,dense};
}
const xs=process.argv.slice(2).map(Number),windows=xs.length?xs:[256,1024,4096,16384,65536,262144];for(const mode of ['analytic','fixed','wide'])for(const X of windows)console.log(JSON.stringify(audit(X,mode)));
