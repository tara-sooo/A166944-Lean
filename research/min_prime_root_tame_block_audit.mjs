// Reproduce: node research/min_prime_root_tame_block_audit.mjs
function audit(X,mode="analytic"){
 const B=Math.ceil(Math.sqrt(7*X)), l=Math.max(1,Math.log(Math.log(B))),analytic=mode==="analytic",K=analytic?Math.max(2,Math.floor(Math.pow(Math.max(1,Math.log(l)),.25))):6,D=analytic?K:3,Q=(mode==="wide"||mode==="narrow")?7:Math.max(5,Math.ceil(B/Math.log(B))),H=analytic?Math.ceil(B/Math.sqrt(Math.log(B))):16,F=analytic?Math.ceil(l*l):4,k=analytic?Math.max(1,Math.floor(Math.sqrt(Math.log(B)))):1,A=analytic?Math.floor(B*B/(l*l)):0;
 const z=analytic?Math.ceil(Math.sqrt(B)):7,Kd=analytic?Math.max(2,Math.floor(Math.pow(l,.25))):6,Jd=analytic?Math.floor(Math.pow(l,.25)):2,J=analytic?Math.floor(Math.pow(Math.log(B),.25)):12;
 const topOverlap=(4*K+1)*(3+Math.ceil(Math.log2(B/Q))),compOverlap=(4*K+1)*(3+Math.ceil(Math.log2(K*D))),Gamma=K*topOverlap,Lambda=D*compOverlap;
 const tf=analytic?Math.floor(l/(8*Math.log(1+Gamma))):3,ts=analytic?Math.floor(Math.log(l)/(4*Math.log(1+Lambda))):3;
 const m=Math.ceil(2*K*D)+2, Wblock=Math.min(Number.MAX_SAFE_INTEGER,2**Math.min(52,2*m)), innerRad=analytic?Math.max(1,Math.floor(l**(1/8))):1, outerRad=analytic?Math.max(innerRad,Math.floor(l**(1/4))):mode==="narrow"?1:4, labelRad=analytic?Math.max(1,Math.floor(l**(1/8))):2;
 const wideGate=Wblock*(D+1)<=Kd && outerRad>=innerRad*(1+4*Wblock*(D+1)) && z>Jd+1 && Q>=z;
 const lim=7*X+5,spf=new Int32Array(lim+1),ps=[];
 for(let n=2;n<=lim;n++)if(!spf[n]){spf[n]=n;if(n<=B&&n%2)ps.push(n);if(n*n<=lim)for(let j=n*n;j<=lim;j+=n)if(!spf[j])spf[j]=n;}
 const factors=n=>{let a=[];while(n>1){const p=spf[n];if(p<=B&&p%2)a.push(p);while(n%p===0)n/=p;}return a;};
 const mod=(a,m)=>((a%m)+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c;}return a;},ok=(b,msg)=>{if(!b)throw Error(msg);};
 const rc=new Int32Array(lim+1);function least(C){if(rc[C])return rc[C]-1;let r=0;for(let n of [C-1,C+1])for(let p of factors(n))if(!r||p<r)r=p;rc[C]=r+1;return r;}
 const W=new Map(),Wlate=new Map();let oldWeight=0,innerWeight=0,outerWeight=0,labelWeight=0,labelNewCount=0,labelNewClock=0,labelNewHighClock=0,seedLabelExtra=0,labelResidualCount=0,labelResidualHigh=0,cleanPriorChecks=0,cleanFutureChecks=0,finalEnergy=new Map(),haloNewCount=0,haloNewClock=0,haloNewHighClock=0,blockCount=0,windowCount=0,forcedDense=0,actualDense=0,geometryChecks=0,gateChecks=0,fullResidualBlocks=0,fullResidualHigh=0,tailHigh=0,defectWeight=0,blockCharge=0,maxWindow=0,haloEnergy=new Map();let N=0,R=0,G=0,events=0,literal=0,nontwin=0,fastSeed=0,fastLong=0,localLong=0,fastAfter=0,slowSeed=0,slowAfter=0,fastClock=0,slowClock=0,remaining=0,medium=0,high=0,low=0,Zmid=0,shortCount=0,shortRemain=0,shortHighRemain=0,compRemain=0,maxTopOverlap=0,maxCompOverlap=0,maxDepth=0,light=0,dense=0,fastNew=Array(tf).fill(0),slowNew=Array(ts).fill(0),fastCounts=Array(tf).fill(0),slowCounts=Array(ts).fill(0),localLongNew=0;
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
   slowAfter+=weight(mark);
   const seed=mark.slice(), inner=mark.slice(), outer=mark.slice(), witness=new Int32Array(n).fill(-1);
   for(let i=0;i<n;i++)if(seed[i]){
     const e=a[i],lo=e.C-outerRad*e.p,hi=e.C+outerRad*e.p;
     for(let j=0;j<n;j++){const f=a[j];if(f.C<lo||f.C+f.p-1>hi)continue;outer[j]=1;if(f.C>=e.C-innerRad*e.p&&f.C+f.p-1<=e.C+innerRad*e.p){inner[j]=1;witness[j]=i;}}
   }
   const v0=weight(seed),v1=weight(inner),v2=weight(outer);
   ok(v1<=3*innerRad*v0&&v2<=3*outerRad*v0,"halo weight");oldWeight+=v0;innerWeight+=v1;outerWeight+=v2;
   for(let i=0;i<n;i++){ok(!inner[i]||outer[i],"nested halos");if(outer[i]&&!seed[i]){haloNewCount++;haloNewClock+=a[i].r;if(a[i].p>=Q)haloNewHighClock+=a[i].r;}if(!outer[i]&&a[i].p>=Q)haloEnergy.set(a[i].C,(haloEnergy.get(a[i].C)||0)+1);}
   const byLabel=new Map();for(let i=0;i<n;i++){const p=a[i].p;if(!byLabel.has(p))byLabel.set(p,[]);byLabel.get(p).push(i);}
   function dilate(s){const d=s.slice();for(const is of byLabel.values())for(let j=0;j<is.length;j++)if(s[is[j]])for(let h=Math.max(0,j-labelRad);h<=Math.min(is.length-1,j+labelRad);h++)d[is[h]]=1;return d;}
   const seedD=dilate(seed), final=dilate(outer);const v3=weight(final);
   ok(v3<=(2*labelRad+1)*v2&&weight(seedD)<=(2*labelRad+1)*v0,"same-label dilation weight");labelWeight+=v3;seedLabelExtra+=weight(seedD)-v0;
   for(const is of byLabel.values())for(let j=0;j<is.length;j++){const i=is[j];if(final[i]){if(!outer[i]){labelNewCount++;labelNewClock+=a[i].r;if(a[i].p>=Q)labelNewHighClock+=a[i].r;}continue;}
     labelResidualCount++;if(a[i].p>=Q){labelResidualHigh+=a[i].r;finalEnergy.set(a[i].C,(finalEnergy.get(a[i].C)||0)+1);}
     ok(j>labelRad,"residual first-label distance");for(let h=1;h<=labelRad;h++){ok(!outer[is[j-h]],"clean prior label hit");cleanPriorChecks++;}
     for(let h=1;h<=Math.min(labelRad,is.length-j-1);h++){ok(!outer[is[j+h]],"clean future label hit");cleanFutureChecks++;}
   }
   const hids=a.map((e,i)=>e.p>=Math.max(Q,z)?i:-1).filter(i=>i>=0);
   const denseFind=(arr)=>{if(!arr.length)return null;const freq=new Map();for(const p of arr)freq.set(p,(freq.get(p)||0)+1);const j=arr.findIndex(p=>freq.get(p)===1);if(j<0)return arr;return denseFind(arr.slice(0,j))||denseFind(arr.slice(j+1));};
   // All tame subwindows up to eight in finite diagnostics; the full asymptotic W is tested only if it fits.
   function checkBlock(is,full){
     const arr=is.map(i=>a[i].p),U=Math.min(...arr),hi=Math.max(...arr),left=a[is[0]].C,right=a[is[is.length-1]].C+a[is[is.length-1]].p-1,span=right-left;
     const kinds=new Set(arr).size, defects=is.slice(m).filter(i=>a[i].j<0||a[i].C-a[a[i].j].C>K*a[i].p);
     ok(hi<=D*U&&span<=is.length*(D*U+Jd),"tame width");ok(kinds<=m+defects.length,"alphabet bound");
     const core=denseFind(arr);if(core){actualDense++;ok([...new Set(core)].every(p=>core.filter(q=>p===q).length>=2),"dense core oracle");}
     if(is.length>=2**kinds){forcedDense++;ok(core!==null,"forced dense core");}
     let allOuter=is.every(i=>outer[i]);
     for(const i of is)if(inner[i]){const h=witness[i];ok(h>=0,"inner witness");const e=a[h];if(left>=e.C-outerRad*e.p&&right<=e.C+outerRad*e.p){geometryChecks++;ok(allOuter,"halo covers block");for(let j=is[0];j<=is[is.length-1];j++)ok(outer[j],"halo covers intervening events");}}
     if(full&&wideGate){gateChecks++;if(!allOuter){ok(is.every(i=>!inner[i]),"outer residual forces all inner unmarked");ok(defects.length>m,"forced intermediate defect count");for(const i of defects)ok(!seed[i]&&a[i].j>=0&&a[i].C-a[a[i].j].C<=Math.min(H*a[i].p,F*a[i].p*a[i].p),"intermediate only");}}
     if(full){blockCount++;if(!allOuter){fullResidualBlocks++;const v=is.filter(i=>!outer[i]).reduce((s,i)=>s+a[i].p,0),d=defects.reduce((s,i)=>s+a[i].p,0);fullResidualHigh+=v;defectWeight+=d;if(wideGate){ok((m+1)*v<=is.length*D*d,"block defect charge");blockCharge+=v;}}}
     windowCount++;maxWindow=Math.max(maxWindow,is.length);
   }
   for(let u=0;u<hids.length;u++){let mn=Infinity,mx=0;for(let v=u;v<hids.length&&v-u<8;v++){const e=a[hids[v]];if(v>u&&e.C-a[hids[v-1]].C-(a[hids[v-1]].p-1)>Jd)break;mn=Math.min(mn,e.p);mx=Math.max(mx,e.p);if(mx>D*mn)break;checkBlock(hids.slice(u,v+1),false);}}
   // Greedy disjoint tame runs and W-blocks, remainder is a boundary tail.
   let start=0;while(start<hids.length){let end=start+1,mn=a[hids[start]].p,mx=mn;while(end<hids.length){const e=a[hids[end]],lo=Math.min(mn,e.p),hi=Math.max(mx,e.p);if(hi>D*lo||e.C-a[hids[end-1]].C-(a[hids[end-1]].p-1)>Jd)break;mn=lo;mx=hi;end++;}
     let u=start;for(;u+Wblock<=end;u+=Wblock)checkBlock(hids.slice(u,u+Wblock),true);
     for(let v=u;v<end;v++)if(!outer[hids[v]])tailHigh+=a[hids[v]].p;
     start=end;
   }
   const mc=new Map();for(let i=0;i<n;i++){const e=a[i];if(mark[i])continue;ok(e.n>k+Math.floor(A/(e.p*e.p)),"base residual");if(e.j>=0)ok(e.C-a[e.j].C<=Math.min(H*e.p,F*e.p*e.p),"long residual");remaining+=e.r;if(e.p===3)low+=e.r;else if(e.p<Q){medium+=e.r;mc.set(e.p,(mc.get(e.p)||0)+1);}else{high+=e.r;W.set(e.C,(W.get(e.C)||0)+1);if(e.C-(2*M-2)>B)Wlate.set(e.C,(Wlate.get(e.C)||0)+1);}}
   for(let v of mc.values())Zmid+=v*v;
   for(const i of short)if(!mark[i]){shortRemain++;if(a[i].p>=Q)shortHighRemain++;let found=false;for(let j=a[i].j+1;j<i;j++)if(a[i].p<=D*a[j].p){found=true;ok(!mark[j]||depth[j]===ts+1,"residual comparable predecessor only in last layer");}if(found)compRemain++;}
 }
 const energy=m=>[...m].reduce((s,[C,n])=>s+BigInt(least(C))*BigInt(n)**2n,0n).toString();
 ok(remaining===low+medium+high,"residual partition");
 return {mode,X,B,Q,K,D,H,F,N,R,G,events,m,Wblock,innerRad,outerRad,wideGate,oldWeight,innerWeight,outerWeight,labelWeight,labelNewCount,labelNewClock,labelNewHighClock,seedLabelExtra,labelResidualCount,labelResidualHigh,cleanPriorChecks,cleanFutureChecks,finalE:energy(finalEnergy),haloNewCount,haloNewClock,haloNewHighClock,haloE:energy(haloEnergy),windowCount,blockCount,forcedDense,actualDense,geometryChecks,gateChecks,fullResidualBlocks,fullResidualHigh,tailHigh,defectWeight,blockCharge,maxWindow,literal,nontwin,tf,ts,fastSeed,fastLong,localLong,localLongNew,fastAfter,slowSeed,slowAfter,fastClock,slowClock,fastNew,fastCounts,slowNew,slowCounts,remaining,low,medium,high,Zmid,E:energy(W),Elate:energy(Wlate),shortCount,shortRemain,shortHighRemain,compRemain,maxTopOverlap,maxCompOverlap,maxDepth,light,dense};
}
const xs=process.argv.slice(2).map(Number),windows=xs.length?xs:[256,1024,4096,16384,65536,262144];for(const mode of ['analytic','fixed','wide','narrow'])for(const X of windows)console.log(JSON.stringify(audit(X,mode)));

function combinatorialOracle(){
 const ok=(b,msg)=>{if(!b)throw Error(msg);};
 function denseFind(w){if(!w.length)return false;const j=w.findIndex(p=>w.filter(q=>q===p).length===1);return j<0||denseFind(w.slice(0,j))||denseFind(w.slice(j+1));}
 function brute(w){for(let i=0;i<w.length;i++){const c=new Map();for(let j=i;j<w.length;j++){c.set(w[j],(c.get(w[j])||0)+1);if([...c.values()].every(n=>n>=2))return true;}}return false;}
 let words=0,forced=0,lagChecks=0,extremal=0;
 for(let h=1;h<=3;h++)for(let n=1;n<=2**h;n++)for(let t=0;t<h**n;t++){let x=t,w=[];for(let j=0;j<n;j++){w.push(x%h);x=Math.floor(x/h);}const d=denseFind(w),b=brute(w),s=new Set(w).size;words++;ok(d===b,"dense singleton recursion vs brute");if(n>=2**s){forced++;ok(d,"dense threshold");}for(let m=1;m<=3;m++){let defects=0;const last=new Map();for(let i=0;i<n;i++){if(i>=m&&(!last.has(w[i])||i-last.get(w[i])>m))defects++;last.set(w[i],i);}ok(s<=m+defects,"lag alphabet bound");lagChecks++;}}
 let w=[];for(let h=1;h<=8;h++){w=[...w,h,...w];ok(w.length===2**h-1&&!denseFind(w),"sharp Zimin word");extremal++;}
 return {words,forced,lagChecks,extremal};
}
console.log(JSON.stringify({oracle:combinatorialOracle()}));
