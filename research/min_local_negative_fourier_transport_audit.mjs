// Fourier gap moments and variable-cell chi-square entropy, Negative MIN.
// Execute with node research/min_local_negative_fourier_transport_audit.mjs.
function audit(){
 const mod=(a,p)=>(a%p+p)%p,ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))};
 const ps=[5,7,11,13,17,19,23,29,31,37,41,43,47,53],rows=[],sets=[];
 let K=1n,D=1,delta=1,B=[0],checks=0;
 for(let p of ps){
  let l=(p-1)/2,beta=1/((p-1)*Math.sin(Math.PI/(2*p)))**2;
  for(let r=1;r<p;r++){let w=(Math.sin(Math.PI*r*l/p)/(l*Math.sin(Math.PI*r/p)))**2;ck(w<=beta+1e-12,"local maximum");checks++}
  let old=K;K*=BigInt(p);D*=1+p*beta;delta*=l/p;
  if(p<=23){
   let C=[];for(let b of B)for(let t=0;t<p;t++){let k=b+t*Number(old);if(mod(-3*k,p)<=(p-3)/2)C.push(k)}B=C.sort((a,b)=>a-b);
   let gaps=B.map((b,i)=>(i===B.length-1?B[0]+Number(K):B[i+1])-b),h=gaps.reduce((s,m)=>s+m/Number(K)*Math.log(m),0);
   let moment=gaps.reduce((s,m)=>s+m/Number(K)*Math.sqrt(m),0);
   ck(h<=Math.min(Math.log(Number(K)),Math.log(4*D)+1)+1e-9,"gap entropy");
   ck(moment<=2*Math.sqrt(4*D)+1e-9,"gap fractional moment");
   let row={z:p,K:K.toString(),D,delta,Hgap:h,Hbound:Math.min(Math.log(Number(K)),Math.log(4*D)+1),halfMoment:moment,momentBound:4*Math.sqrt(D)};
   if(p<=17){
    // Direct CRT correlation vs exact Fourier frequency sum on small complete periods.
    const k=Number(K),local=ps.filter(q=>q<=p).map(q=>{let l=(q-1)/2,m=k/q;return Array.from({length:q},(_,r)=>{if(!r)return 1;let a=mod(r*m,q),t=mod(a*modinv(-3,q),q);return (Math.sin(Math.PI*t*l/q)/(l*Math.sin(Math.PI*t/q)))**2})});
    // CRT character frequency r/k decomposes as local r*(k/q)^(-1) mod q; use inverse, not product.
    function modinv(a,p){for(let i=1;i<p;i++)if(mod(a*i,p)===1)return i;throw Error("inverse")}
    for(let i=0;i<local.length;i++){let q=ps[i],m=k/q,l=(q-1)/2,inv=modinv(m,q)*modinv(-3,q);for(let r=1;r<q;r++){let t=mod(r*inv,q);local[i][r]=(Math.sin(Math.PI*t*l/q)/(l*Math.sin(Math.PI*t/q)))**2}}
    let weights=new Float64Array(k);
    for(let r=0;r<k;r++){let v=1;for(let i=0;i<local.length;i++)v*=local[i][r%ps[i]];weights[r]=v}
    let sum=weights.reduce((s,v)=>s+v,0);ck(Math.abs(sum-1/delta)<1e-7/delta,"Parseval");
    row.variances=[];
    for(let H of [...new Set([1,Math.ceil(1/delta),Math.ceil(D/4),Math.ceil(D),Math.ceil(k/2),k,k+7])]){
     let v=0;for(let r=1;r<k;r++){let u=Math.PI*r/k;v+=weights[r]*(Math.sin(H*u)/(H*Math.sin(u)))**2}
     let vr=1/(H*delta)-1;
     for(let h=1;h<H;h++){let c=1;for(let q of ps.filter(q=>q<=p)){let l=(q-1)/2,r=mod(3*h,q);c*=q*Math.max(0,l-Math.min(r,q-r))/(l*l)}vr+=2*(H-h)*c/H**2}
     ck(Math.abs(v-vr)<1e-7,"Fourier correlation equivalence");ck(v<=(D-1)/H+1e-9,"spectral bound");
     row.variances.push({H,V:v,bound:(D-1)/H});checks+=2;
    }
   }
   rows.push(row);sets.push({p,k:Number(K),B:[...B]});
  }else rows.push({z:p,K:K.toString(),D,delta,Hbound:Math.min(Math.log(Number(K)),Math.log(4*D)+1),momentBound:4*Math.sqrt(D)});
 }
 // Actual elapsed-T trajectories; pad the initial slab to whole cells and include stationary ghosts.
 const R=480000,T=Math.ceil(Math.sqrt(2*R+1)),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1,spf=new Int32Array(2*R+5);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}return {p,w}}
 function cell(a,s){let t=a/6,k=Math.floor(t/s.k),u=t-k*s.k,l=0,r=s.B.length;while(l<r){let m=(l+r)>>1;if(s.B[m]<=u)l=m+1;else r=m}return [6*(k*s.k+(l?s.B[l-1]:s.B.at(-1)-s.k)),6*(k*s.k+(l<s.B.length?s.B[l]:s.k+s.B[0]))]}
 const ss=sets.filter(s=>s.p<=19).map(s=>({s,initial:new Map(),final:new Map(),actual:new Map(),flux:new Map(),left:cell(lo-2*T-6,s)[0],right:cell(hi,s)[1]}));
 let ends=new Map(),events=0;
 const add=(m,k,v=1)=>m.set(k,(m.get(k)||0)+v),f=x=>x?x*Math.log(x):0;
 for(let A=lo;A<=hi;A+=6){
  let a=A,n=3-A/2,end=n+T;
  for(;;){let e=next(a,n);if(n+e.w>end)break;a-=e.p-1;n+=e.w;events++}
  add(ends,a);
  for(let s of ss){let [l]=cell(A,s.s),[r]=cell(a,s.s);add(s.actual,r);if(l!==r){add(s.flux,r,1);add(s.flux,l,-1)}}
 }
 let fine=[...ends.values()].reduce((s,v)=>s+f(v),0)/N,transport=[];
 for(let s of ss){
  let total=0,H0=0,chi=0,C=0,kl=0,terminalSize=0,coarse=0,ghostCoarse=0,lin=0,variance=0;
  for(let a=s.left;a<s.right;){let [b,r]=cell(a,s.s);ck(a===b,"cell iteration");let M=(r-a)/6,realInitial=Math.max(0,Math.min(hi,r-6)-Math.max(lo,a)+6)/6;
   // if intersection empty clamp BEFORE division; all endpoints integral
   let realFinal=s.actual.get(a)||0,d=realFinal-realInitial,m=M+d;
   ck(d===(s.flux.get(a)||0)&&m>=0,"mass flux");total+=M;H0+=M*Math.log(M);C+=M*Math.sqrt(M);chi+=d*d/M;lin+=d*Math.log(M);variance+=M*Math.log(M)**2;
   if(m){kl+=m*Math.log(m/M);terminalSize+=m*Math.log(M)}coarse+=f(realFinal);ghostCoarse+=f(m);checks++;a=r;
  }
  let h0=H0/total,chi2=chi/total,halfMoment=C/total,relative=kl/total,logRenyi=Math.log1p(chi2),hGhost=ghostCoarse/total,hReal=coarse/N;
  ck(Math.abs(hGhost-terminalSize/total-relative)<1e-8&&Math.abs(terminalSize/total-h0-lin/total)<1e-8,"decomposition");
  ck(relative>=-1e-8&&relative<=logRenyi+1e-8&&fine<=hReal+1e-8&&hReal<=total/N*hGhost+1e-8,"entropy");
  let bMoment=total/N*(2*Math.log(halfMoment)+3*logRenyi),bLinear=total/N*(h0+lin/total+logRenyi),bCs=total/N*(h0+Math.sqrt(chi2*Math.max(0,variance/total-h0*h0))+logRenyi);
  ck(hReal<=Math.min(bMoment,bLinear,bCs)+1e-8,"transport bounds");
  transport.push({z:s.s.p,total,N,chi2,h0,hReal,fine,hGhost,relative,halfMoment,linear:lin/total,bMoment,bLinear,bCs});
 }
 return {checks,rows,transport,events};
}
console.log(JSON.stringify(audit(),null,2));
