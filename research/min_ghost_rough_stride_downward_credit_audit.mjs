// Rough-stride roots, actual transition tests, and disjoint downward-pair erasure.
function audit(U,N=128,A=5){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(7,Math.floor(root/8));
 const mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x3ec78a11^U)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),ft=new Int32Array(ps.length),best=new Int32Array(ps.length);
 const out={U,N,V,A,L,root,base,events:0,peakSum:0,roughPairs:0,pLatest:0,qLatest:0,pLatestDouble:0,rootPairs:0,roughChecks:0,localSingle:0,localDouble:0,omitted:0,shortDownwardPairs:0,pairErased:0,recordErased:0,creditPair:0,creditRecord:0,netOrd:0,ordinaryFreshPos:0,ordinaryRecordPos:0,ordinaryNegative:0,scanChecks:0,erasedElapsed:0,erasedGain:0,rootRecordPositive:0};
 function rough(g,k){for(let j=0;j<ps.length&&ps[j]<=k;j++){let h=mod(c[j]+g,ps[j]);if(h===1||h===ps[j]-1)return false;}return true;}
 for(let a=0;a<N;a++){
  let parity=uni(2);first.fill(-1);ft.fill(-1);best.fill(-1);
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let x=uni(p);t[j]=x%2===parity?x:x+p;}
  for(let z=0;z<24;z++){
   let p=ps[uni(ps.length)],v=uni(2*U+1),B=2*(2+uni(2*U));
   for(let j=0;j<ps.length&&ps[j]<=47;j++){
    let ell=ps[j];if(p%ell===0){out.omitted++;continue;}
    let single=0,double=0;
    for(let n=0;n<ell;n++){let x=mod(c[j]+v+p*n,ell),y=mod(x-B,ell);let a=x===1||x===ell-1,b=y===1||y===ell-1;single+=+a;double+=+(a||b);}
    ck(single===2,"two roots");out.localSingle++;
    if(ell>=5&&[B,B-2,B+2].every(x=>x%ell!==0)){ck(double===4,"four roots");out.localDouble++;}else out.omitted++;
   }
  }
  let s=0,g=0,peak=0,hi=0,seq=[{p:0,s:0,g:0,J:-6*parity,chi:parity,fresh:false,best:-1,w:0,d:0}],prev=null;
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(s+w>U)break;let p=ps[i],fresh=first[i]<0,chi=(parity+s+w)%2,J=2*(s+w)-g-p+1-6*chi;
   if(p>=A){
    let k=seq.length,prevJ=seq[k-1].J,inc=J-prevJ;
    if(!fresh&&prev&&p!==prev.p&&p>=base&&prev.p>=base&&g+p-1<=2*U&&4*w>p){
     let q=prev.p,d=g-prev.pre-q+1,up=first[i],uq=first[prev.i],m,n,aa,bb;
     for(let h of [-2,0,2])if(mod(g-up-h,p)===0){m=(g-up-h)/p;aa=h}
     for(let h of [-2,0,2])if(mod(prev.pre-uq-h,q)===0){n=(prev.pre-uq-h)/q;bb=h}
     ck(d>=0&&d<L&&m>=1&&n>=0&&m*p-(n+1)*q===uq-up+bb-aa-1+d,"divisor");
     let lp=ft[i]>ft[prev.i];out.roughPairs++;out.pLatest+=+lp;out.qLatest+=+!lp;out.rootPairs+=+(p>=root&&q>=root);
     let G=lp?uq+(n+1)*q+bb-1+d:up+m*p+aa;ck(G===g&&rough(G,Math.floor(p/8)),"target rough");out.roughChecks++;
     if(lp&&4*prev.w>q){ck(rough(G-q+1-d,Math.floor(q/8)),"predecessor rough");out.pLatestDouble++;out.roughChecks++}
    }
    let x={p,i,s:s+w,g:g+p-1,pre:g,J,chi,fresh,best:best[i],w,inc};
    if(!fresh&&prev&&p>=10*L+14&&prev.p>=16*p&&4*prev.w<=prev.p&&inc>0){ck(inc+prev.inc<=0,"downward signed pair");out.shortDownwardPairs++;}
    seq.push(x);if(best[i]<0||J>=seq[best[i]].J)best[i]=k;prev=x;
   }
   if(fresh){first[i]=g;ft[i]=s+w}
   s+=w;g+=p-1;out.events++;
   if(2*s-g>peak){peak=2*s-g;hi=seq.length-1;}
  }
  let cover=new Uint8Array(hi+1),er=0,erG=0,erT=0,ord=0,fp=0,rp=0,neg=0;
  for(let k=hi;k>0;){
   let x=seq[k],y=seq[k-1],target=k-1,type=0;
   if(!x.fresh&&k>=2&&x.p>=10*L+14&&y.p>=16*x.p&&4*y.w<=y.p&&x.inc>0){target=k-2;type=1;}
   else if(!x.fresh&&x.J<=seq[x.best].J){target=x.best;type=2;}
   let d=x.J-seq[target].J;
   if(type){ck(d<=0,"nonpositive erasure");er-=d;erG+=x.g-seq[target].g;erT+=x.s-seq[target].s;if(type===1){out.pairErased++;out.creditPair-=d;}else{out.recordErased++;out.creditRecord-=d;ck(d%(2*x.p)===0,"record lattice");}}
   else{ord+=d;if(d<0)neg-=d;else if(x.fresh)fp+=d;else{ck(x.J>seq[x.best].J,"strict record");rp+=d;if(x.p>=root)out.rootRecordPositive+=d;}}
   for(let j=target+1;j<=k;j++){ck(!cover[j],"disjoint");cover[j]=1;}
   k=target;
  }
  for(let j=1;j<=hi;j++)ck(cover[j],"coverage");
  ck(ord-er===seq[hi].J-seq[0].J&&ord===fp+rp-neg,"telescoping");
  ck(peak<=5*L+12+fp+Math.max(0,rp-neg-er),"peak with credits");
  out.peakSum+=peak;out.netOrd+=ord;out.ordinaryFreshPos+=fp;out.ordinaryRecordPos+=rp;out.ordinaryNegative+=neg;out.erasedElapsed+=erT;out.erasedGain+=erG;out.scanChecks++;
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?128:256)));
let synthetic=0;for(let L of [6,30,210])for(let p=10*L+15;p<=10*L+100;p+=2)for(let q=16*p+1;q<=16*p+31;q+=2){let wq=Math.floor(q/4),wp=2*p,aq=2*wq-(q-1)+5*L+6,ap=2*wp-(p-1)+5*L+6;if(ap>4*p||aq+ap>0)throw Error('synthetic bound');synthetic++}console.log(JSON.stringify({synthetic}));
