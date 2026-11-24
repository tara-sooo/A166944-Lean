// Local predecessor stride and multi-event signed shadow audit.
function audit(U,N=96,A=5,K=6,F=4){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(7,Math.floor(root/8)),mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x58ed9c13^U)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),ft=new Int32Array(ps.length),best=new Int32Array(ps.length);
 const out={U,N,V,A,L,K,F,root,base,events:0,localPairs:0,bothRepeated:0,pLatest:0,qLatest:0,rootPairs:0,targetDistant:0,positive:0,weight:0,congruenceChecks:0,rootWeight:0,anchors:0,gainShadowEndpoints:0,timeShadowEndpoints:0,shadowPositiveRepeats:0,shadowMaxLength:0,shadowChecks:0,scanShadowErase:0,scanRecordErase:0,scanShadowCredit:0,scanRecordCredit:0,scanOrdinaryNegative:0,scanOrdinaryFresh:0,scanOrdinaryRepeat:0,scanChecks:0,peakSum:0};
 function inv(a,p){let x=1,y=0,r=a,s=p;while(s){let q=Math.floor(r/s);[r,s]=[s,r-q*s];[x,y]=[y,x-q*y];}ck(r===1,"invertible");return mod(x,p);}
 for(let a=0;a<N;a++){
  let parity=uni(2);first.fill(-1);ft.fill(-1);best.fill(-1);
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let x=uni(p);t[j]=x%2===parity?x:x+p;}
  let s=0,g=0,peak=0,hi=0,seq=[{p:0,s:0,g:0,J:-6*parity,fresh:false,best:-1,w:0}],prev=null;
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(s+w>U)break;let p=ps[i],fresh=first[i]<0,J=2*(s+w)-g-p+1-6*((parity+s+w)%2),inc=J-seq[seq.length-1].J;
   if(p>=A){
    if(!fresh&&prev&&prev.p!==p&&p>=base&&prev.p>=base&&p<=F*prev.p&&g+p-1<=2*U){
     let q=prev.p,up=first[i],uq=first[prev.i],d=g-prev.pre-q+1,m,n,aa,bb;
     for(let h of [-2,0,2])if(mod(g-up-h,p)===0){m=(g-up-h)/p;aa=h;}
     for(let h of [-2,0,2])if(mod(prev.pre-uq-h,q)===0){n=(prev.pre-uq-h)/q;bb=h;}
     ck(d>=0&&d<L&&m>=1&&n>=0&&m*p-(n+1)*q===uq-up+bb-aa-1+d,"relation");
     if(n<=K&&n+1<p){
      out.localPairs++;out.bothRepeated+=+!prev.fresh;out.targetDistant+=+(m>K);out.positive+=Math.max(0,inc);out.weight+=p;
      if(p>=root&&q>=root){out.rootPairs++;out.rootWeight+=p;}
      if(ft[i]>ft[prev.i]){let M=(n+1)*q+uq-up+bb-aa-1+d;ck(M>0&&M%p===0&&M/p===m,"latest p divisor");out.pLatest++;}
      else{let residue=mod(inv(n+1,p)*(up-uq+aa-bb+1-d),p);ck(q%p===residue,"latest q residue");let Q=2**Math.floor(Math.log2(q)),cnt=Math.floor((2*Q-1-residue)/p)-Math.floor((Q-1-residue)/p);ck(cnt>=1&&cnt<=1+Q/p+1e-10,"progression count");out.qLatest++;out.congruenceChecks++;}
     }
    }
    let x={p,i,s:s+w,g:g+p-1,pre:g,J,fresh,best:best[i],w,inc};
    let k=seq.length;seq.push(x);if(best[i]<0||J>=seq[best[i]].J)best[i]=k;prev=x;
   }
   if(fresh){first[i]=g;ft[i]=s+w;}
   s+=w;g+=p-1;out.events++;if(2*s-g>peak){peak=2*s-g;hi=seq.length-1;}
  }
  let anchor=new Array(seq.length).fill(-1);
  for(let j=1;j<seq.length;j++){
   let q=seq[j];if(q.p<40*L+56||4*q.w>q.p)continue;out.anchors++;
   for(let i=j+1;i<seq.length;i++){let x=seq[i],gain=20*(x.g-q.g)<=q.p,time=8*(x.s-q.s)<=q.p;if(!gain&&!time)break;
    let d=x.J-seq[j-1].J;ck(8*d<=-q.p,"shadow signed bound");out.shadowChecks++;out.gainShadowEndpoints+=+gain;out.timeShadowEndpoints+=+time;out.shadowPositiveRepeats+=+(!x.fresh&&x.inc>0);out.shadowMaxLength=Math.max(out.shadowMaxLength,i-j+1);anchor[i]=j;
   }
  }
  let cover=new Uint8Array(hi+1),credits=0,ord=0,fpos=0,rpos=0,neg=0;
  for(let i=hi;i>0;){let x=seq[i],j=i-1,type=0;if(!x.fresh&&x.inc>0&&anchor[i]>=1){j=anchor[i]-1;type=1;}else if(!x.fresh&&x.J<=seq[x.best].J){j=x.best;type=2;}let d=x.J-seq[j].J;
   if(type){ck(d<=0,"erase nonpositive");credits-=d;if(type===1){out.scanShadowErase++;out.scanShadowCredit-=d;}else{ck(d%(2*x.p)===0,"record lattice");out.scanRecordErase++;out.scanRecordCredit-=d;}}
   else{ord+=d;if(d<0)neg-=d;else if(x.fresh)fpos+=d;else{ck(x.J>seq[x.best].J,"record");rpos+=d;}}
   for(let h=j+1;h<=i;h++){ck(!cover[h],"disjoint");cover[h]=1;}i=j;
  }
  for(let i=1;i<=hi;i++)ck(cover[i]===1,"coverage");
  ck(ord-credits===seq[hi].J-seq[0].J&&ord===fpos+rpos-neg,"telescoping");ck(peak<=5*L+12+fpos+Math.max(0,rpos-neg-credits),"peak");
  out.scanOrdinaryNegative+=neg;out.scanOrdinaryFresh+=fpos;out.scanOrdinaryRepeat+=rpos;out.peakSum+=peak;out.scanChecks++;
 }
 return out;
}
function synthetic(){
 let count=0,maxLength=0;
 for(let L of [6,30,210])for(let q=40*L+57;q<=40*L+457;q+=2)for(let k=1;k<=12;k++){
  let G=Math.floor(q/20),T=Math.floor(q/8),b=5*L+2*Math.floor(q/4)-(q-1)+6;
  let gs=Array(k).fill(2*Math.floor(G/(2*k)));if(gs.some(x=>x<2))continue;
  let gain=gs.reduce((a,b)=>a+b,0);
  if(8*(b+5*gain)>-q||8*(b+2*T)>-q)throw Error("synthetic shadow");
  count++;maxLength=Math.max(k+1,maxLength);
 }
 return {count,maxLength}
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:96)));
console.log(JSON.stringify(synthetic()));
