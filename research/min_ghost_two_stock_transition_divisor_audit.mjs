// Two-stock transition tickets assigned at the latest first selection.
function audit(U,N=128,A=5){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(7,Math.floor(root/8)),thresholds=[base,root,Math.ceil(U**(2/3))];
 const mod=(x,p)=>(x%p+p)%p,ck=(x,m)=>{if(!x)throw Error(m)};
 let rng=(0x3fb6e2cd^U^A)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),ftime=new Int32Array(ps.length);
 const out={U,V,N,A,L,root,base,events:0,cappedEvents:0,relationChecks:0,pLatest:0,qLatest:0,bothRepeated:0,longTarget:0,zeroTargetsExcluded:0,tickets:0,distinctConsumed:0,thresholds:thresholds.map(Q=>({Q,actual:0,bothRepeated:0,pLatest:0,qLatest:0,longTarget:0,actualWeight:0,repeatWeight:0,ticketWeight:0,positive:0}))};
 const key=(p,q,m,n,a,b,d)=>[p,q,m,n,a,b,d].join(",");
 const offsets=[-2,0,2];
 for(let j0=0;j0<N;j0++){
  let parity=uni(2);first.fill(-1);ftime.fill(-1);
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let x=uni(p);t[j]=x%2===parity?x:x+p;}
  let s=0,g=0,known=[],prev=null,tickets=new Set(),consumed=new Set(),budget=thresholds.map(()=>0),actual=thresholds.map(()=>0);
  function add(p,q,up,uq,m,n,a,b,d){
   if(m<1||n<0||m%2||n%2||n===0&&b!==0)return;
   let Gq=uq+n*q+b,Gp=up+m*p+a;
   if(Gq<uq||Gp<up+p-1||Gq<0||Gp+p-1>2*U||Gq%2||Gp%2||Gp!==Gq+q-1+d)return;
   let k=key(p,q,m,n,a,b,d);if(tickets.has(k))throw Error("duplicate ticket");tickets.add(k);out.tickets++;
   for(let j=0;j<thresholds.length;j++)if(p>=thresholds[j]&&q>=thresholds[j])budget[j]+=p;
  }
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let a=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(a<w||(a===w&&p<ps[i])){w=a;i=j}}
   if(s+w>U)break;
   let x=ps[i],fresh=first[i]<0,cap=g+x-1<=2*U;out.events++;out.cappedEvents+=+cap;
   if(fresh&&cap&&x>=base){
    for(let j of known){let y=ps[j],v=first[j];if(y<base)continue;
     // Latest first label is target p=x. Enumerate n of known q.
     for(let n=0;n*y<=2*U+2;n+=2)for(let a of offsets)for(let b of (n===0?[0]:offsets))for(let d=0;d<L;d+=2){
      let M=(n+1)*y+v-g+b-a-1+d;
      if(M<=0){out.zeroTargetsExcluded+=+(M===0);continue;}
      if(M%x===0)add(x,y,g,v,M/x,n,a,b,d);
     }
     // Latest first label is predecessor q=x. Enumerate m of known p.
     for(let m=2;m*y<=2*U+2;m+=2)for(let a of offsets)for(let b of offsets)for(let d=0;d<L;d+=2){
      let M=m*y+v-g+a-b+1-d;
      if(M<=0){out.zeroTargetsExcluded+=+(M===0);continue;}
      if(M%x===0)add(y,x,v,g,m,M/x-1,a,b,d);
     }
    }
   }
   if(x>=A){
    if(cap&&!fresh&&prev&&prev.p!==x&&x>=base&&prev.p>=base){
     let p=x,q=prev.p,up=first[i],uq=first[prev.i],m,n,a,b;
     for(let h of offsets)if(mod(g-up-h,p)===0){m=(g-up-h)/p;a=h;}
     for(let h of offsets)if(mod(prev.g-uq-h,q)===0){n=(prev.g-uq-h)/q;b=h;}
     let d=g-prev.g-q+1;
     ck(Number.isInteger(m)&&m>=1&&Number.isInteger(n)&&n>=0&&d>=0&&d<L&&d%2===0,"strides and low gain");
     ck(m*p-(n+1)*q===uq-up+b-a-1+d,"relation");
     let lp=ftime[i]>ftime[prev.i];
     if(lp){ck((n+1)*q+uq-up+b-a-1+d===m*p&&m*p>0,"target divisor");out.pLatest++;}
     else{ck(m*p+up-uq+a-b+1-d===(n+1)*q&&(n+1)*q>0,"predecessor divisor");out.qLatest++;}
     let k=key(p,q,m,n,a,b,d);ck(tickets.has(k)&&!consumed.has(k),"distinct earlier ticket");consumed.add(k);out.distinctConsumed++;out.relationChecks++;out.bothRepeated+=+!prev.fresh;out.longTarget+=+(4*w>p);
     let J=2*(s+w)-g-p+1-6*((parity+s+w)%2),pos=Math.max(0,J-prev.J);
     for(let j=0;j<thresholds.length;j++)if(p>=thresholds[j]&&q>=thresholds[j]){let z=out.thresholds[j];z.actual++;z.bothRepeated+=+!prev.fresh;z.pLatest+=+lp;z.qLatest+=+!lp;z.longTarget+=+(4*w>p);z.actualWeight+=p;z.repeatWeight+=prev.fresh?0:p;z.positive+=pos;actual[j]+=p;}
    }
    prev={p:x,i,g,fresh,J:2*(s+w)-g-x+1-6*((parity+s+w)%2)};
   }
   if(fresh){first[i]=g;ftime[i]=s+w;known.push(i);}
   s+=w;g+=x-1;
   if(!cap)break;
  }
  for(let j=0;j<thresholds.length;j++){ck(actual[j]<=budget[j]&&actual[j]<=3*U,"weight cap");out.thresholds[j].ticketWeight+=budget[j];}
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:128)));
