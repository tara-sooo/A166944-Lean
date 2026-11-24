// Discovery-time and discovery-rank local two-stock transition ticket audit.
function audit(U,N=64,A=5,K=4,k=3){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1;}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(7,Math.floor(root/8)),z=Math.max(root,Math.ceil(U/Math.log(U)**2.5));
 const mod=(x,p)=>(x%p+p)%p,ck=(x,m)=>{if(!x)throw Error(m)};let rng=(0x6d8b134f^U)>>>0;function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=rand()}while(x>=a);return x%p;}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),ft=new Int32Array(ps.length),rbase=new Int32Array(ps.length),rroot=new Int32Array(ps.length);
 const out={U,N,V,A,L,K,k,root,base,z,events:0,pairs:0,bothRepeat:0,localTime:0,localRank:0,rankLong:0,rankLongBoth:0,rankLongTimeFar:0,timeBothLongStride:0,rankBothLongStride:0,rootTime:0,rootRankLong:0,rootRankAnalytic:0,rootBothRepeat:0,pLatest:0,qLatest:0,tickets:0,rankTickets:0,timeWeight:0,rankWeight:0,timeBudget:0,rankBudget:0,checks:0,rootChecks:0};
 const offsets=[-2,0,2],key=(p,q,m,n,a,b,d)=>[p,q,m,n,a,b,d].join(",");
 function rough(g,p){for(let j=0;j<ps.length&&ps[j]<=47&&8*ps[j]<=p;j++){let x=mod(c[j]+g,ps[j]);if(x===1||x===ps[j]-1)return false;}return true;}
 for(let a0=0;a0<N;a0++){
  let parity=uni(2);first.fill(-1);ft.fill(-1);rbase.fill(0);rroot.fill(0);
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let x=uni(p);t[j]=x%2===parity?x:x+p;}
  let s=0,g=0,known=[],br=0,rr=0,prev=null,tickets=new Map(),used=new Set(),timeBudget=0,rankBudget=0,tw=0,rw=0;
  function add(p,q,up,uq,m,n,a,b,d,time,rank){
   if(m<1||n<0||m%2||n%2||n===0&&b!==0)return;
   let Gp=up+m*p+a,Gq=uq+n*q+b;if(Gp<up+p-1||Gq<uq||Gp+p-1>2*U||Gp!==Gq+q-1+d||Gp%2||Gq%2)return;
   let r=rank&&rough(Gp,p);if(!time&&!r)return;let ky=key(p,q,m,n,a,b,d);ck(!tickets.has(ky),"ticket uniqueness");tickets.set(ky,{time,rank:r});out.tickets++;if(time)timeBudget+=p;if(r){rankBudget+=p;out.rankTickets++;}
  }
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j;}}
   if(s+w>U)break;let x=ps[i],fresh=first[i]<0,now=s+w,cap=g+x-1<=2*U;out.events++;
   if(fresh&&cap&&x>=base){
    let rb=br+1,rt=x>=root?rr+1:0;
    for(let j of known){let y=ps[j],u=first[j];if(y<base)continue;let tm=now-ft[j]<=K*Math.min(x,y),rk=rb-rbase[j]<=k||(rt>0&&rroot[j]>0&&rt-rroot[j]<=k);if(!tm&&!rk)continue;
     for(let n=0;n*y<=2*U+2;n+=2)for(let a of offsets)for(let b of (n===0?[0]:offsets))for(let d=0;d<L;d+=2){let M=(n+1)*y+u-g+b-a-1+d;if(M>0&&M%x===0)add(x,y,g,u,M/x,n,a,b,d,tm,rk);}
     for(let m=2;m*y<=2*U+2;m+=2)for(let a of offsets)for(let b of offsets)for(let d=0;d<L;d+=2){let M=m*y+u-g+a-b+1-d;if(M>0&&M%x===0)add(y,x,u,g,m,M/x-1,a,b,d,tm,rk);}
    }
   }
   if(x>=A){
    if(cap&&!fresh&&prev&&prev.p!==x&&x>=base&&prev.p>=base){
     let p=x,q=prev.p,up=first[i],uq=first[prev.i],m,n,a,b;
     for(let h of offsets){if(mod(g-up-h,p)===0){m=(g-up-h)/p;a=h;}if(mod(prev.g-uq-h,q)===0){n=(prev.g-uq-h)/q;b=h;}}
     let d=g-prev.g-q+1;ck(d>=0&&d<L&&m>=1&&n>=0&&m*p-(n+1)*q===uq-up+b-a-1+d,"relation");
     let tm=Math.abs(ft[i]-ft[prev.i])<=K*Math.min(p,q),rk=Math.abs(rbase[i]-rbase[prev.i])<=k,rt=p>=root&&q>=root&&Math.abs(rroot[i]-rroot[prev.i])<=k,long=4*w>p;
     out.pairs++;out.bothRepeat+=+!prev.fresh;out.localTime+=+tm;out.localRank+=+rk;out.rankLong+=+(rk&&long);out.rankLongBoth+=+(rk&&long&&!prev.fresh);out.rankLongTimeFar+=+(rk&&long&&!tm);out.timeBothLongStride+=+(tm&&m>K&&n>K);out.rankBothLongStride+=+((rk||rt)&&long&&m>K&&n>K);
     if(p>=root&&q>=root){out.rootTime+=+tm;out.rootRankLong+=+(rt&&long);out.rootRankAnalytic+=+(rt&&long&&p<z);out.rootBothRepeat+=+!prev.fresh;}
     if(tm||((rk||rt)&&long)){let ky=key(p,q,m,n,a,b,d),tkt=tickets.get(ky);ck(tkt&&!used.has(ky),"assigned unique ticket");used.add(ky);if(tm){ck(tkt.time,"time ticket");tw+=p;}if((rk||rt)&&long){ck(tkt.rank&&rough(g,p),"rank rough ticket");rw+=p;}out.checks++;out.pLatest+=+(ft[i]>ft[prev.i]);out.qLatest+=+(ft[i]<ft[prev.i]);out.rootChecks+=+(p>=root&&q>=root);}
    }
    prev={p:x,i,g,fresh};
   }
   if(fresh){first[i]=g;ft[i]=now;known.push(i);if(x>=base)rbase[i]=++br;if(x>=root)rroot[i]=++rr;}
   s=now;g+=x-1;if(!cap)break;
  }
  ck(tw<=timeBudget&&rw<=rankBudget&&tw<=3*U&&rw<=3*U,"weight bound");out.timeWeight+=tw;out.rankWeight+=rw;out.timeBudget+=timeBudget;out.rankBudget+=rankBudget;
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?48:64)));
