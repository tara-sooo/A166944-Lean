// Small fresh predecessor exposure, local divisor stock, exact deletion ranks.
function audit(U,N=96,A=5,K=2,delta=.25,F=4){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let j=p*p;j<=V;j+=p)sv[j]=1}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),z=Math.max(root,Math.ceil(U/Math.log(U)**2.5)),mod=(x,p)=>(x%p+p)%p,ck=(b,m)=>{if(!b)throw Error(m)};
 let rng=(0x7fd15d27^U)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),ftime=new Int32Array(ps.length);
 const out={U,N,V,A,L,K,delta,F,root,z,events:0,smallFresh:0,early:0,late:0,depleted:0,eligibleEarly:0,allowedChecks:0,zeroTargetChecks:0,localStockChecks:0,stockMax:0,upward:0,upwardSmall:0,upwardEarly:0,upwardDepleted:0,upwardProduct:0,upwardSmallWeight:0,upwardEarlyWeight:0,upwardDepletedWeight:0,upwardLateWeight:0,upwardEarlyPositive:0,rankEnumeration:[]};
 function run(parity,deleted=-1,limit=U){
  let s=0,g=0,seq=[];
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){if(j===deleted)continue;let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(s+w>limit)break;
   seq.push({i,p:ps[i],g,s:s+w,w});s+=w;g+=ps[i]-1;
  }return seq;
 }
 function forbidden(seq,qi,limit,parity){
  let p=ps[qi],seen=new Set(),order=[],s=0,g=0;
  function visit(tick){let chi=(parity+tick)%2,cp=mod(1-2*chi-g,p),bp=mod(2*chi-tick,p),key=cp*p+bp;if(!seen.has(key)){seen.add(key);order.push({key,tick})}}
  for(let x of seq){if(x.s>limit)break;for(let a=1;a<=Math.min(x.s-s-1,2*p);a++)visit(s+a);if(x.p>p)visit(x.s);s=x.s;g+=x.p-1}
  for(let a=1;a<=Math.min(limit-s,2*p);a++)visit(s+a);
  return {seen,order};
 }
 for(let n=0;n<N;n++){
  let parity=uni(2);for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let a=uni(p);t[j]=a%2===parity?a:a+p}
  let seq=run(parity),known=[],prev=null;first.fill(-1);ftime.fill(-1);
  for(let h=0;h<seq.length;h++){
   let x=seq[h],p=x.p,i=x.i,fresh=first[i]<0,info=null;
   if(fresh&&p<root){
    let {seen}=forbidden(seq.slice(0,h),i,x.s-1,parity),allowed=p*p-seen.size,key=c[i]*p+mod(t[i],p);
    ck(!seen.has(key)&&allowed>0,"fresh coordinate remains");out.allowedChecks++;
    info={allowed,depleted:allowed<delta*p*p,early:x.s<=K*p*p};out.smallFresh++;out.early+=+info.early;out.late+=+!info.early;out.depleted+=+info.depleted;out.eligibleEarly+=+(info.early&&!info.depleted);
   }
   if(p>=A){
    if(!fresh&&prev?.fresh&&p>F*prev.p&&x.g+p-1<=2*U){
     out.upward++;if(prev.p<root){out.upwardSmall++;out.upwardSmallWeight+=p;let q=prev.p,info=prev.info;ck(info!==null,"small predecessor info");
      if(info.early&&!info.depleted){out.upwardEarly++;out.upwardEarlyWeight+=p;out.upwardEarlyPositive+=Math.max(0,2*(x.s-prev.s)-(x.g+p-1-prev.g-q+1));}
      else out.upwardLateWeight+=p;
      if(info.depleted){out.upwardDepleted++;out.upwardDepletedWeight+=p;}
      if(p*q<=U*Math.log(U)**.03125)out.upwardProduct++;
      let d=x.g-prev.g-q+1,sig0=mod(c[i]+first[i],p)===1?1:-1,sig1=mod(c[i]+x.g,p)===1?1:-1;ck(d>=0&&d<L&&d%2===0,"low gain");ck(first[i]<=prev.g-p+1&&(prev.g-first[i]+q-1+d+sig0-sig1)%p===0,"divisor identity");
      if(info.early&&!info.depleted){ck(prev.tickets.has(i),"early stock contains pair");out.localStockChecks++;}
     }
    }
    let tickets=new Set();
    if(fresh&&p<root&&info.early&&!info.depleted&&x.g<=2*U){
     let R=2**Math.floor(Math.log2(p)),buckets=new Map();
     for(let j of known){let v=ps[j];if(v<=F*p||v>2*U+1)continue;let P=2**Math.floor(Math.log2(v)),u=first[j];ck(u<=x.g-v+1&&ftime[j]<x.s,"known separation");let stock=false;
      for(let a=R-3;a<=2*R+L+1;a++){let n=x.g-u+a;ck(n>0,"positive divisor target");out.zeroTargetChecks++;if(n%v===0)stock=true;}
      if(stock)buckets.set(P,(buckets.get(P)||0)+1);
      for(let d=0;d<L;d+=2){let a=mod(c[j]+x.g+p-1+d,v);if(a===1||a===v-1){ck(stock,"candidate stock");tickets.add(j);out.localStockChecks++;break;}}
     }
     for(let v of buckets.values())out.stockMax=Math.max(out.stockMax,v);
    }
    prev={...x,fresh,info,tickets};
   }
   if(fresh){first[i]=x.g;ftime[i]=x.s;known.push(i)}out.events++;
  }
  // Exact enumeration of all q-coordinate pairs for one q with other phases fixed.
  if(n<3){let qi=n%3,p=ps[qi],del=run(parity,qi),{order}=forbidden(del,qi,U,parity),rank=new Map(order.map((x,j)=>[x.key,{rank:j+1,tick:x.tick}])),oldC=c[qi],oldT=t[qi],hits=0,depleted=0;
   for(let cp=0;cp<p;cp++)for(let bp=0;bp<p;bp++){c[qi]=cp;t[qi]=bp%2===parity?bp:bp+p;let full=run(parity),hit=full.find(x=>x.i===qi),expect=rank.get(cp*p+bp);ck((hit?.s??-1)===(expect?.tick??-1),"deletion first rank");if(hit){hits++;if(p*p-expect.rank+1<delta*p*p)depleted++;}}
   c[qi]=oldC;t[qi]=oldT;ck(depleted<=delta*p*p&&hits===order.length,"depletion counting");out.rankEnumeration.push({p,pairs:p*p,hits,depleted,rankCount:order.length});
  }
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?64:96)));
