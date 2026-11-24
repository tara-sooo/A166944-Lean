// Near-eligibility stock and upward fresh-to-known transition diagnostics.
function audit(U,N=128,A=5){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sv[q]=1}
 const L=2*ps.filter(p=>p<A).reduce((a,b)=>a*b,1),root=Math.ceil(Math.sqrt(2*U)),base=Math.max(7,Math.floor(root/8)),F=4,z=Math.max(root,Math.ceil(U/Math.log(U)**2.5));
 const mod=(x,p)=>(x%p+p)%p,ck=(a,m)=>{if(!a)throw Error(m)};
 let rng=(0x67cd94ef^U^A)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Float64Array(ps.length);
 const out={U,V,N,A,L,root,base,F,z,events:0,freshHigh:0,knownPairs:0,comparablePairs:0,upwardPairs:0,upwardRootPairs:0,upwardRootBelowZ:0,upwardLong:0,upwardWeight:0,upwardRootWeight:0,upwardSurplus:0,rootSurplus:0,ticketChecks:0,stockChecks:0,divisorChecks:0,stockMax:0,maxCandidateMultiplicity:0,earlyFreshKnown:0,earlyFreshKnownWeight:0,lowBoundChecks:0,zeroModChecks:0};
 const band=x=>base*2**Math.floor(Math.log2(x/base));
 for(let n=0;n<N;n++){
  let parity=uni(2);first.fill(-1);let known=[],s=0,g=0,prev=null,block=null;
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let a=uni(p);t[i]=a%2===parity?a:a+p}
  function close(){if(!block)return;ck(block.lowGain<L&&block.lowPeak<=5*L,"low bound");out.lowBoundChecks++;}
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let a=2*p-mod(t[j]+s-(cc===1?0:p+2),2*p);if(a<w||(a===w&&p<ps[i])){w=a;i=j}}
   if(s+w>U)break;
   let p=ps[i],fresh=first[i]<0,dh=2*w-p+1;
   if(p>=A){
    close();
    if(!fresh&&prev?.fresh&&g+p-1<=2*U){
     out.knownPairs++;
     const d=g-prev.g-prev.p+1;ck(d>=0&&d<L&&d%2===0,"actual low gain");
     if(p<=F*prev.p)out.comparablePairs++;
     else{
      out.upwardPairs++;out.upwardWeight+=p;out.upwardLong+=+(4*w>p);out.upwardSurplus+=Math.max(0,dh+prev.lowSigned);
      if(prev.p<root){out.earlyFreshKnown++;out.earlyFreshKnownWeight+=p}
      if(prev.p>=base){
       ck(prev.tickets.has(i),"known upward ticket");out.ticketChecks++;
       let P=band(p),R=band(prev.p);ck(P>F*R/2,"dyadic scale");
       const u=first[i],G=prev.g,offset=prev.p-1+d+prev.signs.get(i)-(mod(c[i]+g,p)===1?1:-1);
       ck(u<=G-P+1&&offset>=R-3&&offset<=2*R+L+1&&G-u+offset>0&&(G-u+offset)%p===0,"actual divisor stock");out.divisorChecks++;
       ck(prev.stock.has(i),"near stock contains actual pair");
      }
      if(prev.p>=root){out.upwardRootPairs++;out.upwardRootWeight+=p;out.rootSurplus+=Math.max(0,dh+prev.lowSigned);out.upwardRootBelowZ+=+(p<z)}
     }
    }
    let tickets=new Set(),stock=new Set(),signs=new Map();
    if(fresh){
     out.freshHigh++;
     if(p>=base&&g<=2*U){
      let R=band(p),bucket=new Map(),mult=new Map();
      for(let j of known){
       let q=ps[j];if(q<F*p||q>2*U+1||q<base)continue;
       let P=band(q),u=first[j],sigma=mod(c[j]+u,q)===1?1:-1;signs.set(j,sigma);
       ck(u<=g-q+1,"first gain separation");
       let hit=false;for(let a=R-3;a<=2*R+L+1;a++){let d0=g-u+a;ck(d0>0,"zero excluded");out.zeroModChecks++;if(d0%q===0)hit=true;}
       if(hit){stock.add(j);bucket.set(P,(bucket.get(P)||0)+1);}
       let num=0;for(let d=0;d<L;d+=2)if([1,q-1].includes(mod(c[j]+g+p-1+d,q)))num++;
       if(num){tickets.add(j);ck(hit,"ticket contained in near stock");mult.set(j,num);out.stockChecks++;}
      }
      for(let k of bucket.values())out.stockMax=Math.max(out.stockMax,k);
      for(let k of mult.values())out.maxCandidateMultiplicity=Math.max(out.maxCandidateMultiplicity,k);
     }
    }
    prev={p,g,fresh,tickets,stock,signs,lowSigned:0};
    block={lowGain:0,lowPeak:0,lowSigned:0};
   }else if(block){block.lowGain+=p-1;block.lowSigned+=dh;block.lowPeak=Math.max(block.lowPeak,block.lowSigned);if(prev)prev.lowSigned+=dh}
   if(fresh){first[i]=g;known.push(i);}
   s+=w;g+=p-1;out.events++;
  }close();
 }
 ck(out.upwardPairs===out.earlyFreshKnown+out.upwardRootPairs,"partition");
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?128:256)));
