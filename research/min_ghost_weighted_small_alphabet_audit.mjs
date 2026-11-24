// Weighted candidate insertion at fresh landings: finite CRT audit.
function audit(Y,N=256){
 const V=8*Y,U=Math.floor(Y*Math.sqrt(Math.log(Y))),z=Math.ceil(U**.8),v=Math.max(4,Math.floor(Math.sqrt(z))),P=z>100?11:7,ps=[];
 for(let p=3;p<V;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 const k=ps.findIndex(p=>p>=z),l=ps.findIndex(p=>p>=P),M=ps.slice(0,l).reduce((a,b)=>a*b,1);
 let rng=(0x6f13272b^Y)>>>0;
 function rand(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let lim=4294967296-4294967296%p,x;do{x=rand()}while(x>=lim);return x%p}
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(m)},c=new Int32Array(ps.length),t=new Int32Array(ps.length);
 let histories=0,candidates=0,div=0,agree=0,short=0,shortAgree=0,shortBad=0,shortKnown=0,shortOwn=0,congruences=0,weight=0,badWeight=0,unionWeight=0,spread=0,spreadAgree=0,actualFresh=0,actualDiverge=0,actualShort=0,actualShortAgree=0,actualMaxGain=0,classes=0;
 for(let j=0;j<N;j++){
  let parity=uni(2);
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let x=uni(p);t[i]=x%2===parity?x:x+p;}
  function next(s,g,lim){let w=Infinity,i0=-1;for(let i=0;i<lim;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+s-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i0])){w=f;i0=i}}return {w,i:i0}}
  function trace(s,g,lim,cap){let start=s,base=g,es=[],terminal=false;for(;;){let a=next(s,g,lim);if(a.i<0){terminal=true;break}if(s+a.w-start>cap)break;s+=a.w;g+=ps[a.i]-1;es.push({s:s-start,p:ps[a.i],d:g-base})}return {es,terminal,d:g-base}}
  function signature(a){return a.es.map(x=>x.s+":"+x.p+":"+x.d).join(",")}
  let g=0,s=0,seen=new Set();
  for(;;){let a=next(s,g,ps.length);if(a.i<0||s+a.w>U)break;
   s+=a.w;let q=ps[a.i],g0=g;g+=q-1;
   if(a.i>=k&&!seen.has(a.i)){
    actualFresh++;let b=trace(s,g,k,v),d=trace(s,g,l,v),diff=signature(b)!==signature(d);actualDiverge+=diff;actualShort+=b.terminal;if(b.terminal&&!diff){actualShortAgree++;actualMaxGain=Math.max(actualMaxGain,b.d);ck(d.terminal&&d.d===b.d&&b.d<2*M,"short barrier")}
    if(histories<48){
     histories++;let lowByResidue=new Map(),allOffsets=new Set(),goodOffsets=new Set();
     for(let qi=k;qi<ps.length;qi++){if(seen.has(qi))continue;let q0=ps[qi],r=q0%M,h=g0+q0-1,A=trace(s,h,l,v),B=trace(s,h,k,v),Akey=signature(A),Bkey=signature(B),w=1/q0**2;
      if(lowByResidue.has(r))ck(lowByResidue.get(r)===Akey,"period");else lowByResidue.set(r,Akey);
      let forbidden=0,idx=0,offset=0;
      for(let u=1;u<=v;u++){
       while(idx<A.es.length&&A.es[idx].s<u)offset=A.es[idx++].d;
       if(idx<A.es.length&&A.es[idx].s===u)continue; // smaller label wins
       let even=(parity+s+u)%2===0;
       for(let pi=l;pi<k;pi++){let p=ps[pi];if(mod(t[pi]+s+u-(even?0:p+2),2*p)!==0)continue;
        let target=mod((even?1:-1)-c[pi]-g0+1-offset,p);
        let hit=mod(q0,p)===target;
        ck(hit===(mod(c[pi]+h+offset,p)===(even?1:p-1)),"CRT");congruences++;if(hit)forbidden++;
       }
      }
      let different=Akey!==Bkey;ck(different===(forbidden>0),"first insertion");
      candidates++;weight+=w;unionWeight+=forbidden*w;if(different){div++;badWeight+=w}else agree++;
      if(B.terminal){short++;allOffsets.add(B.d);if(!different){shortAgree++;goodOffsets.add(B.d);ck(A.terminal&&A.d===B.d&&B.d<2*M,"terminal barrier");let kb=[...seen].some(i=>i>=k&&[1,ps[i]-1].includes(mod(c[i]+h+B.d,ps[i]))),own=[B.d-1,B.d+1,B.d-3].some(x=>x%q0===0);shortKnown+=kb;shortOwn+=own;shortBad+=kb||own;}}
     }
     classes+=lowByResidue.size;spread+=allOffsets.size;spreadAgree+=goodOffsets.size;
    }
   }
   seen.add(a.i);
  }
 }
 ck(badWeight<=unionWeight+1e-8,"weighted union");
 return {Y,V,U,z,P,M,v,N,histories,candidates,div,agree,short,shortAgree,shortBad,shortKnown,shortOwn,congruences,weight,badWeight,unionWeight,weightedDivergence:badWeight/weight,weightedUnion:unionWeight/weight,spread,spreadAgree,classes,actualFresh,actualDiverge,actualShort,actualShortAgree,actualMaxGain};
}
for(const y of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(y)));
