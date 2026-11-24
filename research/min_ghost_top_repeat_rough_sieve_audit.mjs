// Finite CRT audit of rough return candidates and local triple-sieve residues.
function audit(U,N=512){
 const V=4*U,z=Math.max(11,Math.ceil(U/Math.log(U)**1.25)),R=Math.max(3,Math.min(47,Math.floor(z/8))),sieve=new Uint8Array(V+1),ps=[];
 for(let p=2;p<=V;p++)if(!sieve[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sieve[q]=1}
 const small=ps.filter(p=>p<=R);
 let rng=(0xa0986fa1^U)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const ck=(a,m)=>{if(!a)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),candidate=new Uint8Array(ps.length);
 let out={U,V,N,z,R,small,events:0,freshTop:0,firstCandidates:0,firstCandidatePaths:0,repeatTop:0,longTop:0,longTopPaths:0,positiveTop:0,coveredLong:0,shortTop:0,shortNegative:0,positivePeakPaths:0,peakAfterTopLong:0,peakMean:0,repeatPositiveMean:0,topRepeatPositiveMean:0,localChecks:0,multipleSlope:0,collision:0,distinct:0,congruenceChecks:0,roughChecks:0,maxBad:0,topBlockChecks:0};
 const A=5,L=6; 
 function rough(g){for(let j=0;j<small.length;j++){let p=small[j],cc=mod(c[j]+g,p);if(cc===1||cc===p-1)return false}return true}
 function possible(p,g){for(let m=1;m*p<=2*U-g+2;m++)for(let a of [-2,0,2]){let g1=g+m*p+a;if(g1>2*U||g1<g+p-1||g1%2)continue;if(rough(g1))return true}return false}
 for(let k=0;k<N;k++){
  let parity=uni(2);first.fill(-1);candidate.fill(0);
  for(let i=0;i<ps.length;i++){let p=ps[i];c[i]=uni(p);let x=uni(p);t[i]=x%2===parity?x:x+p}
  // Exact local sieve roots for sampled shifts and strides; finite test skips slopes divisible by ell.
  for(let j=0;j<16;j++){
   let v=uni(2*U+5)-2,m=1+uni(Math.floor((2*U+2)/z)+1),bad=0;
   for(let i=0;i<small.length;i++){let p=small[i],co=mod(c[i]+v,p),n=0;for(let x=0;x<p;x++){let h=mod(co+m*x,p);n+=+(x===0||h===1||h===p-1)}
    if(m%p===0){out.multipleSlope++;ck(n===(co===1||co===p-1?p:1),"zero slope");}
    else if(co===1||co===p-1){out.collision++;bad++;ck(n===2,"collision count");}
    else{out.distinct++;ck(n===3,"three residue classes");}
    out.localChecks++;
   }out.maxBad=Math.max(out.maxBad,bad);
  }
  let e=0,g=0,peak=0,rpos=0,tpos=0,long=false,peakLong=false,cand=false;
  let block=null;
  function close(){if(block&&block.top&&block.short){ck(Math.max(0,block.d+block.lowMax)===0,"nonpositive top repeat block");out.topBlockChecks++;}}
  for(;;){
   let w=Infinity,b=-1;
   for(let i=0;i<ps.length;i++){let p=ps[i],cc=mod(c[i]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[i]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[b])){w=f;b=i}}
   if(e+w>U)break;
   let p=ps[b],d=2*w-p+1,repeat=first[b]>=0,top=repeat&&p>=z&&g<=2*U;
   if(p>=A){close();block={top:top&&p>=10*L+2,short:4*w<=p,d,low:0,lowMax:0}}
   else if(block){block.low+=d;block.lowMax=Math.max(block.lowMax,block.low);ck(block.lowMax<=5*L,"low block");}
   ck(w<=2*p,"wait");
   if(!repeat){first[b]=g;if(p>=z&&p<=2*U+1&&g<=2*U){out.freshTop++;candidate[b]=+possible(p,g);if(candidate[b]){out.firstCandidates++;cand=true;}}}
   else{
    rpos+=Math.max(0,d);
    if(top){
     out.repeatTop++;let diff=g-first[b];ck(diff>=p-1&&[-2,0,2].some(a=>diff>=p+a&&mod(diff-a,p)===0),"return progression");out.congruenceChecks++;
     if(4*w>p){long=true;out.longTop++;ck(rough(g),"rough return");out.roughChecks++;ck(candidate[b],"first candidate coverage");out.coveredLong++;}
     else{out.shortTop++;ck(d<=1-p/2,"negative repeat");out.shortNegative+=-d;}
     if(d>0){out.positiveTop++;tpos+=d;}
    }
   }
   e+=w;g+=p-1;out.events++;
   let h=2*e-g;if(h>peak){peak=h;peakLong=long;}
  }close();
  out.peakMean+=peak/N;out.repeatPositiveMean+=rpos/N;out.topRepeatPositiveMean+=tpos/N;out.longTopPaths+=+long;out.positivePeakPaths+=+(peak>0);out.peakAfterTopLong+=+peakLong;out.firstCandidatePaths+=+cand;
 }
 ck(out.longTop===out.coveredLong&&out.repeatTop===out.longTop+out.shortTop,"counts");
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?256:512)));
