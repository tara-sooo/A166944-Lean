// Finite layer-cake check for hard-budget minimum-record scores. Not an asymptotic numerical certificate.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(a,b)=>((a%b)+b)%b;
 const f=new Int32Array(384100);
 for(let p=2;p<f.length;p++)if(!f[p]){f[p]=p;if(p*p<f.length)for(let n=p*p;n<f.length;n+=p)if(!f[n])f[n]=p;}
 function run(R,H,z){
   const out=new Map();
   for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
     let x=A,h=3,M=3,k=0;
     while(A-x<=4*H){
       let w=Infinity,p=0,n=h-x/2;
       for(const s of [1,-1]){
         let v=x+s;
         while(v>1){
           const q=f[v];assert(q>0,"factor range");
           if(q>z)break;
           let t=mod((s===1?0:q+2)-n,2*q);if(!t)t=2*q;
           if(t<w||(t===w&&q<p)){w=t;p=q;}
           while(v%q===0)v/=q;
         }
       }
       if(h+w-1>=H){const old=out.get(x);if(old===undefined||k<old)out.set(x,k);break;}
       x-=p-1;h+=w-(p-1)/2;
       assert(h>=0&&h<H,"height");
       if(h>M){M=h;k++;}
     }
   }
   return out;
 }
 const rows=[];let totalSites=0,profileChecks=0,strictCancellation=0,nontrivialSameSite=0,staticControls=0,staticExtra=0;
 for(const R of [12000,48000,192000]){
   const H=Math.floor(R**.4),A=run(R,H,Infinity);
   for(const z of [Math.floor(2*H/3),Math.floor(H/3),Math.max(9,Math.floor(H/6))]){
     const B=run(R,H,z);
     const X=[...new Set([...A.keys(),...B.keys()])],Kmax=Math.max(...A.values(),...B.values());
     const dHist=new Int32Array(Kmax+2), bHist=new Int32Array(Kmax+2);
     let sharedUnequal=0;
     for(const x of X){
       const a=A.get(x)??Infinity,b=B.get(x)??Infinity;
       if(a!==b){
         const lo=Math.min(a,b),hi=Math.max(a,b);
         dHist[lo]++;if(Number.isFinite(hi))dHist[hi]--;
         if(Number.isFinite(a)&&Number.isFinite(b))sharedUnequal++;
       }
       if(Number.isFinite(b))bHist[b]++;
     }
     let count=0;
     for(let k=0;k<=Kmax;k++){
       count+=dHist[k];let exact=0;for(const x of X)if(((A.get(x)??Infinity)<=k)!==((B.get(x)??Infinity)<=k))exact++;
       assert(count===exact,"level-set exact");
     }
     let sz=0;
     for(let x=6*Math.ceil(R/6);x<=2*R;x+=6)if(Math.min(f[x-1],f[x+1])>z){assert(B.get(x)===0,"static inclusion");sz++;}
     staticControls+=sz;staticExtra+=B.size-sz;nontrivialSameSite+=sharedUnequal;totalSites+=X.length;
     for(const K of [1,3,10,100]){
       const aWeight=x=>Math.exp(-(A.get(x)??Infinity)/K), bWeight=x=>Math.exp(-(B.get(x)??Infinity)/K);
       let lhs=0,ta=0,tb=0;for(const x of X){const a=aWeight(x),b=bWeight(x);lhs+=Math.abs(a-b);ta+=a;tb+=b;}
       let rhs=0,d=0,tHist=0;
       for(let j=0;j<=Kmax;j++){
         d+=dHist[j];const kernel=j===Kmax?Math.exp(-j/K):Math.exp(-j/K)-Math.exp(-(j+1)/K);
         rhs+=d*kernel;tHist+=bHist[j]*Math.exp(-j/K);
       }
       assert(Math.abs(lhs-rhs)<=1e-7*Math.max(1,lhs),"layer cake identity");
       assert(Math.abs(tb-tHist)<=1e-7*Math.max(1,tb),"weighted histogram");
       assert(tb+1e-8>=sz&&tb<=B.size+1e-8,"static score sandwich");
       if(lhs>Math.abs(ta-tb)+1e-8)strictCancellation++;
       profileChecks++;
       if(K===10)rows.push({R,H,z,K,actualWeight:ta,trialWeight:tb,staticCenters:sz,L1:lhs,layerCake:rhs,sharedUnequal,Kmax});
     }
   }
 }
 assert(strictCancellation>0&&nontrivialSameSite>0,"nonvacuous L1 transfer");
 return {totalSites,profileChecks,strictCancellation,nontrivialSameSite,staticControls,staticExtra,rows};
}
console.log(JSON.stringify(audit(),null,2));
