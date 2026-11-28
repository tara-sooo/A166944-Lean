// Floating finite pilot of exact max-recursion inequalities; tolerances are not directed-rounding certificates.
function residualAudit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(x,m)=>((x%m)+m)%m;
 const primes=n=>{let a=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){a.push(p);while(n%p===0)n/=p;}if(n>1)a.push(n);return a;};
 function run(R,H,z,lambda,K){
   const L=Math.log(R),lo=2*Math.floor((R-4*H)/2),hi=2*R,N=(hi-lo)/2+1;
   const ff=Array.from({length:H},(_,h)=>[primes(Math.abs(2*h+3)),primes(Math.abs(2*h-3))]);
   const arr=new Array(N);
   const gains=Array.from({length:2*H+4},(_,p)=>p?Math.exp(-lambda*Math.log(L)*(p-1)/H):1);
   const recWeight=Math.exp(-1/K);
   function cell(x,h){
     const i=(x-lo)/2;let row=arr[i];if(!row){row=new Array(H+1);arr[i]=row;}
     let v=row[h];if(!v){v={F:null,C:null,TF:null,D:0};row[h]=v;}return v;
   }
   function set(v,name,m,w){
     if(!v[name])v[name]=new Map();
     const old=v[name].get(m)||0;if(w>old)v[name].set(m,w);
   }
   const max=m=>{let w=0;if(m)for(const a of m.values())if(a>w)w=a;return w;};
   function winner(x,h){
     const n=h+1-x/2,s=mod(n,2)===0?1:-1;
     for(const p of ff[h][s===1?0:1])if(mod(x+s,p)===0)return p;
     return 0;
   }
   function dest(x,h,p){return p?[x-p+1,h+1-(p-1)/2]:[x,h+1];}
   function send(v,name,m,w,p,h2){
     const record=p>0&&h2>m,m2=record?h2:m;
     set(v,name,m2,w*gains[p]*(record?recWeight:1));
   }
   let totalF=0,totalC=0,sumProjectedDebt=0,sumAugDebt=0,rawF=0,rawC=0,localLower=0,physicalChecks=0,sinkChecks=0,changed=0,multiM=0,projectedSavings=0,maxStates=0;
   let maxViolation=0;
   for(let x=hi;x>=lo;x-=2){
     if(x>=R&&x%6===0){
       const v=cell(x,3);for(const name of ["F","C","TF"])set(v,name,3,1);
     }
     const i=(x-lo)/2,row=arr[i];if(!row)continue;
     for(let h=0;h<=H;h++){
       const v=row[h];if(!v)continue;
       let rmax=0,rsum=0,diff=0;
       if(v.F)for(const [m,w] of v.F){
         let r=Math.max(0,w-(v.TF?.get(m)||0));
         rmax=Math.max(rmax,r);rsum+=r;
         diff=Math.max(diff,w-(v.C?.get(m)||0));
       }
       if(v.F?.size>1){multiM++;maxStates=Math.max(maxStates,v.F.size);}
       if(rsum>rmax+1e-12)projectedSavings++;
       sumProjectedDebt+=rmax;sumAugDebt+=rsum;
       const D=v.D+rmax;
       maxViolation=Math.max(maxViolation,diff-D);
       assert(diff<=D+1e-8,"projected maximum debt");
       physicalChecks++;
       if(h===H){
         const F=max(v.F),C=max(v.C);
         totalF+=F;totalC+=C;localLower+=Math.max(0,F-D);
         assert(F-C<=D+1e-8,"projected sink debt");sinkChecks++;
         continue;
       }
       const p=winner(x,h),q=p<=z?p:0;
       const [tx,th]=dest(x,h,p),[fx,fh]=dest(x,h,q);
       assert(th>=0&&th<=H&&fh>=0&&fh<=H,"height domain");
       if(p!==q){
         changed++;rawF+=max(v.F);rawC+=max(v.C);
       }
       if(fx>=lo&&v.F){
         const y=cell(fx,fh);for(const [m,w] of v.F)send(y,"F",m,w,q,fh);
       }
       if(tx>=lo){
         if(v.C||v.F||D){
           const y=cell(tx,th);
           if(v.C)for(const [m,w] of v.C)send(y,"C",m,w,p,th);
           if(v.F)for(const [m,w] of v.F)send(y,"TF",m,w,p,th);
           y.D=Math.max(y.D,D*gains[p]);
         }
       }
     }
     arr[i]=undefined;
   }
   assert(totalC+1e-6>=localLower,"localized projected lower");
   assert(totalC+1e-6>=totalF-sumProjectedDebt,"projected raw lower");
   assert(sumProjectedDebt<=rawF+1e-6,"physical changed key debt");
   assert(totalC+1e-6>=totalF-rawF&&totalF+1e-6>=totalC-rawC,"two-way trial stability");
   if(z>=2*H+3)assert(Math.abs(totalF-totalC)<1e-7&&rawF===0&&rawC===0,"full cutoff identity");
   return {R,H,z,lambda,K,totalF,totalC,rawF,rawC,sumProjectedDebt,sumAugDebt,localLower,physicalChecks,sinkChecks,changed,multiM,projectedSavings,maxStates,maxViolation};
 }
 const rows=[];
 for(const R of [12000,48000,192000]){
   const H=Math.floor(R**.4),K=Math.log(Math.log(R))**2;
   for(const z of [7,Math.floor(2*H/3),Math.floor(1.5*H),2*H+3])rows.push(run(R,H,z,13,K));
 }
 const totals=rows.reduce((a,b)=>{for(const k of ["physicalChecks","sinkChecks","changed","multiM","projectedSavings"])a[k]=(a[k]||0)+b[k];return a;},{});
 assert(totals.projectedSavings>0&&totals.multiM>0,"nonvacuous projection savings");
 return {totals,rows};
}
console.log(JSON.stringify(residualAudit(),null,2));
