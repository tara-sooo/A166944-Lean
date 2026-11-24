// Selberg-majorant audit for canonical MIN source-weighted energy.
// Run: node research/min_prime_source_selberg_audit.mjs 256 1024 4096 16384 65536 262144
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)), T=Math.floor(B*Math.pow(Math.log(B),1.5));
 const spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){
   spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 }
 const check=(v,m)=>{if(!v)throw Error(m)};
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a};
 const ds=[...new Set([Math.max(3,Math.floor(Math.sqrt(B))), Math.max(3,Math.floor(B**0.75)), Math.max(3,Math.floor(B/2))])];
 function weights(D){
   const mu=new Int32Array(D+1),phi=new Float64Array(D+1);
   mu[1]=1;phi[1]=1;
   for(let d=2;d<=D;d++){const p=spf[d],m=d/p;mu[d]=m%p===0?0:-mu[m];phi[d]=phi[m]*(m%p===0?p:p-1);}
   let G=0;const support=[];
   for(let d=1;d<=D;d+=2)if(mu[d]){G+=1/phi[d];support.push(d);}
   const lambda=new Float64Array(D+1);
   for(const d of support){
     let g=0;for(const k of support){if(k*d>D)break;if(gcd(k,d)===1)g+=1/phi[k];}
     lambda[d]=mu[d]*d/phi[d]*g/G;check(Math.abs(lambda[d])<=1+1e-10,'lambda bound');
   }
   let quad=0;for(const d of support)for(const e of support)quad+=lambda[d]*lambda[e]/(d*e/gcd(d,e));
   check(Math.abs(quad-1/G)<1e-8,'Selberg quadratic identity');
   const s=new Float64Array(X/2);
   for(const d of support){
     let m=Math.ceil((X+1)/d)*d;if(m%2===0)m+=d;
     for(;m<2*X;m+=2*d)s[(m-X-1)/2]+=lambda[d];
   }
   let sum=0,max=0;for(let i=0;i<s.length;i++){s[i]*=s[i];sum+=s[i];max=Math.max(max,s[i]);}
   return {D,G,s,sum,max,quad};
 }
 const ws=ds.map(weights), len=7*X/2+1;
 const W=new Int32Array(len), P=new Int32Array(len), L=new Int32Array(len), LP=new Int32Array(len), F=new Int32Array(len), FP=new Int32Array(len);
 for(const w of ws){w.S=new Float64Array(len);w.SL=new Float64Array(len);w.SF=new Float64Array(len);}
 let events=0,primeEvents=0,roots=0,primeBad=0,travel=0,literal=0;
 function hit(t,C,K){
   let T=K+1,P=0;
   for(const side of [-1,1]){
     let v=C+side;while(v>1){let p=spf[v];if(p>B)break;
       const m=2*p,r=side===-1?0:p+2,u=t+1+((r-(t+1)%m+m)%m);
       if(p>2&&(u<T||(u===T&&u<=K&&p<P))){T=u;P=p;}
       while(v%p===0)v/=p;
     }
   }return [T,P];
 }
 for(let M=X+1;M<2*X;M+=2){
   const i=(M-X-1)/2,prime=spf[M]===M,rootC=2*M-2,K=Math.floor((7*M-1)/4);
   let t=M+2,C=rootC;
   if(prime){roots++;travel+=K-t;for(const w of ws)check(Math.abs(w.s[i]-1)<1e-10,'prime majorant');}
   for(;;){
     const [u,p]=hit(t,C,K);
     if(X<=1024){let a=K+1,b=0;for(let j=t+1;j<=K;j++){
       const g=gcd(j%2?j-2:j,j%2?C+1:C-1);
       if(g>1&&spf[g]<=B){a=j;b=spf[g];break}
     }check(a===u&&b===p,'literal MIN');literal++;}
     if(!p){if(prime&&(spf[C-1]!==C-1||spf[C+1]!==C+1)){primeBad++;check(K-t<2*B,'terminal quiet');}break;}
     const j=C/2,late=C-rootC>B,far=C-rootC>T;
     W[j]++;events++;if(prime){P[j]++;primeEvents++;}
     if(late){L[j]++;if(prime)LP[j]++;}
     if(far){F[j]++;if(prime)FP[j]++;}
     for(const w of ws){w.S[j]+=w.s[i];if(late)w.SL[j]+=w.s[i];if(far)w.SF[j]+=w.s[i];}
     t=u;C+=p-1;
   }
 }
 let S0=0;
 const out=[];
 for(const [label,A,AP,field] of [['full',W,P,'S'],['lateB',L,LP,'SL'],['lateT',F,FP,'SF']]){
   let E=0,EP=0,R=0,RP=0;const rows=ws.map(w=>({D:w.D,G:w.G,ES:0,err:0,cross:0,RS:0,mean:w.sum/(X/2),maxWeight:w.max,scalarErr:0}));
   for(let C=2*X;C<7*X;C+=2){
     const i=C/2,r=Math.min(spf[C-1],spf[C+1]);if(r>B){check(A[i]===0,'eligible');continue;}
     if(label==='full')S0+=r;
     E+=r*A[i]**2;EP+=r*AP[i]**2;R+=r*A[i];RP+=r*AP[i];
     for(let j=0;j<ws.length;j++){
       const w=ws[j],o=rows[j],s=w[field][i],m=A[i]/w.G,d=s-m;
       check(s+1e-7>=AP[i],'pointwise majorant');o.ES+=r*s*s;o.err+=r*d*d;o.cross+=2*r*m*d;o.RS+=r*s;o.scalarErr+=r*d;
     }
   }
   for(const o of rows){
     o.main=E/(o.G*o.G);o.bound=(Math.sqrt(o.main)+Math.sqrt(o.err))**2;
     check(Math.abs(o.ES-o.main-o.err-o.cross)<=1e-7*Math.max(1,o.ES),'exact energy expansion');
     check(EP<=o.ES+1e-7*Math.max(1,o.ES)&&o.ES<=o.bound+1e-7*Math.max(1,o.bound),'energy sandwich');
     o.errScale=o.err/(X*X*B);o.mainScale=o.main/(X*X*B);
   }
   out.push({label,E,EP,R,RP,rows});
 }
 return {X,B,T,roots,events,primeEvents,literal,primeBad,travel,S0,out};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[256,1024,4096,16384,65536,262144])console.log(JSON.stringify(audit(X)));
