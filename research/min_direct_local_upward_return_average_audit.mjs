// Local repeated upward source pairs and averaged singular factor arithmetic.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"factor range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g,q:(H-1+2*I)/p}}}return z}
 function union(a){let out=[];for(let [l,r] of a.sort((a,b)=>a[0]-b[0])){if(out.length&&l<=out.at(-1)[1])out.at(-1)[1]=Math.max(r,out.at(-1)[1]);else out.push([l,r])}return out}
 const st={roots:0,events:0,cap:0,controls:0,guardBins:0,sourceEvents:0,sourceLabels:0,pairs:0,shortPairs:0,longPairs:0,firstEvents:0,roughChecks:0,rootCollisionChecks:0,partitionChecks:0,spanChecks:0,sourceFluxChecks:0,guardWidthChecks:0,syntheticPatterns:0,syntheticResidues:0,syntheticAverage:0,smallFactorChecks:0,weightedSubsetChecks:0,meanMax:0,examples:[]};
 function collision(p,m,e,f,l){let b=[0,-2*m,mod(-2*e*inv(p,l),l),mod(-2*m-2*f*inv(p,l),l)].map(x=>mod(x,l));let bad=mod(m,l)===0||mod(p*m+f,l)===0||mod(p*m-e,l)===0||mod(p*m+f-e,l)===0;ok((new Set(b).size<4)===bad,"collision exact");return b}
 function inspect(rows,T,mode){
   let L=4*T*T,k=Math.floor(Math.sqrt(T)),groups=new Map,K=4;
   for(let z of rows){let j=Math.floor(z.H/L),a=groups.get(j)||[];a.push(z);groups.set(j,a)}
   for(let v of groups.values()){
     let sel=v.filter(z=>z.p>=T&&z.dp>6&&k*z.w<z.g);if(mode&&sel.length)sel=sel.filter(z=>Math.abs(z.dp-sel[0].dp)<=T);if(!sel.length)continue;
     let E=union(sel.map(z=>[z.dp,z.dp+z.g])),M=E.reduce((a,[l,r])=>a+r-l,0),phi=d=>E.reduce((a,[l,r])=>a+Math.max(0,Math.min(d,r)-l),0);
     let by=new Map,total=0,first=0,short=0,long=0,weighted=0;
     for(let z of v){let flux=phi(z.dp)-phi(z.d);if(z.p<T||flux<=0)continue;ok(2*z.w>z.g&&flux<=Math.min(M,3*z.p+1),"flux");st.sourceFluxChecks++;total+=flux;st.sourceEvents++;let a=by.get(z.p)||[];a.push({...z,flux});by.set(z.p,a)}
     for(let [p,a] of by){st.sourceLabels++;weighted+=Math.min(1,M/p);first+=a[0].flux;st.firstEvents++;let gaps=0,large=0;
       for(let i=1;i<a.length;i++){let u=a[i-1],z=a[i],m=(z.q-u.q)/2;ok(Number.isInteger(m)&&m>=1&&z.H-u.H===2*m*p+z.e-u.e,"return");st.pairs++;gaps+=m;
         if(m<=K){short+=z.flux;st.shortPairs++;if(st.examples.length<3)st.examples.push({T,L,M,p,m,q:u.q,q2:z.q,H:u.H,H2:z.H,flux:z.flux,e:u.e,f:z.e})}
         else {long+=z.flux;large++;st.longPairs++}
         for(let l of pr){if(l>=p||4*l>=Math.min(u.g,z.g))break;if(l<=4)continue;let b=collision(p,m,u.e,z.e,l);ok(b.every(r=>mod(u.q,l)!==r),"actual rough");st.roughChecks++;st.rootCollisionChecks++}
       }
       ok(2*p*gaps<=L+2&&large*(K+1)<=gaps,"gap span");st.spanChecks++;
     }
     ok(total===first+short+long&&first<=4*Math.max(T,...v.map(z=>z.p))*weighted+1e-8,"flux partition");st.partitionChecks++;st.guardBins++;ok(M<=sel.reduce((a,z)=>a+z.g,0),"width");st.guardWidthChecks++;
   }st.controls++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
 for(let T of [9,17,31,61])for(let m of [0,1])inspect(rows,T,m)}
 // Exact finite root-collision polynomial, including l=p excluded from the mean.
 for(let p of [11,17,31,61,101,251])for(let e of [-1,1])for(let f of [-1,1])for(let m=1;m<=120;m++){for(let l of pr){if(l>67)break;if(l<=4||l===p)continue;collision(p,m,e,f,l);st.syntheticResidues++}st.syntheticPatterns++}
 // Test truncated weighted-divisor inequality via exact subset weights.
 // These small controls test the algebra, not the asymptotic Mertens constant.
 for(let p of [11,31,101,251])for(let e of [-1,1])for(let f of [-1,1])for(let K of [64,256,1024]){
   let mean=0,smallMean=0;
   for(let m=1;m<=K;m++){let fs=new Set();for(let n of [m,p*m+f,p*m-e,p*m+f-e])for(let l of factors(Math.abs(n)))if(l>4&&l!==p)fs.add(l);
     let J=1;for(let l of fs)J*=l/(l-4);mean+=J;
     let small=[...fs].filter(l=>l<=13),P=small.reduce((a,l)=>a*l/(l-4),1),W=0,S=0,logmean=0;
     for(let mask=0;mask<2**small.length;mask++){let d=1,w=1;for(let i=0;i<small.length;i++)if(mask>>i&1){d*=small[i];w*=4/(small[i]-4)}W+=w;if(d<=K)S+=w;logmean+=w*Math.log(d);st.weightedSubsetChecks++}
     ok(Math.abs(W-P)<=1e-8*P&&Math.abs(logmean/P-small.reduce((a,l)=>a+4*Math.log(l)/l,0))<1e-8,"weighted mean");
     if(logmean/P<=.5*Math.log(K))ok(P<=2*S+1e-8,"Markov cutoff");smallMean+=S;st.smallFactorChecks++;
   }
   st.meanMax=Math.max(st.meanMax,mean/K);ok(Number.isFinite(mean)&&smallMean>=K,"mean finite");st.syntheticAverage++;
 }
 ok(st.shortPairs&&st.longPairs&&st.syntheticResidues&&st.partitionChecks,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
