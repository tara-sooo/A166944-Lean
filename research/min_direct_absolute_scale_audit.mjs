function audit(N=50000,P=499,rootCap=1000000){
 const cap=Math.max(8*N+10000,2*rootCap+10000),spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function factors(z){let a=[];if(z<1||z>cap)throw Error("factor range "+z);while(z>1){let p=spf[z];a.push(p);while(z%p===0)z/=p}return a}
 function next(t,H,adaptive){let b=Math.floor(Math.sqrt(H+1)),best=null;for(let e of [1,-1])for(let p of factors(H-e)){if(adaptive&&p>b)continue;let r=e===1?0:p+2,w=mod(r-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 function literal(t,H,adaptive,W){for(let w=1;w<=W;w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1){let p=spf[g];if(!adaptive||p*p<=H+1)return {p,e,w}}}return null}
 const pi=new Int32Array(Math.floor(Math.sqrt(cap))+2),A=new Float64Array(pi.length);
 for(let i=1;i<pi.length;i++){pi[i]=pi[i-1];A[i]=A[i-1];if(i>=3&&spf[i]===i){pi[i]++;A[i]+=i-1}}
 const L=[0,2,5,11];
 let s={N,P,rootCap,adaptiveEdges:0,windows:0,dyadicWindows:0,windowChecks:0,weightedChecks:0,recordChecks:0,distinctChecks:0,firstMismatch:0,compositeMismatch:0,primeMismatch:0,roughChecks:0,firstCounterexample:null,explicitCounterexample:null,linearScaleCounterexample:null,windowExamples:[],freshCases:0,freshRootChecks:0,freshUncutFound:0,freshAdaptiveFound:0,freshCommonFound:0,minimumDifferences:0,adaptiveBeforeCommon:0,freshExceptional:0,twinEquivalenceChecks:0,twinEquivalenceYes:0,exceptionTwinChecks:0,evenExceptionChecks:0,freshQuadraticChecks:0,freshCoarseChecks:0,smallestExamples:[],nestedChecks:0,nestedExamples:[],literalChecks:0};
 function checkRough(H,e,p,w){let q=(H-e)/p;if(!Number.isInteger(q)||q%2!==1)throw Error("cofactor");for(let z of [H-1,H+1]){let fs=factors(z),r=fs[0];if(2*r<w||2*r===w&&r<p)throw Error("rough factor");if((w/2)**3>H+1){let a=z,n=0;while(a>1){a/=spf[a];n++}if(n>2)throw Error("rough triple");s.roughChecks++}}
 if(q>1&&p*p>H+1){let r=spf[q];if(w>=2*r)throw Error("ignored cofactor");if(w>=2*Math.sqrt(q)&&r!==q)throw Error("prime cofactor")}
 return q}
 function checkWindow(M,X,Y,hs,word,dyadic){
 let i=hs.findIndex(v=>v>=X),j=hs.findIndex(v=>v>=Y),n=j-i,B=Math.floor(Math.sqrt(Y+1)),gain=hs[j]-hs[i],cc=new Map();
 if(i<0||j<0||j<=i)return;
 for(let h=i;h<j;h++)cc.set(word[h],(cc.get(word[h])||0)+1);
 let sorted=[...cc.values()].sort((a,b)=>b-a);if(hs[i]>X+Math.sqrt(X+1)||gain<Y-X-Math.sqrt(X+1)||n*(B-1)<gain)throw Error("crossing");
 if((sorted[0]||0)*A[B]<gain)throw Error("weighted multiplicity");s.weightedChecks++;
 for(let k=0;k<=3;k++){let m=sorted[k]||0,R=sorted.slice(k).reduce((a,b)=>a+b,0);if(n>(L[k]+1)*R+L[k]||R>m*pi[B]||n>(L[k]+1)*m*pi[B]+L[k])throw Error("multiplicity bound");s.windowChecks++}
 s.windows++;if(dyadic)s.dyadicWindows++;
 if(s.windowExamples.length<3||n>s.windowExamples.at(-1).n){let rec={M,X,Y,n,gain,B,distinct:cc.size,top:[...cc].sort((a,b)=>b[1]-a[1]).slice(0,5)};if(s.windowExamples.length<3)s.windowExamples.push(rec);else s.windowExamples[2]=rec}
 }
 for(let M=5;M<=N;M+=2){let H0=2*M-2,t=M+2,H=H0,hs=[H],word=[],counts=new Map(),record=0,maxCount=0,checkedMismatch=false;
 for(let i=0;i<150&&H+Math.floor(Math.sqrt(H+1))+1<=cap;i++){
 let a=next(t,H,true),u=next(t,H,false);
 if(!checkedMismatch){if(u.p*u.p>H+1){let q=checkRough(H,u.e,u.p,u.w),rec={M,t,H,...u,q,j:t+u.w-M-2,adaptive:a};s.firstMismatch++;if(q>1){s.compositeMismatch++;if(!s.firstCounterexample)s.firstCounterexample=rec;if(M===47)s.explicitCounterexample=rec;if(M>1000&&(!s.linearScaleCounterexample||rec.j/M<s.linearScaleCounterexample.j/s.linearScaleCounterexample.M))s.linearScaleCounterexample=rec}else s.primeMismatch++;if(M<=1000){let v=literal(t,H,false,u.w);if(JSON.stringify(v)!==JSON.stringify(u))throw Error("uncut literal");s.literalChecks++}checkedMismatch=true}else if(!a||JSON.stringify(a)!==JSON.stringify(u))throw Error("eligible earliest")}
 if(!a)break;let p=a.p;if(p>record){for(let R=1;R<=4;R++)if(maxCount<=R){if(p>=A.length||p*p>H0+1+R*A[p-1])throw Error("record bound");s.recordChecks++}if(maxCount<=1){if(3*p*p+4*p-3>4*(H0+1))throw Error("odd sum bound");s.distinctChecks++}record=p}
 counts.set(p,(counts.get(p)||0)+1);maxCount=Math.max(maxCount,counts.get(p));if(maxCount===1&&3*(H+p-1-H0)>H0+1)throw Error("distinct gain");
 checkRough(H,a.e,p,a.w);
 t+=a.w;H+=p-1;word.push(p);hs.push(H);s.adaptiveEdges++;
 }
 if(H>H0)checkWindow(M,H0,H,hs,word,false);
 if(word.length>=12)checkWindow(M,hs[3],hs[12],hs,word,false);
 for(let X=2**Math.ceil(Math.log2(H0));X*2<=H;X*=2)checkWindow(M,X,2*X,hs,word,true);
 }
 // Search all odd roots in the necessary fresh-label congruence class, in
 // increasing order, separately in the uncut and adaptive models.
 const seeds=[{T:0,E:0,events:[]},{T:1,E:2,events:[[1,3]]},{T:6,E:4,events:[[4,3],[5,3]]}];
 for(let seed of seeds)for(let p=3;p<=P;p+=2)if(spf[p]===p&&p>2*seed.T+7)for(let e of [1,-1]){
 let {T,E,events}=seed,k=mod(p,4)===mod(1-E,4)?1:3,j=(k*p+E-(e===1?7:1))/2,w=j-T;
 if(!Number.isInteger(j)||w<=0||w>=2*p)throw Error("fresh time");
 if(e===1){let U=(p+3-E)/2;if(Number.isInteger(U)&&U>=5&&U%2===1){let H=p+1,t=U+2+T,v=next(t,H,false);if(v?.p===p&&v.w===w)throw Error('even exception');s.evenExceptionChecks++}}
 let c=mod(2-E+e,p);if(c%2)c+=p;c/=2;let M=c;if(M%2===0)M+=p;while(M<5)M+=2*p;
 let firstU=null,firstA=null,firstCommon=null;
 function match(M,adaptive){let H=2*M-2,t=M+2;for(let [tick,label] of events){let v=next(t,H,adaptive);if(v?.p!==label||t+v.w!==M+2+tick)return null;t+=v.w;H+=v.p-1}
 let v=next(t,H,adaptive);if(v?.p!==p||v.e!==e||t+v.w!==M+2+j)return null;return {M,q:(H-e)/p,H}}
 for(;M<=rootCap;M+=2*p){s.freshRootChecks++;let u=match(M,false),a=match(M,true);
 if(u){let {H,q}=u,r=Math.floor(w/2)+1;if(q===1){s.freshExceptional++;if(e===1||k!==1)throw Error("exception orientation");if(w>2*Math.sqrt(p+2)){if(spf[p-2]!==p-2||next(M+2+j-w,H,true)!==null)throw Error("exception twins");s.exceptionTwinChecks++}}else{if(q<r||2*M<p*r+e+2-E)throw Error("quadratic lower bound");s.freshQuadraticChecks++}
 if((w/2)**3>H+1){if(q>1&&spf[q]!==q)throw Error("rough cofactor");s.freshCoarseChecks++}
 if(!firstU){firstU=u;s.freshUncutFound++}
 if(a&&!firstCommon){firstCommon=a;s.freshCommonFound++}
 }
 if(a&&!firstA){firstA=a;s.freshAdaptiveFound++}
 if(firstU&&firstA&&firstCommon)break;
 }
 if(p>=53&&e===-1&&((T===0&&p%4===1)||(T===1&&p%4===3))){let lin=(p+1-E)/2,isTwin=spf[p-2]===p-2;if((firstU?.M===lin)!==isTwin||isTwin&&(!firstA||firstA.M<=lin))throw Error('two-family twin equivalence');s.twinEquivalenceChecks++;if(isTwin)s.twinEquivalenceYes++}
 if(firstU&&firstA&&firstU.M!==firstA.M)s.minimumDifferences++;
 if(firstCommon&&firstA&&firstA.M<firstCommon.M)s.adaptiveBeforeCommon++;
 s.freshCases++;if([31,53,101,211,257,421].includes(p))s.smallestExamples.push({T,E,p,e,k,j,w,lower:Math.ceil((p*(Math.floor(w/2)+1)+e+2-E)/2),firstU,firstA,firstCommon})
 }
 // Same-side nested renewal lower bound on the quotient, arithmetic controls.
 for(let d of [3,5,7,31,105])for(let p=d+1;p<=499;p+=d)if(p%2&&spf[p]===p)for(let e of [1,-1]){
 for(let q=p;q<=p+6*d;q+=2){let H=p*q+e;if(H%2||mod(H-(e-1),d)!==0)continue;if(q<p+2*d-2)throw Error("nested gap");s.nestedChecks++;if(s.nestedExamples.length<8)s.nestedExamples.push({D:d,p,e,q,H,lower:p*(p+2*d-2)+e})}
 }
 return s
}

console.log(JSON.stringify(audit(Number(process.argv[2]||50000),Number(process.argv[3]||499),Number(process.argv[4]||1000000)),null,2));
