// Fourth-root roughness and three-factor cube packing diagnostics.
function audit(N=200000,steps=180){
 const cap=4*N+20000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function factors(z){let fs=[];while(z>1){let p=spf[z];if(!p)throw Error("range");fs.push(p);z/=p}return fs}
 function next(t,H){let best=null;for(let e of [1,-1])for(let p of new Set(factors(H-e))){if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={p,e,w}}return best}
 function literal(t,H){for(let w=1;w<=2*Math.floor(Math.sqrt(H+1));w++){let n=t+w,e=n%2?-1:1,g=gcd(n%2?n-2:n,H-e);if(g>1&&spf[g]**2<=H+1)return {p:spf[g],e,w}}return null}
 const s={N,steps,events:0,paths:0,truncated:0,windows:0,positiveDemand:0,smallBranch:0,primeBranch:0,tripleBranch:0,primeEvents:0,tripleEvents:0,roughFactorChecks:0,cubeBandChecks:0,cubeBandGroups:0,cubeBandEvents:[0,0,0,0],literalChecks:0,largestTriple:null,closestTriple:null};
 function window(ev,i,j,endH,endT){
 let Y=endH,G=Y-ev[i].H,W=endT-ev[i].t,d=2*ev[i].t-ev[i].H,B=1+Math.floor(8*Math.sqrt(Math.sqrt(Y+1)));
 while((B-1)**4>4096*(Y+1))B--;while(B**4<=4096*(Y+1))B++;
 let U=0,V2=0,V3=0,groups=[new Map(),new Map(),new Map(),new Map()],last=new Map();
 const den=[1,2,4,200];
 for(let k=i;k<j;k++){let z=ev[k],{p,e,w,H}=z,g=p-1;if(p<=B){U+=g;continue}if(4*w<g)continue;
 let a=factors(H-e),b=factors(H+e);
 for(let f of [...a,...b]){if(2*f<w||BigInt(f)**4n<=BigInt(Y+1))throw Error("rough");s.roughFactorChecks++}
 if(a.length<2||a.length>3||b.length>3||!a.includes(p))throw Error("factor count");
 let q=(H-e)/p;if(last.has(p)&&q<=last.get(p))throw Error("repeat");last.set(p,q);
 if(a.length===2){V2+=g;s.primeEvents++;if(spf[q]!==q)throw Error("prime");continue}
 V3+=g;s.tripleEvents++;
 if((p-1)**2*p>64*(Y+1)||p**3>144*(Y+1)||q*64<(p-1)**2)throw Error("triple scale");
 let S=a.reduce((x,y)=>x+y,0),D=Math.max(...a.map(f=>Math.abs(3*f-S)));
 if(!s.largestTriple||p>s.largestTriple.p)s.largestTriple={...z,Y,q,factors:a,S,D};
 if(!s.closestTriple||D*D*s.closestTriple.S<s.closestTriple.D**2*S)s.closestTriple={...z,Y,q,factors:a,S,D};
 for(let l=0;l<den.length;l++){let b=den[l];if(S<12||D*D*b*b>3*S)continue;s.cubeBandEvents[l]++;
 if(27*H>S**3+27||27*b*b*H<b*b*S**3-6*S*S-27*b*b||6*p>3*S)throw Error("cube band");
 let old=groups[l].get(S)||0;groups[l].set(S,old+g);s.cubeBandChecks++;}
 }
 if(11*(U+V2+V3)<G-2*d||4*W>G+11*(U+V2+V3))throw Error("interval");
 s.windows++;let D0=G-2*d;if(D0>0){s.positiveDemand++;if(33*U>=D0)s.smallBranch++;if(33*V2>=D0)s.primeBranch++;if(33*V3>=D0)s.tripleBranch++;if(33*Math.max(U,V2,V3)<D0)throw Error("trichotomy");}
 for(let l=0;l<den.length;l++)for(let [S,g] of groups[l]){let b=den[l];if(9*b*b*g>2*S*S+6*b*b*S+18*b*b)throw Error("cube packing");s.cubeBandGroups++}
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,ev=[];for(let i=0;i<steps;i++){if(H+Math.sqrt(H+1)+1>=cap){s.truncated++;break}let a=next(t,H);if(!a)break;if(M<=1000){if(JSON.stringify(a)!==JSON.stringify(literal(t,H)))throw Error("literal");s.literalChecks++}
 ev.push({...a,M,H,t});H+=a.p-1;t+=a.w;s.events++}
 if(ev.length){s.paths++;window(ev,0,ev.length,H,t);if(ev.length>=4)window(ev,Math.floor(ev.length/2),ev.length,H,t)}
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||200000),Number(process.argv[3]||180)),null,2));
