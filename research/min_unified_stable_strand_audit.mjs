// Standalone stable-strand entropy and clock packing audit. Finite diagnostic parameters are not the analytic scaling.
function stableStrandAudit(X,mode="diagnostic",eps=.5){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,spf=new Int32Array(7*X+10);
 for(let k=2;k<spf.length;k++)if(!spf[k]){spf[k]=k;if(k*k<spf.length)for(let j=k*k;j<spf.length;j+=k)if(!spf[j])spf[j]=k;}
 const mod=(a,m)=>((a%m)+m)%m,fail=(b,s)=>{if(!b)throw Error("X="+X+" "+mode+" "+s)},close=(a,b)=>Math.abs(a-b)<1e-6*(1+Math.abs(b)),factor=n=>{let out=[];while(n>1){const p=spf[n];fail(p>0,"SPF");if(p<=B)out.push(p);while(n%p===0)n/=p;}return out};
 const P=6,S=Math.max(P,P*Math.floor(B/(4*P))),D=mode==="wide"?2*S+2*B+1:4*S+1;
 const high=e=>e.p>=Math.max(5,Math.ceil(B/10))&&2*e.r>e.p;
 const paths=[],jumps=new Map(),vertices=new Map(),stride=7*X+10,key=(j,C)=>j*stride+C,jkey=e=>`${e.v}|${e.C}|${e.p}`;
 let literal=0,events=0,totalClock=0,rawHigh=0,maxGain=0;
 const gcd=(a,b)=>{while(b){let r=a%b;a=b;b=r}return a};
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   const s=M+2,C0=2*M-2,K=Math.floor((7*M-1)/4),es=[],cs=[];let t=s,C=C0;
   while(C-C0<T){
     let r=Infinity,v=Infinity,p=0;
     for(let sign of [-1,1])for(let q of factor(C+sign)){if(q===2)continue;r=Math.min(r,q);let a=sign===-1?0:q+2,vt=t+1+mod(a-t-1,2*q);if(vt<v||(vt===v&&q<p)){v=vt;p=q}}
     if(X<=1024&&literal<4000){let vv=Infinity,pp=0;for(let j=t+1;j<=Math.min(K,t+2*B);j++){let g=j%2?gcd(j-2,C+1):gcd(j,C-1);let q=g>1?factor(g).find(q=>q!==2):undefined;if(q){vv=j;pp=q;break}}
       fail((v>K||!p)?vv===Infinity:vv===v&&pp===p,"literal clock");literal++;
     }
     if(!p||v>K)break;
     const J=C+p-1,e={t,C,v,p,r,J};fail(v-t<=2*r&&v-t<=3*(p-1)&&C<=2*t&&J<=2*v,"event invariant");
     es.push(e);events++;totalClock+=v-t;if(high(e))rawHigh+=v-t;for(let j=t;j<v;j++)cs.push(C);t=v;C=J;
   }
   cs.push(C);const id=paths.length,path={M,s,C0,es,cs,end:t,endC:C,tokens:[]};paths.push(path);maxGain=Math.max(maxGain,C-C0);
   for(let e of es){const k=jkey(e);if(!jumps.has(k))jumps.set(k,[]);jumps.get(k).push(id)}
   for(let k=0;k<cs.length;k++){let j=s+k,c=cs[k],kk=key(j,c),V=vertices.get(kk);if(!V){V={n:0,b:0,next:0,entropy:0};vertices.set(kk,V)}V.n++;
     if(k+1<cs.length){let nk=key(j+1,cs[k+1]);if(V.b)fail(V.next===nk,"deterministic tick");else V.next=nk;V.b++;}
   }
 }
 let N=paths.length,sumE=0,sumDrop=0,sumMerge=0,expiries=0;
 for(let V of vertices.values()){
   expiries+=V.n-V.b;
   if(V.b){const U=vertices.get(V.next);fail(U&&U.n>=V.b,"intact branch");let x=Math.log(V.n/V.b),y=Math.log(U.n/V.b);V.entropy=x+y;sumDrop+=V.b*x;sumMerge+=V.b*y;sumE+=V.b*V.entropy;}
 }
 fail(expiries===N&&sumDrop<=N+1e-7&&sumMerge<=N*(1+Math.log(N))+1e-7&&sumE<=N*(2+Math.log(N))+1e-7,"entropy bound");
 let injectedEntropy=0;for(let a of paths)injectedEntropy+=Math.log(vertices.get(key(a.s,a.C0)).n);
 let loss=0;for(let V of vertices.values())loss+=V.n*Math.log(V.n)-(V.b?V.b*Math.log(V.b):0);
 fail(close(sumMerge+injectedEntropy,loss),"exact merge entropy telescope");
 function crossing(a,K){let lo=0,hi=a.es.length;while(lo<hi){let m=(lo+hi)>>1;if(a.es[m].J>K)hi=m;else lo=m+1}let e=a.es[lo];return e&&e.C<=K&&K<e.J?e:null;}
 let entropyPaid=0,endpointPaid=0,geometrySkipped=0,retained=0,allRetained=0,active=new Map(),minFraction=1,groupChecks=0;
 for(let id=0;id<N;id++){
   let a=paths[id],ts=a.tokens;
   for(let k=0;k+1<a.cs.length;k++){let V=vertices.get(key(a.s+k,a.cs[k]));if(V.entropy>0)ts.push([a.cs[k],V.entropy]);}
   let l=0,r=0,vsum=0;
   for(let e of a.es){
     while(r<ts.length&&ts[r][0]<=e.C+D){vsum+=ts[r++][1]}
     while(l<r&&ts[l][0]<e.C-D){vsum-=ts[l++][1]}
     const w=e.v-e.t;
     if(vsum>eps+1e-9){entropyPaid+=w;continue}
     if(e.C-a.C0<D||a.endC-e.C<D){endpointPaid+=w;continue}
     allRetained+=w;if(!high(e))continue;
     let K=S*Math.floor((e.C-1)/S),past=crossing(a,K-S),future=crossing(a,K+2*S);
     if(!past||!future||past.C<e.C-D||future.C>e.C+D){geometrySkipped+=w;fail(mode!=="wide","wide geometry");continue}
     let gk=K+"|"+jkey(past),g=active.get(gk);
     if(!g){let members=jumps.get(jkey(past)).filter(i=>paths[i].endC>K+2*S);g={K,past,future,members,rep:id,ret:0,V:0};active.set(gk,g);}
     fail(g.members.includes(id)&&g.future.v===future.v&&g.future.J===future.J,"cohort witness");
     let n=vertices.get(key(e.t,e.C)).n,nA=g.members.length;fail(nA<=n&&nA+1e-7>=n*(1-Math.exp(eps)*eps),"stable mass");
     minFraction=Math.min(minFraction,nA/n);g.ret+=w;retained+=w;groupChecks++;
   }
 }
 fail(entropyPaid<=3*(2*D+B)*sumE/eps+1e-6,"linear entropy deletion");
 fail(endpointPaid<=6*N*(D+B)+1e-6,"endpoint deletion");
 let occupancy=new Map(),intervals=new Map(),thin=0,slow=0,low=0,weighted=0,unweighted=0,memberships=0,spanChecks=0,highChecks=0,maxMass=0,linkChecks=0,boundaryGroups=new Map();
 for(let g of active.values()){
   let a=paths[g.rep],n=g.members.length;maxMass=Math.max(maxMass,n);memberships+=n;
   let lo=g.past.v-1,hi=g.future.v;
   let seen=occupancy.get(g.K);if(!seen){seen=new Set();occupancy.set(g.K,seen)}
   for(let j=lo;j<=hi;j++){let C=a.cs[j-a.s],k=key(j,C);fail(!seen.has(k),"disjoint active spans");seen.add(k);spanChecks++;}
   for(let id of g.members){let b=paths[id];for(let j=lo;j<=hi;j++)fail(b.cs[j-b.s]===a.cs[j-a.s],"all original members share actual span")}
   for(let e of a.es)if(g.K<e.C&&e.C<=g.K+S&&high(e)){
     let w=e.v-e.t;g.V+=w;highChecks++;
     if(!intervals.has(e.C))intervals.set(e.C,[]);intervals.get(e.C).push([e.t,e.v]);
   }
   fail(g.ret<=n*g.V&&g.V<=3*(S+B),"common occupation");
   if(n<=8)thin+=g.ret;else if(g.V<=S/4)low+=g.ret;else slow+=g.ret;
   weighted+=n*g.V;unweighted+=g.V;
   for(let L=g.K-S;L<=g.K+2*S;L+=P){let e=crossing(a,L);fail(e&&e.p>3,"strict primorial crossing");}
   for(let L of [g.K,g.K+S]){let e=crossing(a,L),k=L+"|"+jkey(e),old=boundaryGroups.get(k);if(old){fail(old.K!==g.K&&Math.abs(old.K-g.K)===S,"unique adjacent link");let U=vertices.get(key(e.v,e.J)),common=g.members.filter(i=>old.members.includes(i)).length;fail(common+1e-7>=U.n*(1-2*Math.exp(eps)*eps),"adjacent intersection");linkChecks++;}else boundaryGroups.set(k,g);}
 }
 let slabSum=0;
 for(let [C,list] of intervals){list.sort((a,b)=>a[0]-b[0]);let len=0,last=-Infinity;for(let [a,b] of list){fail(a>=last,"disjoint waiting intervals");last=b;len+=b-a}
   fail(len<=3*H+2*B+6,"clock slab");slabSum+=len;
 }
 fail(slabSum===unweighted&&memberships*S<=N*(H+S)&&thin+low+slow===retained,"clock partitions");
 return {X,mode,eps,B,T,P,S,D,N,events,vertices:vertices.size,maxGain,literal,totalClock,rawHigh,entropy:+sumE.toFixed(3),entropyPaid,endpointPaid,allRetained,geometrySkipped,retained,active:active.size,maxMass,minFraction:+minFraction.toFixed(6),groupChecks,spanChecks,highChecks,linkChecks,unweighted,weighted,thin,low,slow};
}
const args=process.argv.slice(2);const mode=args[0]||"diagnostic";const eps=Number(args[1]||".5");for(const X of (args.length>2?args.slice(2).map(Number):[256,1024,4096,16384]))console.log(JSON.stringify(stableStrandAudit(X,mode,eps)));
