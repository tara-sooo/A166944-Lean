// Landing-divisor boundary audit and periodic low-cost envelope.
function audit(X){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,spf=new Int32Array(7*X+4);
 for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const ck=(x,m="assertion")=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,gcd=(a,b)=>{while(b){let c=a%b;a=b;b=c}return a};
 function hit(t,C,K){let n=K+1,p=0;for(let s of [-1,1]){let v=C+s;while(v>1){let q=spf[v];if(q>B)break;let u=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(u<n||(u===n&&q<p)){n=u;p=q}while(v%q===0)v/=q}}return [n,p]}
 let out=[];
 for(let Y of [11,13])for(let mode of ["fullInverse","cellInverse"]){
  let L=2;for(let p=3;p<Y;p++)if(spf[p]===p)L*=p;
  const A=Math.max(2,Math.floor(B/4))*B,T=Math.max(Math.floor(L/4)+1,Math.ceil(X/256)),cell=C=>Math.floor((C-1)/L),pCap=p=>Math.ceil(A/p);
  const head=new Int32Array(7*X/2+2).fill(-1),next=new Int32Array(N),t=new Int32Array(N),K=new Int32Array(N),prevP=new Int32Array(N),prevC=new Int32Array(N),cost=new Float64Array(N),admit=new Map();
  let bands=[...new Set([Y,31,Math.ceil(Math.sqrt(B)),Math.ceil(B/2),Math.ceil(L*Math.log(B))])].sort((a,b)=>a-b).map(Q=>({Q,m:0,keys:0,I:0,maxLandingFactors:0,landingBound:0,capacity:0}));let heights=[...new Set([Math.max(1,Math.floor(B/4)),B,Math.max(1,Math.floor(X/Math.log(Y)**4))])].sort((a,b)=>a-b).map(A0=>({A0,small:0,large:0,highSmall:0,lowSmall:0,bound:0,keys:0}));let R=0,Rlo=0,Rhi=0,S=0,SCell=0,SPrime=0,twin=0,bad=0,events=0,literal=0,cellCount=0,maxAdmit=0,stoppedCells=0,rootsCell=0,maxCellLow=0,primeKeys=0,cellKeys=0,cellI=0,cellH=0,cellU=0,primeI=0,primeH=0,primeU=0,topMass=0,topKeys=0,topI=0,topH=0,topU=0,topPhysical=0,entryChecks=0,executedCellAdmits=0,primeStops=[],cellStops=[];
  const add=(i,C,entry)=>{next[i]=head[C/2];head[C/2]=i;if(entry)admit.set(cell(C),(admit.get(cell(C))||0)+1)};
  for(let i=0;i<N;i++){let M=X+2*i+1;t[i]=M+2;K[i]=Math.floor((7*M-1)/4);add(i,2*M-2,true)}
  function moments(v,a=8){let n0=Math.min(...v.cl.keys()),U=0,J=0,large=0;for(let [n,m] of v.cl){let j=(n-n0)/(2*v.p);ck(Number.isInteger(j)&&j>=0);U+=Math.min(a,m);J+=j*Math.min(a,m);if(m>a)large+=m;}ck(v.H>=4*v.p*J&&2*a*J>=U*U-a*U);ck(U<=a+Math.sqrt(a*v.H/(2*v.p))+1e-7);return {U,large}}
  let start=cell(2*X),end=cell(7*X-2);
  for(let b=start;b<=end;b++){
   let m=admit.get(b)||0;if(!m)continue;cellCount++;maxAdmit=Math.max(maxAdmit,m);let J=b*L,lo=Math.max(2*X,J+2),hi=Math.min(7*X-2,J+L),baseRlo=Rlo,roots=0,stoppedHere=0,entryN=0;
   if(mode==="cellInverse"&&m>=T){
    stoppedCells++;let gates=new Map();
    for(let C=lo;C<=hi;C+=2){let i=head[C/2];head[C/2]=-1;while(i>=0){let j=next[i];entryN++;S++;SCell++;let p=prevP[i],D=prevC[i];if(!p){rootsCell++;roots++;ck(C===2*(X+2*i+1)-2)}else{
      ck(p>=Y&&D<=J&&D+p-1===C&&C>J&&D>J-p+1,"boundary");ck((D-1)%p===0||(D+1)%p===0);entryChecks++;
      let key=D*B+p,h=2*t[i]-C,v=gates.get(key)||{p,D,m:0,H:0,cl:new Map()};ck(h>=0&&h<=6+4*cost[i]);v.m++;v.H+=h;v.cl.set(t[i],(v.cl.get(t[i])||0)+1);gates.set(key,v);
     }i=j}}
    ck(entryN===m&&roots<=Math.floor(L/4)+1);let perP=new Map();
    let land=new Map();for(let v of gates.values()){let C=v.D+v.p-1;ck(C>J&&C<=J+L&&(C%v.p===0||(C+2)%v.p===0),"landing divisor");if(!land.has(C))land.set(C,new Set());ck(!land.get(C).has(v.p));land.get(C).add(v.p);}
    for(let w of bands){let Q=w.Q,local=0,lg=0;
      for(let [C,qs] of land){let k=[...qs].filter(q=>q>=Q).length;ck(k<=2*Math.log(7*X+2)/Math.log(Q)+1e-9);w.maxLandingFactors=Math.max(w.maxLandingFactors,k);lg+=k}
      for(let v of gates.values())if(v.p>=Q){w.m+=v.m;w.keys++;w.I+=1/v.p;local+=v.m;ck(v.m<A/v.p+1e-8)}
      let bound=L*Math.log(7*X+2)/(Q*Math.log(Q));ck(lg<=L*Math.log(7*X+2)/Math.log(Q)+1e-8);ck(local<=A*bound+1e-6);
      w.landingBound+=bound;w.capacity+=A*bound;
    }
    for(let w of heights){let c=0;for(let v of gates.values()){let lowClass=0;for(let [n,z] of v.cl){let h=2*n-(v.D+v.p-1);if(z<=8){w.small+=z;if(h<=w.A0){w.lowSmall+=z;lowClass+=z;}else w.highSmall+=z;}else w.large+=z;}
      ck(lowClass<=8*(1+w.A0/(4*v.p))+1e-8);c+=8*(1+w.A0/(4*v.p));w.keys++;}
      w.bound+=c;ck(w.lowSmall<=w.bound+1e-8);
    }
    for(let v of gates.values()){perP.set(v.p,(perP.get(v.p)||0)+1);ck(perP.get(v.p)<=2,"two gates per prime");let z=moments(v);cellKeys++;cellI+=1/v.p;cellH+=v.H;cellU+=z.U;if(v.p>=Math.ceil(B/2)){topMass+=v.m;topKeys++;topI+=1/v.p;topH+=v.H;topU+=z.U;topPhysical+=z.large}}
    cellStops.push({b,J,m,roots,gates:gates.size});continue;
   }
   executedCellAdmits+=m;
   for(let C=lo;C<=hi;C+=2){let i=head[C/2];if(i<0)continue;let groups=new Map(),r=Math.min(spf[C-1],spf[C+1]);
    while(i>=0){let j=next[i],[n,p]=hit(t[i],C,K[i]);if(X<=1024){let nn=K[i]+1,pp=0;for(let k=t[i]+1;k<=K[i];k++){let g=gcd(k%2?k-2:k,C+(k%2?1:-1));if(g>1&&spf[g]<=B){nn=k;pp=spf[g];break}}ck(nn===n&&pp===p,"literal");literal++}
     if(!p){if(spf[C-1]===C-1&&spf[C+1]===C+1)twin++;else bad++}
     else if(p<Y){let C1=C+p-1;ck(cell(C1)===b,"low stays");R+=r;Rlo+=r;cost[i]+=r;events++;t[i]=n;prevP[i]=p;prevC[i]=C;add(i,C1,false)}
     else{if(!groups.has(p))groups.set(p,[]);groups.get(p).push([i,n])}i=j}
    for(let [p,a] of groups){if(a.length>=pCap(p)){let v={p,m:a.length,H:0,cl:new Map()};for(let [i,n] of a){let h=2*n-(C+p-1);ck(h>=0&&h<=6+4*cost[i]+4*r);v.H+=h;v.cl.set(n,(v.cl.get(n)||0)+1)}let z=moments(v);S+=a.length;SPrime+=a.length;primeKeys++;primeI+=1/p;primeH+=v.H;primeU+=z.U;ck(a.length*p>=A);primeStops.push({p,C,m:a.length,U:z.U})}
     else for(let [i,n] of a){let C1=C+p-1;R+=r;Rhi+=r;cost[i]+=r;events++;t[i]=n;prevP[i]=p;prevC[i]=C;add(i,C1,cell(C1)!==b)}
    }
   }
   let lowcost=Rlo-baseRlo;ck(lowcost<=1.5*L*m,"cell low budget");maxCellLow=Math.max(maxCellLow,lowcost);
  }
  ck(S+twin+bad===N&&S===SCell+SPrime&&R===Rlo+Rhi&&primeI<=SPrime/A+1e-8&&cellH+primeH<=6*S+4*R+4*B*S);
  ck(SCell>=stoppedCells*T&&rootsCell<=stoppedCells*(Math.floor(L/4)+1)&&Rlo<=1.5*L*executedCellAdmits);
  if(mode==="cellInverse")ck(executedCellAdmits<=cellCount*(T-1));
  ck(primeU<=8*primeKeys+Math.sqrt(4*primeH*primeI)+1e-6&&cellU<=8*cellKeys+Math.sqrt(4*cellH*cellI)+1e-6&&topU<=8*topKeys+Math.sqrt(4*topH*topI)+1e-6);
  for(let w of bands)ck(w.I<=w.landingBound+1e-8&&w.m<=w.capacity+1e-6);
  for(let w of heights)ck(w.small+w.large===SCell-rootsCell&&w.lowSmall+w.highSmall===w.small);
  out.push({bands,heights,Y,L,mode,A,T,S,SCell,SPrime,twin,bad,R,Rlo,Rhi,events,literal,cellCount,maxAdmit,stoppedCells,rootsCell,maxCellLow,primeKeys,cellKeys,cellI,cellH,cellU,primeI,primeH,primeU,topMass,topKeys,topI,topH,topU,topPhysical,entryChecks,executedCellAdmits,primeStops,cellStops})
 }
 return {X,B,N,runs:out}
}
function lowAudit(Y){
 let ps=[];for(let p=3;p<Y;p+=2)if(!ps.some(q=>p%q===0))ps.push(p);
 let L=2*ps.reduce((a,b)=>a*b,1),n=L/2;if(n>10000000)throw Error("size");
 let cost=new Int32Array(n+1),sc=0,mc=0;
 for(let i=n-1;i>=0;i--){let C=2*i,best=0,r=0;for(let p of ps)if((C-1)%p===0||(C+1)%p===0){if(!r)r=p;let d=(p-1)/2;if(i+d>n)throw Error("barrier");best=Math.max(best,r+cost[i+d]);}cost[i]=best;sc+=best;mc=Math.max(mc,best)}
 let result={Y,L,meanCost:sc/n,maxCost:mc,ratio:sc/n/(Y*Math.log(Y))};
 if(L<=2310){
  let dp=new Uint16Array((n+1)*L),sum=0,max=0,phaseSum=0;
  for(let i=n-1;i>=0;i--){let C=2*i,eligible=ps.filter(p=>(C-1)%p===0||(C+1)%p===0),r=eligible[0],best=0;if(!r)continue;
   for(let t=0;t<L;t++){let w=L+1,q=0;for(let p of eligible){let phase=(C-1)%p===0?0:p+2,wait=1+((phase-t-1)%(2*p)+2*p)%(2*p);if(wait<w||(wait===w&&p<q)){w=wait;q=p}}
    let v=r+dp[(i+(q-1)/2)*L+(t+w)%L];if(v>cost[i])throw Error("ghost upper");dp[i*L+t]=v;best=Math.max(best,v);phaseSum+=v;
   }sum+=best;max=Math.max(max,best);
  }
  result.clockMaxMean=sum/n;result.clockMax=max;result.clockRatio=sum/n/(Y*Math.log(Y));result.clockPhaseMean=phaseSum/(n*L);
 }
 return result;
}
for(const x of process.argv.slice(2))console.log(JSON.stringify(audit(Number(x))));
for(const Y of [5,7,11,13,17,19,23])console.log(JSON.stringify(lowAudit(Y)));
