// Variable rough anchor mass cap and relative-label signed ledger.
function audit(X,H=24,D=2,s=1,J=4){
 const B=Math.ceil(Math.sqrt(7*X)),N=X/2,T=Math.max(3,Math.floor(B/8)),lim=7*X+10;
 const spf=new Int32Array(lim);for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)spf[j]=p}
 const mod=(a,b)=>(a%b+b)%b,ck=(a,m)=>{if(!a)throw Error(m)};
 const head=new Int32Array(Math.floor(lim/2)).fill(-1),link=new Int32Array(N),times=new Int32Array(N),cut=new Int32Array(N),arrival=new Uint8Array(N),ap=new Int32Array(N),ac=new Int32Array(N),window=new Uint8Array(N),lastH=new Int32Array(N).fill(6);
 const out={X,H,D,s,J,B,N,T,stops:0,lowStops:0,anchorStops:0,bothStops:0,anchorArrivalMass:0,anchorLandingGroups:0,anchorContinuedMass:0,anchorStoppedMass:0,anchorEvents:0,anchorCost:0,anchorContinuedCost:0,anchorStoppedCost:0,anchorWindowCost:0,anchorWindowStarts:0,windowGainTriggers:0,windowGiantTriggers:0,lowCost:0,lowArrivalCost:0,smallCost:0,negativeCost:0,negativeLoss:0,positive:0,positiveMarked:0,positiveSmall:0,marked:0,total:0,terminal:0,twin:0,nontwin:0,checks:0,anchorWindowBudget:0,anchorKeyCount:0,anchorClocks:0};
 const anchorKeys=new Map(),ar=new Int32Array(N);
 function next(C,t){let p=0,n=Infinity,r=Infinity;for(let a of [-1,1]){let v=C+a;while(v>1){let q=spf[v];if(q>B)break;r=Math.min(r,q);let u=t+2*q-mod(t-(a===-1?0:q+2),2*q);if(u<n||(u===n&&q<p)){p=q;n=u}while(v%q===0)v/=q}}return {p,n,r}}
 function add(i,C){link[i]=head[C/2];head[C/2]=i}
 for(let i=0;i<N;i++){let M=X+2*i+1;times[i]=M+2;cut[i]=Math.floor((7*M-1)/4);add(i,2*M-2)}
 for(let C=2*X;C<=7*X-2;C+=2){
  let i=head[C/2];if(i<0)continue;const V=new Map();while(i>=0){let j=link[i];if(!V.has(times[i]))V.set(times[i],[]);V.get(times[i]).push(i);i=j;}
  for(let [t,ids] of V){
   const h=2*t-C,low=h<=H,anch=ids.some(i=>arrival[i]);ck(h>=0,"height");
   if(anch){out.anchorLandingGroups++;out.anchorArrivalMass+=ids.filter(i=>arrival[i]).length}
   let stopped=(low||anch)&&ids.length>=T;
   if(stopped){out.stops+=ids.length;out.lowStops+=low?ids.length:0;out.anchorStops+=anch?ids.length:0;out.bothStops+=low&&anch?ids.length:0;}
   for(let i of ids){
    ck(lastH[i]===h,"state height");
    if(arrival[i]){
     let p=ap[i];
     if(stopped){out.anchorStoppedMass++;out.anchorStoppedCost+=ar[i]}
     else{out.anchorContinuedMass++;out.anchorContinuedCost+=ar[i];out.anchorWindowStarts++;out.anchorWindowBudget+=100*s*(D+5)*p;}
     window[i]=stopped||low?0:1;ac[i]=C;
    }else if(low)window[i]=0;
    arrival[i]=0;
   }
   if(stopped)continue;
   let a=next(C,t);
   for(let i of ids){
    if(!a.p||a.n>cut[i]){out.terminal++;if(a.p)out.nontwin++;else out.twin++;continue;}
    let p=a.p,r=a.r,C1=C+p-1,h1=2*a.n-C1,dh=h1-h;
    ck(h1>=0&&a.n-t<=2*r&&r<=p,"event");
    let anchor=p>=11&&h<=D*p&&(J+4)*r>=p;
    let mark=low||anchor||h1<=H,win=false;
    if(window[i]){
      let A=(D+5)*ap[i],g=C-ac[i];
      if(g>=s*A){window[i]=0;out.windowGainTriggers++}
      else if(p>64*s*A){ck(anchor,"oversize must be anchor");window[i]=0;out.windowGiantTriggers++}
      else if(!anchor&&!low&&h1>H){mark=true;win=true;out.anchorWindowCost+=r;}
    }
    if(anchor){out.anchorEvents++;out.anchorCost+=r;let key=p+"/"+C;if(!anchorKeys.has(key))anchorKeys.set(key,new Set());anchorKeys.get(key).add(a.n);ck(h1<=(D+3)*p+1,"anchor landing height");arrival[i]=1;ap[i]=p;ar[i]=r;window[i]=0;}
    if(low&&!anchor)out.lowCost+=r;else if(!low&&!anchor&&h1<=H)out.lowArrivalCost+=r;
    if(mark){out.marked+=r;out.positiveMarked+=Math.max(0,dh)}
    else if(D*p<h){ck(h>H&&h1>H,'high interior');out.smallCost+=r;out.positiveSmall+=Math.max(0,dh)}
    else{ck(p>=11&&(J+4)*r<p&&dh<0&&J*r<=-dh,"negative charge");out.negativeCost+=r;out.negativeLoss-=dh;}
    out.positive+=Math.max(0,dh);out.total+=r;out.checks++;
    times[i]=a.n;lastH[i]=h1;add(i,C1);
   }
  }
 }
 for(let a of anchorKeys.values()){ck(a.size<=D+5,"clock count");out.anchorClocks+=a.size}out.anchorKeyCount=anchorKeys.size;
 ck(out.stops+out.terminal===N&&out.anchorArrivalMass===out.anchorStoppedMass+out.anchorContinuedMass,"mass conservation");
 ck(out.anchorCost===out.anchorStoppedCost+out.anchorContinuedCost&&out.marked===out.lowCost+out.lowArrivalCost+out.anchorCost+out.anchorWindowCost,"cost conservation");
 ck(out.anchorWindowCost<=out.anchorWindowBudget&&out.anchorStoppedCost<=B*out.stops,"anchor budget");
 ck(out.total===out.marked+out.smallCost+out.negativeCost&&J*out.negativeCost<=out.negativeLoss&&out.negativeLoss<=6*N+out.positive,"signed budget");
 ck(out.positive===out.positiveMarked+out.positiveSmall&&J*out.total<=(J+4)*(out.marked+out.smallCost)+6*N,"reduced residual");
 return out;
}
for(const X of process.argv.slice(2).map(Number))for(const [H,D,s,J] of [[24,2,1,4],[48,4,2,12]])console.log(JSON.stringify(audit(X,H,D,s,J)));
