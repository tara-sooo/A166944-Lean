// Exact quiet-tick coarea and failed-query rank diagnostics.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(a,b)=>(a%b+b)%b,lim=4000005,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<lim;p++)if(!spf[p])for(let n=p*p;n<lim;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){n=Math.abs(n);ck(n>0&&n<lim,"factor domain");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function ev(u,v,z){let p=Infinity,w=Infinity;for(let [n,e] of [[u-1,1],[u+1,-1]])for(let r of fs(n)){if(r>z)continue;let t=mod((e===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 const rows=[];
 for(let [kind,y,z,R,end,D] of [["period",5,7,420,840,20],["period",6,11,4620,9240,24],["period",7,13,60060,120120,28],["period",9,17,1021020,2042040,36],["local",127,254,100000,112000,508],["local",503,1006,1000000,1012000,2012],["local",997,1994,1000000,1012000,3988]]){
  let H=[];for(let p=y;p<=z;p++)if(p>=5&&!spf[p])H.push(p);
  let N=(end-R)/6,period=kind==="period",groups=new Map();
  if(period)for(let p of H){ck(N%p===0,"group size");groups.set(p,{f:new Uint32Array(N/p),hit:new Uint32Array(N/p)})}
  let m=Math.ceil((y-1)/2),amax=3+3*(D+z)+8,a=new Float64Array(amax+1),phi=new Float64Array(amax+1),sq=new Float64Array(amax+1);
  for(let h=1;h<=amax;h++){for(let p of H){if((2*h+1)%p===0)a[h]+=1/p;if((2*h-5)%p===0)a[h]+=1/p}phi[h]=phi[h-1]+a[h];sq[h]=sq[h-1]+a[h]*a[h]}
  let s={kind,y,z,D,roots:0,events:0,threeEvents:0,bandHits:0,negativeQueries:0,quietNegative:0,terminalNegative:0,firingNegative:0,uniqueFiringDomain:0,uniqueFiringChecks:0,groupChecks:0,levelChecks:0,coareaChecks:0,threeChecks:0,phaseChecks:0,terminalStops:0,gainStops:0,sumG:0,sumBandGain:0,oldEnergy:0,newEnergy:0,oldCharge:0,newCharge:0,exactQuietCharge:0,negativeCost:0,extraFiringCost:0,oldSmallCharge:0,newSmallCharge:0,smallFiveCharge:0,oldThreeCharge:0,nonzeroFiveChargeRoots:0,exampleFive:null};
  for(let X=Math.ceil(R/6)*6;X<end;X+=6){
   let u=X,v=X/2+3,G=0,seen=new Map(),hit=new Set(),intervals=[],q=new Uint32Array(amax+1),kmax=3,full=0,quiet=0,top=0,oldSmall=0,newSmall=0,five=0,three=0,firingCost=0,neg=0;
   function tick(n,pwin,terminal){
    let e=n%2?-1:1,h=n-u/2,f=2*h+(e===1?1:-5),candidates=fs(f).filter(p=>p>=y&&p<=z&&p<=pwin);
    if(pwin<Infinity&&pwin>=y&&Math.abs(f)<y*y){ck(candidates.length===1&&candidates[0]===pwin,"unique band at firing");s.uniqueFiringChecks++}
    for(let p of candidates){
     if(hit.has(p))continue;
     let r=mod(e-(u-X),p),S=seen.get(p);if(!S){S=new Set();seen.set(p,S)}if(S.has(r))continue;
     if(mod(X,p)===r){ck(p===pwin&&!terminal,"hit");hit.add(p);s.bandHits++;continue}
     S.add(r);s.negativeQueries++;neg+=1/p;
     if(terminal)s.terminalNegative++;else if(pwin<Infinity){s.firingNegative++;firingCost+=1/p;ck(Math.abs(f)>=y*y,"firing failed query domain")}else s.quietNegative++;
    }
   }
   let events=0,terminal=false;
   while(G<D){
    let z0=ev(u,v,z);if(!isFinite(z0.p)){terminal=true;s.terminalStops++;for(let j=1;j<=2*z;j++)tick(v+j,Infinity,true);break}
    let p=z0.p,w=z0.w,g=p-1,h=v-u/2,k=h+w,hp=k-g/2;ck(hp>=0&&k<=amax,"height");kmax=Math.max(kmax,k);
    for(let j=1;j<=w;j++){tick(v+j,j===w?p:Infinity,false);if(j<w)q[h+j]++;}
    if(p>=y){ck(hit.has(p),"selected high");s.sumBandGain+=g}
    let f=phi[k]-phi[h],qq=phi[k-1]-phi[h],t=a[k];full+=f;quiet+=qq;top+=t;intervals.push([hp+1,k,p]);
    if(p<=11){oldSmall+=phi[k]-phi[hp];newSmall+=phi[k-1]-phi[hp];}
    if(p===3){s.threeEvents++;three+=a[k];ck(k-1===hp&&phi[k-1]-phi[hp]===0,"zero 3 residual");s.threeChecks++}
    if(p===5){let v5=phi[k-1]-phi[hp];five+=v5;if(v5>1e-12&&!s.exampleFive)s.exampleFive={X,u,v,p,w,k,hp,charge:v5};}
    u+=g;v+=w;G+=g;events++;s.events++;
   }
   if(!terminal)s.gainStops++;
   const d=new Uint32Array(amax+1),b=new Uint32Array(amax+1);for(let [l,r,p] of intervals){for(let h=l;h<=r;h++)d[h]++;for(let h=l;h<r;h++)b[h]++}
   let sum=0,oldE=0,newE=0,newC=0,oldC=0,he=v-u/2;
   for(let h=1;h<=kmax;h++){let endpoint=(h<=he?1:0)-(h<=3?1:0);ck(q[h]===endpoint+b[h],"exact quiet level");s.levelChecks++;sum+=b[h];if(h>=m){oldE+=d[h]*d[h];newE+=b[h]*b[h]}oldC+=a[h]*d[h];newC+=a[h]*b[h]}
   ck(sum===G/2-events,"residual length");ck(Math.abs(quiet-(phi[he]-phi[3]+newC))<1e-8&&Math.abs(full-quiet-top)<1e-8,"coarea");s.coareaChecks++;
   let term=H.reduce((s,p)=>s+2/p,0);ck(neg<=quiet+term+firingCost+1e-8,"failed query charge");ck(newC<=Math.sqrt(sq[kmax]*newE)+1e-8,"energy");if(2*kmax+5<y*y){ck(firingCost===0,"no firing failures");s.uniqueFiringDomain++}
   if(period)for(let p of H){let g=groups.get(p),i=((X-R)/6)%g.f.length;g.f[i]+=seen.get(p)?.size||0;g.hit[i]+=hit.has(p)?1:0}
   s.roots++;s.sumG+=G;s.oldEnergy+=oldE;s.newEnergy+=newE;s.oldCharge+=oldC;s.newCharge+=newC;s.exactQuietCharge+=quiet;s.negativeCost+=neg;s.extraFiringCost+=firingCost;s.oldSmallCharge+=oldSmall;s.newSmallCharge+=newSmall;s.oldThreeCharge+=three;s.smallFiveCharge+=five;if(five>1e-12)s.nonzeroFiveChargeRoots++;
  }
  if(period)for(let [p,g] of groups)for(let i=0;i<g.f.length;i++){let q=g.hit[i];ck(g.f[i]===p*q-q*(q+1)/2,"failed rank law");s.groupChecks++}
  ck(s.terminalStops+s.gainStops===s.roots,"stops");rows.push(s);
 }
 return rows
}
console.log(JSON.stringify(audit(),null,2));
