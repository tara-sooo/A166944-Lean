// Three-class residue-code shortening, exact margin certificate and finite diagnostics.
function audit(){
 const D=10n**30n,ceil=(x,y)=>(x+y-1n)/y;
 function log(a,b){a=BigInt(a);b=BigInt(b);if(a<b){let [l,u]=log(b,a);return [-u,-l]}let zl=D*(a-b)/(a+b),zu=zl+1n,lo=0n,hi=0n,pl=zl,ph=zu;for(let i=0;i<1000;i++){lo+=2n*pl/BigInt(2*i+1);hi+=ceil(2n*ph,BigInt(2*i+1));pl=pl*zl*zl/(D*D);ph=ceil(ph*zu*zu,D*D)}hi+=ceil(2n*ph*D*D,2001n*(D*D-zu*zu));return[lo,hi]}
 // Local limiting constants (pi lower bound 3.14159; upper 3.14160).
 let A=314159n,B=314160n,J=100000n;
 if(4n*J*J*1000n>=406n*A*A||4n*J*J*1000n>=46n*9n*A*A)throw Error("coefficient limits");
 if(8n*J*J*1000n>=812n*A*A||32n*J**4n*1000n>=330n*A**4n)throw Error("top moments");
 if(809n*B*B>=8000n*J*J|| (1000n-18n)*B**4n>=96000n*J**4n)throw Error("rest moments");
 // 1/3 -32/pi^4 < .006 iff 982*pi^4 <96000.
 for(let [a,b,c] of [[1000,406,90],[1000,46,307],[1000,812,20],[1000,330,110],[1000,191,165],[1000,6,510]])if(log(a,b)[0]*100n<=BigInt(c)*D)throw Error("log constant");
 if(log(100,36)[0]<=D||log(100,37)[1]>=D||log(1000,368)[1]>=D)throw Error("entropy maximum location");
 let ent=Array.from({length:101},(_,i)=>i===0?0n:ceil(-BigInt(i)*log(i,100)[0],100n));
 let em=(a,b)=>b<=36?ent[b]:a>=37?ent[a]:368n*D/1000n;
 let worst=null,witness,counts=[0,0],cells=0,maxH=0,shorteningNumerator=null;
 for(let i=0;i<=61;i++)for(let j=0;j<100-i;j++){
  let u=Math.max(0,98-i-j),U=100-i-j;
  let S=2*i*i+j*j,den=20000-S,num=12000-S;
  let H=Math.max(1,Math.ceil(1000*num/den)+1);
  let gap=S*(1000-H)+20000*H-12000000;
  if(gap<=0)throw Error("shortening gap");
  if(shorteningNumerator===null||gap<shorteningNumerator)shorteningNumerator=gap;
  let e=em(i,i+1)+em(j,j+1)+em(u,U);
  let best=null,ss;
  for(let s of [1,2]){
   if(s*H>=1000)continue;
   // margin lower, scaled by 10^7 D.
   let m=BigInt(1000-s*H)*BigInt(90*j+307*u)*D+BigInt(H)*BigInt((s===1?20:110)*j+(s===1?165:510)*u)*D-BigInt(H)*e*10000n;
   if(best===null||m>best){best=m;ss=s}
  }
  if(best===null||best<=100000n*D)throw Error("margin <= .01 at "+i+","+j);
  if(worst===null||best<worst){worst=best;witness={i,j,H,s:ss}}
  counts[ss-1]++;cells++;maxH=Math.max(maxH,H);
 }
 const primes=[];for(let p=3;p<=23;p+=2)if(!primes.some(q=>q*q<=p&&p%q===0))primes.push(p);
 const mod=(x,p)=>(x%p+p)%p,choose=(n,k)=>{if(k<0||k>n)return 0;let v=1;for(let i=1;i<=Math.min(k,n-k);i++)v=v*(n-i+1)/i;return v};
 function subs(n,h){let a=[];function go(i,u){if(u.length===h){a.push(u);return}for(let j=i;j<=n-h+u.length;j++)go(j+1,[...u,j])}go(0,[]);return a}
 let stats={cells,counts,worst:Number(worst)/Number(10000000n*D),witness,maxH,shorteningGap:shorteningNumerator/20000000,classes:0,fibreChecks:0,nontrivialFibres:0,shortenedNontrivial:0,weightedChecks:0,energyChecks:0,varianceChecks:0,momentPositions:0,periods:[]};
 for(let [R,M] of [[13,100],[17,400],[19,1200],[23,5000]]){
  let pr=primes.filter(p=>p<=R),P=pr.reduce((a,p)=>a*p,1),L=pr.filter(p=>p>=11),n=L.length,b=L[0],q=Math.floor(Math.log(M)/Math.log(b));
  for(let kind of ["H","d"]){
   let sets=pr.map(p=>Array.from({length:p},(_,j)=>j).filter(j=>kind==="H"?j<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3})));
   let A=sets.reduce((a,s)=>a*s.length,1);
   const ix=L.map(p=>pr.indexOf(p)),inv=pr.map(p=>{let i=1;while((P/p%p)*i%p!==1)i++;return i});
   const co=pr.map((p,i)=>Array.from({length:p},(_,k)=>{let re=0,im=0;for(let a of sets[i]){let ang=2*Math.PI*mod(k*inv[i]*a,p)/p;re+=Math.cos(ang);im+=Math.sin(ang)}return (re*re+im*im)/sets[i].length**2}));
   const cat=(p,k)=>{let f=mod(k*inv[p],pr[p]);return f===0?0:f===1||f===pr[p]-1?1:2};
   let max=[1,0,0],mom=[[1,0,0],[1,0,0]];
   for(let p of ix){let m=[[1,0,0],[1,0,0]];for(let k=1;k<pr[p];k++){let c=cat(p,k),a=co[p][k];max[c]=Math.max(max[c],a);m[0][c]+=a;m[1][c]+=a*a}for(let s=0;s<2;s++)for(let c=1;c<3;c++)mom[s][c]=Math.max(mom[s][c],m[s][c])}
   let groups=new Map;
   for(let k=1;k<=M;k++){let t=[0,0,0];for(let p of ix)t[cat(p,k)]++;let key=t.join(",");if(!groups.has(key))groups.set(key,{t,ks:[]});groups.get(key).ks.push(k)}
   let totalBound=0;
   for(let {t,ks} of groups.values()){
    stats.classes++;let energy=ks.reduce((a,k)=>a+pr.reduce((v,p,i)=>v*co[i][k%p],1),0),best=Infinity;
    for(let h=1;h<=n;h++)for(let j0=0;j0<=Math.min(h,t[0]);j0++)for(let j1=0;j1<=Math.min(h-j0,t[1]);j1++){
     let j2=h-j0-j1;if(j2>t[2])continue;let j=[j0,j1,j2],u=t.map((v,i)=>v-j[i]),cap;
     if(h>q)cap=1;else {let gap=(u[0]**2+u[1]**2/2)/(n-h)-(q-h);if(gap<=0)continue;cap=Math.max(1,Math.floor((u[0]+u[1]-(q-h))/gap+1e-10))}
     let s=2*j1<=t[1]&&2*j2<=t[2]?2:1,prob=t.reduce((v,a,i)=>v*choose(a,j[i]),1)/choose(n,h);
     let F=prob*max[1]**(-(t[1]-s*j1))*max[2]**(-(t[2]-s*j2));
     let B=cap*choose(h,j0)*choose(h-j0,j1)*mom[s-1][1]**j1*mom[s-1][2]**j2;
     let sums=new Float64Array(ks.length),U=subs(n,h);
     for(let sub of U){let fibre=new Map,partial=0;for(let kidx=0;kidx<ks.length;kidx++){let k=ks[kidx],c=[0,0,0];for(let a of sub)c[cat(ix[a],k)]++;if(c.some((v,i)=>v!==j[i]))continue;
       let key=sub.map(a=>k%L[a]).join(","),num=(fibre.get(key)||0)+1;fibre.set(key,num);if(num>cap)throw Error("fibre");
       let w=sub.reduce((v,a)=>v*co[ix[a]][k%L[a]]**s,1);sums[kidx]+=w;partial+=w;
      }
      if(partial>B+1e-7)throw Error("partial");
      for(let v of fibre.values()){stats.fibreChecks++;if(v>1){stats.nontrivialFibres++;if(h<=q)stats.shortenedNontrivial++}}
     }
     for(let i=0;i<ks.length;i++){let k=ks[i],e=pr.reduce((v,p,j)=>v*co[j][k%p],1);if(sums[i]/U.length+1e-9<e*F)throw Error("AMGM");stats.weightedChecks++}
     if(energy>B/F+1e-7)throw Error("energy");stats.energyChecks++;best=Math.min(best,B/F)
    }
    if(!Number.isFinite(best))throw Error("class bound");totalBound+=best;
   }
   if(R<=19){let l=Math.ceil(P**.4),pre=new Uint32Array(P+1);for(let j=0;j<P;j++)pre[j+1]=pre[j]+(pr.every((p,i)=>sets[i].includes(j%p))?1:0);
    if(pre[P]!==A)throw Error("CRT");let count=j=>Math.floor(j/P)*A+pre[mod(j,P)],var0=0;
    for(let j=0;j<P;j++)var0+=(P*(count(j+l)-count(j))/(A*l)-1)**2;var0/=P;let bd=2*totalBound+(P/(2*l*(M+1)))**2*P/A;
    if(var0>bd+1e-7)throw Error("variance");stats.varianceChecks++;stats.momentPositions+=P;stats.periods.push({R,kind,P,M,l,var0,bd})
   }
  }
 }
 return stats
}
console.log(JSON.stringify(audit(),null,2));
