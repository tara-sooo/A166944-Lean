// Last upward deficit crossings before short high resets.
// Run node research/min_clock_deficit_crossing_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>B**(1/16))break;L*=p;z=p;}}
 else {z=3;L=6;}
 const T=mode==='analytic'?Math.max(z+1,Math.ceil(B**.25)):Math.ceil(Math.sqrt(B));
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'||mode==='stress'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'||mode==='stress'?12:24;
 const D0=mode==='analytic'?Math.ceil(40*ell)+1:4;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),degrees=new Uint8Array(len);
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let rare=0,maxDegree=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;for(const C of [2*j,2*j+2])fac(C,()=>degrees[j]++);maxDegree=Math.max(maxDegree,degrees[j]+1);rare+=+(degrees[j]+1>D0);}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1])fac(C+side,q=>{const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(w<v||(w===v&&w<=K&&q<p)){v=w;p=q;}});return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],at=new Map(),W0=new Float64Array(len),WM=new Float64Array(len),WH=new Float64Array(len);
 let R=0,RM=0,RH=0,events=0,literal=0,twins=0;
 for(let i=0;i<N;i++){const M=X+1+2*i,s=M+2,K=Math.floor((7*M-1)/4),path=[];let t=s,C=2*M-2,inc=0,rr=0;
  for(;;){const e={i,M,C,t,inc,p:0,w:0};path.push(e);let row=at.get(C);if(!row){row=[];at.set(C,row);}row.push(e);
   ok(C<=2*t&&C-(2*M-2)<=G,'prefix gain');
   if(t>=s+H)break;
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');twins++;break;}
   const q=r[C/2],cost=Math.max(0,Math.min(v,s+H)-Math.max(t,s+a))/2;
   ok(v-t<=2*q&&q<=p,'wait');e.p=p;e.w=cost/q;rr+=cost;R+=cost;W0[C/2]+=e.w;
   if(p>z&&p<=T){RM+=cost;WM[C/2]+=e.w;}if(p>T){RH+=cost;WH[C/2]+=e.w;}
   t=v;C+=p-1;inc=p;events++;
  }
  ok(rr<=B,'root cost');paths.push(path);
 }




 const P=mode==='analytic'?Math.ceil(B/u**.125):Math.max(19,Math.ceil(B/(mode==='stress'?8:4)));
 const V=mode==='analytic'?Math.max(1,Math.floor(B**.0625)):Math.max(1,Math.min(8,Math.floor((P-9)/10)));
 const Y=mode==='analytic'?Math.max(7,Math.ceil(B**.125)):mode==='stress'?7:13;
 const h=mode==='analytic'?Math.max(1,Math.floor(u**1.5)):mode==='stress'?4:2;
 const lim=12*B+6,Lmin=Math.max(7,Math.ceil(P/4)),Lmax=Math.floor(B/2),key=(J,t,q)=>J+':'+t+':'+q;
 const diff=[new Int32Array(lim+3),new Int32Array(lim+3)];let envelope=0;
 function range(D,q,t,s){
  const J=D+q-1,r0=r[D/2],d=2*t-J;
  if(q<Y||r0===0||4*r0<=q-1||J>=7*X||t%2!==s||d<0||d>lim||(J+2*s)%q||(d-6*s)%(2*q))return null;
  const lo=Math.max(Lmin,d-(4*r0-q+1)+1),hi=Math.min(Lmax,d);
  return lo<=hi?{lo,hi}:null;
 }
 // Stream arithmetic envelopes into difference arrays; no huge key map.
 for(let D=2*X;D<7*X;D+=2){const r0=r[D/2];if(!r0)continue;
  for(let s=0;s<2;s++)fac(D+2*s-1,q=>{
   if(q<Y||4*r0<=q-1)return;const J=D+q-1;if(J>=7*X)return;
   const k0=Math.max(0,Math.ceil((Lmin-6*s)/(2*q))),k1=Math.floor((Math.min(lim,Lmax+4*r0-q)-6*s)/(2*q));
   for(let k=k0;k<=k1;k++){const t=(J+6*s+2*q*k)/2,e=range(D,q,t,s);if(!e)continue;
    const b=+(q>=P);envelope++;diff[b][e.lo]++;diff[b][e.hi+1]--;
   }
  });
 }
 const sup=[0,0],maxSup=[0,0],per=[new Int32Array(lim+1),new Int32Array(lim+1)];
 for(let b=0;b<2;b++){let n=0;for(let l=1;l<=lim;l++){n+=diff[b][l];per[b][l]=n;sup[b]+=n;maxSup[b]=Math.max(maxSup[b],n);}}
 const full=[new Float64Array(len),new Float64Array(len)],groups=new Map(),assign=[];
 let short=0,levels=0,small=0,smallCost=0,near=0,mid=0,totalP=0,checks=0,maxDepth=0,allShort=0;
 for(const path of paths){let lastReset=0,previousEnd=0;
  for(let j=1;j<path.length;j++){
   const v=path[j],a=path[j-1],q=v.inc,r0=r[a.C/2],wait=v.t-a.t,d0=2*a.t-a.C,d1=2*v.t-v.C;
   ok(d1-d0===2*wait-q+1,'drift identity');if(q<Y)smallCost+=wait/2;
   if(d1>d0&&q>=Y){const b=+(q>=P);ok(wait>(q-1)/2&&r0>(q-1)/4,'positive drift roughness');full[b][a.C/2]+=wait/(2*r0);}
   if(d1===6*(v.t%2)){
    if(q>=P&&wait<=V){
     allShort++;const L0=Math.ceil(q/4),L1=Math.floor(q/2);
     if(L0>6&&L1<=d0){
      short++;totalP+=q;const rec={root:v.i,q,levels:L1-L0+1,small:0,thin:0,thick:0,marks:[]};
      const last=new Map();
      for(let k=lastReset+1;k<j;k++){const x=path[k-1],y=path[k],d=2*x.t-x.C,f=2*y.t-y.C;for(let l=Math.max(L0,d+1);l<=Math.min(L1,f);l++)last.set(l,k);}
      ok(last.size===rec.levels&&lastReset>=previousEnd,'complete disjoint excursion');previousEnd=j;levels+=rec.levels;maxDepth=Math.max(maxDepth,j-lastReset-1);
      for(const [l,k] of last){const x=path[k-1],y=path[k],p=y.inc;
       ok(2*x.t-x.C<l&&l<=2*y.t-y.C&&k<j,'actual crossing');
       for(let h0=k+1;h0<j;h0++){const aa=path[h0-1],bb=path[h0];ok(!(2*aa.t-aa.C<l&&l<=2*bb.t-bb.C),'last upward crossing');}checks++;
       if(p<Y){small++;rec.small++;continue;}
       const b=+(p>=P),id=key(y.C,y.t,p),en=range(x.C,p,y.t,y.t%2);ok(en&&en.lo<=l&&l<=en.hi,'assigned crossing in envelope');
       const kk=id+':'+l;let g=groups.get(kk);if(!g){g={b,l,n:0,roots:new Set()};groups.set(kk,g);}
       ok(!g.roots.has(v.i),'no repeated root at same edge and level');g.roots.add(v.i);g.n++;rec.marks.push(kk);if(b)near++;else mid++;
      }assign.push(rec);
     }
    }lastReset=j;
   }
  }
 }
 let thin=0,thick=0,second=[0,0],mass=[0,0],usedSupport=[0,0],maxMass=[0,0],E=[0,0],Eunion=0;
 const actualPer=[new Int32Array(lim+1),new Int32Array(lim+1)];
 for(const g of groups.values()){const b=g.b;mass[b]+=g.n;second[b]+=g.n*g.n;usedSupport[b]++;actualPer[b][g.l]++;maxMass[b]=Math.max(maxMass[b],g.n);if(g.n<=h)thin+=g.n;else thick+=g.n;}
 for(let l=1;l<=lim;l++)for(let b=0;b<2;b++)ok(actualPer[b][l]<=per[b][l],'level support');
 for(let j=lo;j<=hi;j++){E[0]+=r[j]*full[0][j]**2;E[1]+=r[j]*full[1][j]**2;Eunion+=r[j]*(full[0][j]+full[1][j])**2;}
 const eps=1e-6*Math.max(1,Eunion);
 for(let b=0;b<2;b++){ok(second[b]<=144*E[b]+eps,'crossing second moment');ok(mass[b]**2<=sup[b]*second[b]+eps,'crossing Cauchy');}
 ok(small<=4*smallCost&&thin<=h*(sup[0]+sup[1])&&levels===small+thin+thick&&mass[0]===mid&&mass[1]===near,'global crossing budget');
 const counts=[0,0,0],pSums=[0,0,0],roots=[new Set(),new Set(),new Set()];
 for(const a of assign){for(const id of a.marks){if(groups.get(id).n<=h)a.thin++;else a.thick++;}
  ok(a.levels===a.small+a.thin+a.thick,'entry crossing partition');const v=[a.small,a.thin,a.thick],c=v.indexOf(Math.max(...v));
  ok(v[c]*3>=a.levels&&a.levels>=a.q/5,'entry witness quota');counts[c]++;pSums[c]+=a.q;roots[c].add(a.root);}
 ok(pSums[0]<=15*small&&pSums[1]<=15*thin&&pSums[2]<=15*thick,'weighted entry budgets');
 // Near-B version: use exact actual smaller-label drift count, not an independence assumption.
 ok(totalP<=5*(small+mid+near)&&totalP<=5*(small+mid+Math.sqrt(sup[1]*second[1]))+eps,'near-band clock transfer');
 return {X,B,mode,P,V,Y,h,events,literal,R,allShort,short,totalP,levels,small,mid,near,thin,thick,smallCost,envelope,sup,maxSup,usedSupport,maxMass,second,E,Eunion,counts,pSums,rootCounts:roots.map(s=>s.size),checks,maxDepth};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','stress'])console.log(JSON.stringify(audit(X,mode)));
