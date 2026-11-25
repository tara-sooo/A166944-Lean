// Nonreset deficit barriers, all-threshold relaunch scan, and low-predeficit departure support.
// Run node research/min_clock_nonreset_barriers_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,startAge=mode==='full'?0:mode==='early'?B:2*B,a=startAge,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
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

 const Y=Math.max(17,Math.ceil(B**.125)),m=Math.floor(u**2.75),eps=u**(-.125);
 // Original paths streamed. No storage of all events at large X.
 let events=0,checked=0,viol=0,repeat=0,repeatEx=null,low=Infinity,min=Infinity,violEx=null,barrier10=0,barrier20=0,nearReset=0,negative=0,down=0,launch=0,maxRun=0,literal=0;
 const groups=new Map(),rootGroups=X<=65536?[]:null;
 let selectedGain=0,addedGain=0,selectedInc=0,selectedClock=0,addedClock=0;
 for(let M=X+1;M<2*X;M+=2){let t=M+2,C=2*M-2,K=Math.floor((7*M-1)/4),max=0,lastReset=C,lastCanonical=C,run=0,gs=[];
  while(t<M+2+H){const [v,p]=hit(t,C,K);if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin terminal');break;}
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   const q=r[C/2],J=C+p-1,d=2*v-J,s=v%2,pre=2*t-C,wait=v-t,isReset=d===6*s;
   ok(d>=0&&J-(2*M-2)<=G&&wait<=2*q&&q<=p,'prefix bounds');
   const c=C/2+3;if(C%4===0&&t<=c&&c<v&&c<=M+2+H)lastCanonical=C;
   if(!isReset){if(pre>=10){ok(d>=10,'barrier 10');barrier10++;}if(pre>=20){ok(d>=20,'barrier 20');barrier20++;}}
   if(pre<20){ok(C-lastReset<210,'low deficit recent reset');nearReset++;}
   if(d<pre){negative++;if(!isReset)down++;}
   if(p>=Y&&(2*pre<=p-2||(!isReset&&pre<=p))){
    ok(wait>=p/4&&q>=p/8&&d<=4*p+1,'history-independent rough departure');
    const k=(d-6*s)/(2*p);ok(Number.isInteger(k)&&k>=0&&k<=2,'constant post phases');
    if(!isReset&&pre<=p){ok(wait>=p&&q>=p/2,'low nonreset long wait');launch++;}
    // Compare original pre-gain against previous proportional theorem;
    // virtual canonical inside this wait is included when reached by cutoff.
    const added=p<10*(C-lastCanonical)+16;
    const id=J+':'+v+':'+p;let g=groups.get(id);
    if(!g){g={p,n:0,added:0};groups.set(id,g);}
    g.n++;g.added+=+added;if(rootGroups)gs.push(id);
    selectedGain+=p-1;selectedInc++;selectedClock+=Math.max(0,Math.min(v,M+2+H)-Math.max(t,M+2+a))/2;
    if(added){addedGain+=p-1;addedClock+=Math.max(0,Math.min(v,M+2+H)-Math.max(t,M+2+a))/2;}
   }
   events++;
   if(isReset){max=0;lastReset=J;run=0;}else{
    run++;maxRun=Math.max(maxRun,run);
    const P=Math.max(7,pre);
    if(max>=P&&p>=P){repeat++;if(!repeatEx)repeatEx={M,C,t,p,pre,d,P,max};}
    if(p>=7)max=Math.max(max,p);
    if(max){checked++;low=Math.min(low,d);min=Math.min(min,d/max);if(d<=max){viol++;if(!violEx)violEx={M,C,t,p,d,max};}}
   }
   t=v;C=J;
  }
  if(rootGroups)rootGroups.push(gs);
 }
 let env=0,envGain=0,maxPhases=0;
 for(let D=2*X;D<7*X;D+=2){const q=r[D/2];if(!q)continue;
  for(const s of [0,1])fac(D+2*s-1,p=>{
   if(p<Y||8*q<p)return;const J=D+p-1;if(J>=7*X)return;let count=0;
   for(let k=0;6*s+2*p*k<=4*p+1;k++){const t=(J+6*s+2*p*k)/2;if(t%2!==s)continue;env++;envGain+=p-1;count++;}
   maxPhases=Math.max(maxPhases,count);ok(count<=3,'envelope phases');
  });
 }
 let thinGain=0,thinAdded=0,usedGain=0,maxMass=0,addedKeys=0;
 for(const g of groups.values()){usedGain+=g.p-1;maxMass=Math.max(maxMass,g.n);addedKeys+=+(g.added>0);if(g.n<=m){thinGain+=g.n*(g.p-1);thinAdded+=g.added*(g.p-1);}}
 ok(usedGain<=envGain&&groups.size<=env&&thinGain<=m*envGain,'rough support');
 let peeling=null;
 if(rootGroups){const active=new Map([...groups].map(([id,g])=>[id,g.n])),charges=new Map(),removed=new Uint8Array(N);let n=0,passes=0,charged=0;
  for(;;){let changed=0;for(let i=0;i<N;i++){if(removed[i])continue;const ids=rootGroups[i].filter(id=>active.get(id)<=m),gain=ids.reduce((s,id)=>s+groups.get(id).p-1,0);if(gain<eps*B)continue;
   for(const id of ids){const k=(charges.get(id)||0)+1;ok(k<=m,'lifetime');charges.set(id,k);charged+=groups.get(id).p-1;}
   for(const id of rootGroups[i])active.set(id,active.get(id)-1);removed[i]=1;changed++;n++;
  }if(!changed)break;passes++;}
  let retained=0;for(let i=0;i<N;i++)if(!removed[i]){const gain=rootGroups[i].filter(id=>active.get(id)<=m).reduce((s,id)=>s+groups.get(id).p-1,0);ok(gain<eps*B,'fixed point');retained+=gain;}
  ok(charged>=n*eps*B-1e-6&&charged<=m*envGain,'peel gain');peeling={n,passes,charged,retained};
 }
 return {X,B,Y,N,events,checked,viol,repeat,repeatEx,low:Number.isFinite(low)?low:null,min:Number.isFinite(min)?min:null,violEx,barrier10,barrier20,nearReset,negative,down,launch,maxRun,literal,selectedInc,selectedGain,addedGain,selectedClock,addedClock,keys:groups.size,addedKeys,maxMass,env,envGain,maxPhases,thinGain,thinAdded,peeling};
}
function synthetic(){
 const X=65536,B=Math.ceil(Math.sqrt(7*X)),spf=new Int32Array(7*X+4);
 for(let p=2;p<spf.length;p++)if(!spf[p]){spf[p]=p;if(p*p<spf.length)for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;}
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a;};
 // A literal MIN scan independent of the arithmetic event-search function.
 function hit(t,C){for(let v=t+1;v<=t+2*B;v++){const n=gcd(v%2?v-2:v,v%2?C+1:C-1);if(n>1&&spf[n]<=B)return [v,spf[n]];}return null;}
 let t=97711,C=195332,seq=[],max=0;
 for(let j=0;j<100;j++){
  const h=hit(t,C);if(!h)throw Error('synthetic terminal');const [v,p]=h,J=C+p-1,d=2*v-J,pre=2*t-C;
  seq.push({C,t,p,v,J,pre,d});
  if(d===6*(v%2))throw Error('unexpected reset');
  if(max>=31&&pre<=31&&p>=31){if(p!==137||C!==195498||pre!==30||d!==280||seq[0].p!==31)throw Error('synthetic mismatch');return {B,threshold:31,sequence:seq};}
  max=Math.max(max,p);C=J;t=v;
 }
 throw Error('no synthetic repeat');
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,131072,262144,524288,1048576])console.log(JSON.stringify(audit(X,'analytic')));
console.log(JSON.stringify(synthetic()));
