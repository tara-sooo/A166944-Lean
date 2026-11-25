// True clock birth drawdown and rough arrival-lag quotas.
// Run node research/min_clock_true_birth_audit.mjs 1024 4096 16384 65536
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
  ok(rr<=(H-startAge)/2,'root cost');paths.push(path);
 }











 const m=mode==='analytic'?u**2.5:mode==='wide'?64:8,Y=mode==='analytic'?Math.max(17,Math.ceil(B**.125)):mode==='wide'?7:17;
 const lim=12*B+6,ell0=1+Math.log(u),lagCut=mode==='analytic'?Math.ceil(B**.125):mode==='wide'?7:17,nodes=new Map(),key=e=>e.t+':'+e.C,def=e=>2*e.t-e.C;
 for(const path of paths){const stop=path[path.length-1].t;let a=null;
  for(const e of path){let v=nodes.get(key(e));if(!v){v={id:key(e),t:e.t,C:e.C,d:def(e),children:new Map(),next:null,tags:[]};nodes.set(v.id,v);}
   v.tags.push({i:e.i,M:e.M,stop,child:a?a.id:'root',p:e.inc,pre:a});if(a){let g=v.children.get(a.id);if(!g){g={p:e.inc,n:0};v.children.set(a.id,g);}g.n++;ok(g.p===e.inc&&(!a.next||a.next===v),'deterministic successor');a.next=v;}v.incByTag??=new Map();v.incByTag.set(e.i,e.inc);a=v;
  }
 }
 const P=n=>n*(n-1),groups=new Map(),band=d=>Math.floor(Math.log2(lim/d));
 function cap(d,q,rough){const j=band(d),D=lim/2**j;return B*m*q*(rough?u*u:1/ell0)/(D*D*(j+1)**2);}
 let pairs=0,oldI=0,oldEntry=0,trueI=0,trueD=0,trueA=0,trueL=0,oldL=0,firstMatched=0,firstRise=0,firstDrop=0,entrySaving=0,oldDebit=0,newDebit=0,oldSmall=0,newSmall=0,rootLate=0,rootEarly=0,earlySame=0,earlyMixed=0,sameIncoming=0,sameIncomingLarge=0,longLag=0,shortLag=0,smallTrue=0,smallTrueDebit=0,localCredit=0,maxLag=0,maxNew=0,oracle=0;
 let oldHeavy=0,trueHeavy=0,oldAfter=0,newAfter=0,roughAfter=0,plainAfter=0,roughRaw=0,plainRaw=0;
 const pairData=[]; const improved=new Map();let improvedOld=0,credit=0,creditEnergy=0,lowTruePaid=0,impRoughPaid=0,impPlainPaid=0,impRawRough=0,impRawPlain=0,impDirect=0,impSame=0,impLongSmall=0,impMixedPaid=0;
 for(const v of nodes.values()){
  const cs=[...v.children.values()],b=P(v.tags.length)-cs.reduce((s,e)=>s+P(e.n),0);if(!b)continue;
  const suffix=new Map();let cur=v,mi=v.d,A=0,D=0;
  while(cur){suffix.set(cur.t,{mi,A,D,d:cur.d});if(!cur.next)break;const z=cur.next.d-cur.d;A+=Math.max(0,z);D+=Math.max(0,-z);cur=cur.next;mi=Math.min(mi,cur.d);}
  for(let i=0;i<v.tags.length;i++)for(let j=0;j<i;j++){
   const x=v.tags[i],y=v.tags[j];if(x.child===y.child)continue;pairs+=2;
   const s=suffix.get(Math.min(x.stop,y.stop)),I=v.d-s.mi,L0=s.D-I;ok(L0>=0,'old matched');
   let t=v.t,C=v.C,d=v.d,q=0,lag=0,rough=false,entry=0,extra=0,delta=0,cat='direct';
   const same=x.p>0&&x.p===y.p;
   if(same){const a=x.pre.t<y.pre.t?x:y,b=x.pre.t<y.pre.t?y:x;ok(a.pre.C===b.pre.C&&a.pre.t<b.pre.t,'same label distinct predecessor times');
    C=b.pre.C;t=b.pre.t;d=b.pre.d;q=b.pre.incByTag.get(b.i);const q0=a.pre.incByTag.get(a.i);
    lag=t-a.pre.t;maxLag=Math.max(maxLag,lag);ok(lag<2*r[C/2]&&v.t-t>0,'true waiting birth');
    ok(hit(a.pre.t,C,v.t)[0]===v.t&&hit(t,C,v.t)[0]===v.t,'same event after waiting birth');
    delta=v.d-d;extra=Math.min(Math.max(0,delta),I);firstRise+=2*Math.max(0,delta);firstDrop+=2*Math.max(0,-delta);
    if(v.d!==6*(v.t%2))entry=Math.min(Math.max(0,a.pre.d-v.d),Math.max(0,b.pre.d-v.d));
    if(delta>0){const w=v.t-t,r0=r[C/2],p=x.p;ok(w>(p-1)/2&&extra<=24*r0*(w/(2*r0))*((v.t-a.pre.t)/(2*r0))+1e-9,'matched first rise energy');localCredit+=2*r0*(w/(2*r0))*((v.t-a.pre.t)/(2*r0));}
    if(!q){cat='lateRoot';rootLate+=2;ok(d===6,'later canonical root');}
    else {
     ok((C+2*(t%2))%q===0&&(d-6*(t%2))%(2*q)===0,'true incoming congruence');
     rough=q>=Y&&lag>=q; if(rough){ok(2*r[C/2]>q,'rough lag');longLag+=2;}else shortLag+=2;
     if(!q0){cat='earlyRoot';rootEarly+=2;ok(a.pre.d===6,'earlier root');}
     else if(q===q0){cat='sameIncoming';sameIncoming+=2;ok(lag%(2*q)===0&&r[C/2]>q,'same incoming separated clock phases');if(q>=Y){ok(rough,'same incoming rough');sameIncomingLarge+=2;}}
     else{cat='mixedIncoming';earlyMixed+=2;}
    }
   }
   const mn=Math.min(d,s.mi),It=d-mn,Lt=s.D+Math.max(0,-delta)-It;
   ok(Lt===L0+extra&&Lt>=0&&entry<=Math.max(0,-delta),'true matching identities');
   ok(I+entry<=It+extra,'old debit dominated');ok(It+extra-(I+entry)===Math.max(0,-delta)-entry,'entry saving');
   oldI+=2*I;oldEntry+=2*entry;oldL+=2*L0;trueI+=2*It;trueL+=2*Lt;trueD+=2*(s.D+Math.max(0,-delta));trueA+=2*(s.A+Math.max(0,delta));firstMatched+=2*extra;entrySaving+=2*(Math.max(0,-delta)-entry);
   oldDebit+=2*(I+entry);newDebit+=2*It;maxNew=Math.max(maxNew,It);
   const h=Math.abs(x.M-y.M),j0=Math.floor(Math.log2(8*B/h)),width=8*B/2**j0,c0=B*m/(width*(j0+1)**2);
   const small=v.tags.length<=m||v.d<=m,smallT=v.tags.length<=m||d<=m;
   const ro=small?0:Math.max(0,I+entry-c0),rn=smallT?0:Math.max(0,It-c0);oldAfter+=2*ro;newAfter+=2*rn;
   if(small)oldSmall+=2*(I+entry);if(smallT){newSmall+=2*It;smallTrue+=2;}else trueHeavy+=2*It;
   if(same&&q&&d>6&&d!==6*(t%2)&&rn>0){
    const id=C+':'+t+':'+q+':'+(rough?1:0);let g=groups.get(id);if(!g){g={C,t,q,d,rough,mass:0,rest:0};groups.set(id,g);}g.mass+=2;g.rest+=2*rn;
   }
   // Maintain the OLD actual debit and prior small/source/mixed payments.
   // Move only the genuinely matched first-rise part to a separate upstream
   // ledger. New low-true-birth and arrival quotas act on its remainder.
   let rem=ro;
   if(!same&&x.p>0&&y.p>0&&x.p!==y.p&&v.d>6&&v.d!==6*(v.t%2)&&rem>0){
    // Defer mixed quota to its exact aggregate label cross product.
    const np=v.tags.filter(a=>a.p===x.p).length,nq=v.tags.filter(a=>a.p===y.p).length;
    const j1=band(v.d),D1=lim/2**j1,Y0=Math.max(3,Math.ceil(B**.125)),h0=x.p>=Y0&&y.p>=Y0?1:ell0**2;
    const f=Math.min(1,B*m*x.p*y.p/(D1*D1*(j1+1)**2*h0*2*np*nq));
    impMixedPaid+=2*f*rem;rem*=1-f;
   }
   improvedOld+=2*rem;
   const moved=Math.min(rem,extra);credit+=2*moved;rem-=moved;
   ok(rem<=It+1e-8,'remaining old debit dominated by true drawdown');
   if(moved){const a=x.pre.t<y.pre.t?x:y,b=x.pre.t<y.pre.t?y:x,r0=r[C/2];creditEnergy+=2*r0*((v.t-a.pre.t)/(2*r0))*((v.t-b.pre.t)/(2*r0));}
   if(same&&d<=m){lowTruePaid+=2*rem;rem=0;}
   if(rem>0){
    if(same&&q&&d>6&&d!==6*(t%2)){
     const rr=(q>=Y&&lag>=q)||lag>=lagCut;
     if(rr)ok(2*r[C/2]>lagCut,'large-lag roughness');
     const id=C+':'+t+':'+q+':'+(+rr),g=improved.get(id)||{C,t,q,d,rough:rr,mass:0,rest:0};
     g.mass+=2;g.rest+=2*rem;improved.set(id,g);if(rr&&q<Y)impLongSmall+=2*rem;
    }else if(same)impSame+=2*rem;else impDirect+=2*rem;
   }
   // Independent true first-meeting check on a deterministic pair sample:
   // intersect actual half-open waiting intervals at common horizons.
   if((x.i*131+y.i*17)%4093===0){
    const a=paths[x.i],b=paths[y.i];let k=0,l=0,first=null;
    while(k<a.length&&l<b.length){if(a[k].C<b[l].C){k++;continue;}if(b[l].C<a[k].C){l++;continue;}
     const lo0=Math.max(a[k].t,b[l].t),hi0=Math.min(k+1<a.length?a[k+1].t-1:a[k].t,l+1<b.length?b[l+1].t-1:b[l].t);
     if(lo0<=hi0){first=[lo0,a[k].C];break;}k++;l++;
    }ok(first&&first[0]===t&&first[1]===C,'independent true meeting');oracle++;
   }
  }
 }
 ok(trueL===oldL+firstMatched&&trueD===trueI+trueL&&oldDebit+entrySaving===newDebit+firstMatched,'integrated transfer');
 // Count independent relaxed later-arrival support per (deficit band,q).
 const types=new Map();let roughPaid=0,plainPaid=0,roughKeys=0,plainKeys=0,roughMass=0,plainMass=0;
 for(const g of groups.values()){const j=band(g.d),id=j+':'+g.q+':'+(+g.rough),s=types.get(id)||{j,q:g.q,rough:g.rough,n:0};s.n++;types.set(id,s);
  const paid=g.rest*Math.min(1,cap(g.d,g.q,g.rough)/g.mass);
  if(g.rough){roughPaid+=paid;roughRaw+=g.rest;roughKeys++;roughMass+=g.mass;}else{plainPaid+=paid;plainRaw+=g.rest;plainKeys++;plainMass+=g.mass;}
 }
 let supportChecks=0,envelope=0;
 const impTypes=new Map();let impEnvelope=0,impChecks=0;
 for(const g of improved.values()){
  const j=band(g.d),D=lim/2**j,h0=g.q>=Y?1:ell0;
  const c=B*m*g.q*(g.rough?u*u:1)/(D*D*(j+1)**2*h0),paid=g.rest*Math.min(1,c/g.mass);
  if(g.rough){impRoughPaid+=paid;impRawRough+=g.rest;}else{impPlainPaid+=paid;impRawPlain+=g.rest;}
  const id=j+':'+g.q+':'+(+g.rough),v=impTypes.get(id)||{j,q:g.q,rough:g.rough,n:0};v.n++;impTypes.set(id,v);
 }
 for(const {j,q,rough,n} of impTypes.values()){
  const D=lim/2**j;let cnt=0;
  for(const s of [0,1])for(let k=1;6*s+2*q*k<=D;k++){const d=6*s+2*q*k;if(d<=D/2)continue;
   let C=2*X+(((-2*s-2*X)%q+q)%q);if(C%2)C+=q;if(((C+d)/2)%2!==s)C+=2*q;
   for(;C<7*X;C+=4*q)if(!rough||2*r[C/2]>lagCut)cnt++;
  }ok(n<=cnt,'improved long-lag envelope');impEnvelope+=cnt;impChecks++;
 }
 const impRest=impRawRough+impRawPlain-impRoughPaid-impPlainPaid+impSame+impDirect;
 ok(Math.abs(oldAfter-impMixedPaid-improvedOld)<1e-6*Math.max(1,oldAfter)&&Math.abs(improvedOld-credit-lowTruePaid-impRoughPaid-impPlainPaid-impRest)<1e-6*Math.max(1,oldAfter),'old debit priority partition');
 ok(credit<=24*creditEnergy+1e-6,'conditional first rise credit');
 const improvement={lagCut,improvedOld,credit,creditEnergy,lowTruePaid,impRoughPaid,impPlainPaid,impRawRough,impRawPlain,impDirect,impSame,impLongSmall,impMixedPaid,impRest,impChecks,impEnvelope,keys:improved.size};
 for(const s0 of types.values()){const {j,q,rough,n}=s0,D=lim/2**j;let cnt=0;
  for(const s of [0,1])for(let k=1;6*s+2*q*k<=D;k++){const d=6*s+2*q*k;if(d<=D/2)continue;
   let C=2*X+(((-2*s-2*X)%q+q)%q);if(C%2)C+=q;if(((C+d)/2)%2!==s)C+=2*q;
   for(;C<7*X;C+=4*q)if(!rough||2*r[C/2]>q)cnt++;
  }ok(n<=cnt,'later arrival envelope');envelope+=cnt;supportChecks++;
 }
 return {improvement,X,B,mode,m,Y,N,R,events,literal,pairs,oldI,oldEntry,oldDebit,newDebit,trueL,oldL,firstMatched,firstRise,firstDrop,entrySaving,trueA,trueD,rootLate,rootEarly,sameIncoming,sameIncomingLarge,earlyMixed,longLag,shortLag,maxLag,smallTrue,newSmall,oldSmall,oldAfter,newAfter,roughPaid,plainPaid,rest:newAfter-roughPaid-plainPaid,roughRaw,plainRaw,roughKeys,plainKeys,roughMass,plainMass,supportChecks,envelope,oracle,localCredit,maxNew};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
