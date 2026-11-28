// Modular short-path approximation: actual high anchors and separate local CRT lattice checks.
// Run: node research/lean/negative_min_modular_short_transfer_audit.mjs
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)}, mod=(a,m)=>(a%m+m)%m;
 const MAX=6200010,sp=new Int32Array(MAX),pr=[];
 for(let p=2;p<MAX;p++)if(!sp[p]){sp[p]=p;pr.push(p);if(p*p<MAX)for(let j=p*p;j<MAX;j+=p)if(!sp[j])sp[j]=p}
 function factors(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a}
 function trialFactors(n){let a=[];for(let p of pr){if(p*p>n)break;if(n%p===0){a.push(p);while(n%p===0)n/=p}}if(n>1)a.push(n);return a}
 function labels(x,n){let s=mod(n,2)?-1:1;return factors(x+s).filter(q=>mod(n,2*q)===(s===1?0:q+2))}
 function next(x,n){let w=Infinity,p=0;for(let s of [-1,1])for(let q of factors(x+s)){let u=mod((s===1?0:q+2)-n,2*q)||2*q;if(u<w||u===w&&q<p){w=u;p=q}}return{w,p}}
 function base(z){return 4*pr.filter(p=>p>2&&p<=z).reduce((a,b)=>a*b,1)}
 function small(x,n,z){let s=mod(n,2)?-1:1;for(let q of pr){if(q>z)break;if(q>2&&mod(x+s,q)===0&&mod(n,2*q)===(s===1?0:q+2))return q}return 0}
 function profile(x,n,z,T){let g=0,a=[];for(let u=1;u<=T;u++){let q=small(x-g,n+u,z);a.push({g,q});if(q)g+=q-1}return a}
 let rows=[],canonicalRoots=0,anchors=0,firstChecks=0,profileChecks=0,repeatedProfiles=0,divisorChecks=0,outsidePins=0,rawDefects=0,effectiveDefects=0,good=0,actualTicks=0,nearPairs=0,separatedStates=0,strictIncrease=0,allSmallEvents=0,firstDivergenceChecks=0;
 for(let [R,z,T] of [[12000,5,8],[48000,7,10],[192000,7,14],[768000,11,20],[3072000,11,25]]){
  let B=base(z),D=z*T,cache=new Map(),keep=[],aCount=0,badCount=0,effCount=0,incCount=0;
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   canonicalRoots++;let p=sp[A+1],v=(A+1)/p;
   if(p<=D+12||v<=4*p||sp[v]!==v||v%12!==7||sp[A-1]<4*p)continue;
   let w=(3*p-7)/2,e=next(A,3-A/2);ok(e.p===p&&e.w===w,"first actual high event");firstChecks++;anchors++;aCount++;
   let x=p*(v-1),n=p-x/2,key=mod(p,B)+","+mod(v,B),plan=profile(x,n,z,T);
   let reduced=profile(mod(x,B),mod(n,B),z,T);ok(JSON.stringify(plan)===JSON.stringify(reduced),"translation profile");profileChecks++;
   if(cache.has(key)){ok(cache.get(key)===JSON.stringify(plan),"same residue pair");repeatedProfiles++;}else cache.set(key,JSON.stringify(plan));
   let bad=false,firstEff=0,gg=0;
   for(let u=1;u<=T;u++){
    let {g,q}=plan[u-1],s=mod(n+u,2)?-1:1,b=s===1?0:3,y=x-g;
    let all=labels(y,n+u),ff=2*p+2*u-g+1-2*b;
    ok(ff>0&&g%2===0&&g<p-1,"positive pin");
    let via=factors(ff).filter(t=>t>z&&mod(y+s,t)===0&&mod(n+u,2*t)===(s===1?0:t+2));
    let out=all.filter(t=>t>z);ok(via.join(",")===out.join(","),"outside divisor enumeration");divisorChecks++;
    for(let t of out){ok(t!==p&&ff%t===0&&mod(p*(v-1)-g+s,t)===0,"two pins");outsidePins++}
    if(out.length)bad=true;
    if(!q&&out.length&&!firstEff)firstEff=u;
    ok(q===(all.find(t=>t<=z)||0),"trial min");
    if(q)gg=g+q-1;
   }
   if(bad){rawDefects++;badCount++}
   if(firstEff){effectiveDefects++;effCount++}
   let ax=x,nn=n,firstDiff=0,recs=[[x,n]];
   for(let u=1;u<=T;u++){
    let s=mod(nn+1,2)?-1:1,fac=trialFactors(ax+s),lab=fac.find(t=>mod(nn+1,2*t)===(s===1?0:t+2))||0;
    ok(lab===(labels(ax,nn+1)[0]||0),"independent literal");actualTicks++;
    let tr=plan[u-1];if(!firstDiff&&(ax!==x-tr.g||lab!==tr.q))firstDiff=u;
    if(lab)ax-=lab-1;nn++;recs.push([ax,nn]);
   }
   ok(firstDiff===firstEff,"first effective defect equality");firstDivergenceChecks++;
   if(!bad){
    ok(!firstDiff&&ax===x-gg&&ax/2+nn===p+T-gg/2,"good full suffix");
    ok(gg<=D&&ax/2+nn>=p-D/2,"gain and height");good++;
    if(ax/2+nn>p){strictIncrease++;incCount++}
    allSmallEvents+=plan.filter(t=>t.q).length;keep.push({x,n,p,recs});
   }
  }
  keep.sort((a,b)=>a.x-b.x);let bad=new Set();
  for(let i=0;i<keep.length;i++)for(let j=i+1;j<keep.length&&keep[j].x-keep[i].x<=D;j++){
   let a=keep[i],b=keep[j];if(Math.abs(a.n-b.n)>T)continue;ok(a.p!==b.p&&Math.abs(a.p-b.p)<=T+D/2,"near pins");bad.add(i);bad.add(j);nearPairs++;
  }
  let states=new Set();for(let i=0;i<keep.length;i++)if(!bad.has(i))for(let [x,n] of keep[i].recs){let k=x+","+n;ok(!states.has(k),"separated actual connectors");states.add(k);separatedStates++}
  rows.push({R,z,T,B,anchors:aCount,profiles:cache.size,anyOutside:badCount,effectiveDefects:effCount,retained:keep.length,strictIncrease:incCount,separated:keep.length-bad.size,states:states.size});
 }
 // A separate local lattice audit. All states are noncanonical unless a
 // canonical ancestor is separately proved; here none is asserted.
 let localRows=[],latticeStarts=0,latticeGood=0,latticeBad=0,latticePins=0,latticeCrtChecks=0,latticeLiteralTicks=0,activeLocal=0;
 for(let [z,D,R,H] of [[5,3,24000,400],[7,4,48000,900],[11,6,192000,6000]]){
  let Q=base(z),X0=R,X1=2*R,H0=H,H1=2*H,classes=[];
  // select successful vertical trial classes and a few moving classes
  for(let a=0;a<Q&&classes.length<16;a+=2)for(let b=0;b<Q&&classes.length<16;b++){
   let n=b-a/2,plan=profile(a,n,z,3*D),g=0,t=0,hit=false;
   for(let j=0;j<plan.length;j++){let q=plan[j].q;if(q)g+=q-1;t=j+1;if(t-g/2===D){hit=true;break}if(g>4*D)break}
   if(!hit||g>4*D)continue;
   // Mix different residues, not exhaustive class sampling.
   if(mod(a+3*b,17)!==0)continue;
   classes.push({a,b,g,t,plan:plan.slice(0,t)});
  }
  let localStart=0,localGood=0,localBad=0,crtTotal=0;let outputSet=new Set();
  for(let a of classes){
   let xx=X0+mod(a.a-X0,Q),hh=H0+mod(a.b-H0,Q);
   let nx=Math.max(0,Math.floor((X1-xx)/Q)+1),nh=Math.max(0,Math.floor((H1-hh)/Q)+1);
   // Exact CRT count for each possible outside-prime eligibility at each
   // planned prestate, checked against direct lattice enumeration.
   let counts=new Map(),upper=0;
   for(let u=1;u<=a.t;u++){
    let g=a.plan[u-1].g,s=mod(a.b-a.a/2+u,2)?-1:1,b=s===1?0:3;
    for(let q of pr){if(q<=z)continue;if(q>4*H+20)break;
     let cx=0,ch=0;for(let i=0;i<nx;i++)if(mod(xx+i*Q-g+s,q)===0)cx++;
     for(let j=0;j<nh;j++)if(mod(2*(hh+j*Q)+2*u-g+1-2*b,q)===0)ch++;
     ok(cx<=nx/q+1&&ch<=nh/q+1,"CRT lattice count");
     if(cx&&ch){counts.set(u+","+q,cx*ch);upper+=cx*ch}
     latticeCrtChecks++;
    }
   }
   let observed=new Map(),bad=0;
   for(let i=0;i<nx;i++)for(let j=0;j<nh;j++){
    let x=xx+i*Q,h=hh+j*Q,n=h-x/2;localStart++;latticeStarts++;let fail=false;
    for(let u=1;u<=a.t;u++){
     let y=x-a.plan[u-1].g;
     for(let q of labels(y,n+u))if(q>z){fail=true;let k=u+","+q;observed.set(k,(observed.get(k)||0)+1);latticePins++}
    }
    if(fail){bad++;localBad++;latticeBad++;continue}
    localGood++;latticeGood++;
    let y=x,nn=n;
    for(let u=1;u<=a.t;u++){
     let q=labels(y,nn+1)[0]||0;ok(q===a.plan[u-1].q,"actual local path");if(q)y-=q-1;nn++;latticeLiteralTicks++;
    }
    ok(y===x-a.g&&y/2+nn===h+D,"local first section");
    if(Math.min(sp[x-1],sp[x+1])<=2*z)activeLocal++;
    outputSet.add(y+","+(h+D));
   }
   ok(bad<=upper,"union count");
   for(let [k,v] of counts)ok((observed.get(k)||0)===v,"exact CRT count equals literal eligibility");
   for(let [k,v] of observed)ok(counts.get(k)===v,"no uncounted pins");
   crtTotal+=upper;
  }
  localRows.push({z,D,R,H,Q,classes:classes.length,starts:localStart,good:localGood,bad:localBad,unionUpper:crtTotal,distinctOutputs:outputSet.size});
 }
 return{rows,localRows,canonicalRoots,anchors,firstChecks,profileChecks,repeatedProfiles,divisorChecks,outsidePins,rawDefects,effectiveDefects,good,actualTicks,nearPairs,separatedStates,strictIncrease,allSmallEvents,firstDivergenceChecks,latticeStarts,latticeGood,latticeBad,latticePins,latticeCrtChecks,latticeLiteralTicks,activeLocal}
}
console.log(JSON.stringify(audit(),null,2));
