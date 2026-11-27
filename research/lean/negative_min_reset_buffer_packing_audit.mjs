// Reset-buffer packing and mixed-scale Selberg arithmetic: finite controls only.
// Run: node research/lean/negative_min_reset_buffer_packing_audit.mjs
function audit(){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,m)=>(a%m+m)%m;
 const MAX=1600002,sp=new Int32Array(MAX+3);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let q=p*p;q<sp.length;q+=p)if(!sp[q])sp[q]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor domain");a.push(p);while(n%p===0)n/=p}return a}
 function trial(n){let a=[];for(let p=3;p*p<=n;p+=2)if(n%p===0){a.push(p);while(n%p===0)n/=p}if(n>1)a.push(n);return a}
 function next(x,n){let w=Infinity,p=0,s=0;for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){w=t;p=q;s=e}}return {w,p,s}}
 function literal(x,n,T){let a=trial(x-1),b=trial(x+1);for(let i=1;i<=T;i++){let nn=n+i,fs=nn%2===0?b:a,ps=fs.filter(p=>mod(nn,2*p)===(nn%2===0?0:p+2));if(ps.length)return {w:i,p:Math.min(...ps),s:nn%2===0?1:-1}}return null}
 const qmin=x=>Math.min(sp[x-1],sp[x+1]);
 let roots=0,firstTicks=0,pairs=0,pairPins=0,roughChecks=0,detChecks=0,mixedChecks=0,wordChecks=0,shortTicks=0,shortEvents=0,crossEvents=0,crossTicks=0,uniqueCuts=0,sourceChecks=0,stationaryChecks=0,squarePairs=0,squareSameLabelPairs=0,squareRoots=0,squareTicks=0,squareEvents=0,squarePositionChecks=0,rows=[];
 function forms(x,p,low,shifts,divs,mixed=false){
  let M=[...new Set([p,...low])].reduce((a,r)=>a*BigInt(r),1n);
  let f=shifts.map((d,i)=>{let r=BigInt(divs[i]);ok(M%r===0n&&BigInt(x+d)%r===0n,"integer forms");return [M/r,BigInt(x+d)/r]});
  let bad=BigInt(1);for(let [a] of f)bad*=a;
  for(let i=0;i<f.length;i++)for(let j=i+1;j<f.length;j++){let d=f[i][0]*f[j][1]-f[j][0]*f[i][1];ok(d!==0n,"distinct roots");detChecks++;bad*=d;}
  if(mixed)for(let l of [11,13,17,19,23,29,31,37])if(bad%BigInt(l)!==0n){
   let n4=0,n2=0;for(let t=0;t<l;t++){let hit=f.map(([a,b])=>(a*BigInt(t)+b)%BigInt(l)===0n);if(hit.some(Boolean))n4++;if(hit[0]||hit[1])n2++}
   ok(n4===4&&n2===2,"mixed residue count");mixedChecks++;
  }
 }
 for(let [R,J,K] of [[12000,4,17],[48000,6,23],[192000,10,31],[768000,16,43]]){
  let H=Math.max(1,Math.floor(J/2)),arr=[];
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let p=sp[A+1],v=(A+1)/p;if(p<=Math.max(4*J,K)||v<=p||sp[v]!==v||p%12!==1||v%12!==1||sp[A-1]<p)continue;
   let x=A-p+1;if(qmin(x)<11)continue;
   let n=3-A/2,e=next(A,n),l=literal(A,n,e.w);
   ok(e.p===p&&e.s===1&&e.w===(p-7)/2&&l&&l.p===p&&l.w===e.w,"reset event");
   ok(n+e.w===-x/2&&literal(x,n+e.w,3)===null,"three ticks");roots++;firstTicks+=e.w+3;sourceChecks++;
   arr.push({A,p,x,bad:false});
  }
  arr.sort((a,b)=>a.x-b.x);
  let near=0,roughBad=0;
  const T=Math.ceil(8*Math.sqrt(2*R+1)),D=4*T+20;let E=0,same=0;
  for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length&&arr[j].x-arr[i].x<=D;j++){
   let a=arr[i],b=arr[j],d=b.x-a.x;E++;squarePairs++;
   if(a.p===b.p){ok(d%a.p===0&&d>0,"same-label far pin");same++;squareSameLabelPairs++}
   else forms(a.x,a.p,[b.p],[a.p,a.p-2,d+b.p,d+b.p-2],[a.p,1,b.p,1]);
  }
  let sep=[];for(let a of arr)if(!sep.length||a.x-sep[sep.length-1].x>D)sep.push(a);
  ok(sep.length*(arr.length+2*E)>=arr.length**2,"independent set lower");
  let visited=new Map(),sqEvents=0;
  for(let a of sep){
   let x=a.A,n=3-x/2,t=0;squareRoots++;
   while(true){
    ok(x>=a.A-2*t-6&&x<=a.A&&x>=a.x-2*T-6&&x<=a.x+a.p-1,"square horizon envelope");
    if(visited.has(x))ok(visited.get(x)===a.A,"square horizon spatial separation");else visited.set(x,a.A);
    squarePositionChecks++;
    let e=next(x,n);if(t+e.w>T){ok(literal(x,n,T-t)===null,"square literal tail");squareTicks+=T-t;break}
    let l=literal(x,n,e.w);ok(l&&l.p===e.p&&l.w===e.w&&l.s===e.s,"square literal event");t+=e.w;n+=e.w;x-=e.p-1;squareTicks+=e.w;squareEvents++;sqEvents++;
   }
  }
  for(let i=0;i<arr.length;i++){
   let a=arr[i];for(let j=i+1;j<arr.length&&arr[j].x-a.x<=4*J;j++){
    let b=arr[j],d=b.x-a.x;ok(a.p!==b.p&&a.x%a.p===0&&b.x%b.p===0,"near pair pins");pairPins+=2;
    ok((d+b.p-a.p)%6===0&&(d+b.p-a.p)!==0,"source difference");
    forms(a.x,a.p,[b.p],[a.p,a.p-2,d+b.p,d+b.p-2],[a.p,1,b.p,1]);pairs++;near++;a.bad=b.bad=true;
   }
   let any=false;
   for(let d=-4*J;d<=4*J;d+=2){let y=a.x+d;roughChecks++;if(qmin(y)>=K){forms(a.x,a.p,[],[a.p,a.p-2,d-1,d+1],[a.p,1,1,1],true);any=true;}}
   if(any){a.bad=true;roughBad++}
  }
  let good=arr.filter(a=>!a.bad),owner=new Map(),cuts=new Set(),maxCross=0,lowEvents=0,zero=0;
  for(let a of good){
   let x=a.x,n=3-x/2,t=0,ev=0,g=0,word=[];
   for(let i=0;i<=H;i++){
    ok(x>=a.x-J-6&&x<=a.x&&qmin(x)<K,"common horizon envelope");
    if(owner.has(x))ok(owner.get(x)===a.A,"disjoint actual positions");else owner.set(x,a.A);
    stationaryChecks++;
    if(i===H)break;
    let l=literal(x,n,1);if(l){x-=l.p-1;g+=l.p-1;word.push(l.p);ev++;shortEvents++;ok(l.p<=2*(i+1)+7,"age bound");forms(x,a.p,word,[g+a.p,g+a.p-2,-1,1],[a.p,1,1,1],true);wordChecks++;}
    n++;t++;shortTicks++;
   }
   if(ev===0)zero++;lowEvents+=ev;
   // Independent crossing run from reset: include pre-crossing sites only.
   x=a.x;n=3-x/2;t=0;
   while(x>=a.x-J){
    ok(qmin(x)<K,"clear interval");let e=next(x,n),l=literal(x,n,e.w);
    ok(l&&l.p===e.p&&l.w===e.w&&l.s===e.s,"crossing literal");ok(e.w<2*K,"cross wait");
    if(owner.has(x))ok(owner.get(x)===a.A,"pre-crossing disjoint");else owner.set(x,a.A);
    let y=x-e.p+1;for(let cut=Math.max(y,a.x-J);cut<x;cut++){ok(!cuts.has(cut),"unique assigned cuts");cuts.add(cut);uniqueCuts++;}
    x=y;n+=e.w;t+=e.w;crossEvents++;crossTicks+=e.w;
   }
   ok(t<=2*K*(Math.floor(J/2)+1),"crossing time");maxCross=Math.max(maxCross,t);
  }
  ok(cuts.size===good.length*J,"all assigned unit cuts swept");
  rows.push({R,J,K,H,roots:arr.length,near,roughBad,retained:good.length,lowEvents,zero,distinctVisited:owner.size,assignedCuts:cuts.size,maxCross,squareHorizon:T,squarePairCount:E,sameLabelPairs:same,squareSelected:sep.length,squareEvents:sqEvents});
 }
 // Check expansion majorant at individual small integer differences.
 let expansionChecks=0;
 for(let n=3;n<=10000;n++){
  let ps=[...new Set([...fac(n-2),...fac(n),...fac(n+2)])].filter(p=>p>=11);
  let num=1n,den=1n,numU=1n,denU=1n;
  for(let p of ps){num*=BigInt(p);den*=BigInt(p-4);numU*=BigInt(p+8);denU*=BigInt(p);}
  ok(num*denU<=numU*den,"bad factor expansion majorant");expansionChecks++;
 }
 return {roots,firstTicks,pairs,pairPins,roughChecks,detChecks,mixedChecks,wordChecks,shortTicks,shortEvents,crossEvents,crossTicks,uniqueCuts,sourceChecks,stationaryChecks,expansionChecks,squarePairs,squareSameLabelPairs,squareRoots,squareTicks,squareEvents,squarePositionChecks,rows}
}
console.log(JSON.stringify(audit(),null,2));
