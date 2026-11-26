// Ordered high-word spatial/clock rounding and coupled low-gain cone certificates.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(x,p)=>(x%p+p)%p,N=400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function event(a,v){let p=Infinity,w=Infinity,e=0,q=Infinity;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){q=Math.min(q,r);let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e,q}}
 function up(b,r,m){return b+mod(r-b,m)}
 let z={canonicalRoots:0,canonicalEvents:0,canonicalBlocks:0,otherRoots:0,otherEvents:0,otherBlocks:0,controls:0,marks:0,distinctFirst:0,spaceChecks:0,timeChecks:0,slackChecks:0,iterations:0,maxIterations:0,spaceExact:0,timeExact:0,jointExact:0,jointImproves:0,clockImproves:0,shortGainChecks:0,shortTimeChecks:0,shortGainAll:0,shortTimeAll:0,controlsWithMarks:0,maxGainImprovement:0,meanRatioSum:0,ratioControls:0,positiveSpace:0,positiveJoint:0,examples:[],rows:[]};
 function check(arr,A,v0,T,row){
  let M=Math.floor((T-2)/2),D=6*M-1,sh=0,uh=0,s=0,u=0,gs=0,gu=0,js=0,ju=0,jl=0,jr=0,first=new Set(),shortS=true,shortU=true,oldS=0,oldU=0,lastS=0,lastU=0,n=0;
  ck(M>=1,"M");
  for(let x of arr){
   if(x.p<T){s+=(x.p-1)/2;u+=x.w;ck(x.w<=3*(x.p-1)&&(x.p-1)/2<=M*x.w,"cone event");continue}
   let p=x.p,as=mod((A-2*sh-x.e)*((p+1)/2),p),au=mod((x.e===-1?0:p+2)-v0-uh-x.w,2*p);
   // use safe arithmetic: N small, p<=N+1, product < 2^53
   ck(mod(s-as,p)===0,"space residue");ck(mod(u-au,2*p)===0,"time residue");
   z.spaceChecks++;z.timeChecks++;n++;z.marks++;if(!first.has(p)){first.add(p);z.distinctFirst++}
   gs=up(gs,as,p);gu=up(gu,au,2*p);
   ck(gs<=s&&gu<=u,"independent greedy");
   if(s-oldS>=p)shortS=false;if(u-oldU>=2*p)shortU=false;
   if(shortS){ck(gs===s,"short gain exact");z.shortGainChecks++}
   if(shortU){ck(gu===u,"short time exact");z.shortTimeChecks++}
   oldS=s;oldU=u;
   let al=mod(6*as-au,2*p),ar=mod(M*au-as,p),sl=6*s-u,sr=M*u-s;
   ck(mod(sl-al,2*p)===0&&mod(sr-ar,p)===0,"slack residues");
   ck(sl>=jl&&sr>=jr,"slack monotone");z.slackChecks++;
   sh+=(p-1)/2;uh+=x.w;
   // h after high event = A/2+v0 + uh+u - sh-s
   let C=sh-uh-A/2-v0;
   let iter=0;
   while(true){
    let ns=up(Math.max(js,Math.ceil((ju+jl)/6),Math.ceil((M*jl+jr)/D)),as,p),
        nu=up(Math.max(ju,Math.ceil((js+jr)/M),Math.ceil((jl+6*jr)/D),js+C),au,2*p),
        nl=up(jl,al,2*p),nr=up(jr,ar,p);
    ck(ns<=s&&nu<=u&&nl<=sl&&nr<=sr,{A,T,p,ns,nu,nl,nr,s,u,sl,sr});
    iter++;if(ns===js&&nu===ju&&nl===jl&&nr===jr)break;js=ns;ju=nu;jl=nl;jr=nr;
   }
   z.iterations+=iter;z.maxIterations=Math.max(z.maxIterations,iter);
   ck(js>=gs&&ju>=gu,"joint dominates");
   if(gs===s)z.spaceExact++;if(gu===u)z.timeExact++;if(js===s&&ju===u)z.jointExact++;
   if(js>gs){z.jointImproves++;z.maxGainImprovement=Math.max(z.maxGainImprovement,2*(js-gs));if(z.examples.length<8)z.examples.push({A,T,p,gs:2*gs,js:2*js,actual:2*s,gu,ju,u})}
   if(ju>gu)z.clockImproves++;lastS=s;lastU=u;
  }
  z.controls++;if(n){z.controlsWithMarks++;if(shortS)z.shortGainAll++;if(shortU)z.shortTimeAll++;if(gs)z.positiveSpace++;if(js)z.positiveJoint++;if(lastS){z.meanRatioSum+=js/lastS;z.ratioControls++}}
  row.controls++;row.marks+=n;row.actual+=2*lastS;row.space+=2*gs;row.joint+=2*js;
 }
 // Every canonical root through 60000: stopped prefix, trim crossing
 // event so all gains lie within half-distance budget.
 let row={type:"canonical",controls:0,marks:0,actual:0,space:0,joint:0};
 for(let A=12;A<=60000;A+=6){let a=A,v=-A/2+3,arr=[];while(a>A/2){let x=event(a,v);if(v+x.w>-1)break;z.canonicalEvents++;if(a-x.p+1<=A/2)break;arr.push({a,v,...x});a-=x.p-1;v+=x.w}
  for(let T of [11,Math.max(5,Math.ceil(Math.sqrt(A)/4)),Math.max(5,Math.ceil(Math.sqrt(A)))])check(arr,A,-A/2+3,T,row);
  z.canonicalRoots++;if(arr.length)z.canonicalBlocks++;
 }z.rows.push(row);
 for(let R of [10000,40000,100000,180000]){
  let row={type:"noncanonical",R,controls:0,marks:0,actual:0,space:0,joint:0};
  for(let vmode of [0,17,1])for(let A=2*R-300+(6-(2*R-300)%6)%6;A<2*R;A+=6){
   let a=A,v=vmode===1?Math.floor(A/5):vmode,arr=[];
   function flush(){if(!arr.length)return;for(let T of [11,23,Math.max(5,Math.ceil(Math.sqrt(R)/4)),Math.ceil(Math.sqrt(R))])check(arr,arr[0].a,arr[0].v,T,row);z.otherBlocks++;arr=[]}
   while(a>=R){let x=event(a,v);if(x.q>Math.sqrt(a+1))flush();else arr.push({a,v,...x});a-=x.p-1;v+=x.w;z.otherEvents++}
   flush();z.otherRoots++;
  }z.rows.push(row);
 }
 return z
}
console.log(JSON.stringify(audit(),null,2));
