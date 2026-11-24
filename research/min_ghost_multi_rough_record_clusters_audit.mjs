// Multiple rough return tickets and local root-collision audit.
function audit(U,N=128){
 const V=4*U,ps=[],sv=new Uint8Array(V+1);
 for(let p=2;p<=V;p++)if(!sv[p]){if(p>2)ps.push(p);if(p*p<=V)for(let q=p*p;q<=V;q+=p)sv[q]=1}
 const mod=(x,p)=>(x%p+p)%p,ck=(a,m)=>{if(!a)throw Error(m)};
 let rng=(0xa791e351^U)>>>0;function u32(){rng^=rng<<13;rng^=rng>>>17;rng^=rng<<5;return rng>>>0}
 function uni(p){let a=4294967296-4294967296%p,x;do{x=u32()}while(x>=a);return x%p}
 const z0=Math.ceil(Math.sqrt(2*U)),Q=Math.max(7,Math.floor(z0/8)),K=3;
 const c=new Int32Array(ps.length),t=new Int32Array(ps.length),first=new Int32Array(ps.length),best=new Float64Array(ps.length);
 const out={U,V,N,z0,Q,K,events:0,peakSum:0,firstCount:0,repeatLong:0,repeatRecordLong:0,rootLong:0,rootRecordLong:0,localRootChecks:0,noninvertible:0,collision:0,fullRoots:0,recordTimeChecks:0,rows:[2,3].map(k=>({k,allClusters:0,allWeight:0,recordClusters:0,recordWeight:0,rootClusters:0,rootWeight:0,rootRecordClusters:0,rootRecordWeight:0,ticketCount:0,ticketWeight:0,rootTicketWeight:0,checks:0,recordTimeClusters:0}))};
 function rough(p,g){for(let j=0;j<ps.length&&ps[j]<=47&&8*ps[j]<=p;j++)if([1,ps[j]-1].includes(mod(c[j]+g,ps[j])))return false;return true}
 for(let n=0;n<N;n++){
  let parity=uni(2);first.fill(-1);best.fill(-Infinity);
  for(let j=0;j<ps.length;j++){let p=ps[j];c[j]=uni(p);let a=uni(p);t[j]=a%2===parity?a:a+p;}
  // Enumerate forbidden roots for two and three distinct slopes.
  for(let j=0;j<24;j++){
   let k=2+j%2,v=uni(2*U+1),ms=[1+uni(2*U+1)],as=[2*(uni(3)-1)];
   for(let h=1;h<k;h++){ms.push(ms[h-1]+1+uni(12));as.push(2*(uni(3)-1))}
   for(let i=0;i<ps.length&&ps[i]<=47;i++){
    let ell=ps[i],bad=ms.some(m=>m%ell===0)||ms.some((m,h)=>ms.slice(0,h).some(a=>(m-a)%ell===0));
    let forb=new Set([0]);for(let x=0;x<ell;x++)if(ms.some((m,h)=>[1,ell-1].includes(mod(c[i]+v+as[h]+m*x,ell))))forb.add(x);
    out.localRootChecks++;
    if(bad){out.noninvertible++;continue;}
    let roots=[];for(let h=0;h<k;h++)for(let sg of [-1,1]){let rr=[];for(let x=0;x<ell;x++)if(mod(c[i]+v+as[h]+ms[h]*x-sg,ell)===0)rr.push(x);ck(rr.length===1,"unique root");roots.push(rr[0])}
    let distinct=new Set([0,...roots]);ck(distinct.size===forb.size,"union roots");
    if(distinct.size===2*k+1)out.fullRoots++;else{
     out.collision++;let witness=roots.includes(0)||roots.some((x,h)=>roots.slice(0,h).includes(x));ck(witness,"collision witness");
     for(let h=0;h<k;h++)for(let j0=0;j0<h;j0++)for(let s1 of [-1,1])for(let s2 of [-1,1]){
      let a=roots[2*h+(s1===1?1:0)],b=roots[2*j0+(s2===1?1:0)];
      ck((a===b)===(mod(ms[j0]*(s1-c[i]-v-as[h])-ms[h]*(s2-c[i]-v-as[j0]),ell)===0),"collision linear equation");
     }
    }
   }
  }
  let e=0,g=0,peak=0,lists=new Map(),all=new Map(),records=new Map(),budget=[0,0],rootBudget=[0,0],weights=[0,0],rootWeights=[0,0],recordWeights=[0,0],rootRecordWeights=[0,0];
  function countTickets(p,map,k){let total=0;function walk(m,depth){if(depth===k){total++;return}for(let a=1;a<=K;a++)for(let x of map.get(m+a)||[])walk(m+a,depth+1)}for(let [m,gs] of map)for(let x of gs)walk(m,1);return total}
  for(;;){
   let w=Infinity,i=-1;for(let j=0;j<ps.length;j++){let p=ps[j],cc=mod(c[j]+g,p);if(cc!==1&&cc!==p-1)continue;let f=2*p-mod(t[j]+e-(cc===1?0:p+2),2*p);if(f<w||(f===w&&p<ps[i])){w=f;i=j}}
   if(e+w>U)break;
   let p=ps[i],fresh=first[i]<0,J=2*(e+w)-g-p+1-6*((parity+e+w)%2),rec=J>best[i];
   if(fresh){first[i]=g;if(p>=Q&&p<=2*U+1&&g<=2*U){
     out.firstCount++;let map=new Map(),lookup=new Map();for(let m=1;m*p-2<=2*U-g;m++)for(let a of [-2,0,2]){
      let x=g+m*p+a;if(x<g+p-1||x>2*U||x%2||!rough(p,x))continue;ck(!lookup.has(x),"ticket unique");lookup.set(x,m);if(!map.has(m))map.set(m,[]);map.get(m).push(x);
     }lists.set(i,lookup);
     for(let j=0;j<2;j++){let k=j+2,n=countTickets(p,map,k),r=out.rows[j];r.ticketCount+=n;r.ticketWeight+=p*n;budget[j]+=p*n;if(p>=z0){rootBudget[j]+=p*n;r.rootTicketWeight+=p*n}}
   }}else if(p>=Q&&g<=2*U&&4*w>p){
    out.repeatLong++;out.repeatRecordLong+=+rec;out.rootLong+=+(p>=z0);out.rootRecordLong+=+(p>=z0&&rec);
    let m=lists.get(i)?.get(g);ck(m!==undefined&&rough(p,g),"actual long return in ticket list");
    let x={m,g,s:e+w,J};let a=all.get(i)||[],b=records.get(i)||[];
    a.push(x);all.set(i,a);
    if(rec){if(b.length){let y=b[b.length-1];ck(J-y.J>=2*p&&x.s-y.s>=2*p&&x.m>y.m,"strict long record interval");if(x.s-y.s<=K*p){ck(x.m-y.m<=2*K+1,"local time implies local gain");out.recordTimeChecks++}}b.push(x);records.set(i,b);}
    for(let j=0;j<2;j++){
     let k=j+2,r=out.rows[j];let valid=v=>v.length>=k&&v.slice(-k+1).every((y,h)=>y.m-v[v.length-k+h].m<=K&&y.m>v[v.length-k+h].m);
     if(valid(a)){r.allClusters++;r.allWeight+=p;weights[j]+=p;if(p>=z0){r.rootClusters++;r.rootWeight+=p;rootWeights[j]+=p}r.checks++}
     if(rec&&valid(b)){r.recordClusters++;r.recordWeight+=p;recordWeights[j]+=p;if(p>=z0){r.rootRecordClusters++;r.rootRecordWeight+=p;rootRecordWeights[j]+=p}r.checks++}
     if(rec&&b.length>=k&&b.slice(-k+1).every((y,h)=>y.s-b[b.length-k+h].s<=K*p))r.recordTimeClusters++;
    }
   }
   best[i]=Math.max(best[i],J);e+=w;g+=p-1;peak=Math.max(peak,2*e-g);out.events++;
  }
  for(let j=0;j<2;j++){ck(weights[j]<=budget[j]&&recordWeights[j]<=budget[j]&&rootWeights[j]<=rootBudget[j]&&rootRecordWeights[j]<=rootBudget[j],"weighted cluster ticket injection");ck(weights[j]<=4*U&&recordWeights[j]<=4*U,"realized weight cap")}
  out.peakSum+=peak;
 }
 return out;
}
for(const U of process.argv.slice(2).map(Number))console.log(JSON.stringify(audit(U,U>=65536?128:256)));
