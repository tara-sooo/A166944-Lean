// Clustered recovery matching with exact geometric levels and completed slabs.
function audit(N=30000){
 const spf=new Int32Array(Math.max(100000,4*N+30000));for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const mod=(x,p)=>(x%p+p)%p;
 const st={roots:0,events:0,blocks:0,rejectedNear:0,markedBlocks:0,marks:0,slots:0,matched:0,lowPaid:0,exceptionSlots:0,pendingSlots:0,clusters:0,pointChecks:0,slabs:0,slabPayments:0,good:0,bad:0,goodWeight:0,bandClusters:0,witnesses:[]};
 function inspect(ev,S,R,T0=47,phase=0,tag=null){
  if(!ev.length)return;
  let K=0,L=0,C=0;
  for(let v of ev){C=Math.max(C,v.p);if(v.p<=S){L+=v.p-1;K=Math.max(K,L)}else L=0}
  let T=Math.max(T0,200*K,47),marked=ev.map(v=>v.a1&&v.p>R&&v.p>=T);
  st.blocks++;if(!marked.some(Boolean))return;
  for(let i=0;i<ev.length;i++)if(marked[i])for(let j=i;j<ev.length;j++)if(ev[j].near&&25*ev[j].p<24*ev[i].p){st.rejectedNear++;return}
  st.markedBlocks++;
  // Geometric reference levels ratio 31/20, exact common denominator.
  let a=BigInt(phase||T),b=BigInt(phase?1:5);
  while(5n*a>=31n*BigInt(T)*b/20n){ // exact correction to avoid truncation at boundary
   if(100n*a<31n*BigInt(T)*b)break;
   a*=20n;b*=31n;
  }
  while(5n*a<BigInt(T)*b){a*=31n;b*=20n}
  let ar=[];while(10n*a<=19n*BigInt(C)*b){ar.push([a,b]);a*=31n;b*=20n}
  if(ar.length<5)throw Error("grid");
  const D=ar.at(-1)[1],ys=ar.map(([a,b])=>a*(D/b));
  if(ar.some(([a,b])=>D%b!==0n))throw Error("denominator");
  let active=ys.map(()=>null),pending=[],marks=[],cluster=null,matched=0,lowPaid=0,exc=0,slots=0,slabs=0,bandClusters=0;
  function close(){if(!cluster)return;let v=cluster.v;
   if(cluster.point.length){
    if(!v)throw Error("initial run paid");
    if(v.a1||v.near&&v.D!==0)throw Error("precursor");
    if(v.D!==0&&cluster.point.length>1)throw Error("two levels in nonreset cluster");
    if(v.D===0)exc+=cluster.point.length;else{matched++;if(cluster.point[0].low)lowPaid++}
   }
   let pay=cluster.pay;
   if(pay>0n){
    if(!v||v.a1||v.near&&v.D!==0)throw Error("slab precursor");
    if(pay>BigInt(v.p-1+K)*D)throw Error("capacity");
    if(v.D!==0&&v.p<=R)bandClusters++;
   }
   cluster=null;
  }
  for(let i=0;i<ev.length;i++){
   let v=ev[i],x=BigInt(v.d+3)*D,y=BigInt(v.dp+3)*D;
   if(v.p>S){close();cluster={v,point:[],pay:0n,start:i};st.clusters++}
   else if(!cluster)cluster={v:null,point:[],pay:0n,start:i};
   if(marked[i]){
    let inds=[];for(let j=0;j<ys.length;j++)if(5n*ys[j]>BigInt(v.p)*D&&10n*ys[j]<=19n*BigInt(v.p)*D)inds.push(j);
    if(inds.length<5)throw Error("slot lower");
    let m={p:v.p,i,bad:false,pending:0n,paid:0n,assigned:0n,slots:inds.length};marks.push(m);slots+=inds.length;st.marks++;
    for(let j of inds){if(active[j]!==null||x>=ys[j]||y<ys[j])throw Error("up slot");active[j]=m}
    for(let j of inds.slice(0,-1)){let a=ys[j],b=ys[j+1];if(pending.some(o=>o.a<b&&a<o.b))throw Error("overlap");pending.push({a,b,m,j});m.pending+=b-a;m.assigned+=b-a;slabs++}
    if(3100n*m.assigned<2839n*BigInt(v.p)*D)throw Error("slab width");
   }
   if(y>=x)continue;
   for(let j=0;j<ys.length;j++)if(active[j]&&y<ys[j]&&ys[j]<=x){
    let m=active[j],z=cluster.v;if(!z||z.a1||z.near&&z.D!==0)throw Error("point precursor");
    if(z.D!==0){if(2n*BigInt(z.p)*D>=ys[j]+BigInt(K-3)*D||30n*BigInt(z.D)*D<=4n*BigInt(m.p)*D-270n*D)throw Error("point scale");st.pointChecks++}
    cluster.point.push({j,m,low:v.p<=S});active[j]=null;
   }
   let left=[],pay=0n;
   for(let o of pending){let a=o.a>y?o.a:y,b=o.b<x?o.b:x;if(b>a){
     let z=cluster.v;if(!z||z.a1||z.near&&z.D!==0)throw Error("allocation precursor");
     if(z.D===0||z.p>R)o.m.bad=true;
     o.m.pending-=b-a;o.m.paid+=b-a;pay+=b-a;st.slabPayments++;
    }
    if(o.a<y)left.push({...o,b:o.b<y?o.b:y});
   }
   if(pay>x-y)throw Error("payment");cluster.pay+=pay;pending=left;
  }
  close();
  let remain=active.filter(Boolean).length,N=ev.filter(v=>v.D===0&&v.p>=7).length; // reset count, rather than inferred canonical visits, in finite audit
  if(matched+exc+remain!==slots||5*marks.length>matched+(N+1)*ys.length)throw Error("point count");
  let good=0,bad=0,weight=0,paid=0n;
  for(let m of marks){if(m.paid+m.pending!==m.assigned)throw Error("conservation");if(m.pending||m.bad)bad++;else{good++;weight+=m.p;paid+=m.paid}}
  let exceptional=ev.filter(v=>v.p>S&&(v.D===0||v.p>R&&!v.a1&&!v.near)).length;
  if(bad>(exceptional+1)*ys.length||paid>BigInt(bandClusters*(R-1+K))*D||3100n*paid<2839n*BigInt(weight)*D)throw Error("slab supply");
  st.slots+=slots;st.matched+=matched;st.lowPaid+=lowPaid;st.exceptionSlots+=exc;st.pendingSlots+=remain;st.slabs+=slabs;st.good+=good;st.bad+=bad;st.goodWeight+=weight;st.bandClusters+=bandClusters;
  if(tag)st.witnesses.push({tag,S,R,T,K,phase,marks:marks.length,slots,matched,lowPaid,pendingSlots:remain,slabs,good,bad,weight,bandClusters,goodPaid:Number(paid)/Number(D)});
 }
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,ev=[];st.roots++;
  for(let j=0;j<180;j++){if(H+Math.sqrt(H+1)>=spf.length)break;let a=next(t,H);if(!a)break;let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,q=(H-a.e)/a.p,b=(q-a.p)/2,c=(q+a.p)/2;ev.push({...a,d,dp,I,D,a1:a.p>=47&&a.p>=5*d+15&&D===2*a.p,near:c>=64&&2*b*b<=c});H=Z;t=n;st.events++}
  for(let i=0;i<ev.length;i++)if(ev[i].a1)for(let S of [3,5,7,11])for(let len of [1,4,12])inspect(ev.slice(i,i+len),S,47);
 }
 // Reconstruct both previous canonical CRT controls, independently verifying every tick.
 function witness(word,oddLast=false){
  let sh=[0],max=Math.max(...word);for(let p of word)sh.push(sh.at(-1)+p-1);
  let H=0n,P=4n,checks=0;
  for(let s=3;s<=3*max+6;s+=2){if(spf[s]!==s)continue;let at=word.indexOf(s),rr=at>=0?mod((oddLast&&at===word.length-1?-1:1)-sh[at],s):0;
   function valid(x){return sh.slice(0,oddLast?-2:-1).every((h,i)=>word[i]===s?mod(x+h,s)===1:![1,s-1].includes(mod(x+h,s)))&&(!oddLast||((s!==7||mod(x+sh[word.length-1],s)===s-1)&&((2*word.at(-2)-3)%s!==0||s===7||mod(x+sh[word.length-1],s)!==s-1)))}
   if(at>=0){if(!valid(rr))throw Error("selected")}else{while(rr<s&&!valid(rr))rr++;if(rr===s)throw Error("empty")}
   let L=BigInt(s),a=Number(P%L),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}if(a!==1)throw Error("inverse");H+=P*BigInt(mod(u*mod(rr-Number(H%L),s),s));P*=L;checks+=word.length;
  }
  if(H<100000000n)H+=P;
  let H0=H,t=H/2n+3n,rel=0,ev=[];
  for(let i=0;i<word.length;i++){let p=word[i],d=Number(2n*t-H),w=oddLast&&i===word.length-1?1:(3*p-d-1)/2,n=t+BigInt(w);
   for(let j=1;j<=w;j++){let tick=t+BigInt(j),e=tick%2n?-1n:1n,a=e===1n?tick:tick-2n,b=H-e;while(b)[a,b]=[b,a%b];if(a!==(j===w?BigInt(p):1n))throw Error("literal")}
   let Z=H+BigInt(p-1),dp=Number(2n*n-Z),I=Number(n%2n),D=dp-6*I;
   if(BigInt(p)**2n>H+1n)throw Error("eligibility");
   ev.push({p,w,d,dp,I,D,a1:p>=47&&p>=5*d+15&&D===2*p,near:false});H=Z;t=n;rel+=w;
  }
  // Huge H, small selected p: all are far, since a near label exceeds .96 sqrt(H-1).
  if(H0<10n**20n)throw Error("far");
  let tag={word,rootDigits:(H0/2n+1n).toString().length,ticks:rel,checks};
  return {ev,tag};
 }
 let a=witness([10039,6709,4513,7],true);for(let S of [3,5,7,11])inspect(a.ev,S,7000,10000,9027,a.tag);
 let b=witness([7687,5233,3541,2389,1621,1093,733,7369]);for(let S of [3,5,7,47])inspect(b.ev,S,7500,7000,0,b.tag);
 if(!st.witnesses.some(w=>w.lowPaid>0)||!st.witnesses.some(w=>w.good>0))throw Error("witness coverage");
 return st;
}
console.log(JSON.stringify(audit(Number(process.argv[2]||30000)),null,2));
