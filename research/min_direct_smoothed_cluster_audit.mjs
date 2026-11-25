// Scale-local cluster matching with exceptional long low-label runs.
function audit(N=30000){
 const spf=new Int32Array(Math.max(100000,4*N+30000));for(let i=2;i<spf.length;i++)if(!spf[i]){spf[i]=i;if(i*i<spf.length)for(let j=i*i;j<spf.length;j+=i)if(!spf[j])spf[j]=i}
 const mod=(a,b)=>(a%b+b)%b,st={roots:0,events:0,blocks:0,marks:0,slots:0,bandSlots:0,longSlots:0,exceptionSlots:0,pendingSlots:0,intersections:0,paidLong:0,paidBand:0,paidExceptional:0,clusters:0,positiveBandClusters:0,positiveLongRuns:0,capacityChecks:0,periodTests:0,controls:[]};
 const tbl=new Map();
 for(let S of [3,5,7,11,13]){
  let ps=[];for(let p=3;p<=S;p+=2)if(spf[p]===p)ps.push(p);let P=ps.reduce((a,p)=>a*p,1),pre=new Int32Array(P+1);
  for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>j%p<=(p-3)/2)?1:0);
  let A=pre[P],cnt=j=>Math.floor(j/P)*A+pre[mod(j,P)],mom=new Map;
  tbl.set(S,{P,cnt,variance:l=>{if(!mom.has(l)){let sum=0;for(let j=0;j<P;j++)sum+=(P*(cnt(j+l)-cnt(j))/(A*l)-1)**2;mom.set(l,sum/P)}return mom.get(l)}})
 }
 function check(ev,S,R,T,U,K,tag=null){
  if(!ev.length||T<48||200*K>T)return;
  let mark=ev.map(v=>v.a1&&v.p>R&&v.p>=T&&v.p<=U);if(!mark.some(Boolean))return;
  for(let i=0;i<ev.length;i++)if(mark[i])for(let j=i;j<ev.length;j++)if(ev[j].near&&25*ev[j].p<24*ev[i].p)return;
  st.blocks++;
  let cl=[],which=[],G=0,reset=0,B=0;
  for(let i=0;i<ev.length;i++){let v=ev[i];G+=v.p-1;if(v.p>S){cl.push({v,i,low:0,slots:[],paid:0n,band:false,except:false});if(v.D===0)reset++;else if(!v.near&&!v.a1&&v.p>R)B++}else{if(!cl.length)cl.push({v:null,i,low:0,slots:[],paid:0n,band:false,except:false});cl.at(-1).low+=v.p-1}which.push(cl.at(-1))}
  let a=BigInt(T),b=5n,ar=[];while(10n*a<=19n*BigInt(U)*b){ar.push([a,b]);a*=31n;b*=20n}
  let D=10n*ar.at(-1)[1],ys=ar.map(([a,b])=>a*(D/b)),L=ys.length,span=(19n*BigInt(U)-2n*BigInt(T))*(D/10n);
  if(U<=2*T&&L>7)throw Error("dyadic slots");
  let pend=[],active=ys.map(()=>null),W=0,m=0,slots=0,lowPaid=0n,bandPaid=0n,excPaid=0n,bs=0,ls=0,es=0;
  function scale(c,p,y){let v=c.v;if(!v||v.D===0||v.a1||v.near||v.p<=S)throw Error("precursor");
   if(2n*BigInt(v.p)*D>=y+BigInt(K-3)*D||30n*BigInt(v.D)*D<=BigInt(4*p-270)*D||v.p>=p)throw Error("scale");
  }
  for(let i=0;i<ev.length;i++){let v=ev[i],c=which[i],x=BigInt(v.d+3)*D,y=BigInt(v.dp+3)*D;
   if(mark[i]){
    let lo=BigInt(v.p)*(D/5n),hi=19n*BigInt(v.p)*(D/10n);
    if(x>lo||y<hi||pend.some(o=>o.a<hi&&lo<o.b))throw Error("up allocation");
    pend.push({a:lo,b:hi,p:v.p});let num=0;
    for(let j=0;j<L;j++)if(lo<ys[j]&&ys[j]<=hi){if(active[j]!==null)throw Error("slot overlap");active[j]=v.p;num++}
    if(num<5)throw Error("five");slots+=num;W+=v.p;m++;
   }
   if(y>=x)continue;
   for(let j=0;j<L;j++)if(active[j]!==null&&y<ys[j]&&ys[j]<=x){
    let p=active[j];active[j]=null;if(!c.v)throw Error("initial");
    if(c.slots.includes(j))throw Error("repeat slot");c.slots.push(j);
    if(c.low>K){ls++;continue}
    if(c.v.D===0||c.v.p>R&&!c.v.near&&!c.v.a1){es++;continue}
    scale(c,p,ys[j]);bs++;
   }
   let next=[],pay=0n;
   for(let o of pend){let aa=o.a>y?o.a:y,bb=o.b<x?o.b:x;if(bb>aa){
    let z=bb-aa;pay+=z;st.intersections++;
    if(v.p<=S&&c.low>K){lowPaid+=z;c.longPaid=(c.longPaid||0n)+z}
    else{
     if(!c.v||c.v.a1||c.v.near&&c.v.D!==0)throw Error("payment precursor");
     if(c.v.D===0||c.v.p>R){excPaid+=z;c.except=true;c.exc=(c.exc||0n)+z}
     else{scale(c,o.p,bb);bandPaid+=z;c.band=true;c.paid+=z}
    }
   }if(o.a<y)next.push({...o,b:o.b<y?o.b:y})}
   if(pay>x-y)throw Error("per-event");pend=next;
  }
  let J=0,long=0,GL=0,exc=0,BC=0;
  for(let c of cl){
   st.clusters++;if(c.low>K){long++;GL+=c.low}
   if(c.longPaid){if(c.longPaid>BigInt(c.low)*D)throw Error("long capacity");st.positiveLongRuns++}
   if(c.band){J++;if(c.paid>BigInt(c.v.p-1+(c.low<=K?c.low:0))*D)throw Error("band capacity")}
   if(c.except){exc++;if(c.exc>span)throw Error("exception capacity")}
   if(c.low<=K&&c.v&&c.v.D!==0&&!c.v.near&&!c.v.a1&&c.v.p<=R){BC+=c.slots.length;if(c.slots.length>1)throw Error("injective")}
  }
  let pending=pend.reduce((s,o)=>s+o.b-o.a,0n),ps=active.filter(v=>v!==null).length;
  if(17n*BigInt(W)*(D/10n)!==pending+lowPaid+bandPaid+excPaid||pending>span||exc>reset+B||slots!==bs+ls+es+ps||bs!==BC||5*m>J+L*(reset+B+long+1)||17n*BigInt(W)*(D/10n)>BigInt((R-1+K)*J+GL)*D+span*BigInt(reset+B+1))throw Error("global capacity");
  st.capacityChecks++;st.marks+=m;st.slots+=slots;st.bandSlots+=bs;st.longSlots+=ls;st.exceptionSlots+=es;st.pendingSlots+=ps;st.paidLong+=Number(lowPaid)/Number(D);st.paidBand+=Number(bandPaid)/Number(D);st.paidExceptional+=Number(excPaid)/Number(D);st.positiveBandClusters+=J;
  let tb=tbl.get(S);
  if(tb&&K>=4&&ev[0].H!==undefined){
   let l=Math.min(tb.P,Math.floor(K/4));
   for(let c of cl){if(!c.low)continue;let start=c.v?ev[c.i].H+c.v.p-1:ev[c.i].H;if(tb.cnt(start/2+c.low/2)!==tb.cnt(start/2))throw Error("barrier")}
   if(l===tb.P?GL!==0:GL>4*(G/2+tb.P)*tb.variance(l)+1e-7)throw Error("variance cap");st.periodTests++;
  }
  if(tag)st.controls.push({tag,S,R,T,U,K,marks:m,J,long,GL,bandSlots:bs,longSlots:ls,exceptionSlots:es,pending:ps,lowPaid:Number(lowPaid)/Number(D),bandPaid:Number(bandPaid)/Number(D)});
 }
 function next(t,H){let a=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!a||w<a.w||w===a.w&&p<a.p)a={p,e,w}}}return a}
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,ev=[];st.roots++;for(let j=0;j<180;j++){if(H+Math.sqrt(H+1)>=spf.length)break;let a=next(t,H);if(!a)break;let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I,q=(H-a.e)/a.p,b=(q-a.p)/2,c=(q+a.p)/2;ev.push({...a,H,d,dp,I,D,a1:a.p>=47&&a.p>=5*d+15&&D===2*a.p,near:c>=64&&2*b*b<=c});H=Z;t=n;st.events++}
  for(let i=0;i<ev.length;i++)if(ev[i].a1)for(let S of [3,5,7,11])for(let len of [4,12]){let T=ev[i].p;check(ev.slice(i,i+len),S,47,T,2*T,Math.floor(T/200))}
 }
 // Independently rebuild the prior eight-event exact CRT witness.
 let word=[7687,5233,3541,2389,1621,1093,733,7369],sh=[0];for(let p of word)sh.push(sh.at(-1)+p-1);
 let H=0n,P=4n,checks=0;
 for(let s=3;s<=3*Math.max(...word)+6;s+=2){if(spf[s]!==s)continue;let at=word.indexOf(s),rr=at>=0?mod(1-sh[at],s):0;let valid=x=>sh.slice(0,-1).every((h,i)=>word[i]===s?mod(x+h,s)===1:![1,s-1].includes(mod(x+h,s)));if(at>=0){if(!valid(rr))throw Error("CRT")}else{while(rr<s&&!valid(rr))rr++;if(rr===s)throw Error("empty")}
  let L=BigInt(s),a=Number(P%L),b=s,u=1,v=0;while(b){let q=Math.floor(a/b);[a,b]=[b,a-q*b];[u,v]=[v,u-q*v]}if(a!==1)throw Error("inverse");H+=P*BigInt(mod(u*mod(rr-Number(H%L),s),s));P*=L;checks+=word.length}
 if(H<100000000n)H+=P;let H0=H,t=H/2n+3n,ticks=0,ev=[];
 for(let p of word){let d=Number(2n*t-H),w=(3*p-d-1)/2,n=t+BigInt(w);for(let j=1;j<=w;j++){let tick=t+BigInt(j),e=tick%2n?-1n:1n,a=e===1n?tick:tick-2n,b=H-e;while(b)[a,b]=[b,a%b];if(a!==(j===w?BigInt(p):1n))throw Error("literal");ticks++}let Z=H+BigInt(p-1),dp=Number(2n*n-Z);if(dp!==2*p||BigInt(p*p)>H+1n)throw Error("post");ev.push({p,w,d,dp,D:dp,I:0,a1:p>=47&&p>=5*d+15,near:false});H=Z;t=n}
 let tag={rootDigits:(H0/2n+1n).toString().length,ticks,checks};
 for(let S of [47,750,1700,3600,6000])check(ev,S,7500,7000,14000,35,tag);
 if(!st.controls.some(x=>x.longSlots>0&&x.lowPaid>0)||!st.controls.some(x=>x.bandSlots>=5))throw Error("coverage");
 return st;
}
console.log(JSON.stringify(audit(Number(process.argv[2]||30000)),null,2));
