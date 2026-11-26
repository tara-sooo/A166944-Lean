// Time-localized height guard flux and scale-restricted upward source capacities.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g,q:(H-1+2*I)/p}}}return z}
 function union(a){let out=[];for(let [l,r] of a.sort((a,b)=>a[0]-b[0])){if(out.length&&l<=out.at(-1)[1])out.at(-1)[1]=Math.max(r,out.at(-1)[1]);else out.push([l,r])}return out}
 const st={roots:0,events:0,cap:0,controls:0,bins:0,nonemptyGuards:0,fastSelected:0,upward:0,lowSources:0,midSources:0,largeSources:0,roughResidues:0,localProgressions:0,fluxChecks:0,largeTailChecks:0,localBalances:0,globalBalances:0,nonzeroMid:0,nonzeroTail:0,disconnected:0,multiBins:0,sourceLabels:0,nearChecks:0,examples:[],synthetic:0};
 function inspect(rows,T,L,mode){
  if(!rows.length)return;
  let k=Math.floor(Math.sqrt(T));if(k<3)return;
  let groups=[];for(let z of rows){let j=Math.floor(z.H/L);if(!groups.length||groups.at(-1).j!==j)groups.push({j,rows:[]});groups.at(-1).rows.push(z)}
  let C=Math.max(...rows.map(z=>z.p)),G=0,FC=0,MC=0,LC=0,IC=0,TC=0,Nb=0,has=false;
  for(let {j,rows:v} of groups){
   let gain=v.reduce((s,z)=>s+z.g,0);G+=gain;ok(gain<=L+C,"bin gain");
   let sel=v.filter(z=>z.p>=T&&z.dp>6&&k*z.w<z.g);if(mode===1&&sel.length){let a=sel[0].dp;sel=sel.filter(z=>Math.abs(z.dp-a)<=T)}if(!sel.length)continue;
   let E=union(sel.map(z=>[z.dp,z.dp+z.g])),M=E.reduce((s,[a,b])=>s+b-a,0),F=sel.reduce((s,z)=>s+z.g,0),B=Math.max(T,2*M+1);
   const phi=d=>E.reduce((s,[a,b])=>s+Math.max(0,Math.min(d,b)-a),0);
   let low=0,mid=0,tail=0,drop=0,counts=new Map,up=0;let ids=new Set(sel);
   for(let z of v){let dv=phi(z.dp)-phi(z.d);ok(Math.abs(dv)<=Math.abs(z.dp-z.d)&&Math.abs(dv)<=M,"flux");st.fluxChecks++;
    if(ids.has(z)){ok(k*(-dv)>(k-2)*z.g,"fast drop");drop-=dv}
    if(dv<=0)continue;st.upward++;up+=dv;ok(z.dp>z.d&&2*z.w>z.g,"upward clock");
    if(z.p<T){low+=dv;st.lowSources++;continue}
    if(z.p>B){tail+=dv;st.largeSources++;ok(dv*(B-1)<=M*z.g,"large tail");continue}
    mid+=dv;st.midSources++;
    ok(dv<=Math.min(M,3*z.g+4),"source cap");let key=[z.p,z.I].join(","),o=counts.get(key)||{p:z.p,I:z.I,qs:[],flux:0};o.qs.push(z.q);o.flux+=dv;counts.set(key,o);
    ok(E.some(([a,b])=>z.dp>a&&z.d<b&&z.dp<=b+3*z.g+4),"source height locality");st.nearChecks++;
    for(let f of pr){if(4*f>=z.g||f>=z.p)break;ok(z.q%f!==0&&(z.p*z.q+2*z.e)%f!==0,"rough");st.roughResidues++}
   }
   for(let o of counts.values()){let qs=o.qs;ok(qs.every((q,i)=>!i||q>qs[i-1])&&qs.at(-1)-qs[0]<L/o.p+1&&o.flux<=qs.length*Math.min(M,3*o.p+1),"local progression");st.localProgressions++}
   ok(k*drop>(k-2)*F&&up===low+mid+tail,"positive partition");ok(drop<=up+phi(v[0].d)-phi(v.at(-1).dp),"exact potential");
   ok((k-2)*F<=k*(low+mid+tail+M)&&tail*(B-1)<=M*gain,"local balance");st.localBalances++;st.largeTailChecks++;if(mid)st.nonzeroMid++;if(tail)st.nonzeroTail++;if(E.length>1)st.disconnected++;
   if(st.examples.length<3&&mid&&tail)st.examples.push({T,L,j,M,B,F,gain,low,mid,tail,labels:[...counts.values()].map(o=>o.p),E});
   st.sourceLabels+=new Set([...counts.values()].map(o=>o.p)).size;st.fastSelected+=sel.length;st.nonemptyGuards++;FC+=F;MC+=M;LC+=low;IC+=mid;TC+=tail;Nb++;has=true;
  }
  ok((k-2)*FC<=k*(MC+LC+IC+TC)&&2*TC<=G,"global clipped tail");st.globalBalances++;st.controls++;st.bins+=groups.length;if(Nb>1)st.multiBins++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
 for(let T of [9,17,31,61])for(let mode of [0,1])inspect(rows,T,4*T*T,mode)}
 // Independent exact overlap tail controls.
 for(let i=1;i<=2000;i++){let E=union([[i%23,i%23+3],[40+i%7,60+i%7]]),M=E.reduce((s,[a,b])=>s+b-a,0),p=3+2*(i%200),B=2*M+1;let a=i%90,b=a+3*p+1,over=E.reduce((s,[u,v])=>s+Math.max(0,Math.min(b,v)-Math.max(a,u)),0);ok(over<=Math.min(M,b-a),"overlap");if(p>B)ok(over*(B-1)<=M*(p-1),"tail");st.synthetic++}
 ok(st.fastSelected&&st.midSources&&st.largeSources&&st.lowSources&&st.multiBins&&st.roughResidues&&st.disconnected,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
