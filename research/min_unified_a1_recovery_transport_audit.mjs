// Actual prime-root MIN and exact BigInt canonical control; weights in fifth-deficit units.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(x,m)=>(x%m+m)%m;
 const limit=Math.max(7*Math.max(...Xs)+100,40000),spf=new Int32Array(limit+1),primes=[];
 for(let p=2;p<=limit;p++)if(!spf[p]){primes.push(p);for(let j=p;j<=limit;j+=p)if(!spf[j])spf[j]=p}
 const a1=(p,d,dp,I)=>p>=47&&p>=5*d+15&&dp-6*I===2*p;
 const blank=()=>({marks:0,total:0,paid:0,pending:0,late:0,long:0,largeRelay:0,shortRelay:0,reset:0,nonreset:0,thinDirect:0,thinRelay:0,longGain:0,area:0,matches:0});
 function inspect(es,B,c,out){
  const {R,Y,l,A,M}=c;ok(Y>R&&4*l<Y/5,"config");
  let runs=[],runAt=new Map();
  for(let i=0;i<es.length;){if(es[i].p>R){i++;continue}let k=i;while(k+1<es.length&&es[k+1].p<=R)k++;
   let r={i,k,g:es[k].J-es[i].C,pre:i?es[i-1]:null};runs.push(r);for(let j=i;j<=k;j++)runAt.set(j,r);i=k+1}
  let G=es.length?es.at(-1).J-es[0].C:0,pending=[],dir=new Map(),rel=new Map(),area=0,late=0,long=0,largeRelay=0,shortRelay=0,reset=0,nonreset=0,total=0,paid=0,marks=0;
  let longGain=runs.filter(r=>r.g>=4*l).reduce((a,r)=>a+r.g,0);
  for(let k=0;k<es.length;k++){
   const e=es[k],x=5*(e.d+3),xp=5*(e.dp+3),g=e.p-1;
   let last=0,norm=0,raw=0;for(let a of pending.slice().sort((a,b)=>a.a-b.a)){ok(a.a>=last&&a.b<=x&&a.a>=Y&&a.b<=5*B,"pending disjoint bounded");last=a.b;raw+=a.b-a.a;norm+=(a.b-a.a)*a.weight/a.p}
   ok(raw<=5*B&&norm<=15*Math.log(5*B/Y)+1e-8,"pending capacity");area+=g*norm;
   if(xp<x){
    let remain=[],local=0,locWeight=0;
    for(let a of pending){let lo=Math.max(xp,a.a),hi=Math.min(x,a.b);if(hi<=lo){remain.push(a);continue}
     ok(hi===a.b&&a.i<k,"first downcross");let len=hi-lo,w=len*a.weight,lag=e.C-es[a.i].J;ok(lag>=0,"lag");local+=len;locWeight+=w;paid+=w;out.matches++;if(lo>a.a)remain.push({...a,b:lo});
     if(lag>=A*a.p){late+=w;continue}
     const D=e.dp-6*e.I;if(D===0)ok(e.p>a.p/5-9,"reset scale");else ok(!e.near&&e.p<a.p/2&&e.dp+3>2*a.p/15&&e.dp+3<a.p,"nonreset scale");
     if(e.p<=R){let r=runAt.get(k);ok(r&&r.pre&&r.i>a.i&&D!==0,"low provider");if(r.g>=4*l){long+=w;continue}
      let f=r.pre,dx=f.dp-6*f.I;ok(dx!==0&&!f.a1&&!f.near,"short low precursor not RESET/A1/near");
      ok(5*(f.dp+3)>=hi&&5*(f.dp+3)<=lo+5*r.g,"precursor band");
      ok(f.p<(a.p+r.g)/2&&dx>a.p/5-9,"precursor multiplier");
      ok(f.C>=es[a.i].J&&f.C-es[a.i].J<=lag,"precursor age");
      rel.set(r.i,(rel.get(r.i)||0)+w);if(f.p>=M*l)largeRelay+=w;else shortRelay+=w;
     }else{dir.set(k,(dir.get(k)||0)+w);if(D===0)reset+=w;else nonreset+=w}
    }
    ok(local<=x-xp&&locWeight<=3*(x-xp),"provider cap");pending=remain;
   }
   if(e.a1&&e.p>=Y&&e.p>R){let a=e.p,b=5*e.p,weight=1+e.p%3;ok(x<=a&&xp>b&&!pending.some(z=>Math.min(z.b,b)>Math.max(z.a,a)),"mark birth");pending.push({a,b,p:e.p,i:k,weight});total+=(b-a)*weight;marks++}
  }
  let pend=pending.reduce((s,a)=>s+(a.b-a.a)*a.weight,0);ok(total===paid+pend&&paid===late+long+largeRelay+shortRelay+reset+nonreset,"partition");
  ok(pend<=15*B&&late*A<=area+1e-6&&area<=15*G*Math.log(5*B/Y)+1e-6,"age and terminal");ok(long<=15*longGain&&largeRelay<=90*G/M+1e-6,"run and large relay");
  let thinDirect=0,thinRelay=0;for(let [k,w] of dir){let e=es[k];ok(w<=15*Math.max(0,e.d-e.dp),"direct cap");if(w/e.p<=5)thinDirect+=w}
  for(let [k,w] of rel){let r=runAt.get(k);ok(r.i===k&&w<=15*r.g&&r.g<4*l,"relay cap");if(r.pre.p<M*l&&w/(4*l)<=5)thinRelay+=w}
  for(let [key,v] of Object.entries({marks,total,paid,pending:pend,late,long,largeRelay,shortRelay,reset,nonreset,thinDirect,thinRelay,longGain,area}))out[key]+=v;
 }
 const configs=[{R:3,Y:67,l:2,A:1,M:4},{R:5,Y:77,l:3,A:2,M:16},{R:7,Y:87,l:4,A:4,M:4}];
 const runs=[];
 for(let X of Xs){let B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),N=0,events=0,reaches=0,literal=0,outputs=configs.map(c=>({config:c,...blank()}));
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){N++;let C=2*M-2,t=M+2,es=[];
   while(C-(2*M-2)<T){let p=0,w=Infinity,I=0;for(let side=0;side<2;side++){let z=C-1+2*side;while(z>1){let s=spf[z];while(z%s===0)z/=s;if(s*s>C+1)continue;let w0=mod((side?s+2:0)-t,2*s)||2*s;if(w0<w||w0===w&&s<p){p=s;w=w0;I=side}}}
    if(!p)break;let J=C+p-1,d=2*t-C,dp=2*(t+w)-J,q=(C-1+2*I)/p,xx=(q+p)/2,kk=(q-p)/2,near=xx>=64&&2*kk*kk<=xx;
    if(X===4096){for(let z=t+1;z<=t+w;z++){let a=z-2*(z%2),b=C-1+2*(z%2);while(b){let v=a%b;a=b;b=v}let s=a>1?spf[a]:0;if(s&&s*s>C+1)s=0;ok(s===(z===t+w?p:0),"literal gcd");literal++}}
    ok(d>=0&&dp>=0&&w<=3*(p-1),"model");es.push({C,J,p,w,d,dp,I,a1:a1(p,d,dp,I),near});C=J;t+=w;
   }events+=es.length;if(C-(2*M-2)>=T)reaches++;for(let o of outputs)inspect(es,B,o.config,o);
  }runs.push({X,B,T,N,events,reaches,literal,outputs});
 }
 // Prior exact canonical witness from the independent precursor-exclusion audit.
 const word=[10039,6709,4513,7],p=word[0],r=word[2],sh=[0];for(let s of word)sh.push(sh.at(-1)+s-1);
 let C=0n,Q=4n,crt=0;
 for(let s of primes.filter(s=>s>=3&&s<=3*p+6)){let at=word.indexOf(s),rr=at>=0?mod((at===3?-1:1)-sh[at],s):0;
  let valid=x=>sh.slice(0,3).every((h,i)=>word[i]===s?mod(x+h,s)===1:![1,s-1].includes(mod(x+h,s)))&&(s!==7||mod(x+sh[3],s)===s-1)&&((2*r-3)%s!==0||s===7||mod(x+sh[3],s)!==s-1);
  if(at<0)while(rr<s&&!valid(rr))rr++;ok(rr<s&&valid(rr),"CRT");
  let a=Number(Q%BigInt(s)),b=s,u=1,v=0;while(b){let k=Math.floor(a/b);[a,b]=[b,a-k*b];[u,v]=[v,u-k*v]}ok(a===1,"inverse");C+=Q*BigInt(mod(u*mod(rr-Number(C%BigInt(s)),s),s));Q*=BigInt(s);crt+=4;
 }
 if(C<100000000n)C+=Q;
 let C0=C,t=C/2n+3n,es=[],ticks=0;
 for(let i=0;i<word.length;i++){let s=word[i],d=Number(2n*t-C),w=i===3?1:(3*s-d-1)/2,v=t+BigInt(w);
  for(let j=1;j<=w;j++){let n=t+BigInt(j),I=n%2n,a=n-2n*I,b=C-1n+2n*I;while(b)[a,b]=[b,a%b];ok(a===BigInt(j===w?s:1),"CRT literal");ticks++}
  let J=C+BigInt(s-1),dp=Number(2n*v-J),I=Number(v%2n);ok(BigInt(s)**2n<=C+1n,"eligible");let co=(C-1n+2n*BigInt(I))/BigInt(s),kk=(co-BigInt(s))/2n,xx=(co+BigInt(s))/2n,near=xx>=64n&&2n*kk*kk<=xx;
  es.push({C:Number(C-C0),J:Number(J-C0),p:s,w,d,dp,I,a1:a1(s,d,dp,I),near});C=J;t=v;
 }
 const witness=[];
 for(let c of [{R:7,Y:10000,l:400,A:4,M:4},{R:7,Y:10000,l:400,A:4,M:16},{R:7000,Y:10000,l:400,A:4,M:16},{R:7,Y:10000,l:400,A:.1,M:16}]){let o={config:c,...blank()};inspect(es,p,c,o);witness.push(o)}
 ok(witness.some(o=>o.shortRelay>0)&&witness.some(o=>o.largeRelay>0)&&witness.some(o=>o.late>0)&&witness.some(o=>o.long>0),"witness exercises all");
 return {runs,witness,rootDigits:(C0/2n+1n).toString().length,ticks,crt,word,deficits:es.map(e=>e.dp)};
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
