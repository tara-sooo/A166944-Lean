// Actual reset triple/four-form and canonical height-flux finite audit.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let out=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J;path.push({C,t,J,n,I,e:1-2*I,p,w,g:p-1,d,dp,reset:dp===6*I});events++;C=J;t=n;
   }tags.push({M,C0,F:C,df:2*t-C,path})
  }
  for(let Y of [11,31,61]){
   let P=Math.min(B,4*Y),K=4,k=Math.floor(Math.sqrt(Y)),controls=0,triples=0,good=0,bad=0,first=0,F=0,Rw=0,roughPairs=0,roughChecks=0,rootChecks=0,pairTuples=0,oneTuples=0,pairCap=0,oneCap=0,goodGain=0,prevGain=0,fluxControls=0,selected=0,short=0,ext=0,positive=0,outPos=0,resetPos=0,terminal=0,guardLen=0,fluxEvents=0,disconnected=0,extChecks=0;
   for(let t of tags){
    let list=t.path.filter(e=>e.reset&&e.p>=Y&&e.p<=P),n=list.length;
    if(n){controls++;let f=list.reduce((s,e)=>s+e.g,0),rwb=0,gb=0,bb=0,fb=list.slice(0,2).reduce((s,e)=>s+e.g,0),pairs=new Map(),ones=new Map();
     F+=f;first+=fb;
     for(let j=1;j<n;j++){let a=list[j-1],b=list[j],E=b.C-a.J;ok(E>=0,"relay");rwb+=b.p*E;if(j<2)continue;triples++;
      let prev=list[j-2],E0=a.C-prev.J;
      if(E>K||E0>K){bb+=b.g;bad++;continue}gb+=b.g;good++;prevGain+=a.g;ok(b.g<=5*a.g,"bounded ending ratio");
      if(6+5*K>(Y-1)/2)continue;
      ok(4*a.w>=a.g&&4*b.w>=b.g,"two actual long clocks");let d=b.C-a.C,p=a.p,r=b.p,disc=d*(d-2)*(d+2),q=(a.C-a.e)/p;
      ok(d===p-1+E&&d>=6&&p!==r&&Number.isInteger(q),"four-form input");
      let primes=[];for(let l=5;9*l<Y-1;l+=2)if(spf[l]===l)primes.push(l);
      let four=v=>[v,v*p+2*a.e,v*p+p+a.e+E-2,v*p+p+a.e+E];
      let vals=four(q);ok(vals[2]===b.C-1&&vals[3]===b.C+1,"four forms");
      for(let l of primes){ok(vals.every(z=>z%l!==0),"four-form roughness");roughChecks++;
       let roots=Array.from({length:l},(_,v)=>v).filter(v=>four(v).some(z=>z%l===0));
       if(disc%l!==0)ok(roots.length===4,"generic four roots");rootChecks++;
      }
      roughPairs++;
      let pk=[p,r,E,a.I,b.I].join("/"),z=pairs.get(pk)||{a,b,E,primes,starts:new Set()};ok(!z.starts.has(a.C)&&mod(a.C-z.a.C,p*r)===0,"pair progression");z.starts.add(a.C);pairs.set(pk,z);
      let id=[p,E,a.I].join("/"),o=ones.get(id)||{a,E,primes,starts:new Set()};ok(!o.starts.has(a.C),"one label unique start");o.starts.add(a.C);ones.set(id,o);
     }
     ok(f===fb+gb+bb&&bb<=6*rwb/(K+1)+1e-7,"triple tail capacity");Rw+=rwb;goodGain+=gb;
     for(let z of pairs.values()){let {a,b,E,primes}=z,p=a.p,r=b.p,step=p*r,cnt=0;
      for(let m=Math.ceil((t.C0-a.C)/step);m<=Math.floor((t.F-1-a.C)/step);m++){let C=a.C+m*step,J=C+p-1+E;if(primes.every(l=>[C-1,C+1,J-1,J+1].every(v=>v%l!==0)))cnt++}
      ok(z.starts.size<=cnt,"pair finite sieve capacity");pairCap+=cnt*(r-1);pairTuples++;
     }
     for(let z of ones.values()){let {a,E,primes}=z,p=a.p,cnt=0;for(let C=t.C0+mod(a.e-t.C0,p);C<t.F;C+=p){let J=C+p-1+E;if(primes.every(l=>[C-1,C+1,J-1,J+1].every(v=>v%l!==0)))cnt++}ok(z.starts.size<=cnt,"one-label four-form capacity");oneCap+=cnt*(p-1);oneTuples++}
    }
    for(let mode of [0,1]){
     let high=t.path.filter(e=>!e.reset&&e.dp>6&&e.p>=Y&&e.p<=P),heights=[...new Set(high.map(e=>e.dp))].sort((a,b)=>a-b);
     if(mode===1)heights=heights.slice(0,2);
     let A=new Set(heights),sel=high.filter(e=>A.has(e.dp));if(!sel.length)continue;
     let set=new Set(sel),map=new Map();for(let e of sel)map.set(e.dp,Math.max(map.get(e.dp)||0,e.g));
     let union=[];for(let [a,g] of [...map].sort((a,b)=>a[0]-b[0])){let last=union.at(-1);if(last&&a<=last[1])last[1]=Math.max(last[1],a+g);else union.push([a,a+g])}
     let phi=d=>union.reduce((s,[a,b])=>s+Math.max(0,Math.min(b,d)-a),0),len=union.reduce((s,[a,b])=>s+b-a,0),alpha=1-2/k;
     let sh=0,ex=0,pp=0,po=0,pn=0,sd=0,op=0;
     ok(phi(6)===0,"canonical zero guard");
     for(let e of t.path){let v=phi(e.dp)-phi(e.d);ok(Math.abs(v)<=Math.abs(e.dp-e.d)&&v*(e.dp-e.d)>=0,"potential monotone Lipschitz");if(e.reset){ok(v<=0,"reset cannot supply positive guarded flux");resetPos++}
      if(set.has(e)){selected++;ok((e.dp-6*e.I)% (2*e.p)===0,"actual ending divisor");
       if(k*e.w<e.g){sh+=e.g;sd-=v;ok(-v>=alpha*e.g,"short localized drop")}
       else{ex+=e.g;for(let l=3;2*l<e.w;l+=2)if(spf[l]===l){ok((e.C-1)%l!==0&&(e.C+1)%l!==0,"extended roughness");extChecks++}}
       pp+=Math.max(0,v)
      }else{po+=Math.max(0,v);if(!e.reset)op+=Math.max(0,v)}
      pn+=Math.max(0,-v);fluxEvents++;
     }
     ok(po===op&&pp+po-pn===phi(t.df),"canonical exact guarded flux");
     ok(alpha*sh+phi(t.df)<=pp+po+1e-7&&sd>=alpha*sh-1e-7&&pp<=(3+4/(Y-1))*ex+1e-7,"no initial guard credit");
     fluxControls++;if(union.length>1)disconnected++;short+=sh;ext+=ex;positive+=pp;outPos+=po;terminal+=phi(t.df);guardLen+=len;
    }
   }
   ok(F===first+goodGain+(F-first-goodGain)&&F-first-goodGain<=6*Rw/(K+1)+1e-7,"aggregate relay tail");
   out.push({X,focus,N:tags.length,events,Y,P,K,k,controls,triples,good,bad,first,F,Rw,goodGain,prevGain,roughPairs,roughChecks,rootChecks,pairTuples,oneTuples,pairCap,oneCap,fluxControls,selected,short,ext,positive,outPos,resetPos,terminal,guardLen,fluxEvents,disconnected,extChecks});
  }
 }
 return out
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
