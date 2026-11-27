// Arbitrary postheight periodic negative MIN terminal map for small-only relays.
// node research/min_local_negative_periodic_relay_height_audit.mjs [R ...]
function audit(Rs){
 const spf=new Int32Array(2*Math.max(...Rs)+10),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,n){let p=Infinity,w=Infinity,e=0;for(let s of [-1,1])for(let q of fs(a-s)){let d=mod((s===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d;e=s}}return {p,w,e}}
 const ck=(v,m)=>{if(!v)throw Error(JSON.stringify(m))},q=a=>Math.min(spf[a-1]||a-1,spf[a+1]||a+1);
 const specs=[{z:3,ps:[3],Q:6},{z:5,ps:[3,5],Q:30},{z:7,ps:[3,5,7],Q:210},{z:11,ps:[3,5,7,11],Q:2310},{z:13,ps:[3,5,7,11,13],Q:30030}];
 function terminal(a,n,s){
  let a0=a,n0=n,k=0;
  for(;;){let p=Infinity,w=Infinity;
   for(let r of s.ps)for(let e of [-1,1])if(mod(a-e,r)===0){
    let d=mod((e===-1?0:r+2)-n,2*r)||2*r;
    if(d<w||d===w&&r<p){p=r;w=d}
   }
   if(!Number.isFinite(p))break;
   let b=a-p+1;ck(Math.floor(a/s.Q)===Math.floor(b/s.Q),"restricted barrier");
   a=b;n+=w;k++;ck(a0-a<s.Q&&k<=s.Q/2,"restricted termination");
  }
  return {g:a0-a,t:n-n0,k};
 }
 let rows=[];
 for(let R of Rs){
  const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
  let controls=specs.map(s=>({...s,pairs:0,strong:0,nonreset:0,fast:0,maxGain:0,terminalChecks:0,roughChecks:0,keys:new Map(),seen:new Set(),firstSample:null})),events=0,checks=0;
  for(let A=lo;A<=hi;A+=6){
   let a=A,n=3-A/2,j=Math.floor((A-lo)/W),n0=3-(lo+j*W)/2,end=n0+T;
   let trace=[];
   for(;;){let e=next(a,n),t=n+e.w;if(t>end)break;trace.push({a,n,t,...e});a-=e.p-1;n=t;events++}
   for(let c of controls){
    let prev=null;
    for(let i=0;i<trace.length;i++){
     let e=trace[i];if(e.p<=c.z)continue;
     if(prev!==null){
      let s=trace[prev],p=s.p,r=e.p,h=s.t+(s.a-p+1)/2,x=s.a-p+1,E=x-e.a,D=e.t-s.t;
      ck(E>=0&&E<c.Q&&D<=3*E+e.w,"small-only relay gain and time");
      c.pairs++;c.maxGain=Math.max(c.maxGain,E);if(e.w<=2*c.z)c.fast++;
      else{
       let res=mod(s.a,2*c.Q),key=[p,h,res,s.e].join(":");
       let v=c.keys.get(key);
       if(!v){v=terminal(x,s.t,c);c.keys.set(key,v);
        let x0=res-p+1,t0=h-x0/2;
        let u=terminal(x0,t0,c),w=terminal(x0+2*c.Q,t0-c.Q,c);
        ck(v.g===u.g&&v.t===u.t&&v.k===u.k&&v.g===w.g&&v.t===w.t&&v.k===w.k,"arbitrary height CRT translation");
        c.terminalChecks+=3;
       }
       ck(v.g===E&&v.t===e.n-s.t&&v.k===i-prev-1,"restricted terminal equals actual full small relay");
       c.terminalChecks++;c.strong++;c.nonreset+=+(h!==0&&h!==3);
       if(c.firstSample===null&&h!==0&&h!==3&&E>0)c.firstSample={A,x:s.a,p,h,r,E,relayTicks:v.t,targetWait:e.w};
       if(s.w>=p**.8&&e.w>=r**.8){
        ck(q(s.a)>=p**.8/2&&q(e.a)>=r**.8/2,"rough source and terminal");
        for(let l of [5,7,11,13,17,19,23,29,31,37])if(l>c.z&&l<Math.min(p**.8/2,r**.8/2)){
         ck([s.a-1,s.a+1,e.a-1,e.a+1].every(v=>mod(v,l)!==0),"four rough forms");c.roughChecks++;
        }
       }
      }
      checks++;
     }
     prev=i;
    }
   }
  }
  rows.push({R,N,T,events,checks,controls:controls.map(c=>({z:c.z,Q:c.Q,pairs:c.pairs,strong:c.strong,nonreset:c.nonreset,fast:c.fast,maxGain:c.maxGain,terminalChecks:c.terminalChecks,roughChecks:c.roughChecks,distinctKeys:c.keys.size,sample:c.firstSample}))});
 }
 return rows;
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
