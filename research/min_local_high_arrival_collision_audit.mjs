// Compressed exact arrival graph: relaxed high clocks, exact small relays, actual path controls.
function audit(maxR=1000000){
 const lim=4*maxR+300,spf=new Uint32Array(lim+1);
 for(let p=2;p*p<=lim;p++)if(!spf[p])for(let n=p*p;n<=lim;n+=p)if(!spf[n])spf[n]=p;
 const mod=(x,m)=>(x%m+m)%m,ck=(x,m)=>{if(!x)throw Error(m)};
 function fs(n){ck(n>0&&n<=lim,"domain");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function gcd(a,b){while(b){let z=a%b;a=b;b=z}return Math.abs(a)}
 function next(u,v,small=false){let f=small?[3,5,7,11].filter(p=>(u-1)%p===0):fs(u-1),g=small?[3,5,7,11].filter(p=>(u+1)%p===0):fs(u+1),p=Infinity,w=Infinity,e=0;for(let [A,s] of [[f,1],[g,-1]])for(let r of A){let z=mod((s===1?0:r+2)-v,2*r)||2*r;if(z<w||z===w&&r<p){p=r;w=z;e=s}}return {p,w,e,twin:!small&&f[0]===u-1&&g[0]===u+1}}
 function relay(u,v,U,V){let x=u,t=v,n=0;while(x<U){let a=next(x,t,true);if(!isFinite(a.p))return false;x+=a.p-1;t+=a.w;n++;ck(n<=25,"restricted event count")}return x===U&&t===V}
 function inverse(U,V,T,K,R){
  let d=2*V-U,res=[];
  for(let u=Math.max(R,U-104);u<=U;u+=2)for(let e of [1,-1]){
   let s=e===1?0:6;
   for(let p of fs(u+(e===1?0:2))){
    if(p<T||p>2*T)continue;
    for(let a=Math.max(1,Math.ceil((d-192-s)/(2*p)));a<=Math.min(K,Math.floor((d+16-s)/(2*p)));a++){
     let dd=2*a*p+s,v=(u+dd)/2;
     if(mod(v,2*p)!==(e===1?0:p+2)||v>u+1||u>=2*R)continue;
     if(relay(u,v,U,V))res.push({u,v,p,e,a})
    }
   }
  }
  return res;
 }
 let out=[];
 for(let [R,T,K] of [[100000,127,6],[100000,251,6],[1000000,251,6],[1000000,503,6],[1000000,997,6],[100000,127,60]].filter(a=>a[0]<=maxR)){
  let states=new Map(),s={R,T,K,arrivals:0,relayStates:0,distinctEndpoints:0,ambiguous:0,maxLabels:0,distinctLabelPairs:0,sameMultiplierPairs:0,crossMultiplierPairs:0,narrowControls:0,narrowHighControls:0,literalTicks:0,inverseChecks:0,example:null,maxExample:null,actualRoots:0,actualEvents:0,actualCovered:0,actualAmbiguous:0};
  function add(U,V,z){let d=2*V-U;if(d<=198||d>2*K*T)return;
   ck(U-z.u>=0&&U-z.u<=104&&V-z.v>=0&&V-z.v<=133,"relay extent");
   ck(d-(2*z.v-z.u)>=-16&&d-(2*z.v-z.u)<=192,"signed relay");
   s.relayStates++;let key=U+":"+V,prev=states.get(key);
   if(!prev){states.set(key,[z]);return}
   for(let a of prev){ck(a.p!==z.p,"same label ambiguity "+JSON.stringify({U,V,a,z}));
    let c=a.a*a.p-z.a*z.p;ck(Math.abs(c)<=107&&c!==0,"linear relation");s.distinctLabelPairs++;
    if(a.a===z.a)s.sameMultiplierPairs++;else s.crossMultiplierPairs++;
    ck((U-z.u)%2===0,"parity");ck((U-(U-z.u)+(z.e===1?0:2))%z.p===0,"offset congruence");
    if(!s.example)s.example={U,V,d,a,z,c};
   }
   prev.push(z);
  }
  for(let u=R;u<2*R;u+=2)for(let e of [1,-1]){
   let c=e===1?0:6;for(let p of fs(u+(e===1?0:2))){
    if(p<T||p>2*T)continue;
    for(let a=1;a<=K;a++){
     let d=2*a*p+c,v=(u+d)/2;
     if(v>u+1||mod(v,2*p)!==(e===1?0:p+2))continue;
     let z={u,v,p,e,a};s.arrivals++;
     let U=u,V=v;
     for(let n=0;;n++){
      add(U,V,z);let q=next(U,V,true);if(!isFinite(q.p))break;
      if(u<R+100){for(let i=1;i<=q.w;i++){let t=V+i,g=gcd(t%2?t-2:t,t%2?U+1:U-1),k=[3,5,7,11].find(r=>g%r===0);ck(i===q.w?k===q.p:k===undefined,"literal relay");s.literalTicks++}}
      U+=q.p-1;V+=q.w;ck(n<25,"relay cap");
     }
    }
   }
  }
  s.distinctEndpoints=states.size;
  let top=[];
  for(let [key,list] of states){
   if(list.length>1){s.ambiguous++;if(list.length>s.maxLabels){s.maxLabels=list.length;s.maxExample={key,list};}if(top.length<8)top.push([key,list]);}
   const narrow=list.filter(a=>2*K*(a.p-T)<=T);
   if(narrow.length){s.narrowControls++;for(let a of narrow)for(let b of narrow)if(a.p!==b.p&&T>214)ck(a.a===b.a,"narrow stratum");}
   if(narrow.some(a=>a.a>=54)&&T>214){ck(narrow.length===1,"narrow high uniqueness");s.narrowHighControls++;}
  }
  if(s.maxExample)top.push([s.maxExample.key,s.maxExample.list]);
  for(let [key,list] of top){let [U,V]=key.split(":").map(Number);let cand=inverse(U,V,T,K,R);ck(cand.length===list.length&&list.every(a=>cand.some(b=>a.u===b.u&&a.v===b.v&&a.p===b.p&&a.e===b.e&&a.a===b.a)),"inverse replay");s.inverseChecks++;}
  // Independent canonical path controls, stop before twin or local exit.
  for(let X=Math.ceil(R/6)*6;X<Math.min(R+60000,2*R);X+=6){
   let u=X,v=X/2+3,last=null;s.actualRoots++;
   while(u<X+4*T){
    let z=next(u,v);if(z.twin)break;let U=u+z.p-1,V=v+z.w,dd=2*V-U,s0=z.e===1?0:6;
    if(z.p>=T&&z.p<=2*T&&U>=R&&U<2*R&&(dd-s0)/(2*z.p)>=1&&(dd-s0)/(2*z.p)<=K){last={u:U,v:V,p:z.p,e:z.e,a:(dd-s0)/(2*z.p)}}else if(z.p>11)last=null;
    if(last&&dd>198&&dd<=2*K*T){let a=states.get(U+":"+V)||[];ck(a.some(q=>q.u===last.u&&q.v===last.v&&q.p===last.p&&q.e===last.e),"actual coverage");s.actualCovered++;if(a.length>1)s.actualAmbiguous++}
    u=U;v=V;s.actualEvents++;
   }
  }
  out.push(s);
 }
 return out;
}
console.log(JSON.stringify(audit(Number(process.argv[2]||1000000)),null,2));
