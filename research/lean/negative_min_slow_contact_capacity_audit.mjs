// Common-clock first-contact capacity: exact slow-arrival pins and loss decomposition.
// Run: node research/lean/negative_min_slow_contact_capacity_audit.mjs
// Finite proxies test arithmetic, not asymptotic sieve estimates.
function audit(){
 const ok=(b,m)=>{if(!b)throw Error(m)}, mod=(a,p)=>(a%p+p)%p;
 const MAX=400002,sp=new Int32Array(MAX+3);
 for(let p=2;p<sp.length;p++)if(!sp[p]){sp[p]=p;if(p*p<sp.length)for(let j=p*p;j<sp.length;j+=p)if(!sp[j])sp[j]=p}
 function fac(n){let a=[];while(n>1){let p=sp[n];ok(p>0,"factor range");a.push(p);while(n%p===0)n/=p}return a}
 function next(x,n){let w=Infinity,p=0,s=0;for(let e of [-1,1])for(let q of fac(x+e)){let t=mod((e===1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){w=t;p=q;s=e}}return {w,p,s}}
 function literal(x,n,w){let fs=[[],[]];for(let e of [-1,1]){let v=x+e,a=[];for(let p=3;p*p<=v;p+=2)if(v%p===0){a.push(p);while(v%p===0)v/=p}if(v>1)a.push(v);fs[e===1?0:1]=a}for(let i=1;i<=w;i++){let nn=n+i,par=mod(nn,2),hits=fs[par].filter(p=>mod(nn,2*p)===(par?p+2:0));if(hits.length)return {w:i,p:Math.min(...hits),s:par?-1:1}}return null}
 const qmin=x=>Math.min(sp[x-1],sp[x+1]);
 let roots=0,events=0,ticks=0,keys=0,pins=0,pairs=0,resetPairs=0,detChecks=0,shiftChecks=0,roughKeys=0,mixedKeys=0,mergeBins=0,mergeLoss=0,charged=0,slowSlow=0,slowIdle=0,fastCharge=0,shortIdle=0,rows=[];
 for(let R of [12000,48000,192000]){
  const T=Math.ceil(8*Math.sqrt(2*R+1)),U=Math.max(7,Math.floor(R**.25)),Y=Math.max(U,Math.floor(T/40)),D=8;
  let keymap=new Map(),windows=0,localMerge=0,localSlowPair=0,localRough=0,localReset=0;
  // Fixed absolute-clock windows: sample 4 windows of width 1200 in slab.
  for(let j=0;j<4;j++){
   const lo=6*Math.ceil((R+j*R/5)/6),hi=lo+1200,start=3-lo/2,stop=start+T;
   let states=new Map();windows++;
   for(let A=lo;A<=hi;A+=6){
    roots++;let x=A,n=3-A/2,entry=n;
    while(n<start){
     let e=next(x,n);if(n+e.w>start){n=start;break}let l=literal(x,n,e.w);ok(l&&l.p===e.p&&l.w===e.w&&l.s===e.s,"pre-window event");
     n+=e.w;x-=e.p-1;entry=n;events++;
    }
    if(!states.has(x)||states.get(x)>entry)states.set(x,entry);
   }
   for(let n=start;n<stop;n++){
    let bins=new Map();
    for(let [x,entry] of states){
     let e=next(x,n),p=e.w===1?e.p:0,s=p?e.s:0,y=x-(p?p-1:0);
     let rec={x,y,p,s,n:n+1,entry:p?n+1:entry,w:p?n+1-entry:0};
     if(p){
      events++;ticks++;ok(literal(x,n,1)?.p===p,"literal event");
      ok(rec.w<=2*qmin(x),"actual phase wait");let h=y/2+n+1,c=s===1?0:2,b=s===1?0:3;
      ok(h>=0&&mod(y-c,p)===0&&mod(h-b,p)===0,"height/spatial pins");pins++;
      if(!keymap.has(y+","+rec.n))keymap.set(y+","+rec.n,new Map());let mp=keymap.get(y+","+rec.n);
      if(!mp.has(p)||mp.get(p).w<rec.w)mp.set(p,rec);
      if(rec.w>=U&&p>=Y){
       for(let d=0;d<=D;d+=2){if(qmin(y-d)<U/2)continue;
        let v=(y-c)/p,n0=p+d-1;
        let f=[[1,1],[p,p-2*s],[p,c-d-1],[p,c-d+1]];
        ok(f[0][0]*v+f[0][1]===(x+s)/p&&f[1][0]*v+f[1][1]===x-s,"source forms");
        ok(f[2][0]*v+f[2][1]===y-d-1&&f[3][0]*v+f[3][1]===y-d+1,"target forms");
        for(let i=0;i<4;i++)for(let j=i+1;j<4;j++){let a=f[i][0]*f[j][1]-f[j][0]*f[i][1];ok(a!==0,"nondegenerate shift");for(let l of [11,13,17,19,23,29,31])if(a%l===0)ok((p*n0*(n0-2)*(n0+2))%l===0,"bad-prime localization");detChecks++}
        shiftChecks++;if(d===0){roughKeys++;localRough++}
       }
      }
     }else ticks++;
     if(!bins.has(y))bins.set(y,[]);bins.get(y).push(rec);
    }
    let nextStates=new Map();
    for(let [y,arr] of bins){
     let idle=arr.find(r=>!r.p),slow=arr.filter(r=>r.p&&r.w>=U),fast=arr.filter(r=>r.p&&r.w<U);
     let loss=arr.length-1;if(loss){
      mergeBins++;mergeLoss+=loss;localMerge+=loss;
      let ss=idle?0:slow.length*(slow.length-1)/2,si=idle&&qmin(y)>=U/2?slow.length:0,sh=idle&&qmin(y)<U/2?slow.length:0;
      ok(loss<=fast.length+ss+si+sh,"loss accounting");
      slowSlow+=ss;slowIdle+=si;shortIdle+=sh;fastCharge+=fast.length;charged+=fast.length+ss+si+sh;
      if(idle&&slow.length) mixedKeys+=slow.length;
     }
     nextStates.set(y,Math.min(...arr.map(r=>r.entry)));
    }
    ok(states.size-nextStates.size===[...bins.values()].reduce((a,b)=>a+b.length-1,0),"exact mass loss");states=nextStates;
   }
  }
  // Supplement window samples by actual first arrivals throughout the slab.
  for(let A=Math.ceil(R/6)*6;A<=2*R;A+=6){
   let n=3-A/2,e=next(A,n);if(e.w<U||e.w>2*T)continue;
   let y=A-e.p+1,nn=n+e.w;
   let rec={x:A,y,p:e.p,s:e.s,n:nn,entry:nn,w:e.w};
   ok(e.w<=2*qmin(A),"first wait");let h=y/2+nn,b=e.s===1?0:3,c=1-e.s;
   ok(h>=0&&mod(h-b,e.p)===0&&mod(y-c,e.p)===0,"first arrival pins");
   let l=literal(A,n,e.w);ok(l&&l.p===e.p&&l.w===e.w&&l.s===e.s,"first literal");
   const key=y+","+nn;
   if(!keymap.has(key))keymap.set(key,new Map());let mp=keymap.get(key);
   if(!mp.has(e.p)||mp.get(e.p).w<rec.w)mp.set(e.p,rec);
  }
  for(let [key,mp] of keymap){
   let arr=[...mp.values()].filter(r=>r.w>=U);keys+=mp.size;
   for(let i=0;i<arr.length;i++)for(let j=i+1;j<arr.length;j++){
    let a=arr[i],b=arr[j],p=a.p,q=b.p,s=a.s,c=1-s,y=a.y,h=y/2+a.n,bc=s===1?0:3;
    ok(s===b.s&&p!==q&&mod(y-c,p*q)===0&&mod(h-bc,p*q)===0,"double incoming");
    let t=(y-c)/(p*q);ok(t>=1&&Number.isInteger(t),"positive cofactor");
    let f=[[1,0],[t,1],[q*t+1,-2*s],[q*t,q-2*s]];
    let vals=f.map(([aa,bb])=>aa*p+bb);
    ok(vals[1]===(b.x+s)/q&&vals[2]===a.x-s&&vals[3]===b.x-s,"double source forms");
    for(let k=0;k<4;k++)for(let l=k+1;l<4;l++){ok(f[k][0]*f[l][1]!==f[l][0]*f[k][1],"double determinant");detChecks++}
    pairs++;localSlowPair++;
    if(p*q>2*T+100){ok(h===bc,"height forced to reset");resetPairs++;localReset++}
   }
  }
  rows.push({R,T,U,Y,windows,localMerge,localSlowPair,localRough,localReset});
 }
 return {roots,events,ticks,keys,pins,pairs,resetPairs,detChecks,shiftChecks,roughKeys,mixedKeys,mergeBins,mergeLoss,charged,slowSlow,slowIdle,fastCharge,shortIdle,rows}
}
console.log(JSON.stringify(audit(),null,2));
