// Actual two-high-event controls: four source forms and time-pin packing.
function audit(Rs){
 const ck=(h,m)=>{if(!h)throw Error(JSON.stringify(m))},mod=(a,b)=>(a%b+b)%b;
 const spf=new Int32Array(2*Math.max(...Rs)+10);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n,q=x=>Math.min(lpf(x-1),lpf(x+1));
 function factors(n){let a=[];while(n>1){let p=lpf(n);a.push(p);while(n%p===0)n/=p}return a}
 function next(x,n){let p=Infinity,w=Infinity,e=0;for(let f of [-1,1])for(let r of factors(x-f)){let d=mod((f===-1?0:r+2)-n,2*r)||2*r;if(d<w||d===w&&r<p){p=r;w=d;e=f}}return {p,w,e}}
 const rough=(p,q)=>BigInt(p)**3n<=(2n*BigInt(q))**5n;
 const primes=[7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];
 let rows=[],checks=0;
 for(let R of Rs){
   const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
   const P=11,B=8;
   let pairs=0,short=0,both=0,imbalanced=0,rootEvents=0,sourceKeys=new Set(),clockKeys=new Map();
   let caps=[1,4,16,64].map(M=>({M,charge:0,shortBoth:0,shortImbalanced:0}));
   for(let l=lo;l<=hi;l+=W){
     const end=3-l/2+T,maxA=Math.min(hi,l+W-6);let group=new Map();
     for(let A=l;A<=maxA;A+=6){
       let x=A,n=3-A/2,prev=null;
       for(;;){
         let {p,w,e}=next(x,n),t=n+w;if(t>end)break;
         let qq=q(x),isRough=rough(p,qq),bothShort=false,imb=false;
         if(p>=P&&prev){
           let a=prev,D=a.x-x,E=D-a.p+1,dt=t-a.t;
           ck(E>=0&&dt>0&&dt<=3*E+2*qq,"actual relay time");pairs++;checks++;
           ck(mod(a.x-a.e,a.p)===0&&mod(x-e,p)===0,"source pins");checks++;
           if(p===a.p){ck(E>=p-1,"same label relay");checks++}
           if(E<=B){
             short++;ck(p!==a.p,"distinct for short relay");
             ck(mod(a.t-(a.e===-1?0:a.p+2),2*a.p)===0&&mod(t-(e===-1?0:p+2),2*p)===0,"clock pins");checks++;
             let key=[a.p,p,a.e,e,E,a.x,dt].join(",");
             let clocks=clockKeys.get(key)||new Set();clocks.add(a.t);clockKeys.set(key,clocks);
             if(isRough&&a.rough){
               both++;bothShort=true;sourceKeys.add([a.p,p,a.e,e,E,a.x].join(","));
               let delta=2n*BigInt(a.p)*BigInt(p)*BigInt(D)*BigInt(D-2)*BigInt(D+2);
               ck(delta!==0n,"distinct source forms");
               let forms=[(a.x-a.e)/a.p,a.x+a.e,(x-e)/p,x+e];
               ck(forms.every(Number.isInteger),"integer forms");
               for(let ell of primes){
                 if(delta%BigInt(ell)!==0n){
                   let nroots=0;for(let u=0;u<ell;u++)if([u-1,u+1,u-D-1,u-D+1].some(c=>mod(c,ell)===0))nroots++;
                   ck(nroots===4,"four roots after CRT");checks++;
                 }
                 if(ell<Math.min(a.q,qq)){ck(forms.every(c=>mod(c,ell)!==0),"roughness");checks++}
               }
             }
             if(qq*4<=a.p&&B*4<=a.p){imb=true;imbalanced++}
           }
         }
         if(p>=P)prev={p,x,t,e,q:qq,rough:isRough};
         let key=[x,t,p].join(",");let arr=group.get(key)||[];arr.push({A,qq,p,isRough,bothShort,imb});group.set(key,arr);
         rootEvents++;x-=p-1;n=t;
       }
     }
     for(let arr of group.values()){
       arr.sort((a,b)=>a.A-b.A);
       for(let c of caps)for(let a of arr.slice(0,c.M)){
         if(a.p>=P&&a.isRough)c.charge+=2*a.qq;
         if(a.bothShort)c.shortBoth+=2*a.qq;
         if(a.imb)c.shortImbalanced+=2*a.qq;
       }
     }
   }
   for(let [key,set] of clockKeys){
     let [p,r]=key.split(",").map(Number),a=[...set].sort((x,y)=>x-y);
     for(let i=1;i<a.length;i++){ck((a[i]-a[i-1])%(2*p*r)===0,"CRT clock spacing");checks++}
   }
   rows.push({R,N,T,P,B,rootEvents,pairs,short,both,imbalanced,sourceKeys:sourceKeys.size,clockKeys:clockKeys.size,caps});
 }
 return {checks,rows};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
