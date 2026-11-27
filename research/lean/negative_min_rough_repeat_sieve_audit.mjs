// Rough same-label repeat sieve controls. Exact actual MIN events and
// source-pair residues; finite controls, not a proof of the sieve asymptotics.
function audit(Rs){
 const ck=(h,m)=>{if(!h)throw Error(JSON.stringify(m))},mod=(a,b)=>(a%b+b)%b;
 const spf=new Int32Array(2*Math.max(...Rs)+10);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n,q=x=>Math.min(lpf(x-1),lpf(x+1));
 function factors(n){let a=[];while(n>1){let p=lpf(n);a.push(p);while(n%p===0)n/=p}return a}
 function next(x,n){let p=Infinity,w=Infinity,e=0;for(let f of [-1,1])for(let r of factors(x-f)){let d=mod((f===-1?0:r+2)-n,2*r)||2*r;if(d<w||d===w&&r<p){p=r;w=d;e=f}}return {p,w,e}}
 const rough=(p,q)=>BigInt(p)**3n<=(2n*BigInt(q))**5n;
 const smallPrimes=[7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];
 let checks=0,rows=[];
 for(let R of Rs){
   const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
   let controls=[1,4,16,64].map(M=>({M,total:0,first:0,short:0,long:0,firstAfterNonrough:0,shortK1:0,shortK2:0,shortK8:0,events:0,shortEvents:0,roughEvents:0})),rootEvents=0,keys=0,sourceTuples=new Set(),pairs=0;
   for(let l=lo;l<=hi;l+=W){
     const n0=3-l/2,end=n0+T,maxA=Math.min(hi,l+W-6);
     let group=new Map();
     for(let A=l;A<=maxA;A+=6){
       let x=A,n=3-A/2,prev=new Map(),any=new Set();
       for(;;){
         let z=next(x,n),{p,w,e}=z,t=n+w;
         if(t>end)break;
         let qq=q(x),kind="none",k=0;
         if(11<=p&&p<=T&&rough(p,qq)){
           ck(qq<=p&&mod(x-e,p)===0,"rough source pin");
           let v=prev.get(p);
           if(!v)kind=any.has(p)?"firstAfterNonrough":"first";
           else{
             k=(v.x-x-v.e+e)/(2*p);
             ck(Number.isInteger(k)&&k>=1&&v.x-x>=2*(p-1),"repeat separation and quotient");
             let u=(v.x-v.e)/p;
             ck(Number.isInteger(u)&&x===p*(u-2*k)+e&&u>0&&u-2*k>0,"four forms");
             let f=[u,u-2*k,p*u+2*v.e,p*(u-2*k)+2*e];
             let delta=2n*BigInt(p)*BigInt(k)*BigInt(p*k-e)*BigInt(p*k+v.e)*BigInt(p*k+v.e-e);
             ck(delta!==0n,"nonzero discriminant");
             for(let ell of smallPrimes){
               if(delta%BigInt(ell)!==0n){
                 let forbidden=0;
                 for(let a=0;a<ell;a++)if([a,a-2*k,p*a+2*v.e,p*(a-2*k)+2*e].some(c=>mod(c,ell)===0))forbidden++;
                 ck(forbidden===4,["four roots",p,k,v.e,e,ell]);checks++;
               }
               if(ell<Math.min(v.q,qq)){ck(f.every(c=>mod(c,ell)!==0),"rough source pair");checks++}
             }
             kind=k<=4?"short":"long";
             sourceTuples.add([p,k,v.e,e,v.x].join(","));pairs++;
           }
           prev.set(p,{x,e,q:qq});
         }
         any.add(p);
         let key=[x,t,p].join(","),arr=group.get(key)||[];
         arr.push({A,kind,k,qq});group.set(key,arr);
         rootEvents++;x-=p-1;n=t;
       }
     }
     for(let [key,arr] of group){
       keys++;arr.sort((a,b)=>a.A-b.A);
       let p=Number(key.split(",")[2]);
       for(let c of controls)for(let a of arr.slice(0,c.M)){
         c.events++;
         if(a.kind!=="none"){
           let val=2*a.qq;c.total+=val;c[a.kind]+=val;c.roughEvents++;
           if(a.kind==="short"){c.shortEvents++}
           if(a.k>0&&a.k<=1)c.shortK1+=val;
           if(a.k>0&&a.k<=2)c.shortK2+=val;
           if(a.k>0&&a.k<=8)c.shortK8+=val;
         }
       }
     }
   }
   for(let c of controls)ck(c.total===c.first+c.firstAfterNonrough+c.short+c.long,"partition");
   rows.push({R,N,T,rootEvents,keys,pairs,distinctSourceTuples:sourceTuples.size,controls:controls.map(c=>({...c,normalizedTotal:c.total/(N*T),normalizedShort:c.short/(N*T),shortFraction:c.total?c.short/c.total:0}))});
 }
 return {checks,rows};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
