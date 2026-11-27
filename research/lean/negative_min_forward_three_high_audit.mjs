// Actual negative MIN: forward three-high-event ledger, six-form and
// fast clock constraints. Finite audit; no asymptotic inference.
function audit(Rs=[12000,48000,192000]){
 const mod=(a,b)=>(a%b+b)%b,ck=(b,m)=>{if(!b)throw Error(JSON.stringify(m))};
 const spf=new Int32Array(2*Math.max(...Rs)+16);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n,q=x=>Math.min(lpf(x-1),lpf(x+1));
 function factors(n){let a=[];while(n>1){let p=lpf(n);a.push(p);while(n%p===0)n/=p}return a}
 function next(x,n){let p=Infinity,w=Infinity,e=0;for(let f of [-1,1])for(let r of factors(x-f)){let d=mod((f===-1?0:r+2)-n,2*r)||2*r;if(d<w||d===w&&r<p){p=r;w=d;e=f}}return {p,w,e}}
 const gcd=(a,b)=>{a=Math.abs(a);while(b){let t=a%b;a=b;b=t}return a};
 const rough=(p,q)=>BigInt(p)**3n<=(2n*BigInt(q))**5n;
 const small=[7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97];
 let checks=0,rows=[];
 for(let R of Rs){
   const T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),N=(hi-lo)/6+1;
   const z=5,Y0=11,Y1=Math.max(17,Math.floor(T/2)),U=4,Q=30;
   const controls=[1,4,16,64].map(M=>({M,medium:0,clean:0,tail:0,narrowBad:0,bigBad:0,narrow:0,gain:0,fast2:0,fast3:0,slow3:0,repeated13:0,firstPositive:0,imbalanced:0,residual:0,removed:0}));
   let rootEvents=0,prefixes=0,literalTicks=0,triples=0,repeat13=0,clockKeys=new Map(),fourKeys=0,sixKeys=0;
   for(let l=lo;l<=hi;l+=W){
     const end=3-l/2+T,maxA=Math.min(hi,l+W-6),group=new Map(),paths=[];
     for(let A=l;A<=maxA;A+=6){
       let x=A,n=3-A/2,events=[];
       for(;;){
         const {p,w,e}=next(x,n),t=n+w;if(t>end)break;
         const qq=q(x),a={x,t,p,w,e,qq,A,rough:rough(p,qq)};
         events.push(a);const key=[x,t,p].join(","),arr=group.get(key)||[];arr.push(a);group.set(key,arr);
         rootEvents++;x-=p-1;n=t;
       }
       if(R===Rs[0]){
         let xx=A,ii=0;
         for(let t=3-A/2+1;t<=end;t++){
           const g=t%2===0?gcd(t,xx+1):gcd(t-2,xx-1),p=g>1?lpf(g):0;
           if(p){let a=events[ii++];ck(a&&a.x===xx&&a.t===t&&a.p===p,"literal comparator");checks++;xx-=p-1}
           literalTicks++;
         }
         ck(ii===events.length,"event count");checks++;
       }
       paths.push(events);
     }
     for(let arr of group.values())arr.sort((a,b)=>a.A-b.A).forEach((a,i)=>a.rank=i+1);
     for(let es of paths)for(let c of controls){
       let d=es.findIndex(a=>a.rank>c.M);if(d<0)d=es.length;
       ck(es.slice(d).every(a=>a.rank>c.M),"irreversible rank cap");checks++;
       let ev=es.slice(0,d),high=[],narrow=0,gain=0,medium=0,first=0,imb=0,rep=0,seen=new Set();
       for(let i=0;i<ev.length;i++){
         let a=ev[i],p=a.p;gain+=p-1;
         if(z<p&&p<Y0)narrow++;
         if(p>=Y0)high.push(i);
         if(Y0<=p&&p<Y1&&a.rough){
           let v=2*a.qq;medium+=v;
           if(U*a.qq<=p)imb+=v;
           else if(!seen.has(p)){first+=v;seen.add(p)}
           else rep+=v;
         }
       }
       ck(first+imb+rep===medium&&first<=2*Y1*Y1&&U*imb<=3*gain,"cost ledger");checks++;
       let clean=0,tail=0,narrowBad=0,bigBad=0,fast2=0,fast3=0,slow3=0,repeated=0;
       for(let j=0;j<high.length;j++){
         const i=high[j],a=ev[i];if(!(a.p<Y1&&a.rough))continue;
         const v=2*a.qq;
         if(j+2>=high.length){tail+=v;continue}
         const i1=high[j+1],i2=high[j+2],b=ev[i1],cc=ev[i2];
         const g1=ev.slice(i+1,i1),g2=ev.slice(i1+1,i2);
         if([...g1,...g2].some(e=>z<e.p)){narrowBad+=v;continue}
         if(b.p>=U*Y1||cc.p>=U*Y1){bigBad+=v;continue}
         const E1=a.x-(a.p-1)-b.x,E2=b.x-(b.p-1)-cc.x,d1=b.t-a.t,d2=cc.t-b.t;
         ck(E1>=0&&E2>=0&&E1<Q&&E2<Q,"wall gain");
         ck(E1===g1.reduce((s,a)=>s+a.p-1,0)&&E2===g2.reduce((s,a)=>s+a.p-1,0),"relay gain");
         ck(d1<=3*E1+2*b.qq&&d2<=3*E2+2*cc.qq,"clock gap");
         checks+=3;
         clean+=v;triples++;
         // For the CRT / six-form estimates require B<Y0-1; finite
         // Q=30 can exceed Y0-1, so separately test E1,E2<Y0-1.
         if(a.p===cc.p){ck(b.p+E1+E2>=a.p,"repeated endpoints");repeat13++;repeated+=v;checks++}
         if(E1<Y0-1&&E2<Y0-1){ck(a.p!==b.p&&b.p!==cc.p,"distinct adjacent labels");checks++}
         if(!b.rough)fast2+=v;else if(!cc.rough)fast3+=v;else slow3+=v;
         if(!b.rough||!cc.rough){
           // Fix spatial keys, signs and exact gaps: all valid starting
           // clocks belong to one class modulo twice distinct labels.
           if(c.M===64){
             const pair=!b.rough,labels=pair?[a.p,b.p]:[a.p,b.p,cc.p];
             const key=(pair?[a.x,a.p,b.p,a.e,b.e,E1,d1]:[a.x,a.p,b.p,cc.p,a.e,b.e,cc.e,E1,E2,d1,d2]).join(",");
             const L=2*[...new Set(labels)].reduce((s,p)=>s*p,1);
             const old=clockKeys.get(key);
             if(old!==undefined){ck(mod(a.t-old,L)===0,"clock CRT");checks++}else clockKeys.set(key,a.t);
           }
         }
         if(b.rough&&cc.rough&&c.M===64){
           let D=a.x-b.x,F=a.x-cc.x;
           if(D>2&&F-D>2){
             const shifts=[-1,1,D-1,D+1,F-1,F+1];
             let disc=1n;for(let h=0;h<6;h++)for(let k=h+1;k<6;k++)disc*=BigInt(shifts[k]-shifts[h]);
             ck(disc!==0n,"nonzero six discriminant");checks++;sixKeys++;
             for(let ell of small){
               if(disc%BigInt(ell)!==0n&&[a.p,b.p,cc.p].every(p=>p!==ell)){
                 ck(new Set(shifts.map(s=>mod(s,ell))).size===6,"six distinct local roots");checks++;
               }
               if(ell<Math.min(a.qq,b.qq,cc.qq)){ck(shifts.every(s=>mod(a.x-s,ell)!==0),"six rough exclusions");checks++}
             }
           }
         }
         if(a.p===cc.p&&E1+E2<a.p/2&&c.M===64){
           ck(b.p>=a.p/2,"endpoint repetition lower bound");checks++;
           const pinA=a.e===-1?0:a.p+2,pinC=cc.e===-1?0:cc.p+2;
           ck(mod(d1+d2-(pinC-pinA),2*a.p)===0,"repeated endpoint clock relation");checks++;
         }
       }
       ck(medium===clean+tail+narrowBad+bigBad&&clean===fast2+fast3+slow3,"forward partition");
       ck(U*medium<=U*clean+4*U*Y1*(1+narrow)+6*gain,"forward scaled bound");
       ck(tail<=4*Y1&&narrowBad<=4*Y1*narrow&&U*bigBad<=6*gain,"separate charging");checks+=5;
       Object.assign(c,{medium:c.medium+medium,clean:c.clean+clean,tail:c.tail+tail,narrowBad:c.narrowBad+narrowBad,bigBad:c.bigBad+bigBad,narrow:c.narrow+narrow,gain:c.gain+gain,fast2:c.fast2+fast2,fast3:c.fast3+fast3,slow3:c.slow3+slow3,repeated13:c.repeated13+repeated,firstPositive:c.firstPositive+first,imbalanced:c.imbalanced+imb,residual:c.residual+rep,removed:c.removed+first+imb});prefixes++;
     }
   }
   rows.push({R,N,T,z,Y0,Y1,U,Q,rootEvents,prefixes,literalTicks,triples,repeat13,sixKeys,clockKeys:clockKeys.size,controls:controls.map(c=>({...c,normalizedMedium:c.medium/(N*T),normalizedClean:c.clean/(N*T)}))});
 }
 return {checks,rows};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
