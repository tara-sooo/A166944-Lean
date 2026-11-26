// Reset-only band audit; exact integer clock selection and GCD controls.
function resetBandAudit(limit=2000000){
 const a=new Uint32Array(2*limit+3);
 for(let p=3;p*p<a.length;p+=2)if(!a[p])for(let n=p*p;n<a.length;n+=2*p)if(!a[n])a[n]=p;
 function fac(n){let f=[];while(n>1){let p=a[n]||n;f.push(p);n/=p;}return f}
 const mod=(x,m)=>(x%m+m)%m;
 const require=(x,m)=>{if(!x)throw Error(m)};
 const gcd=(x,y)=>{while(y){let z=x%y;x=y;y=z}return Math.abs(x)};
 function event(u){let v=u/2+3,w=Infinity,p=Infinity,minus=fac(u-1),plus=fac(u+1);for(let [f,s] of [[minus,0],[plus,1]])for(let q of f){let k=mod((s?q+2:0)-v,2*q)||2*q;if(k<w||k===w&&q<p){w=k;p=q}}return {w,p,minus,plus,twin:minus.length===1&&plus.length===1}}
 let counts={roots:0,firstReset:0,firstNonTwinReset:0,firstLargeReset:0,firstLargeNonTwinReset:0,largeCandidates:0,largeCharacterizationTrue:0,largeCharacterizationFalse:0,largeCandidatesNonTwin:0,largeCharacterizationNonTwinTrue:0,largeCharacterizationNonTwinFalse:0,onePrimeOpposite:0,twoPrimeOpposite:0,chainsWithRepeat:0,repeatPairs:0,chainEvents:0,literalTicks:0,balancedPairChecks:0,determinantChecks:0};
 let maxima={length:{n:0},gainRatio:{ratio:0},repeatRatio:{ratio:0},pRatio:{ratio:0},twoNearBalance:{ratio:Infinity}};
 let examples={large:null,pair:null,repeat:null};let histogram={};let slab={};
 const get=u=>{let {w,p,minus,plus,twin}=event(u);return {w,p,minus,plus,twin,reset:p%12===1&&2*w===p-1}};
 for(let X=12;X<=limit;X+=12){
   counts.roots++;let f=get(X);
   const band=1<<Math.floor(Math.log2(X));
   let s=slab[band]||(slab[band]={roots:0,nonTwinReset:0,largeNonTwinReset:0,maxLength:0,maxRatio:0});s.roots++;
   if(f.reset){counts.firstReset++;if(!f.twin){counts.firstNonTwinReset++;s.nonTwinReset++}if(4*f.p*f.p>=X){counts.firstLargeReset++;if(!f.twin){counts.firstLargeNonTwinReset++;s.largeNonTwinReset++}}}
   // All sufficiently large candidate plus labels, not just the winning ones.
   for(let p of new Set(f.plus))if(p%12===1&&(p-1)**3>64*(X+1)&&p<X+1){
     counts.largeCandidates++;
     const m=(X+1)/p;
     let predicted=false;
     if(f.plus.length===2&&m>=p&&m%12===1){
       if(f.minus.length===1)predicted=true;
       else if(f.minus.length===2){
         let r=f.minus.find(q=>q%4===1),q=f.minus.find(q=>q%4===3);
         predicted=r!==undefined&&q!==undefined&&r>p+6&&3*q>p+6;
       }
     }
     let actual=f.reset&&f.p===p;
     require(predicted===actual,"large characterization "+X+" "+p);
     counts[actual?"largeCharacterizationTrue":"largeCharacterizationFalse"]++;
     if(!f.twin){counts.largeCandidatesNonTwin++;counts[actual?"largeCharacterizationNonTwinTrue":"largeCharacterizationNonTwinFalse"]++}
     if(actual){counts[f.minus.length===1?"onePrimeOpposite":"twoPrimeOpposite"]++;if(!examples.large)examples.large={X,p,m,minus:f.minus,w:f.w}}
   }
   let u=X,chain=[],prev=new Map(),repeated=false;
   while(u<2*X){
     let z=get(u);if(z.twin||!z.reset)break;
     let p=z.p,w=z.w;
     require(p*p<=u+1,"p cap "+u);
     require(z.plus.includes(p)&&u%12===0,"reset plus");
     if(prev.has(p)){let d=u-prev.get(p);require(d%(12*p)===0,"repeat spacing");counts.repeatPairs++;repeated=true;if(!examples.repeat)examples.repeat={X,p,drift:d};let ratio=d/(12*p);if(ratio>maxima.repeatRatio.ratio)maxima.repeatRatio={X,u,p,ratio}}
     prev.set(p,u);
     const ratio=p/Math.sqrt(u+1);if(ratio>maxima.pRatio.ratio)maxima.pRatio={u,p,ratio};
     if((p-1)**3>64*(u+1)){
       require(z.plus.length===2,"large plus semiprime");
       const m=(u+1)/p;
       require(p<=m&&m%12===1,"large cofactor");
       if(chain.length){
         let last=chain.at(-1);
         if(last.m!==null){
           require(p*m===last.p*(last.m+1)-1,"determinant");counts.determinantChecks++;
           let h=Math.round((Math.sqrt(last.u+1)-1)/12)*12+1;
           let B=Math.max(...[last.p,last.m,p,m].map(y=>Math.abs(y-h)));
           require(2*B*B+B+1>=h,"balanced obstruction");
           counts.balancedPairChecks++;
           let ratio=B/Math.sqrt(h);if(ratio<maxima.twoNearBalance.ratio)maxima.twoNearBalance={u:last.u,p:last.p,m:last.m,r:p,n:m,h,B,ratio};
           if(!examples.pair)examples.pair={u:last.u,p:last.p,m:last.m,r:p,n:m};
         }
       }
       chain.push({u,p,m});
     }else chain.push({u,p,m:null});
     if(X<3000||X%120012===0){for(let j=1;j<=w;j++){let n=u/2+3+j,d=gcd(n%2?n-2:n,n%2?u+1:u-1);require(j===w?(a[d]||d)===p:d===1,"literal");counts.literalTicks++}}
     u+=p-1;
   }
   if(repeated)counts.chainsWithRepeat++;
   counts.chainEvents+=chain.length;histogram[chain.length]=(histogram[chain.length]||0)+1;
   const G=u-X,K=prev.size;
   if(chain.length>maxima.length.n)maxima.length={X,n:chain.length,K,G,labels:chain.map(z=>z.p)};
   const ratio=G/Math.sqrt(X);if(ratio>maxima.gainRatio.ratio)maxima.gainRatio={X,G,K,n:chain.length,ratio,labels:chain.map(z=>z.p)};
   s.maxLength=Math.max(s.maxLength,chain.length);s.maxRatio=Math.max(s.maxRatio,ratio);
   if(K<=11&&K>0){
     // Pre-offset span at most G; finite exact inequality including all events.
     require((12-K)*G<=12*K*Math.sqrt(u+1),"small-support chain cap");
   }
 }
 return {limit,counts,maxima,examples,histogram,slab};
}
console.log(JSON.stringify(resetBandAudit(Number(process.argv[2]||2000000)),null,2));
