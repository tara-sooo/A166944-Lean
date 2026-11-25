function audit(N=100000,steps=24){
 const cap=8*N+10000,spf=new Int32Array(cap+1);for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 function factors(z){let a=[];while(z>1){if(z>cap)throw Error("range");let p=spf[z];a.push(p);z/=p}return a}
 function next(t,C){if(C%2||C<4)throw Error('invalid horizon');let B=Math.floor(Math.sqrt(C+1)),best=null;for(let s of [-1,1])for(let p of new Set(factors(C+s))){if(p>B)continue;let r=s===-1?0:p+2,w=((r-t)%(2*p)+2*p)%(2*p)||2*p;if(!best||w<best.w||w===best.w&&p<best.p)best={w,p,s}}return best}
 let res={N,steps,edges:0,resetEven:0,resetOdd:0,cofactorPrimeChecks:0,compositeDeficitChecks:0,minEven:0,minOdd:0,minEvenTwin:0,minOddTwin:0,minEvenComposite:0,minOddComposite:0,forced3:0,minEvenExamples:[],minOddExamples:[],lateExamples:[],backwardClockChecks:0,minBackwardChecks:0,sameSidePredecessorChecks:0,oppositeSidePredecessorChecks:0,lateSameSideChecks:0,pairChecks:0,primeRootsEven:0,primeRootsOdd:0};
 for(let M=5;M<=N;M+=2){let C=2*M-2,t=M+2,history=[],prev=null;for(let i=0;i<steps;i++){
 if(C+Math.floor(Math.sqrt(C+1))+1>cap)throw Error("range upper");let e=next(t,C);if(!e)break;let {p,w,s}=e,d=2*t-C,n=t+w,Z=C+p-1,delta=2*n-Z,q=(C+s)/p;
 if(!Number.isInteger(q)||q<p||delta<0||d<0||delta!==d+2*w-p+1)throw Error("geometry");
 res.edges++;history.push([n,p,Z,delta]);
 // Independent backwards-clock characterization of the chosen arrival.
 let B=Math.floor(Math.sqrt(C+1));for(let side of [-1,1])for(let a of new Set(factors(C+side))){if(a>B)continue;let target=side===-1?0:a+2,lag=((n-target)%(2*a)+2*a)%(2*a);if(lag===0){if(a<p)throw Error('backward tie');lag=2*a;}if(w>lag)throw Error('backward clock');res.backwardClockChecks++;}
 let fa=factors(q),r=fa[0],comp=fa.length>1;
 if(comp&&r<p){if(w>=2*r||d<p+1+delta-4*r)throw Error("late entry");res.compositeDeficitChecks++}
 if(q<p*p&&d<p+1+delta-4*Math.floor(Math.sqrt(q))){if(comp)throw Error("prime cofactor");res.cofactorPrimeChecks++}
 let type=(s===-1&&delta===0&&n%2===0)?'Even':(s===1&&delta===6&&n%2===1)?'Odd':null;
 if(type){res['reset'+type]++;let m=q+1;if(Z!==p*m+(type==='Even'?0:-2)||q%4!==(type==='Even'?3:1))throw Error("reset quotient class");
 if(p%4===(type==='Even'?1:3)&&q===p+2&&p>=11){res['min'+type]++;if(spf[M]===M)res['primeRoots'+type]++;let rec={M,primeRoot:spf[M]===M,p,q,d,w,Z,n,delta,history:history.slice(),next:next(n,Z)};
 if(!comp){res['min'+type+'Twin']++;let e2=rec.next;if(!e2||e2.p!==3||e2.w!==4)throw Error("forced3");res.forced3++;if(res['min'+type+'Examples'].length<4)res['min'+type+'Examples'].push(rec)}
 else{res['min'+type+'Composite']++;if(d<p+1+delta-2*r||w>r-1)throw Error('sharp late entry');res.minBackwardChecks++;rec.r=r;if(res.lateExamples.length<6)res.lateExamples.push(rec)}
 if(prev){let l=prev.p;if(prev.s===s){if((p+1)%l||w<l-1||w%2)throw Error('same-side square ancestry');res.sameSidePredecessorChecks++;if(comp){if(!(l<r))throw Error('small predecessor');res.lateSameSideChecks++;}}else {let u=s===-1?2*w+8:2*w-4,H=u*u+(s===-1?2:-2);if(H%l||H===0)throw Error('opposite-side square ancestry');res.oppositeSidePredecessorChecks++;}}
 }
 }
 t=n;C=Z;prev=e;
 }}
 // Independent exact conditional prediction for all actual prime pairs in both classes,
 // whether or not the reset is reachable; check only state arithmetic and next clock.
 for(let p=13;p*(p+3)+1<cap;p+=2)if(spf[p]===p&&spf[p+2]===p+2){let Z=p*(p+3)-(p%4===1?0:2),t=Z/2+(p%4===1?0:3),e=next(t,Z);if(e?.p!==3||e?.w!==4)throw Error("conditional phase");res.pairChecks++}
 // Separate abstract phase-space controls: exact two-edge histories, NOT canonical roots.
 let abstract={targets:0,arrivals:0,compositeArrivals:0,primeArrivals:0,oddArrivals:0,oppositePairs:0,samePairs:0,compositeOppositePairs:0,compositeSamePairs:0,oppositeExample:null,oddExample:null};
 for(let p=11;p<=500&&p*(p+3)+1<cap;p+=2)if(spf[p]===p){let q=p+2,s=p%4===1?-1:1,delta=s===-1?0:6,C=p*q-s,Z=C+p-1,n=(Z+delta)/2,r=spf[q],comp=r!==q;abstract.targets++;for(let w=1;w<=2*p;w++){let t=n-w,d=2*t-C;if(d<0)continue;let win=next(t,C);if(!win||win.p!==p||win.w!==w||win.s!==s)continue;abstract.arrivals++;if(comp){abstract.compositeArrivals++;if(w>r-1||d<p+1+delta-2*r)throw Error('abstract late entry')}else abstract.primeArrivals++;if(s===1){abstract.oddArrivals++;if(!abstract.oddExample)abstract.oddExample={p,q,C,Z,n,t,w,d,delta,comp}}
 let side=t%2?1:-1;for(let l of new Set(factors(C+(side===1?2:0)))){if(l===2)continue;let Cp=C-l+1;if(Cp<4||2*(t-1)<Cp)continue;let prev=next(t-1,Cp);if(!prev||prev.w!==1||prev.p!==l||prev.s!==side)continue;if(side===s){abstract.samePairs++;if((p+1)%l||w<l-1||w%2)throw Error('abstract same side');if(comp){abstract.compositeSamePairs++;if(!(l<r))throw Error('abstract descent')}}else{abstract.oppositePairs++;let u=s===-1?2*w+8:2*w-4,H=u*u+(s===-1?2:-2);if(H%l||H===0)throw Error('abstract opposite side');if(comp){abstract.compositeOppositePairs++;if(!abstract.oppositeExample)abstract.oppositeExample={p,q,r,s,C,Z,t,n,w,d,delta,l,side,Cp,start:t-1}}}}
 }}res.abstract=abstract;return res
}

console.log(JSON.stringify(audit(Number(process.argv[2] || 100000),Number(process.argv[3] || 24)),null,2));
