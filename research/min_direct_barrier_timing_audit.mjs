// Barrier capacities, timing dichotomy and truncated deficit potential audit.
function audit(N=100000,steps=180){
 const cap=4*N+30000,spf=new Int32Array(cap+1);
 for(let i=2;i<=cap;i++)if(!spf[i]){spf[i]=i;if(i*i<=cap)for(let j=i*i;j<=cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(x,p)=>(x%p+p)%p;
 function next(t,H){let b=null;for(let e of [1,-1]){let z=H-e;while(z>1){let p=spf[z];if(!p)throw Error("range");while(z%p===0)z/=p;if(p*p>H+1)continue;let w=mod((e===1?0:p+2)-t,2*p)||2*p;if(!b||w<b.w||w===b.w&&p<b.p)b={p,e,w}}}return b}
 const tables=[];for(let R of [5,7,11,13,17]){let ps=[];for(let p=3;p<=R;p+=2)if(spf[p]===p)ps.push(p);let P=ps.reduce((a,p)=>a*p,1),A=ps.reduce((a,p)=>a*(p-1)/2,1),pre=new Uint32Array(P+1);
 for(let j=0;j<P;j++)pre[j+1]=pre[j]+(ps.every(p=>mod(2*j,p)%2===0&&mod(2*j,p)<=p-3)?1:0);
 if(pre[P]!==A)throw Error("period");let C=j=>Math.floor(j/P)*A+pre[j%P];tables.push({R,P,A,count:(h,z)=>C(z/2)-C(h/2)})}
 let s={N,steps,roots:0,events:0,paths:0,terminal:0,capUnresolved:0,intervals:0,barrierCapacityChecks:0,farCountChecks:0,goodBadChecks:0,badEvents:0,shortReset:0,nonreset:0,chargeChecks:0,rootSparseChecks:0,potentialChecks:0,potentialIntervalChecks:0,localTimeChecks:0,goodEvents:0,farEvents:0,positiveResidual:0,example:null};
 function check(ev,roots,i,j){if(i>=j)return;let h=ev[i].H,z=ev[j-1].Z,G=z-h,t0=ev[i].t,t1=ev[j-1].n,rootN=roots.filter(t=>t>t0&&t<=t1).length,C=Math.floor(Math.sqrt(z+1));
 for(let {R,P,A,count} of tables){let B=count(h,z),Ng=0,Nc=0,Bn=0,F=0,m=0,Bf=0,F0=0,m0=0,B0=0,F1=0,m1=0,B1=0,Fg=0,mg=0,Bg=0,Fb=0,mb=0,Bb=0,charges=new Map(),L=2*Math.floor(R/8),sumU=0,sumV=0,highTicks=0;
 for(let k=i;k<j;k++){let a=ev[k],g=a.p-1,b=count(a.H,a.Z);
 if(2*P*b>A*(g+2*P))throw Error("capacity");s.barrierCapacityChecks++;
 let d=a.d0+2*a.w,up=Math.max(0,d-L)-Math.max(0,a.d0-L),v=Math.max(0,d-L)-Math.max(0,a.d1-L),ct=Math.max(0,a.w-Math.max(0,(L-a.d0)/2));if(up!==2*ct||v!==Math.min(g,Math.max(0,d-L)))throw Error("potential local");sumU+=up;sumV+=v;highTicks+=ct;s.potentialChecks++;
 if(a.p<=R){if(b)throw Error("low");continue}
 if(a.near){Ng+=g;Nc++;Bn+=b;continue}
 F+=g;m++;Bf+=b;s.farEvents++;
 if(a.D===0){F0+=g;m0++;B0+=b}else{F1+=g;m1++;B1+=b}
 if(a.D===0&&4*a.w>=g){Fg+=g;mg++;Bg+=b;s.goodEvents++}
 else{Fb+=g;mb++;Bb+=b;s.badEvents++;
 let ix,dd;if(a.D!==0){ix=k+1;dd=a.d1;s.nonreset++}else{ix=k;dd=a.d0;s.shortReset++}
 if(2*dd<g||dd<(R-1)/2)throw Error("charge");charges.set(ix,dd);s.chargeChecks++}
 }
 let Q0=Math.max(0,ev[i].d0-L),Q1=Math.max(0,ev[j-1].d1-L);
 if(Q1-Q0!==sumU-sumV||2*highTicks!==sumU||4*sumV<3*F||2*highTicks<3*F/4-Q0)throw Error("potential interval");s.potentialIntervalChecks++;
 let res=A*(G-Ng)-2*P*A*(Nc+1);
 if(B!==Bn+Bf||Bf!==Bg+Bb||Bf!==B0+B1||F!==Fg+Fb||m!==mg+mb)throw Error("partition");
 if(A*(F+2*P*m)<res||A*(C+2*P)*m<res||2*P*F<res||2*P*Bf<res)throw Error("far count/gain");
 if(A*(Fg+2*P*mg)<2*P*Bg||A*(Fb+2*P*mb)<2*P*Bb||2*charges.size<mb||4*[...charges.values()].reduce((x,y)=>x+y,0)<Fb)throw Error("charge global");
 if(res>0)s.positiveResidual++;
 // All high resets (p>R>=5) normalize before the next such reset;
 // at most one pending, including when the prefix ends on a terminal.
 if(m0>rootN+1||2*P*F1<A*(G-Ng-F0)-2*P*A*(Nc+m0+1))throw Error("root sparse");
 s.intervals++;s.farCountChecks++;s.goodBadChecks++;s.rootSparseChecks++;
 if(mb&&(!s.example||Fb>s.example.Fb))s.example={H:h,Z:z,R,F,Fg,Fb,mb,chargeCount:charges.size,chargeSum:[...charges.values()].reduce((x,y)=>x+y,0),highTicks,Q0};
 // For a preceding subinterval, exact local high-tick extension,
 // whenever its elapsed time is at least F/16.
 if(i>0&&16*(t0-ev[0].t)>=F){
 let prior=0;for(let k=0;k<i;k++){let a=ev[k];prior+=Math.max(0,a.w-Math.max(0,(L-a.d0)/2))}
 if(32*(prior+highTicks)<F)throw Error("local time");s.localTimeChecks++;
 }
 }
 }
 for(let M=5;M<=N;M+=2){s.roots++;let t=M+2,H=2*M-2,ev=[],roots=[];
 for(let k=0;k<steps;k++){if(H+Math.sqrt(H+1)+30>=cap)throw Error("cap");let a=next(t,H);if(!a){s.terminal++;break}
 let n=t+a.w,Z=H+a.p-1,d0=2*t-H,d1=2*n-Z,D=d1-3*(1-a.e),q=(H-a.e)/a.p,x=(a.p+q)/2,u=(q-a.p)/2;
 let rt=H/2+3;if(H%4===0&&rt>t&&rt<n)roots.push(rt);
 if(Z%4===0&&d1===6)roots.push(n);
 ev.push({...a,t,n,H,Z,d0,d1,D,near:x>=64&&2*u*u<=x});s.events++;t=n;H=Z;
 if(k===steps-1)s.capUnresolved++}
 if(ev.length){s.paths++;check(ev,roots,0,ev.length);if(ev.length>=4)check(ev,roots,Math.floor(ev.length/2),ev.length)}
 }
 return s
}
console.log(JSON.stringify(audit(Number(process.argv[2]||100000),Number(process.argv[3]||180)),null,2));
