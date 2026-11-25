// Four-form rough-pair support and actual synchronous clock packing audit. Finite diagnostics, not asymptotic parameters.
function roughPairAudit(X){
 const B=Math.ceil(Math.sqrt(7*X)),T=Math.min(8*B,Math.floor(X/2)),H=T+B,Q=Math.max(5,Math.ceil(B/10)),R=Math.max(3,Math.min(Math.ceil(Math.sqrt(B)),Math.ceil(Q/2))),L=8,m=8,lo=2*X-2,hi=7*X,lim=hi+B+L+10;
 const spf=new Int32Array(lim),fail=(b,s)=>{if(!b)throw Error(X+" "+s)},mod=(a,m)=>((a%m)+m)%m;
 for(let p=2;p<lim;p++)if(!spf[p]){spf[p]=p;if(p*p<lim)for(let j=p*p;j<lim;j+=p)if(!spf[j])spf[j]=p;}
 function factors(n){let a=[];while(n>1){let p=spf[n];if(p!==2&&p<=B)a.push(p);while(n%p===0)n/=p;}return a;}
 const r=new Int32Array(lim);for(let C=lo;C<=hi;C+=2){let a=factors(C-1),b=factors(C+1);r[C]=Math.min(a[0]||B+1,b[0]||B+1);}
 const fwd=new Set(),back=new Set(),key=(C,p,e)=>`${C}|${p}|${e}`,pairs=new Set();let formChecks=0,goodPrimeChecks=0;
 for(let p=Q;p<=B;p++)if(spf[p]===p&&p%2)for(let sig of [-1,1]){
   let k0=Math.ceil(((lo+sig)/p-1)/2),k1=Math.floor(((hi+sig)/p-1)/2);
   for(let k=k0;k<=k1;k++){let a=2*k+1,C=p*a-sig;fail(C%2===0&&C>=lo&&C<=hi,"quotient");if(2*r[C]<=p)continue;
     for(let e=0;e<=L;e+=2){let J=C+p-1+e;if(J>hi||r[J]<R)continue;
       const forms=[a,p*a-2*sig,p*a+p+e-sig-2,p*a+p+e-sig];
       fail(forms[1]===C-sig&&forms[2]===J-1&&forms[3]===J+1,"forms");formChecks++;
       for(let q=3;q<R;q+=2)if(spf[q]===q)fail(forms.every(v=>v%q!==0),"four rough forms");
       const offs=[0,-2*sig,p+e-sig-2,p+e-sig];
       for(let q of [7,11,13,17,19,23]){if(q===p||offs.some((v,i)=>offs.slice(i+1).some(w=>(v-w)%q===0)))continue;
         let roots=0;for(let x=0;x<q;x++)if([2*x+1,p*(2*x+1)-2*sig,p*(2*x+1)+offs[2],p*(2*x+1)+offs[3]].some(v=>v%q===0))roots++;
         fail(roots===4,"four distinct forbidden residues");goodPrimeChecks++;
       }
       const z=key(C,p,e);fail(!pairs.has(z),"unique sign");pairs.add(z);fwd.add(C);back.add(J);
     }
   }
 }
 let brute=0;for(let C=lo;C<=hi;C+=2)for(let p of [...factors(C-1),...factors(C+1)])if(p>=Q&&2*r[C]>p)for(let e=0;e<=L;e+=2){let J=C+p-1+e;if(J<=hi&&r[J]>=R){fail(pairs.has(key(C,p,e)),"brute support");brute++;}}
 fail(brute===pairs.size,"support equality");
 const paths=[],state=new Map(),stride=lim;let N=0,raw=0,rawHigh=0,events=0,actualNear=0,actualNextRough=0;
 for(let M=X;M<2*X;M++)if(spf[M]===M){
   N++;let t=M+2,C=2*M-2,C0=C,K=Math.floor((7*M-1)/4),es=[];
   while(C-C0<T){let v=Infinity,p=0,rr=r[C];for(let s of [-1,1])for(let q of factors(C+s)){let phase=s===-1?0:q+2,j=t+1+mod(phase-t-1,2*q);if(j<v||(j===v&&q<p)){v=j;p=q}}
     if(!p||v>K)break;let J=C+p-1,w=v-t;fail(w<=2*rr&&w<=3*(p-1),"clock");const high=p>=Q&&2*rr>p;let e={C,t,v,p,J,high};es.push(e);events++;raw+=w;if(high)rawHigh+=w;
     for(let j=t;j<v;j++){let k=j*stride+C,a=state.get(k);if(!a){a={C,j,n:0,high,p};state.set(k,a)}fail(a.high===high&&a.p===p,"state exit");a.n++;}
     C=J;t=v;
   }
   for(let i=0;i<es.length;i++)if(es[i].high){const a=es[i];if(a.J<=hi&&r[a.J]>=R){actualNextRough++;fail(pairs.has(key(a.C,a.p,0)),"actual rough landing");}
     let j=i+1;while(j<es.length&&es[j].C-a.J<=L){if(es[j].high){actualNear++;fail(pairs.has(key(a.C,a.p,es[j].C-a.J))&&back.has(es[j].C),"actual close high pair");}j++;}
   }
   paths.push(es);
 }
 let paidForward=0,paidBack=0,largeMass=0,remaining=0,allPaid=0,forwardStates=0,backStates=0,retainedIsolation=0,retainedHighGap=0;
 for(let a of state.values()){
   let F=fwd.has(a.C)&&a.high,G=back.has(a.C);
   if(a.n<=m&&(F||G)){allPaid+=a.n;if(a.high){if(F){paidForward+=a.n;forwardStates++;}else{paidBack+=a.n;backStates++;}}}
   else if(a.high){remaining+=a.n;if((F||G)&&a.n>m)largeMass+=a.n;}
 }
 fail(paidForward+paidBack+remaining===rawHigh,"partition");
 for(let es of paths)for(let i=0;i<es.length;i++){let a=es[i];if(!a.high)continue;
   let thin=false;for(let j=a.t;j<a.v;j++){let b=state.get(j*stride+a.C);if(b.n<=m&&!fwd.has(a.C)&&!back.has(a.C))thin=true;}
   if(!thin)continue;
   for(let J=a.J;J<=Math.min(hi,a.J+L);J+=2){fail(r[J]<R,"retained isolated landing");retainedIsolation++;}
   let k=i+1;while(k<es.length&&!es[k].high)k++;if(k<es.length){fail(es[k].C-a.J>L,"retained next high gap");retainedHighGap++;}
 }
 return {X,B,T,Q,R,L,m,N,events,states:state.size,raw,rawHigh,triples:pairs.size,forwardHorizons:fwd.size,backHorizons:back.size,formChecks,goodPrimeChecks,actualNear,actualNextRough,paidForward,paidBack,allPaid,remaining,largeMass,forwardStates,backStates,retainedIsolation,retainedHighGap};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(roughPairAudit(X)));
