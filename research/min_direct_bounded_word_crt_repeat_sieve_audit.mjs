// Bounded MIN words: first-occurrence CRT, repeated-label linear constraint, and rough source lines.
function audit(N=60000){
 const lim=2000000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g}}}return z}
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 const st={roots:0,events:0,cap:0,controls:0,words:0,adjacent:0,repeatWords:0,distinctWords:0,actualRepeat:0,repeatSource:0,repeatOther:0,dependentSourceExcluded:0,offsetChecks:0,repeatOffsetChecks:0,crtChecks:0,roughChecks:0,linearChecks:0,dependentIntervalChecks:0,disjointChecks:0,causalPairs:0,causalRepeated:0,examples:[],synthetic:0};
 function check(v,T,B){
  let hi=v.map((z,i)=>({...z,i})).filter(z=>z.p>=T&&z.p<=6*T),taken=-1,usedLow=0,lowTotal=v.filter(z=>z.p<T).reduce((a,z)=>a+z.g,0);
  for(let i=0;i<hi.length;i++){let s=hi[i];if(2*s.w<=s.g)continue;
   for(let j=i+1;j<hi.length&&j<=i+4;j++){let t=hi[j],raw=v.slice(s.i,t.i+1);if(raw.some(z=>z.p>6*T))break;let low=raw.filter(z=>z.p<T).reduce((a,z)=>a+z.g,0);if(low>B)break;if(s.p===t.p)continue;
    let a=hi.slice(i,j+1),offs=[],sum=0,seen=new Map,repeat=null,P=1n,H0=0n;
    for(let k=0;k<a.length;k++){let z=a[k],E=z.H-s.H-sum;ok(E>=0&&E<=B&&(k===0?E===0:E>=offs[k-1]),"offset");offs.push(E);st.offsetChecks++;
     if(k)ok(z.p!==a[k-1].p,"adjacent same");let residue=mod(z.e-sum-E,z.p);
     if(!seen.has(z.p)){let p=BigInt(z.p),v0=BigInt(mod(residue-Number(H0%p),z.p)),c=BigInt(inv(Number(P%p),z.p));H0+=P*((v0*c)%p);P*=p;seen.set(z.p,{k,residue});}
     else {let o=seen.get(z.p);ok(o.residue===residue&&mod(E,z.p)===mod(z.e-sum-o.residue,z.p),"repeat offset");st.repeatOffsetChecks++;if(!repeat)repeat=[o.k,k];seen.set(z.p,{k,residue});}
     sum+=z.g;
    }
    ok((BigInt(s.H)-H0)%P===0n,"CRT");st.crtChecks++;
    let q0=(H0-BigInt(s.e))/BigInt(s.p),slope=P/BigInt(s.p),z0=(BigInt(s.H)-H0)/P;
    ok(q0+slope*z0===BigInt((s.H-s.e)/s.p),"source line");
    for(let f of pr){if(f>=T||4*f>=s.g)break;let f0=BigInt(f),r1=mod(-Number(q0%f0)*inv(Number(slope%f0),f),f),r2=mod(-Number((BigInt(s.p)*q0+BigInt(2*s.e))%f0)*inv(Number(P%f0),f),f);ok(r1!==r2&&mod(Number(z0%f0),f)!==r1&&mod(Number(z0%f0),f)!==r2,"rough");st.roughChecks++}
    st.words++;if(a.length===2)st.adjacent++;
    if(repeat){st.repeatWords++;let [l,k]=repeat,p=a[l].p,m=(a[k].H-a[l].H-a[k].e+a[l].e)/(2*p),counts=new Map;
     ok(Number.isInteger(m)&&m>=1,"repeat m");for(let n=l+1;n<k;n++)counts.set(a[n].p,(counts.get(a[n].p)||0)+1);
     ok(!counts.has(p)&&counts.size>0,"consecutive occurrences");let E=offs[k]-offs[l],lhs=(2*m-1)*p-[...counts].reduce((s,[r,c])=>s+r*c,0),rhs=E-(k-l)-a[k].e+a[l].e;ok(lhs===rhs,"linear");st.linearChecks++;
     let dep=p!==s.p?p:[...counts.keys()][0],coef=dep===p?2*m-1:-counts.get(dep),base=lhs-coef*dep,lo=-(k-l)-a[k].e+a[l].e,hi0=lo+B;
     ok(dep!==s.p&&coef!==0&&lo<=base+coef*dep&&base+coef*dep<=hi0,"dependent interval");let aa=(lo-base)/coef,bb=(hi0-base)/coef;ok(Math.floor(Math.max(aa,bb))-Math.ceil(Math.min(aa,bb))+1<=B+1,"capacity");st.dependentIntervalChecks++;st.dependentSourceExcluded++;if(p===s.p)st.repeatSource++;else st.repeatOther++;
     if(st.examples.length<3)st.examples.push({T,B,labels:a.map(z=>z.p),offsets:offs,repeat:[l,k],m,dep,coef,H:s.H,low});
    } else st.distinctWords++;
    let overlap=Math.max(0,Math.min(s.dp,t.d)-Math.max(s.d,t.dp));
    if(t.dp<t.d&&overlap>0){let u=Math.max(s.d,t.dp),end=Math.min(s.dp,t.d);let min=Math.min(...raw.slice(0,-1).map(z=>z.dp));if(min>u&&end>u){st.causalPairs++;if(repeat)st.causalRepeated++}}
    if(s.i>taken){taken=t.i;usedLow+=low;ok(usedLow<=lowTotal,"disjoint low budget");st.disjointChecks++}
   }
  }st.controls++;
 }
 for(let n=5;n<=N;n+=2){let H=2*n-2,t=n+2,v=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;v.push(z);H+=z.g;t+=z.w}st.events+=v.length;if(v.length===180)st.cap++;
 for(let T of [11,17,31,61])check(v,T,Math.min(T-4,Math.ceil(Math.log(T)**2)))}
 for(let p of [11,17,31,61])for(let c=1;c<=5;c++)for(let B of [0,1,3,7])for(let a=-30;a<=30;a++){let x=0;for(let r=-100;r<=100;r++)if(a<=c*r&&c*r<=a+B)x++;ok(x<=B+1,"integer interval");st.synthetic++}
 ok(st.words&&st.repeatWords&&st.distinctWords&&st.roughChecks&&st.repeatSource&&st.repeatOther,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||60000)),null,2));
