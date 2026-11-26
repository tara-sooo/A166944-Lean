// Height-localized sparse-level gain and clipped-potential flux audit.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"factor range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g,q:(H-1+2*I)/p}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,slow:0,fast:0,roughChecks:0,residueChecks:0,levelFactors:0,sideChecks:0,levelHorizonChecks:0,potentialChecks:0,fastDropChecks:0,externalPositive:0,positiveChecks:0,unionChecks:0,netChecks:0,highBaseline:0,smallLocalWidth:0,multiLevel:0,multiComponents:0,revisited:0,synthetic:0,examples:[]};
 function union(map){let ints=[...map].map(([a,g])=>[a,a+g]).sort((a,b)=>a[0]-b[0]),out=[];for(let [a,b] of ints){if(out.length&&a<=out.at(-1)[1])out.at(-1)[1]=Math.max(out.at(-1)[1],b);else out.push([a,b])}return out}
 function check(rows,l,T){
  if(!l.length)return;
  let k=Math.floor(Math.sqrt(T)),a0=k-2,Mp=new Map,S=new Set(),A=new Set(),R=0,pairs=new Map,prev=-1;
  for(let z of l){ok(z.p>=T&&z.dp>6,"selected");let x=(z.dp-6*z.I)/2;ok(x>0&&x%z.p===0,"factor");ok((z.dp/2)%z.p===0?z.I===0:z.I===1,"side");ok(mod(z.H-z.e-z.p*(2*z.I-2*x/z.p-1),4*z.p)===0,"fixed level phase");st.levelFactors++;st.sideChecks++;st.levelHorizonChecks++;
   let key=[z.dp,z.p,z.I].join(","),old=pairs.get(key);if(old!==undefined){ok(z.H>old&&mod(z.H-old,4*z.p)===0,"revisit");st.revisited++}pairs.set(key,z.H);
   Mp.set(z.dp,Math.max(Mp.get(z.dp)||0,z.g));S.add(z.p);A.add(z.dp);R=Math.max(R,z.p);
  }
  let seg=union(Mp),M=seg.reduce((s,[a,b])=>s+b-a,0),sum=[...Mp.values()].reduce((s,g)=>s+g,0);
  ok(M<=sum&&M<=A.size*(R-1)&&M<=Math.max(...A)-Math.min(...A)+R-1,"union size");st.unionChecks++;
  let phi=d=>seg.reduce((s,[a,b])=>s+Math.max(0,Math.min(d,b)-a),0),F=0,Fslow=0,Ffast=0,Pout=0,Pin=0,U=0,net=0,negFast=0;
  let ids=new Set(l.map(z=>z.i));
  for(let i=0;i<rows.length;i++){let z=rows[i],dv=phi(z.dp)-phi(z.d);ok(Math.abs(dv)<=Math.abs(z.dp-z.d)&&dv*(z.dp-z.d)>=0,"monotone Lipschitz");st.potentialChecks++;net+=dv;
   if(!ids.has(i)){U+=z.g;Pout+=Math.max(dv,0);if(dv>0)st.externalPositive++;continue}
   F+=z.g;Pin+=Math.max(dv,0);
   if(k*z.w<z.g){Ffast+=z.g;negFast-=dv;ok(k*(-dv)>=a0*z.g,"localized fast drop");st.fastDropChecks++;st.fast++}
   else{Fslow+=z.g;st.slow++;ok(dv<=3*z.g+4,"slow supply");st.positiveChecks++;
    for(let f of pr){if(2*f>=z.w||f>=z.p)break;ok((z.H-1)%f!==0&&(z.H+1)%f!==0,"rough");st.roughChecks++;ok(z.q%f!==0&&(z.p*z.q+2*z.e)%f!==0,"cofactor residue");st.residueChecks++}
   }
  }
  ok(F===Ffast+Fslow&&net===phi(rows.at(-1).dp)-phi(rows[0].d),"telescoping");ok(negFast<=Pin+Pout+phi(rows[0].d)-phi(rows.at(-1).dp),"net budget");
  ok(a0*Ffast<=k*(Pin+Pout+M)&&Pout<=5*U&&Pin*(T-1)<=((3*(T-1)+4)*Fslow),"weighted supply");st.netChecks++;
  if(rows[0].d>R)st.highBaseline++;if(M<R*2)st.smallLocalWidth++;if(A.size>1)st.multiLevel++;if(seg.length>1)st.multiComponents++;
  if(st.examples.length<3&&Ffast&&Fslow&&Pout&&seg.length>1)st.examples.push({T,k,A:[...A],labels:[...S],M,F,Fslow,Ffast,Pout,Pin,U,initial:rows[0].d,final:rows.at(-1).dp});
  st.blocks++;st.selected+=l.length;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push({...z,i:j});H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
 for(let T of [9,17,31,61]){let l=rows.filter(z=>z.p>=T&&z.p<=8*T&&z.dp>6);if(!l.length)continue;check(rows,l,T);let a=l[0].dp;check(rows,l.filter(z=>Math.abs(z.dp-a)<=T),T);check(rows,l.filter(z=>z.dp%6===a%6),T)}
 // Also start at a later plateau to exercise inherited high deficits.
 if(rows.length>5){let r=rows.slice(Math.floor(rows.length/2)).map((z,i)=>({...z,i}));check(r,r.filter(z=>z.p>=9&&z.dp>6),9)}
 }
 // Scalar independent union/flux checks, not MIN trajectories.
 for(let j=0;j<3000;j++){let map=new Map;for(let i=0;i<1+j%12;i++)map.set(100+(j*17+i*31)%300,1+(j*13+i*23)%90);let s=union(map),phi=d=>s.reduce((v,[a,b])=>v+Math.max(0,Math.min(d,b)-a),0);for(let [a,g] of map)ok(phi(a+g)-phi(a)===g,"synthetic union covers each interval");st.synthetic++}
 ok(st.fast&&st.slow&&st.externalPositive&&st.roughChecks&&st.revisited&&st.highBaseline&&st.multiComponents,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
