// Near-square first-pair label gaps, two-plateau roughness and direct causal recovery.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 function factors(x){ok(x>0&&x<lim,"range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function inv(a,b){let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,g,q:(H-1+2*I)/p}}}return z}
 function roots(p,e,D,f){let a=[0,mod(-2*e*inv(p,f),f),mod(-(e+D-1)*inv(p,f),f),mod(-(e+D+1)*inv(p,f),f)];ok((new Set(a).size<4)===(mod(D,f)===0||mod(D-2,f)===0||mod(D+2,f)===0),"collision");return a}
 const st={roots:0,events:0,cap:0,controls:0,pairs:0,closeLabels:0,crt:0,delta:0,doubleExtended:0,fast:0,rough:0,actualFourRoots:0,overlapChecks:0,positiveDirect:0,matched:0,guaranteed:0,disjoint:0,synthetic:0,syntheticRoots:0,examples:[]};
 for(let n=5;n<=N;n+=2){let H=2*n-2,t=n+2,v=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;v.push(z);H+=z.g;t+=z.w}st.events+=v.length;if(v.length===180)st.cap++;
  for(let T of [11,17,31,61]){let B=Math.min(T-4,Math.ceil(Math.log(T)**2)),K=6,hi=v.map((z,i)=>({...z,i})).filter(z=>z.p>=T),Glo=v.filter(z=>z.p<T).reduce((a,z)=>a+z.g,0),last=-1,used=0;
   for(let j=1;j<hi.length;j++){let s=hi[j-1],z=hi[j],p=s.p,r=z.p;if(p>K*T||r>K*T||2*s.w<=s.g)continue;let low=v.slice(s.i+1,z.i),E=low.reduce((a,z)=>a+z.g,0);if(E>B)continue;
    let D=z.H-s.H;ok(D===p-1+E&&p!==r,"gap");st.delta++;st.pairs++;if(Math.abs(p-r)<=8)st.closeLabels++;
    let H0=s.e+p*mod((z.e-D-s.e)*inv(p,r),r);ok(mod(s.H-H0,p*r)===0,"CRT");st.crt++;
    let cutoff=Math.ceil(Math.sqrt(T));
    if(z.w>=cutoff){st.doubleExtended++;
      for(let f of pr){if(f>=p||2*f>=Math.min(s.w,z.w))break;if(f<=4)continue;let a=roots(p,s.e,D,f);ok(a.every(b=>mod(s.q,f)!==b),"rough");st.rough++;st.actualFourRoots++}
    }else st.fast++;
    if(z.dp<z.d){
     let u=s.dp-s.d,vv=z.d-z.dp,lo=Math.max(s.d,z.dp),hh=Math.min(s.dp,z.d),m=Math.min(s.dp,...low.map(z=>z.dp)),match=Math.max(0,Math.min(hh,m)-lo);
     // All matched levels are within both endpoints and above source pre; no intervening down consumes them.
     ok(match>=Math.max(0,Math.min(u,vv)-10*E)&&match<=Math.min(u,vv),"direct overlap");
     let rel=low.reduce((a,z)=>a+Math.abs(z.dp-z.d),0);ok(rel<=5*E&&Math.abs(z.d-s.dp)<=rel&&match>=Math.max(0,Math.min(u,vv)-2*rel),"variation");
     st.overlapChecks++;st.matched+=match;st.guaranteed+=Math.max(0,Math.min(u,vv)-10*E);if(match){st.positiveDirect++;if(st.examples.length<3&&z.w<cutoff&&E>0)st.examples.push({T,p,r,H:s.H,H2:z.H,E,D,sourceRise:u,targetDrop:vv,wait:z.w,match})}
    }
    if(s.i>last){last=z.i;used+=E;ok(used<=Glo,"disjoint low");st.disjoint++}
   }st.controls++;
  }
 }
 for(let p of [11,17,31,61,101,251])for(let e of [-1,1])for(let E=0;E<120;E+=2){let D=p-1+E;for(let f of pr){if(f>67)break;if(f<=4||f===p)continue;roots(p,e,D,f);st.syntheticRoots++}st.synthetic++}
 ok(st.pairs&&st.fast&&st.doubleExtended&&st.actualFourRoots&&st.positiveDirect&&st.syntheticRoots,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
