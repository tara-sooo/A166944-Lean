// Fixed deficit-cut clock supply and canonical unit-wait recovery cylinders.
function audit(N=30000){
 const cap=300000,spf=new Int32Array(cap);for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i*i<cap)for(let j=i*i;j<cap;j+=i)if(!spf[j])spf[j]=i}
 const mod=(x,p)=>(x%p+p)%p,pr=[];for(let p=3;p<cap;p+=2)if(spf[p]===p)pr.push(p);
 const factors=x=>{let a=[];while(x>1){let p=spf[x];if(!p)throw Error("range");a.push(p);while(x%p===0)x/=p}return a};
 function winner(t,H){let best=null;for(let e of [1,-1])for(let f of factors(H-e)){if(f*f>H+1)continue;let lag=mod((e===1?0:f+2)-t,2*f)||2*f;if(!best||lag<best.w||lag===best.w&&f<best.p)best={p:f,w:lag,e}}return best}
 function forbidden(s,h,I,f,W,J){
  let d=mod((2*h+1)*s+6*(I-J),f),lag=mod(d*((f+1)/2),f);
  if(lag%2!==mod(I-J,2))lag+=f;
  return {lag,no:(lag===0&&f<s)||(lag>0&&lag<W)}
 }
 let st={abstractStates:0,validAbstract:0,invalidAbstract:0,clockChecks:0,unitTests:0,unitSaturation:0,cutTests:0,crtCounts:0,crtCandidates:0,roots:0,events:0,cutIncidences:0,eligibleRecovery:0,canonicalWitnesses:[]};
 for(let s of [5,7,11,13,17,23,31,47,71])for(let I of [0,1])for(let h of [1,2,3,7,19,(s*s-1)/2,(s**3-1)/2]){
  let e=1-2*I,res=mod(e+s*(2*I-2*h-1),4*s),dp=2*s*h+6*I;
  for(let W of [...new Set([1,2,Math.floor((s-3)/2)])].filter(w=>w<=Math.floor((s-3)/2))){
   let b=dp+2;
   for(let j=0;j<60;j++){
    let H=s*s+10000+mod(res-s*s-10000,4*s)+4*s*j,n=(H+s-1+dp)/2,t=n-W;
    if(!Number.isInteger(n)||n%2!==I||H%s!==mod(e,s)||!(dp<b&&b<=2*t-H))throw Error("geometry");
    let ok=true;for(let f of pr){if(f*f>H+1)break;if(f===s)continue;
     for(let J of [0,1])if(mod(H-(1-2*J),f)===0){
      let a=forbidden(s,h,I,f,W,J),actual=mod(n-(J?f+2:0),2*f);if(a.lag!==actual)throw Error("lag");
      st.clockChecks++;if(a.no)ok=false;
     }
    }
    let win=winner(t,H),actual=!!win&&win.p===s&&win.w===W&&win.e===e;
    if(actual!==ok)throw Error("exact candidate");
    st.abstractStates++;if(ok)st.validAbstract++;else st.invalidAbstract++;
    if(W===1){let unit=pr.filter(f=>f<s&&(2*h+1)%f===0).every(f=>mod(H-e,f)!==0);if(unit!==actual)throw Error("unit");st.unitTests++;if(2*h+1===s*s||2*h+1===s**3){if(!actual)throw Error("saturation");st.unitSaturation++}}
   }
   let tiny=pr.filter(f=>f<=11&&f!==s),forbid=new Map(tiny.map(f=>[f,[0,1].filter(J=>forbidden(s,h,I,f,W,J).no).map(J=>mod(1-2*J,f))])),P=tiny.reduce((a,f)=>a*f,1),A=tiny.reduce((a,f)=>a*(f-forbid.get(f).length),1),cnt=0;
   for(let j=0;j<P;j++){let H=res+4*s*j;if(tiny.every(f=>!forbid.get(f).includes(mod(H,f))))cnt++}
   if(cnt!==A)throw Error("CRT");st.crtCounts++;st.crtCandidates+=P;
  }
 }
 for(let M=5;M<=N;M+=2){st.roots++;let H=2*M-2,t=M+2;
  for(let j=0;j<180;j++){if(H+Math.sqrt(H+1)>=cap)break;let a=winner(t,H);if(!a)break;let n=t+a.w,Z=H+a.p-1,d=2*t-H,dp=2*n-Z,I=(1-a.e)/2,D=dp-6*I;st.events++;
   if(a.p>=5&&D>0&&dp<d){let s=a.p,h=D/(2*s);if(!Number.isInteger(h))throw Error("multiplier");st.eligibleRecovery++;
    for(let b=dp+2;b<=d;b+=2){let hh=Math.floor((b-6*I-1)/(2*s)),r=b-6*I-2*s*hh;if(h!==hh||r<2||r>s-3||a.w>(s-1-r)/2||mod(H-(a.e+s*(2*I-2*h-1)),4*s)!==0)throw Error("cut");st.cutIncidences++;
     for(let f of pr){if(f*f>H+1)break;if(f===s)continue;for(let J of [0,1])if(mod(H-(1-2*J),f)===0){if(forbidden(s,h,I,f,a.w,J).no)throw Error("actual clock");st.cutTests++}}
    }
   }H=Z;t=n;
  }
 }
 function data(p,word){let G=0;return word.map((s,i)=>{let j=i+1,I=j%2,e=1-2*I,c=2*j+1-6*I-G,offset=p-1+G-e;G+=s-1;return{s,j,I,c,offset,F:2*p+c}})}
 function residues(p,word){let a=data(p,word),out=[];
  for(let f of pr){if(f>3*p+6)break;let hit=a.find(v=>v.s===f),fixed=f===p?1:hit?mod(-hit.offset,f):null;
   let ok=r=>(f===p?r===1:r!==1&&r!==f-1)&&a.every(v=>v.F%f!==0||(v.s===f?mod(r+v.offset,f)===0:mod(r+v.offset,f)!==0));
   let r=fixed===null?0:fixed;if(fixed===null)while(r<f&&!ok(r))r++;if(r===f||!ok(r))return null;out.push([f,r])
  }return out
 }
 function witness(p,word){let a=data(p,word),rr=residues(p,word);if(!rr||a.some(v=>v.F<=0||v.F%v.s!==0||v.F%(v.s*v.s)===0))throw Error("witness data");
  let H=0n,P=4n;for(let [s,r] of rr){let L=BigInt(s),x=Number(P%L),y=s,u=1,v=0;while(y){let q=Math.floor(x/y);[x,y]=[y,x-q*y];[u,v]=[v,u-q*v]}if(x!==1)throw Error("inverse");H+=P*BigInt(mod(u*mod(r-Number(H%L),s),s));P*=L}
  if(H<BigInt(p*p+10))H+=P;
  let H0=H,t=H/2n+3n,ticks=0,post=[],labels=[p,...word],waits=[(3*p-7)/2,...word.map(()=>1)];
  for(let i=0;i<labels.length;i++){let s=labels[i],w=waits[i],n=t+BigInt(w);
   for(let j=1;j<=w;j++){let tick=t+BigInt(j),I=tick%2n,e=1n-2n*I,x=tick-2n*I,y=H-e;while(y)[x,y]=[y,x%y];if(x!==(j===w?BigInt(s):1n))throw Error("literal");ticks++}
   let Z=H+BigInt(s-1),dp=Number(2n*n-Z),I=Number(n%2n),D=dp-6*I;if(BigInt(s)**2n>H+1n||D<=0||D%(2*s)!==0)throw Error("witness D");
   if(i===0&&D!==2*p)throw Error("A1");if(i>0&&D/(2*s)!==(a[i-1].F/s-1)/2)throw Error("h formula");post.push({s,w,dp,h:D/(2*s)});t=n;H=Z
  }
  st.canonicalWitnesses.push({p,word,digits:(H0/2n+1n).toString().length,ticks,residueChecks:rr.length*(word.length+2),post})
 }
 witness(79,[31,7,41,13]);witness(1279,[7]);
 let found=0;for(let p=1001;p<=N;p+=2)if(spf[p]===p&&p%12===7&&(2*p-3)%31===0&&(2*p-25)%7===0&&(2*p-3)%961!==0&&(2*p-25)%49!==0&&residues(p,[31,7])){witness(p,[31,7]);if(++found===2)break}
 if(found!==2)throw Error("witness coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||30000)),null,2));
