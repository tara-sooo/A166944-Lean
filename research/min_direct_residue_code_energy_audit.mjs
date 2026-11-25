// Low-frequency CRT residue-code shortening and weighted moment energy.
function audit(){
 const ps=[];for(let p=3;p<=31;p+=2)if(!ps.some(q=>q*q<=p&&p%q===0))ps.push(p);
 const mod=(a,b)=>(a%b+b)%b,choose=(n,k)=>{if(k<0||k>n)return 0;let v=1;for(let i=1;i<=Math.min(k,n-k);i++)v=v*(n-i+1)/i;return v};
 function subsets(n,h){let out=[];function go(i,a){if(a.length===h){out.push(a);return}for(let j=i;j<=n-h+a.length;j++)go(j+1,[...a,j])}go(0,[]);return out}
 const local=(j,p,kind)=>kind==="H"?j<=(p-3)/2:p===3||[0,1].every(I=>{let r=mod(2*j-6*I,2*p);return r<2||r>p-3});
 let st={localChecks:0,fibreChecks:0,shortenedTests:0,nontrivialFibres:0,maxFibre:0,shortenedNontrivial:0,energyChecks:0,partialWeightChecks:0,pointwiseChecks:0,varianceChecks:0,momentPositions:0,periods:[],marginChecks:[]};
 for(let [R,M] of [[13,40],[17,160],[19,400],[23,5000],[29,20000],[31,50000]]){
  let pr=ps.filter(p=>p<=R),P=pr.reduce((a,p)=>a*p,1),L=pr.filter(p=>p>=11),n=L.length,b=L[0],q=0;while(b**(q+1)<=M)q++;
  let kap=Math.max(...L.map(p=>1/(((p-3)/2)*Math.sin(Math.PI/p))));
  for(let kind of ["H","d"]){
   let sets=pr.map(p=>Array.from({length:p},(_,j)=>j).filter(j=>local(j,p,kind))),A=sets.reduce((a,s)=>a*s.length,1);
   let coeff=pr.map((p,i)=>{let inv=1;while((P/p%p)*inv%p!==1)inv++;return Array.from({length:p},(_,k)=>{let re=0,im=0;for(let j of sets[i]){let angle=2*Math.PI*mod(k*inv*j,p)/p;re+=Math.cos(angle);im+=Math.sin(angle)}return (re*re+im*im)/sets[i].length**2})});
   let ix=L.map(p=>pr.indexOf(p)),ms=[1,2].map(s=>Math.max(...ix.map(i=>coeff[i].slice(1).reduce((a,b)=>a+b**s,0))));
   let groups=Array.from({length:q+1},()=>[]);
   for(let k=1;k<=M;k++){
    let t=L.filter(p=>k%p===0).length;if(t>q)throw Error("divisors");
    groups[t].push({k,e:pr.reduce((v,p,i)=>v*coeff[i][k%p],1)});
   }
   let totalBound=0,totalEnergy=0;
   for(let t=0;t<=q;t++){
    if(!groups[t].length)continue;
    let best=Infinity,E=groups[t].reduce((a,o)=>a+o.e,0);
    for(let h=1;h<=n;h++)for(let j=Math.max(0,h+t-n);j<=Math.min(t,h);j++){
     let u=t-j,cap;
     if(h>q)cap=1;
     else{let den=u*u-(n-h)*(q-h);if(den<=0||h===n)continue;cap=Math.max(1,Math.floor((n-h)*(u-q+h)/den))}
     let s=2*(h-j)<=n-t?2:1;
     if(s*(h-j)>n-t)throw Error("moment exponent");
     const sub=subsets(n,h),prob=choose(t,j)*choose(n-t,h-j)/choose(n,h);
     const F=prob*kap**(-2*(n-t-s*(h-j))),B=cap*choose(h,j)*ms[s-1]**(h-j);
     best=Math.min(best,B/F);
     let sum=0,avgByK=new Float64Array(groups[t].length),countByK=new Uint32Array(groups[t].length);
     for(let U of sub){
      let fibres=new Map(),sumU=0;
      for(let i=0;i<groups[t].length;i++){
       let k=groups[t][i].k,rs=U.map(a=>k%L[a]);if(rs.filter(x=>x===0).length!==j)continue;
       let key=rs.join(","),cnt=(fibres.get(key)||0)+1;fibres.set(key,cnt);
       if(cnt>cap)throw Error("fibre bound");
       let v=U.reduce((v,a)=>v*(k%L[a]===0?1:coeff[ix[a]][k%L[a]]**s),1);
       sumU+=v;avgByK[i]+=v;countByK[i]++;
      }
      if(sumU>B+1e-8)throw Error("partial sum");
      st.partialWeightChecks++;
      for(let v of fibres.values()){st.fibreChecks++;st.maxFibre=Math.max(st.maxFibre,v);if(v>1){st.nontrivialFibres++;if(h<=q)st.shortenedNontrivial++}}
     }
     for(let i=0;i<groups[t].length;i++){
      if(Math.abs(countByK[i]/sub.length-prob)>1e-10||avgByK[i]/sub.length+1e-10<groups[t][i].e*F)throw Error("weighted AMGM");
      sum+=avgByK[i]/sub.length;st.pointwiseChecks++;
     }
     if(sum>B+1e-8||E>B/F+1e-8)throw Error("summed energy");
     st.energyChecks++;if(h<=q)st.shortenedTests++;
    }
    if(!Number.isFinite(best)||E>best+1e-8)throw Error("minimum");
    totalBound+=best;totalEnergy+=E;
   }
   if(R<=19){
    let l=Math.ceil(P**(12/25)),pre=new Uint32Array(P+1);
    for(let k=0;k<P;k++)pre[k+1]=pre[k]+(pr.every((p,i)=>sets[i].includes(k%p))?1:0);
    if(pre[P]!==A)throw Error("CRT");
    const count=j=>Math.floor(j/P)*A+pre[mod(j,P)];let v=0;
    for(let k=0;k<P;k++)v+=(P*(count(k+l)-count(k))/(A*l)-1)**2;
    v/=P;let upper=2*totalBound+(P/(2*l*(M+1)))**2*P/A;
    if(v>upper+1e-8)throw Error("variance");
    st.varianceChecks++;st.momentPositions+=P;st.periods.push({R,kind,P,M,q,l,v,upper,totalEnergy,totalBound});
   }
  }
 }
 const D=10n**40n,ceil=(x,y)=>(x+y-1n)/y;
 function log(a,b){a=BigInt(a);b=BigInt(b);if(a<b){let [l,u]=log(b,a);return [-u,-l]}let zl=D*(a-b)/(a+b),zu=zl+1n,lo=0n,hi=0n,pl=zl,ph=zu;for(let i=0;i<300;i++){lo+=2n*pl/BigInt(2*i+1);hi+=ceil(2n*ph,BigInt(2*i+1));pl=pl*zl*zl/(D*D);ph=ceil(ph*zu*zu,D*D)}hi+=ceil(2n*ph*D*D,601n*(D*D-zu*zu));return[lo,hi]}
 function lower(terms){let x=0n;for(let[c,a,b]of terms){let[l,u]=log(a,b);x+=BigInt(c)*(c>=0?l:u)}return x}
 for(let [h,s,a,b] of [[521,1,0,25],[490,2,25,35],[460,2,35,44],[410,2,44,52]]){
  // Plotkin gap at left endpoint in units 1/10^7, or injection.
  let gap=(1000-h)*a*a-(520-h)*10000;if(gap<=0||s*h>=1000)throw Error("gap");
  let terms=[[2*(100-b)*(1000-s*h),314159,200000],[h*b,b,100],[h*(100-b),100-b,100]];
  if(s===2)terms.push([h*(100-b),3,1]);
  let margin=lower(terms);
  // Minus derivative at right endpoint, scaled by 1000.
  let dt=[[2*(1000-s*h),314159,200000],[h,100-b,b]];
  if(s===2)dt.push([h,3,1]);
  let derivative=lower(dt);
  if(margin<=700n*D||derivative<=0n)throw Error("positive margin");
  st.marginChecks.push({h:h/1000,s,left:a/100,right:b/100,plotkinGap:gap/1e7,marginLower:Number(margin)/Number(100000n*D),minusDerivativeLower:Number(derivative)/Number(1000n*D)});
 }
 if(!st.shortenedTests||!st.shortenedNontrivial)throw Error("missing nontrivial shortening");
 return st
}
console.log(JSON.stringify(audit(),null,2));
