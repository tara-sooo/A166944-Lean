// Deficit level-crossing potential, exact CRT preemption and actual band checks.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(a,b)=>(a%b+b)%b,limit=4000000,spf=new Uint32Array(limit+1);
 for(let p=2;p*p<=limit;p++)if(!spf[p])for(let n=p*p;n<=limit;n+=p)if(!spf[n])spf[n]=p;
 function factors(n){n=Math.abs(n);ck(n>=1&&n<=limit,"factor "+n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p;}return a}
 function next(u,v,y){let p=Infinity,w=Infinity,e=0;for(let [n,s] of [[u-1,1],[u+1,-1]])for(let q of factors(n)){if(q>=y)continue;let t=mod((s===1?0:q+2)-v,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t;e=s}}return {p,w,e}}
 let results=[];
 for(let [kind,y,R,end,C] of [["period",7,60,120,64],["period",11,420,840,64],["period",13,4620,9240,64],["period",17,60060,120120,64],["period",19,1021020,2042040,64],["local",127,100000,112000,8],["local",503,1000000,1012000,8],["local",997,1000000,1012000,8]]){
  let H=[];for(let p=y;p<=2*y;p++)if(!spf[p])H.push(p);let cap=C*y,amax=3+3*(cap+2*y)+10,a=new Float64Array(amax+1),Phi=new Float64Array(amax+1);
  for(let h=1;h<=amax;h++){for(let p of H){if((2*h+1)%p===0)a[h]+=1/p;if((2*h-5)%p===0)a[h]+=1/p;}Phi[h]=Phi[h-1]+a[h]}
  let s={kind,y,R,end,C,roots:0,complete:0,censored:0,events:0,quietTicks:0,coareaChecks:0,exactCRTChecks:0,actualBandChecks:0,actualPreempt:0,actualAny:0,sumGain:0,sumEvents:0,sumPreemptProb:0,sumAnyProb:0,sumUnion:0,sumUp:0,sumDown:0,sumTerminalPotential:0,sumSmallGain:0,maxPreemptProb:0,maxUp:0,maxG:0,maxEvents:0,example:null};
  function probability(m){let a=1;for(let [p,S] of m)a*=1-S.size/p;return 1-a}
  function add(m,p,r){if(!m.has(p))m.set(p,new Set());m.get(p).add(r)}
  for(let X=Math.ceil(R/6)*6;X<end;X+=6){
   s.roots++;let u=X,v=X/2+3,h=3,G=0,N=0,small=0,up=0,down=0,union=0,marks=new Map(),path=[];
   while(G<=cap){
    let z=next(u,v,y);if(!isFinite(z.p))break;
    let g=z.p-1,k=h+z.w,hp=k-g/2;ck(hp>=0&&k<=amax,"height");
    up+=Phi[k]-Phi[h];down+=Phi[k]-Phi[hp];
    for(let j=1;j<z.w;j++){
     let t=v+j,e=t%2?-1:1,f=2*(h+j)+(e===1?1:-5);
     for(let p of factors(f))if(p>=y&&p<=2*y){add(marks,p,mod(e-u,p));union+=1/p;}
     s.quietTicks++;
    }
    if(X<R+60)path.push({u,v,w:z.w});
    u+=g;v+=z.w;G+=g;N++;if(z.p<=11)small+=g;h=hp;s.events++;
   }
   if(G>cap){s.censored++;continue}
   s.complete++;ck(h===v-u/2,"height identity");let diff=Phi[h]-Phi[3];ck(Math.abs(up-down-diff)<1e-8,"coarea");ck(union<=up+1e-8,"union vs up");s.coareaChecks++;
   const pre=probability(marks),predPre=[...marks.values()].some(q=>q.has(0));
   ck(pre<=union+1e-8,"union");if(X<R+60){
    let check=new Map();
    for(let st of path)for(let p of H)for(let e of [1,-1]){
     let delta=mod(e-st.u,p);while(delta%4!==0)delta+=p;
     let V=st.v+delta/2,w=mod((e===1?0:p+2)-V,2*p)||2*p;
     if(w<st.w)add(check,p,mod(e-st.u,p));s.exactCRTChecks++;
    }
    for(let p of H){let x=marks.get(p)||new Set(),z=check.get(p)||new Set();ck(x.size===z.size&&[...x].every(r=>z.has(r)),"exact quiet residue")}
   }
   for(let p of H)for(let e of [1,-1])add(marks,p,mod(e-u,p));
   let any=probability(marks),predAny=[...marks.values()].some(q=>q.has(0));ck(any+1e-10>=pre,"terminal law");
   let U=X,V=X/2+3,actAny=false,actPre=false;
   while(true){let z=next(U,V,2*y+1);if(!isFinite(z.p))break;if(z.p>=y){actAny=true;actPre=U!==u;break}U+=z.p-1;V+=z.w;ck(U<=u,"old prefix")}
   ck(actAny===predAny&&actPre===predPre,"actual band first clock");s.actualBandChecks++;if(actAny)s.actualAny++;if(actPre)s.actualPreempt++;
   s.sumGain+=G;s.sumEvents+=N;s.sumPreemptProb+=pre;s.sumAnyProb+=any;s.sumUnion+=union;s.sumUp+=up;s.sumDown+=down;s.sumTerminalPotential+=diff;s.sumSmallGain+=small;s.maxUp=Math.max(s.maxUp,up);s.maxG=Math.max(s.maxG,G);s.maxEvents=Math.max(s.maxEvents,N);
   if(pre>s.maxPreemptProb){s.maxPreemptProb=pre;s.example={X,G,N,pre,any,up,down,h,union}}
  }
  results.push(s);
 }
 return results;
}
console.log(JSON.stringify(audit(),null,2));
