// Uncapped divisor multiplicity, endpoint bins and actual successor roughness.
function audit(N=40000){
 const lim=1600000,spf=new Int32Array(lim),pr=[];for(let i=2;i<lim;i++)if(!spf[i]){spf[i]=i;if(i>2)pr.push(i);if(i*i<lim)for(let j=i*i;j<lim;j+=i)if(!spf[j])spf[j]=i}
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b,gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return Math.abs(a)};
 function inv(a,b){if(b===1)return 0;let c=b,x=1,y=0;a=mod(a,b);while(c){let q=Math.floor(a/c);[a,c]=[c,a-q*c];[x,y]=[y,x-q*y]}ok(a===1,"inverse");return mod(x,b)}
 function factors(x){ok(x>0&&x<lim,"factor range");let a=[];while(x>1){let p=spf[x];a.push(p);while(x%p===0)x/=p}return a}
 function next(H,t){let z=null;for(let I=0;I<2;I++)for(let p of factors(H-1+2*I)){if(p*p>H+1)continue;let w=mod((I?p+2:0)-t,2*p)||2*p;if(!z||w<z.w||w===z.w&&p<z.p){let d=2*t-H,g=p-1,dp=d+2*w-g;z={H,p,w,I,e:1-2*I,d,dp,x:(dp-6*I)/2,g}}}return z}
 const st={roots:0,events:0,cap:0,blocks:0,selected:0,pairs:0,close:0,crossBand:0,crossBin:0,multiBandBlocks:0,bands:0,bins:0,multiEdgeBins:0,unique:0,crt:0,tuple:0,rangeBudget:0,globalBudget:0,weightedBudget:0,uncappedChecks:0,highEscapes:0,zeroShift:0,multipleFactors:0,largeDeficit:0,roughChecks:0,roughResidues:0,flatRuns:0,flatEvents:0,syntheticRough:0,syntheticGroups:0,syntheticCRT:0,syntheticRange:0,examples:[]};
 function band(p,T){let V=T;while(p>=2*V)V*=2;return V}
 function inspect(rows,T,nu,uncapped){
  let beta=nu===2?1.45:1.8,cap=Math.floor(T**beta),W0=Math.ceil(T**.95),R=Math.min(cap,8*T);
  let l=rows.map((z,i)=>({...z,i})).filter(z=>z.p>=T&&z.p<=R&&z.x>0);if(!l.length)return;
  st.blocks++;st.selected+=l.length;
  let G=rows.reduce((s,z)=>s+z.g,0),F=l.reduce((s,z)=>s+z.g,0),Vd=0,TV=[0];for(let z of rows){Vd+=Math.abs(z.dp-z.d);TV.push(Vd)}
  let A=Math.floor((T-1)/4),B=Math.floor((T-1)/20),Q=Math.floor(A/2)+3,Etotal=0,Dtotal=0,lowClose=0,high=0,bad=0,groups=new Map,usedBands=new Set(l.map(z=>band(z.p,T)));
  if(usedBands.size>1)st.multiBandBlocks++;
  for(let j=1;j<l.length;j++){let u=l[j-1],v=l[j],E=v.H-u.H-u.g,d=v.dp-u.dp,c=v.x-u.x;st.pairs++;Etotal+=E;Dtotal+=Math.abs(d);
   if(E>B||Math.abs(d)>A){bad+=v.g;continue}
   ok(u.p!==v.p&&Math.abs(c)<=Q,"close distinct");
   if(u.x>cap||v.x>cap)st.highEscapes++;if(u.x>=T*T||v.x>=T*T)st.largeDeficit++;if(c===0)st.zeroShift++;
   st.close++;lowClose+=v.g;
   let fa=factors(u.x).filter(p=>p>=T),fb=factors(v.x).filter(p=>p>=T);ok(fa.includes(u.p)&&fb.includes(v.p),"divisor");if(fa.length>1||fb.length>1)st.multipleFactors++;st.unique+=2;ok(4*v.w>=v.g,"automatic long");st.roughChecks++;
   let V=band(v.p,T),L=T*V,k=Math.floor(u.H/L);
   if(band(u.p,T)!==V)st.crossBand++;
   if(Math.floor(v.H/L)!==k)st.crossBin++;
   let key=[V,k].join(","),g=groups.get(key)||{V,k,ends:[],tuples:new Set};groups.set(key,g);
   let P=u.p*v.p,H0=u.e+u.p*mod((v.e-u.g-E-u.e)*inv(u.p,v.p),v.p);ok(P>=L&&mod(u.H-H0,P)===0&&u.H>=k*L&&u.H<(k+1)*L,"CRT");
   let q0=(H0+u.g+E-v.e)/v.p,z=(u.H-H0)/P;ok(Number.isInteger(q0)&&Number.isInteger(z),"cofactor line");for(let f of pr.filter(f=>8*f<T-1)){let a=mod(-q0*inv(u.p,f),f),b=mod(-(v.p*q0+2*v.e)*inv(P,f),f);ok(a!==b&&mod(z,f)!==a&&mod(z,f)!==b,"rough residues");st.roughResidues++}let tuple=[v.x,c,E,u.I,v.I,u.p,v.p].join(",");ok(!g.tuples.has(tuple),"unique tuple in bin");g.tuples.add(tuple);g.ends.push(v);st.crt++;st.tuple++;
   if(st.examples.length<3&&band(u.p,T)!==V)st.examples.push({T,nu,p:u.p,r:v.p,x:u.x,x2:v.x,H:u.H,H2:v.H,E,d,V,L,k});
  }
  let totals=new Map;
  for(let {V,k,ends} of groups.values()){let a=ends[0],b=ends.at(-1),min=Math.min(...ends.map(z=>z.x)),max=Math.max(...ends.map(z=>z.x)),W=Math.max(W0,max-min+1),v=TV[b.i+1]-TV[a.i+1];ok(2*(max-min)<=v+6&&2*W<=2*(W0+4)+v,"local range");
   let o=totals.get(V)||{last:-1,variation:0,W:0,n:0};ok(a.i>o.last,"same-band disjoint");o.last=b.i;o.variation+=v;o.W+=W;o.n++;totals.set(V,o);st.bins++;if(ends.length>1)st.multiEdgeBins++;
  }
  let weightedW=0,weightedN=0,sumV=0;
  for(let [V,o] of totals){ok(o.variation<=Vd&&2*o.W<=2*(W0+4)*o.n+Vd,"band range budget");ok(o.n<=Math.floor(rows.at(-1).H/(T*V))-Math.floor(rows[0].H/(T*V))+1,"bin count");weightedW+=V*o.W;weightedN+=V*o.n;sumV+=V;st.bands++;st.rangeBudget++}
  ok(sumV<=2*R&&2*weightedW<=2*(W0+4)*weightedN+sumV*Vd,"weighted range budget");st.weightedBudget++;
  ok(Etotal<=G-F&&Dtotal<=Vd&&F===l[0].g+lowClose+high+bad,"global partition");ok(bad*(A+1)*(B+1)<=R*((A+1)*(G-F)+(B+1)*Vd),"global relay");st.globalBudget++;if(uncapped)st.uncappedChecks++;
 }
 for(let M=5;M<=N;M+=2){let H=2*M-2,t=M+2,rows=[];st.roots++;for(let j=0;j<180;j++){let z=next(H,t);if(!z)break;rows.push(z);H+=z.g;t+=z.w}st.events+=rows.length;if(rows.length===180)st.cap++;
  for(let T of [11,17,31,61,101])inspect(rows,T,1,true);for(let i=0;i<rows.length;){let j=i;while(j<rows.length&&rows[j].dp===rows[j].d&&rows[j].d===rows[i].d)j++;if(j===i){i++;continue}let d=rows[i].d;if(d>6){let fs=new Set([3,...factors(d/2),...factors((d-6)/2)]),P=1;for(let f of fs)P*=f;let g=0;for(let k=i;k<j;k++){let a=rows[k];ok(fs.has(a.p)&&2*a.w===a.g,"flat support");let J=Math.ceil(a.H/(2*P))*2*P;ok(J>=a.H+a.g,"flat barrier");g+=a.g;st.flatEvents++}ok(g<2*P,"flat gain");st.flatRuns++}i=j}}
 // Independent CRT controls with a bin attached to the first horizon, not the second.
 for(let T of [11,31,101])for(let p of pr.filter(p=>p>=T&&p<4*T))for(let r of pr.filter(r=>r>=T&&r<4*T&&r!==p))for(let E of [0,2,4]){
   let V=band(r,T),L=T*V,P=p*r,x=1+p*mod((-1-(p-1)-E-1)*inv(p,r),r);
   ok(P>=L&&mod(x,p)===1&&mod(x+p-1+E,r)===r-1,"synthetic CRT");let k=Math.floor(x/L);ok(Math.floor((x+P)/L)>k,"one start per bin");st.syntheticCRT++;
 }
 // Arbitrary ordered endpoint lists; variation can be reused across bands only with geometric weight.
 for(let T of [11,31,101])for(let j=0;j<500;j++){let h=0,x=T*3,Vd=0,prev=2*x,groups=new Map;for(let i=0;i<100;i++){h+=2*(1+(i*31+j)%T);x=Math.max(T,x+(i*17+j)%13-6);let d=2*x+6*(i%2),diff=Math.abs(d-prev);Vd+=diff;prev=d;let V=T*2**((i+j)%4),k=Math.floor(h/(T*V)),key=[V,k].join(","),a=groups.get(key)||{V,min:x,max:x,first:Vd,last:Vd};a.min=Math.min(a.min,x);a.max=Math.max(a.max,x);a.last=Vd;groups.set(key,a)}
 let m=new Map;for(let a of groups.values()){ok(2*(a.max-a.min)<=a.last-a.first+6,"synthetic range");m.set(a.V,(m.get(a.V)||0)+a.last-a.first);st.syntheticGroups++}for(let v of m.values()){ok(v<=Vd,"synthetic band disjoint");st.syntheticRange++}
 }
 for(let p of [31,61,101])for(let r of [37,67,103])for(let q of [1,3,13,101])for(let f of [3,5,7]){let a=mod(-q*inv(p,f),f),b=mod(-(r*q+2)*inv(p*r,f),f);ok(a!==b,"independent roots");st.syntheticRough++}ok(st.close&&st.multiBandBlocks&&st.flatRuns&&st.syntheticCRT,"coverage");return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||40000)),null,2));
