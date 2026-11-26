// Rough known-support frontiers and prefix-cost CRT certificates.
function audit(){
 const ck=(c,m)=>{if(!c)throw Error(m)},mod=(a,b)=>(a%b+b)%b,lim=2200000,spf=new Uint32Array(lim);
 for(let p=2;p*p<lim;p++)if(!spf[p])for(let n=p*p;n<lim;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){n=Math.abs(n);ck(n>=1&&n<lim,"factor range");let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function event(u,v,z){let p=Infinity,w=Infinity,q=Infinity;for(let [n,e] of [[u-1,1],[u+1,-1]])for(let r of fs(n)){if(r>z)continue;q=Math.min(q,r);let t=mod((e===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w,q}}
 const controls=[
 {base:[3],z:17,D:40,t:7,s:0,R:1021020,L:6000},
 {base:[3],z:31,D:80,t:11,s:.2,R:10000,L:12000},
 {base:[3,5],z:127,D:240,t:17,s:.2,R:100000,L:12000},
 {base:[3],z:251,D:80,t:31,s:0,R:100000,L:12000},
 {base:[3,5],z:997,D:60,t:53,s:0,R:1000000,L:12000},
 {base:[3],z:997,D:20,t:53,s:.1,R:1000000,L:12000}
 ];
 const rows=[];
 for(let c of controls){
  const {base,z,D,t,s,R,L}=c,A=[];for(let p=3;p<=z;p+=2)if(!spf[p])A.push(p);
  const P=4*base.reduce((x,p)=>x*p,1),M0=2*D/P,H=A.filter(p=>!base.includes(p)),pmin=H[0],J=Math.ceil(Math.log(M0)/Math.log(pmin)),a=p=>p**(s-1),f=p=>-Math.log1p(-a(p));
  ck(M0>1&&t<=z,"parameters");
  const st={...c,P,M0,J,roots:0,classes:0,states:0,queries:0,frontiers:0,roughCertIncidences:0,roughCertScore:0,actualFrontiers:0,actualRough:0,actualRoughScore:0,actualCross:0,bigCross:0,bigCrossScore:0,bigCrossRoughScore:0,terminal:0,events:0,wallChecks:0,clockChecks:0,depthMassChecks:0,maxDepthMass:0,roughCoverage:0,allCoverage:0,largeBoundChecks:0,roughAtBigCross:0,crtSieveChecks:0,crtSieveUpper:0,roughAtDepth:{},frontiersAtDepth:{}};
  const certs=new Map();
  function knownTerm(r,G,K){for(let p of base)if(mod(r+G,p)===1||mod(r+G,p)===p-1)return false;for(let [p,b] of K)if(mod(b+G,p)===1||mod(b+G,p)===p-1)return false;return true}
  function cert(r,G,W,K,M,F,depth){
   let x=r,m=P;for(let [p,b] of K){let j=0;while(mod(x+m*j,p)!==b)j++;x+=m*j;m*=p;}
   ck(m===P*M&&m<2*D,"frontier modulus");const w=Math.exp(-F),tilt=w*M**(s-1);let n=0,nn=0;
   const sieve=A.filter(p=>p<t&&m%p!==0);
   for(let X=x+Math.ceil((R-x)/m)*m;X<R+L;X+=m){
    nn++;let u=X+G; if(sieve.every(p=>mod(u,p)!==1&&mod(u,p)!==p-1)){ck(A.filter(p=>p<t).every(p=>mod(u,p)!==1&&mod(u,p)!==p-1),"known factors");n++;}
   }
   let Q=1,dens=1;for(let p of sieve){if(Q*p>Math.max(1,L/m))break;Q*=p;dens*=1-2/p;}
   let bound=(nn+Q)*dens;ck(n<=bound+1e-8,"finite CRT sieve bound");st.crtSieveChecks++;st.crtSieveUpper+=bound*w;
   st.roughCertIncidences+=n;st.roughCertScore+=w*n;
   return {x,m,G,W,F,depth,tilt,w};
  }
  for(let r=0;r<P;r+=6){
   st.classes++;let arr=[],masses=new Map(),stack=[{G:0,W:0,j:1,i:0,neg:new Map(),K:new Map(),M:1,F:0,atStart:true}];
   while(stack.length){
    let {G,W,j,i,neg,K,M,F,atStart}=stack.pop();st.states++;
    if(M>=M0)continue;ck(G<D,"wall before threshold");
    while(G<D&&j<=2*z){
     if(atStart){atStart=false;if(knownTerm(r,G,K)){let x=cert(r,G,W,K,M,F,K.size);arr.push(x);st.frontiers++;st.frontiersAtDepth[K.size]=(st.frontiersAtDepth[K.size]||0)+1;masses.set(K.size,(masses.get(K.size)||0)+x.tilt);}}
     let n=r/2+3+W+j,h=3+W+j-G/2,e=n%2?-1:1,def=2*h+(e===1?1:-5);
     if(i===A.length){j++;i=0;continue}
     let p=A[i++];if(def%p)continue;let b=mod(e-G,p);
     if(base.includes(p)||K.has(p)){if((base.includes(p)?mod(r,p):K.get(p))===b){G+=p-1;W+=j;j=1;i=0;atStart=true;ck(G<P*M/2&&G<D,"relaxed wall");st.wallChecks++}continue}
     let S=neg.get(p)||new Set();if(S.has(b))continue;
     st.queries++;let kn=new Map(K);kn.set(p,b);
     stack.push({G:G+p-1,W:W+j,j:1,i:0,neg,K:kn,M:M*p,F,atStart:true});
     let ng=new Map(neg),T=new Set(S);T.add(b);ng.set(p,T);neg=ng;F+=f(p);
    }
   }
   let sum=0;for(let [k,m] of masses){ck(k<J&&m<=1+1e-9,"depth mass");st.depthMassChecks++;st.maxDepthMass=Math.max(st.maxDepthMass,m);sum+=m}ck(sum<=J+1e-8,"total mass");
   certs.set(r,arr);
  }
  for(let X=Math.ceil(R/6)*6;X<R+L;X+=6){
   let G=0,W=0,M=1,K=new Map(),neg=new Map(),F=0,stop=false,depths=new Set();
   while(!stop&&G<D){
    let u=X+G,v=X/2+3+W,{p,w,q}=event(u,v,z),front=knownTerm(mod(X,P),G,K),F0=F;
    if(front){ck(!depths.has(K.size),"unique frontier depth");depths.add(K.size);st.actualFrontiers++;
     const cs=certs.get(mod(X,P)),matches=cs.filter(l=>l.G===G&&l.W===W&&l.depth===K.size&&mod(X-l.x,l.m)===0&&Math.abs(l.F-F)<1e-9);ck(matches.length>0,"frontier coverage");st.allCoverage++;
     if(q>=t){st.actualRough++;st.actualRoughScore+=Math.exp(-F);st.roughCoverage++;st.roughAtDepth[K.size]=(st.roughAtDepth[K.size]||0)+1;}
    }
    if(!isFinite(p)){st.terminal++;break}
    ck(p<=7+6*G+4*q,"rough inequality");st.largeBoundChecks++;
    for(let j=1;j<=w&&!stop;j++){let n=v+j,h=n-u/2,e=n%2?-1:1,def=2*h+(e===1?1:-5);
     for(let r of fs(def)){if(r>z||r>p&&j===w)continue;let b=mod(e-G,r),yes=mod(X,r)===b;
      if(!base.includes(r)&&!K.has(r)){let S=neg.get(r)||new Set();if(!S.has(b)){if(yes){K.set(r,b);M*=r;if(M>=M0){st.actualCross++;stop=true;if(r>16*D+16){st.bigCross++;st.bigCrossScore+=Math.exp(-F0);ck(front&&q>D,"big crossing frontier");if(q>=t){st.roughAtBigCross++;st.bigCrossRoughScore+=Math.exp(-F0)}}}}else{S.add(b);neg.set(r,S);F+=f(r)}}}
      if(yes){ck(r===p&&j===w,"clock");st.clockChecks++;break}
     }
    }
    G+=p-1;W+=w;st.events++;if(!stop){ck(G<P*M/2&&G<D,"actual wall");st.wallChecks++}
   }
   st.roots++;
  }
  ck(st.actualRoughScore<=st.roughCertScore+1e-7&&st.roughCertScore<=st.crtSieveUpper+1e-7,"weighted rough cover");ck(st.bigCrossRoughScore<=st.actualRoughScore+1e-7,"large rough subset");
  rows.push(st);
 }
 return rows;
}
console.log(JSON.stringify(audit(),null,2));
