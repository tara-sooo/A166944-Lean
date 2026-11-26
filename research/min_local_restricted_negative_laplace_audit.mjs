// Negative-query Laplace certificates and virtual-terminal cost obstruction.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(m)},mod=(a,b)=>(a%b+b)%b,lim=2200000,spf=new Uint32Array(lim);
 for(let p=2;p*p<lim;p++)if(!spf[p])for(let n=p*p;n<lim;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){n=Math.abs(n);ck(n>=1&&n<lim,"factor range "+n);let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(u,v,z){let p=Infinity,w=Infinity;for(let [n,e] of [[u-1,1],[u+1,-1]])for(let r of fs(n)){if(r>z)continue;let t=mod((e===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 const controls=[
 {base:[3],z:7,D:18,s:.5,R:420,len:420,tree:true},
 {base:[3,5],z:13,D:65,s:.4,R:60060,len:60060,tree:true},
 {base:[3],z:17,D:300,s:.3,R:1021020,len:1021020,tree:true},
 {base:[3],z:31,D:300,s:.4,R:10000,len:10000,tree:true},
 ...[10000,100000,1000000].map(R=>{let y=Math.sqrt(R);return {base:[3],z:Math.ceil(Math.sqrt(3*R+1)),D:Math.ceil(y**.9),s:2/Math.log(y),R,len:R===1000000?120000:R,tree:false}})
 ];
 let out=[];
 for(let c of controls){
  let {base,z,D,s,R,len,tree}=c,A=[];for(let p=3;p<=z;p+=2)if(!spf[p])A.push(p);
  let H=A.filter(p=>!base.includes(p)),P=4*base.reduce((t,p)=>t*p,1),M0=2*D/P,a=p=>p**(s-1),f=p=>-Math.log1p(-a(p));
  ck(M0>1&&s>=0&&s<1,"parameters");
  let st={...c,P,M0,roots:0,states:0,queries:0,leaves:0,multiLeaves:0,leafTilt:0,maxBaseTilt:0,certWeighted:0,covered:0,cross:0,terminal:0,exits:0,events:0,ticks:0,negQueries:0,virtualNeg:0,termChecks:0,clockChecks:0,wallChecks:0,score:0,crossScore:0,termScore:0,virtualScore:0,meanCost:0,meanCrossCost:0,meanTermCost:0,meanVirtualTermCost:0,terminalCostLowerMin:Infinity,terminalCostMin:Infinity,treeWeightChecks:0};
  let certs=new Map();
  if(tree)for(let r=0;r<P;r+=6){
   let leaves=[],mass=0,stack=[{G:0,W:0,j:1,i:0,neg:new Map(),known:new Map(),M:1,F:0}];
   while(stack.length){
    let {G,W,j,i,neg,known,M,F}=stack.pop();st.states++;
    if(M>=M0){
     let x=r,m=P;for(let [p,v] of known){let k=0;while(mod(x+k*m,p)!==v)k++;x+=k*m;m*=p}
     ck(m===P*M&&m<2*D*z,"certificate modulus");let n=Math.max(0,Math.ceil((R+len-x)/m)-Math.ceil((R-x)/m));
     let w=Math.exp(-F),tilt=w*M**(s-1);mass+=tilt;st.certWeighted+=n*w;st.leaves++;if(known.size>=2)st.multiLeaves++;leaves.push({x,m,F});continue;
    }
    ck(G<D,"wall");
    while(G<D&&j<=2*z){
     let t=r/2+3+W+j,h=3+W+j-G/2,e=t%2?-1:1,def=2*h+(e===1?1:-5);
     if(i===A.length){i=0;j++;continue}
     let p=A[i++];if(def%p)continue;let b=mod(e-G,p);
     if(base.includes(p)||known.has(p)){if((base.includes(p)?mod(r,p):known.get(p))===b){G+=p-1;W+=j;j=1;i=0;ck(G<P*M/2&&G<D,"relaxed wall");st.wallChecks++}continue}
     let S=neg.get(p)||new Set();if(S.has(b))continue;
     st.queries++;ck(Math.abs(Math.exp(-f(p))+a(p)-1)<1e-12,"mass conservation");let kn=new Map(known);kn.set(p,b);
     stack.push({G:G+p-1,W:W+j,j:1,i:0,neg,known:kn,M:M*p,F});
     let ng=new Map(neg),T=new Set(S);T.add(b);ng.set(p,T);neg=ng;F+=f(p);
    }
   }
   ck(mass<=1+1e-10,"tilted mass");st.treeWeightChecks++;st.leafTilt+=mass;st.maxBaseTilt=Math.max(st.maxBaseTilt,mass);certs.set(r,leaves)
  }
  for(let X=Math.ceil(R/6)*6;X<R+len;X+=6){
   let G=0,W=0,M=1,F=0,known=new Set(),neg=new Map(),hit=false,terminal=false;
   while(G<D&&!hit){
    let u=X+G,v=X/2+3+W,{p,w}=next(u,v,z);
    if(!isFinite(p)){terminal=true;break}
    for(let j=1;j<=w&&!hit;j++){
     st.ticks++;let t=v+j,h=t-u/2,e=t%2?-1:1,def=2*h+(e===1?1:-5);
     for(let q of fs(def)){if(q>z||q>p&&j===w)continue;let b=mod(e-G,q),yes=mod(X,q)===b;
      if(!base.includes(q)&&!known.has(q)){
       let S=neg.get(q)||new Set();if(!S.has(b)){
        if(yes){known.add(q);M*=q;if(M>=M0)hit=true;}
        else{F+=f(q);st.negQueries++;S.add(b);neg.set(q,S)}
       }
      }
      if(yes){ck(j===w&&q===p,"clock");st.clockChecks++;break}
     }
    }
    G+=p-1;W+=w;st.events++;
    if(!hit){ck(G<P*M/2&&G<D,"actual wall");st.wallChecks++}
   }
   st.roots++;st.score+=Math.exp(-F);st.meanCost+=F;
   if(hit){st.cross++;st.crossScore+=Math.exp(-F);st.virtualScore+=Math.exp(-F);st.meanCrossCost+=F;
    if(tree){let cs=certs.get(mod(X,P));ck(cs.some(l=>mod(X-l.x,l.m)===0&&Math.abs(F-l.F)<1e-9),"weighted coverage");st.covered++}
   }else{
    ck(terminal,"terminal partition");st.terminal++;st.termScore+=Math.exp(-F);st.meanTermCost+=F;
    let full=F,lower=0;
    for(let p of H){if(known.has(p))continue;lower+=2*f(p);let S=neg.get(p)||new Set();for(let e of [1,-1]){let b=mod(e-G,p);ck(mod(X,p)!==b,"terminal negative");if(!S.has(b)){full+=f(p);st.virtualNeg++;S.add(b)}}}
    ck(full+1e-8>=lower,"virtual terminal lower");st.termChecks++;st.meanVirtualTermCost+=full;st.terminalCostLowerMin=Math.min(st.terminalCostLowerMin,lower);st.terminalCostMin=Math.min(st.terminalCostMin,full);st.virtualScore+=Math.exp(-full);
   }
   if(G>=D){st.exits++;ck(hit,"exit");}
  }
  st.bound=len/6*(1+2*D*z/len)/M0**s;
  if(tree){ck(st.crossScore<=st.certWeighted+1e-7&&st.certWeighted<=st.bound+1e-7,"weighted interval bound");ck(st.score-st.bound<=st.terminal+1e-7,"terminal lower bound")}
  // (Non-tree controls merely measure physical vs virtual cost; mathematical bound not independently enumerated.)
  for(let k of ["score","crossScore","termScore","virtualScore","meanCost"])st[k]/=st.roots;
  if(st.cross)st.meanCrossCost/=st.cross;
  if(st.terminal){st.meanTermCost/=st.terminal;st.meanVirtualTermCost/=st.terminal}else{st.terminalCostMin=null;st.terminalCostLowerMin=null}
  st.bound/=st.roots;out.push(st)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
