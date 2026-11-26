// Dense-band extension: full-period fresh-label and first-repeat checks, local pair controls.
function audit(){
 const mod=(a,b)=>(a%b+b)%b,ck=(c,m)=>{if(!c)throw Error(m)};
 const prime=n=>{if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true};
 function event(x,v,A){let p=Infinity,w=Infinity,e=0;for(let r of A){let z=mod(x,r),s=z===1?1:z===r-1?-1:0;if(!s)continue;let t=mod((s===1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e}}
 function lowCap(A){let Q=2*A.reduce((s,p)=>s*p,1),F=new Int32Array(Q+2),L=0;for(let x=Q-2;x>=0;x-=2){for(let p of A)if(x%p===1||x%p===p-1){ck(x+p-1<=Q,"wall");F[x]=Math.max(F[x],p-1+F[x+p-1])}L=Math.max(L,F[x])}return {Q,L,P:2*Q}}
 function old(X,A,L){let x=X,v=X/2+3,a=[];while(true){let z=event(x,v,A);if(!isFinite(z.p))return {x,v,a,G:x-X};a.push({x,v,...z});x+=z.p-1;v+=z.w;ck(x-X<=L,"old cap")}}
 function walk(X,A,H,L,D){let x=X,v=X/2+3,hs=[],low=0,seen=new Set(),firstRepeat=null,steps=0;let o=old(X,A,L);for(;;){if(x-X>=D)break;let z=event(x,v,A.concat(H));if(!isFinite(z.p))break;
  if(H.includes(z.p)){if(!hs.length)ck(x===o.x&&v===o.v,"no preemption");let e=low;ck(e<=L,"low relay");let k=hs.findIndex(q=>q.p===z.p);
   if(k>=0&&!firstRepeat){ck(hs.length>=2,"adjacent repeat");let m=hs.length,cs=hs.slice(k).reduce((s,q)=>s+q.p-1,0)+hs.slice(k+1).reduce((s,q)=>s+q.E,0)+e;ck(cs===x-hs[k].x,"repeat displacement");ck(mod(cs-z.e+hs[k].e,z.p)===0,"repeat relation");
    let a=hs[m-1],other=hs.slice(k+1,m-1).reduce((s,q)=>s+q.p,0),sumE=hs.slice(k+1).reduce((s,q)=>s+q.E,0)+e;
    let mult=(cs-z.e+hs[k].e)/z.p;ck(a.p===(mult-1)*z.p+(m-k)-sumE+z.e-hs[k].e-other,"determined last prime");
    firstRepeat={j:m+1,k,p:z.p,last:a.p,mult};}
   hs.push({x,v,p:z.p,e:z.e,E:e,w:z.w});seen.add(z.p);low=0;
  }else{low+=z.p-1;ck(low<=L,"low cap")}
  x+=z.p-1;v+=z.w;steps++;ck(steps<200000,"finite");
 }return {G:x-X,hs,firstRepeat,steps,old:o,exit:x-X>=D}}
 let periods=[],local=[];
 for(let [A,H] of [[[3],[31,37,41]],[[3],[43,47,53]],[[3,5],[103,107]],[[3],[31,37,41,43]]]){
  let {Q,L,P}=lowCap(A),y=Math.min(...H);ck(y>6*L+5&&H.every(p=>p<=2*y),"band");let F=P*H.reduce((a,b)=>a*b,1),N=F/6,base=F,D=y*y,M=Math.floor(L/2)+1,S=H.reduce((a,b)=>a+1/b,0),s={A,H,y,L,P,N,roots:0,events:0,first:0,second:0,third:0,repeat:0,repeatChecks:0,firstRepeatHist:{},hist:{},sumG:0,sumTruncatedG:0,nonRepeatHigh:0,maxHigh:0,exactFirstProbability:1-H.reduce((a,b)=>a*(1-2/b),1),repeatBound:0,repeatExample:null};
  for(let X=base;X<base+F;X+=6){
   let a=walk(X,A,H,L,D);s.roots++;s.events+=a.steps;s.sumG+=a.G;s.sumTruncatedG+=Math.min(a.G,D);let h=a.hs.length;s.maxHigh=Math.max(s.maxHigh,h);s.hist[h]=(s.hist[h]||0)+1;
   if(h)s.first++;if(h>=2)s.second++;if(h>=3)s.third++;
   if(a.firstRepeat){s.repeat++;s.repeatChecks++;let j=a.firstRepeat.j;s.firstRepeatHist[j]=(s.firstRepeatHist[j]||0)+1;if(!s.repeatExample)s.repeatExample={X,...a.firstRepeat,hs:a.hs.slice(0,j)}}
   else s.nonRepeatHigh+=h;
  }
  ck(s.roots===N&&Math.abs(s.first-N*s.exactFirstProbability)<1e-5,"exact first count");
  let t=2*M*S,repeat=0;
  for(let j=3;j<=H.length+1;j++)repeat+=2**j*(j-2)*(4*j+3)*M**(j-1)*S**(j-2)/y;
  s.repeatBound=repeat;ck(s.repeat<=N*repeat+1e-8,"repeat probability");
  for(let j=1;j<=H.length;j++){
   let atLeast=Object.entries(s.hist).reduce((n,[k,v])=>n+(+k>=j?v:0),0);
   ck(atLeast<=N*(2*S*t**(j-1)+repeat)+1e-8,"tail bound");
  }
  s.meanTruncatedG=s.sumTruncatedG/N;s.meanG=s.sumG/N;periods.push(s);
 }
 for(let [A,y,R] of [[[3],31,10000],[[3,5],103,100000],[[3,5,7],293,1000000],[[3,5,7,11],907,1000000]]){
  let {Q,L,P}=lowCap(A),H=[];for(let p=y;p<=2*y;p++)if(prime(p))H.push(p);ck(y>6*L+5,"local threshold");let D=R,s={A,y,R,D,L,bandCount:H.length,roots:0,events:0,first:0,second:0,third:0,repeat:0,thirdReturn:0,firstPairs:0,firstOffsets:0,sumTruncatedG:0,maxHigh:0,pairControls:0,repeatControls:0,firstExample:null,repeatExample:null};
  let pair=new Set(),fset=new Set();const fst=new Map();
  for(let X=Math.ceil(R/6)*6;X<2*R;X+=6){
   let a=walk(X,A,H,L,D);s.roots++;s.events+=a.steps;s.sumTruncatedG+=Math.min(a.G,D);let h=a.hs.length;s.maxHigh=Math.max(s.maxHigh,h);
   if(h){s.first++;let f=a.hs[0];fset.add(f.x);fst.set(f.x,(fst.get(f.x)||0)+1);ck(f.x-X<=L&&mod(f.x-f.e,f.p)===0,"first root range")}
   if(h>=2){s.second++;let [p,r]=a.hs;ck(p.p!==r.p&&r.E<=L&&r.x===p.x+p.p-1+r.E&&mod(r.x-r.e,r.p)===0,"pair CRT");pair.add(p.x+":"+p.p+":"+r.p+":"+r.E+":"+p.e+":"+r.e);s.pairControls++}
   if(h>=3){s.third++;if(a.hs[0].p===a.hs[2].p){s.thirdReturn++;let [p,r,t]=a.hs;let j=(t.x-p.x-t.e+p.e)/p.p;ck(Number.isInteger(j),"return modulus");ck(r.p===(j-1)*p.p+2-r.E-t.E+t.e-p.e,"return determined");s.repeatControls++}}
   if(a.firstRepeat){s.repeat++;if(!s.repeatExample)s.repeatExample={X,...a.firstRepeat,hs:a.hs.slice(0,a.firstRepeat.j)}}
   if(h>=2&&!s.firstExample)s.firstExample={X,hs:a.hs.slice(0,2)}
  }
  let M=Math.floor(L/2)+1,cap=Math.floor(L/6)+1,span=R+L+1;
  ck(s.first<=cap*H.reduce((n,p)=>n+2*(Math.floor(span/p)+1),0),"local first supply");
  ck(s.second<=cap*4*M*H.reduce((n,p)=>n+H.reduce((m,r)=>m+(p!==r?Math.floor(span/(p*r))+1:0),0),0),"local pair supply");
  s.firstPairs=pair.size;s.firstOffsets=fset.size;s.maxFirstMass=Math.max(0,...fst.values());s.meanTruncatedG=s.sumTruncatedG/s.roots;local.push(s);
 }
 return {periods,local}
}
console.log(JSON.stringify(audit(),null,2));
