// Short-relay CRT pair capacity and bounded-low-support time audit.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=400000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let n=p*p;n<=N+2;n+=p)if(!spf[n])spf[n]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;if(p>2)a.push(p);while(n%p===0)n/=p}return a}
 function q(a){return Math.min(...fs(a-1),...fs(a+1))}
 function next(a,v,A){let p=Infinity,w=Infinity,e=0;for(let [d,s] of [[a+1,-1],[a-1,1]])for(let r of fs(d)){if(A&&!A.has(r))continue;let t=mod((s===-1?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t;e=s}}return {p,w,e}}
 function run(A,v,lo,allowed=null){let arr=[];while(A>=lo&&A>=2&&v< -1){let x=next(A,v,allowed);if(!isFinite(x.p)||v+x.w> -1)break;arr.push({a:A,v,...x,q:q(A),b:A-x.p+1});A-=x.p-1;v+=x.w;}return arr}
 let out={roots:0,events:0,blocks:0,pairs:0,short:0,long:0,repeats:0,shortDistinct:0,crtChecks:0,capacityChecks:0,macroChecks:0,wallChecks:0,restrictedRoots:0,restrictedEvents:0,restrictedBlocks:0,restrictedPairs:0,roughMacroChecks:0,roughMacroPairs:0,rows:[]};
 function check(arr,lo,hi,T,B,lowSet=null,z=7){
  if(!arr.length)return;let D=hi-lo+1,Q=lowSet?2*[...lowSet].reduce((a,p)=>a*p,1):0;
  let high=arr.filter(x=>x.p>=T),L=new Set(high.map(x=>x.p)),shortW=0,longW=0,lowW=0,lowG=0,relayG=0,lastW=high.at(-1)?.w||0,groups=new Map(),maxQ=Math.sqrt(hi+1),pairs=0;
  for(let x of arr)if(x.p<T){lowW+=x.w;lowG+=x.p-1;if(lowSet)ck(lowSet.has(x.p),"low support")}
  for(let i=0;i+1<high.length;i++){
   let x=high[i],y=high[i+1],E=x.b-y.a;ck(E>=0&&E%2===0,"relay");
   relayG+=E;pairs++;out.pairs++;
   if(x.p===y.p){ck(E>=x.p-1,"same label requires relay");out.repeats++}
   if(E>B){longW+=x.w;out.long++;continue}
   out.short++;ck(x.p!==y.p,"distinct short");out.shortDistinct++;
   ck(mod(x.a-x.e,x.p)===0&&mod(x.a-(x.p-1+E+y.e),y.p)===0,"pair CRT");out.crtChecks++;
   // Group by ordered labels, exact relay gain and both signs.
   let key=[x.p,y.p,E,x.e,y.e].join(","),g=groups.get(key)||{x,y,E,n:0,W:0};
   g.n++;g.W+=x.w;groups.set(key,g);shortW+=x.w;
   if(x.q>z&&y.q>z){let a=x.a,p=x.p,m=(a-x.e)/p,e=x.e,forms=[m,p*m+2*e,p*(m-1)+e-E,p*(m-1)+e-E+2];ck(forms.every(n=>fs(n).every(l=>l>z)),"macro forms");out.roughMacroChecks++;out.roughMacroPairs++}
  }
  let exactBound=0;
  for(let g of groups.values()){
   let {x,y,n,W}=g,cap=Math.floor((D-1)/(2*x.p*y.p))+1;
   ck(n<=cap,"CRT spacing");let U=2*Math.min(x.p,maxQ)*cap;
   // Non-twin sources only: if a twin source occurs, before zero it cannot fire
   // along a canonical run, but arbitrary-phase controls may have one.
   ck(W<=U+1e-9,{W,U,x,y,n});exactBound+=U;out.capacityChecks++;
  }
  let M=Math.floor(B/2)+1,cap=4*M*L.size*Math.max(0,L.size-1)*(D/T+2*maxQ);
  ck(shortW<=exactBound+1e-9&&exactBound<=cap+1e-7,"short capacity");
  ck(longW<=2*maxQ*relayG/(B+1)+1e-7,"long capacity");
  ck(arr.reduce((s,x)=>s+x.w,0)===lowW+shortW+longW+lastW,"decomposition");
  if(lowSet){
   ck(lowG<=Q*(high.length+1),"wall low gain");ck(lowW<=3*Q*(high.length+1),"wall low time");ck(relayG<=lowG,"relay sum");out.wallChecks++;
   if(B>=Q)ck(longW===0,"bounded relays");
   out.restrictedBlocks++;out.restrictedPairs+=pairs;
  }
  out.blocks++;out.macroChecks++;
  return {high:high.length,labels:L.size,shortW,longW,lowW,lastW,relayG,exactBound,cap,wait:arr.reduce((s,x)=>s+x.w,0)};
 }
 for(let [R,T,B] of [[10000,17,10],[30000,31,14],[100000,53,24],[180000,101,48]]){
  let row={R,T,B,roots:0,events:0,blocks:0,high:0,shortW:0,longW:0,lowW:0,lastW:0,relayG:0};
  for(let A=Math.ceil(R/6)*6;A<2*R;A+=198){
   let arr=run(A,-A/2+3,R);out.roots++;row.roots++;row.events+=arr.length;out.events+=arr.length;
   // Trim any actual twin source, preserving contiguous blocks.
   let b=[];for(let x of arr){if(x.q>Math.sqrt(x.a+1)){if(b.length){let t=check(b,R,2*R-1,T,B);for(let k of ["high","shortW","longW","lowW","lastW","relayG"])row[k]+=t[k];row.blocks++;b=[]}}else b.push(x)}
   if(b.length){let t=check(b,R,2*R-1,T,B);for(let k of ["high","shortW","longW","lowW","lastW","relayG"])row[k]+=t[k];row.blocks++}
  }out.rows.push(row)
 }
 // Artificial finite-support restrictions, but all selected clocks checked
 // against the restriction; q bound uses the actual least eligible restricted
 // prime, so only keep blocks where unrestricted q equals restricted q and
 // every step agrees with the unrestricted winner.
 for(let [R,T,A0,hs] of [[10000,17,[3,5],[17,19,23,29,31]],[30000,31,[3,5,7],[31,37,41,43,47,53,59,61]],[100000,101,[3,5],[101,103,107,109,113,127,131,137,139,149,151]]]){
  let lowSet=new Set(A0),allowed=new Set([...A0,...hs]),Q=2*A0.reduce((a,p)=>a*p,1),B=Math.min(Q,T-2);if(B%2)B--;
  let row={R,T,Q,B,restricted:true,roots:0,events:0,blocks:0,high:0,shortW:0,longW:0,lowW:0,lastW:0,relayG:0};
  for(let A=Math.ceil(R/6)*6;A<2*R;A+=6){
   let arr=run(A,-A/2+3,R,allowed);out.restrictedRoots++;row.roots++;out.restrictedEvents+=arr.length;row.events+=arr.length;
   let b=[];function flush(){if(!b.length)return;let t=check(b,R,2*R-1,T,B,lowSet);for(let k of ["high","shortW","longW","lowW","lastW","relayG"])row[k]+=t[k];row.blocks++;b=[];}
   for(let x of arr){let n=next(x.a,x.v,null);if(n.p===x.p&&n.w===x.w&&x.q<=Math.sqrt(x.a+1))b.push(x);else flush()}flush()
  }out.rows.push(row)
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
