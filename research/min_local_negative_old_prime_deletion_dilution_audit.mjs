// Old-prime deletion certificate: exact first-use record traffic and moment dilution.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,Pall=[3,5,7,11,13,17,19,23];
 function run(A,b,P,target=0){
  let a=A,n=3-A/2,h=3,first=null,records=3,history=[],d=0;
  while(true){let p=0,w=Infinity,side=0;
   for(let q of P)for(let e of [-1,1])if(mod(a-e,q)===0){let t=mod((e===-1?0:q+2)-n,2*q)||2*q;if(t<w||t===w&&q<p){p=q;w=t;side=e}}
   if(h+w>b){return {a,first,history,n:b-a/2,h,t:b+1-h};}
   let pre=h+w;if(p===target&&!first)first={a,b:pre,side,record:pre>=records};
   if(target===0)history.push({a,n,h,p,w,side});records=Math.max(records,pre);a-=p-1;n+=w;h=pre-(p-1)/2;
  }
 }
 let out={controls:0,fullRoots:0,oldRoots:0,activationChecks:0,certificateChecks:0,firstUseChecks:0,momentChecks:0,baseVirginPairChecks:0,rows:[]};
 for(let [b,p] of [[5,5],[5,11],[6,7],[6,13],[7,5],[8,11],[8,17]]){
  let P=Pall.filter(q=>q<=2*b+1),old=P.filter(q=>q!==p),L=4*old.reduce((a,c)=>a*c,1),M=L/6,L2=L*p,side=(2*b+1)%p===0?-1:1;
  ck(p*p>2*b+1&&((side===-1?2*b+1:2*b-5)%p===0),"hypotheses");
  let U=new Map(),first=new Map(),actual=new Map(),oldLift=new Map(),allFullCut=new Map(),certs=new Map();
  for(let j=0;j<M;j++){
   let A=6*j,r=run(A,b,old),a0=mod(r.a,L);U.set(a0,(U.get(a0)||0)+1);out.oldRoots++;
   if(mod(b-r.a/2,2)!==(side===-1?0:1))continue;
   let t=0;while(mod(r.a+t*L,p)!==mod(side,p))t++;ck(t<p,"unique activation lift");let a=mod(r.a+t*L,L2),root=A+t*L;
   oldLift.set(a,(oldLift.get(a)||0)+1);out.activationChecks++;
   let pass=true;
   function wait(x,n,e){return mod((e===-1?0:p+2)-n,2*p)||2*p}
   for(let s of r.history){for(let e of [-1,1])if(mod(s.a+t*L-e,p)===0){let w=wait(s.a+t*L,s.n-t*L/2,e);if(w<s.w||w===s.w&&p<s.p)pass=false}}
   // The old exit is at preheight b+1; only ticks through b-1
   // may disqualify the designated activation at b.
   for(let e of [-1,1])if(mod(r.a+t*L-e,p)===0){let w=wait(r.a+t*L,r.h-(r.a+t*L)/2,e);if(w<b-r.h)pass=false}
   if(pass){first.set(a,(first.get(a)||0)+1);certs.set(root,a)}out.certificateChecks++;
  }
  for(let j=0;j<M*p;j++){
   let A=6*j,r=run(A,b,P,p),f=r.first;
   if(f&&f.b===b&&f.record){let a=mod(f.a,L2);actual.set(a,(actual.get(a)||0)+1);ck(certs.get(A)===a,{b,p,A,f,cert:certs.get(A)});out.firstUseChecks++}
   else ck(!certs.has(A),{b,p,A,f,cert:certs.get(A)});
   allFullCut.set(mod(r.a,L2),(allFullCut.get(mod(r.a,L2))||0)+1);out.fullRoots++;
  }
  ck(first.size===actual.size,"source sets");
  for(let [a,m] of actual)ck(first.get(a)===m&&m<=oldLift.get(a),"exact mass");
  let moments=[];
  for(let r of [1,2,3]){
   let u=0,v=0,w=0;for(let [a,m] of U)if(mod(b-a/2,2)===(side===-1?0:1))u+=m**r;
   for(let m of oldLift.values())v+=m**r;for(let m of actual.values())w+=m**r;ck(u===v&&w<=v,"dilution moment");out.momentChecks++;moments.push({r,oldEligible:u/M,activation:v/(M*p),firstUse:w/(M*p),retention:w/v});
  }
  out.rows.push({b,p,side,M,full:M*p,moments,activatedSites:oldLift.size,firstUseSites:actual.size});out.controls++;
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
