// Adaptive negative-drift discount and projected boundary support diagnostic.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),P=focus?30:6,kap=2,alpha=1/8,kap2=1.5,eps=.25,cs=4,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(b,s)=>{if(!b)throw Error(X+" "+s)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,events=0,hit=0,G=0,oldF=0,oldCell=0,newF=0,newCell=0,proj=0,removed=0,removedProj=0,credit=0,creditProj=0,initial=0,firstBad=0,firstBadException=0,newTarget=0,ex=0,checks=0,cellChecks=0,negAdm=0,weak=0,weakGain=0,roughShort=0,roughLong=0,small=0,keys=new Map(),roughKeys=new Map(),bound=0,fullBound=0,fullCell=0,fullProj=0,fullGain=0;
 function add(m,k,v){m.set(k,(m.get(k)||0)+v)}
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],st=[[-1,6]],ms=[],I=0,gm=0,prev=-1,l=0;
  while(C-C0<T){
   let p=0,v=Infinity,r=Infinity;
   for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;
   let J=C+p-1,g=p-1,w=v-t,dp=2*t-C,d=2*v-J,delta=d-dp,D=Math.max(0,-delta),n=Math.ceil(J/P)-Math.ceil(C/P),f=P*n,bad=p>=kap*P&&r<alpha*g,i=es.length,E=Math.max(0,delta-3*g);
   ok(dp>=0&&d>=0&&w<=2*r&&r<=p&&E<=4&&(!n||P%p!==0),"event");
   let gam=D?(bad?f/D:Math.min(1,f/D)):0;
   ok(gam<=cs+1e-9&&(!bad||D>0),"gamma");
   let fnew=f-gam*D,fp=bad?0:Math.max(0,f-Math.max(0,g-4*r)),lc=n?l:0;
   ok(fnew>=-1e-8&&fnew<=fp+1e-8&&fp<=f+1e-8&&(!n||lc<=P),"discount");
   if(n){l=0;prev=i}else l+=g;
   let e={C,J,p,r,g,w,dp,d,delta,D,n,f,bad,gam,fnew,fp,lc,E};es.push(e);events++;
   if(delta>0)st.push([i,delta]);else if(D){let left=D;gm=Math.max(gm,gam);while(left){let a=st.at(-1),len=Math.min(left,a[1]);left-=len;a[1]-=len;if(!a[1])st.pop();if(a[0]<0)I+=gam*len;else if(gam)ms.push({i:a[0],j:i,c:gam*len});}}
   C=J;t=v;
  }
  let gain=C-C0,next=new Int32Array(es.length),k=-1;for(let i=es.length-1;i>=0;i--){if(es[i].n)k=i;next[i]=k}
  let F0=0,F1=0,FC0=0,FC1=0,FP=0,raw=0,del=0,rt=0,ee=0,src=new Map(),snk=new Map(),cell=new Map(),all=0,tagWeak=0,tagWeakGain=0;
  for(let e of es){all+=e.f;F1+=e.fnew;if(!e.bad&&e.n){F0+=e.f;FC0+=e.f+e.lc/4;FC1+=e.fnew+e.lc/4;FP+=e.fp+e.lc/4;
   if(e.D){negAdm++;credit+=e.f-e.fnew;creditProj+=e.f-e.fp}
   let v=e.fp+e.lc/4;
   if(e.p>=kap2*P&&e.r<=eps*e.g){weak++;tagWeak+=v;tagWeakGain+=e.g;ok(v<=1.25*P+4*eps*e.g+1e-7,"weak long gain bound")}
   else{for(let K=P*Math.ceil(e.C/P);K<e.J;K+=P){let key=[K,e.C,e.p].join("|");add(keys,key,v/e.n);if(e.r>=e.g/Math.log(2+e.p)){add(roughKeys,key,v/e.n);if(e.p<kap2*P)roughShort++;else roughLong++;}else small++;}}
  }}
  for(let m of ms){raw+=m.c;let h=next[m.i];ok(h>=m.i&&h<=m.j,"first crossing");if(es[h].bad){del+=m.c;let a=es[m.i],b=es[m.j];if(h!==m.j||b.p<3*a.p||b.C-a.J>b.p/3)firstBadException+=m.c;continue}rt+=m.c;add(src,m.i,m.c);add(snk,m.j,m.c)}
  for(let [i,c] of src){let e=es[i],z=Math.max(0,c/gm-3*e.g);ok(z<=e.E+1e-7&&!snk.has(i)&&c<=gm*Math.max(0,e.delta)+1e-7,"source");ee+=z;add(cell,next[i],z);checks++}
  let gs=[...src.keys()].reduce((s,i)=>s+es[i].g,0),gt=[...snk.keys()].reduce((s,i)=>s+es[i].g,0);
  for(let [j,c] of snk)ok(c<=gm*es[j].D+1e-7,"sink");
  for(let [i,z] of cell){let e=es[i];ok(!e.bad&&z<=e.lc+8+1e-7,"cell unit excess");cellChecks++}
  ok(eq(F1+raw+I,all)&&eq(F0+F1-F1,F0)&&gs+gt<=gain&&rt<=gm*(3*gain+ee)/4+1e-7,"exact credit ledger");
  let lower=(1-3*gm/4)*gain-P-I-del;
  ok(F1+gm*ee/4>=lower-1e-7&&FP>=FC1-1e-7&&FC1<=FC0+1e-7,"weighted sufficient envelope");
  ok(tagWeak<=4*eps*tagWeakGain+1.25*P*es.filter(e=>e.n&&!e.bad&&e.p>=kap2*P&&e.r<=eps*e.g).length+1e-7,"weak total");
  removed+=tagWeak;weakGain+=tagWeakGain;bound+=lower;G+=gain;oldF+=F0;oldCell+=FC0;newF+=F1;newCell+=FC1;proj+=FP;initial+=I;firstBad+=del;newTarget+=raw;ex+=ee;
  if(gain>=T){hit++;fullGain+=gain;fullBound+=lower;fullCell+=FC1;fullProj+=FP}
 }
 let remSum=[...keys.values()].reduce((a,b)=>a+b,0),roughSum=[...roughKeys.values()].reduce((a,b)=>a+b,0),paid=0,roughPaid=0;
 for(let [k,v] of keys)if(v<=2*P)paid+=v;
 for(let [k,v] of roughKeys)if(v<=2*P)roughPaid+=v;
 ok(eq(remSum+removed,proj)&&roughPaid<=paid+1e-7&&newCell<=oldCell+1e-7,"global grouping");
 let rd=x=>+x.toFixed(6);return {X,focus,B,T,P,N,events,hit,G,oldF,oldCell:rd(oldCell),newF:rd(newF),newCell:rd(newCell),proj:rd(proj),credit:rd(credit),creditProj:rd(creditProj),removed:rd(removed),weak,weakGain,remainingProj:rd(remSum),roughSum:rd(roughSum),keys:keys.size,roughKeys:roughKeys.size,roughShort,roughLong,small,paid:rd(paid),roughPaid:rd(roughPaid),initial:rd(initial),firstBad:rd(firstBad),firstBadException:rd(firstBadException),newTarget:rd(newTarget),ex:rd(ex),checks,cellChecks,negAdm,bound:rd(bound),fullGain,fullBound:rd(fullBound),fullCell:rd(fullCell),fullProj:rd(fullProj)}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
