// Weighted boundary flux certificate: finite diagnostic of target-source excess and 3-run packing.
function audit(X,focus=false){
const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),P=focus?30:6,kap=2,alpha=1/8,lim=7*X+B+20,S=new Int32Array(lim);
const ok=(x,m)=>{if(!x)throw Error(X+" "+m)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
let N=0,events=0,hit=0,G=0,F=0,Fs=0,Fr=0,R=0,discard=0,initial=0,Ex=0,Es=0,Er=0,rawEx=0,positiveEx=0,sourceChecks=0,cellChecks=0,paired=0,unpaired=0,p3Consecutive=0,p3Ex=0,maxCell=0,maxEffectiveCell=0,weightedL=0,weightedR=0,refinedR=0,nonvacuous=0,fullL=0,fullR=0,fullRefined=0,fullGain=0,firstBadEarlier=0,firstBadNotDisparate=0,capChecks=0,liveR=0,nonzero=0,synthetic=0;
for(let M=X;M<2*X;M++)if(S[M]===M){
 N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],st=[[-1,6]],matches=[],ig=0,gm=0;
 while(C-C0<T){
  let p=0,v=Infinity,r=Infinity,sg=0;
  for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j;sg=s}}
  if(!p||v>cut)break;
  let J=C+p-1,g=p-1,w=v-t,dp=2*t-C,d=2*v-J,delta=d-dp,n=Math.ceil(J/P)-Math.ceil(C/P),cost=P*n,bad=p>=kap*P&&r<alpha*g,i=es.length,E=Math.max(0,delta-3*g);
  ok(dp>=0&&d>=0&&w<=2*r&&w<=2*p&&w<=3*g&&E<=4&&(!n||P%p!==0),"event");
  if(p===3&&i&&es[i-1].p===3){p3Consecutive++;ok(es[i-1].sg===1&&sg===-1&&w===1&&E===0,"consecutive 3");}
  if(E&&p===3)p3Ex++;
  rawEx+=E;
  es.push({C,J,p,g,w,d,dp,delta,n,cost,bad,sg,E});
  events++;if(delta>0)st.push([i,delta]);else if(delta<0){let left=-delta,gamma=bad?cost/left:0;gm=Math.max(gm,gamma);
    while(left){let a=st.at(-1),l=Math.min(left,a[1]);left-=l;a[1]-=l;if(!a[1])st.pop();if(a[0]<0)ig+=gamma*l;else if(gamma)matches.push({i:a[0],j:i,c:gamma*l});}
  }C=J;t=v;
 }
 const gain=C-C0,gg=es.reduce((z,e)=>z+e.cost,0),fs=es.reduce((z,e)=>z+(!e.bad&&e.p<kap*P?e.cost:0),0),fr=es.reduce((z,e)=>z+(!e.bad&&e.p>=kap*P?e.cost:0),0),f=fs+fr;
 const next=new Int32Array(es.length);let k=-1;for(let i=es.length-1;i>=0;i--){if(es[i].n)k=i;next[i]=k}
 let rr=0,dd=0,src=new Map(),snk=new Map(),cell=new Map(),ex=0,exs=0,exr=0,cs=0,cr=0;
 const add=(m,k,v)=>m.set(k,(m.get(k)||0)+v);
 for(let m of matches){rr+=m.c;let h=next[m.i],a=es[m.i],b=es[m.j];ok(h>=m.i&&h<=m.j,"next crossing");
  if(es[h].bad){dd+=m.c;if(h<m.j)firstBadEarlier++;if(!(h===m.j&&b.p>=3*a.p&&b.C-a.J<=b.p/3))firstBadNotDisparate+=m.c;continue;}
  add(src,m.i,m.c);add(snk,m.j,m.c);
 }
 for(let [i,c] of src){let a=es[i],h=next[i];ok(gm>0&&c<=gm*Math.max(0,a.delta)+1e-7&&!snk.has(i),"source capacity");
  let z=Math.max(0,c/gm-3*a.g);ok(z<=a.E+1e-7,"source excess");sourceChecks++;if(z>1e-9)positiveEx++;
  ex+=z;add(cell,h,z);
 }
 for(let [j,c] of snk)ok(c<=gm*es[j].g+1e-7,"sink capacity");
 let prev=-1;
 for(let h=0;h<es.length;h++)if(es[h].n){let f=es[h],l=0,ee=0;for(let i=prev+1;i<h;i++){let a=es[i];l+=a.g;ee+=a.E;if(a.p===3&&a.E){if(i===prev+1)unpaired++;else{ok(es[i-1].p!==3,"pair predecessor");paired++;}}}
  ok(l<=P&&ee<=4*l/3+4+1e-7,"cell excess packing");capChecks++;
  let z=cell.get(h)||0;if(z>1e-9)nonzero++;ok(z<=ee+f.E+1e-7&&z<=4*P/3+8+1e-7,"effective cell excess");
  if(!f.bad){cellChecks++;maxCell=Math.max(maxCell,(ee+f.E)/P);maxEffectiveCell=Math.max(maxEffectiveCell,z/P);if(f.p<kap*P){exs+=z;cs+=(4*P/3+8);}else{exr+=z;cr+=(4*P/3+8);}}
  else ok(z===0,"bad cell removed");prev=h;
 }
 let rem=rr-dd,gs=[...src.keys()].reduce((z,i)=>z+es[i].g,0),gt=[...snk.keys()].reduce((z,i)=>z+es[i].g,0);
 ok(eq(rr+ig+f,gg)&&gs+gt<=gain&&rem<=gm*(3*gs+ex)+1e-7&&rem<=gm*gt+1e-7&&rem<=gm*(3*gain+ex)/4+1e-7&&eq(ex,exs+exr),"gain packing");
 const lhs=(1-3*gm/4)*gain-P-ig-dd,rhs=f+gm*ex/4,ref=f+gm*(cs+cr)/4;
 ok(rhs>=lhs-1e-7&&ref>=rhs-1e-7,"weighted certificate");
 if(lhs>0)nonvacuous++;
 weightedL+=lhs;weightedR+=rhs;refinedR+=ref;G+=gain;F+=f;Fs+=fs;Fr+=fr;R+=rr;discard+=dd;initial+=ig;Ex+=ex;Es+=exs;Er+=exr;liveR+=rem;
 if(gain>=T){hit++;fullGain+=gain;fullL+=lhs;fullR+=rhs;fullRefined+=ref;}
}
// Synthetic tightness for the noncrossing excess packing: alternating 5,3 gains with E=4,4.
// It is an abstract local capacity test, not an assertion of a realized MIN word.
for(let n=1;n<=64;n++){ok(8*n===4*(6*n)/3,"abstract pair capacity");synthetic++}
const rd=x=>+x.toFixed(6);return {X,focus,B,T,P,N,events,hit,G,F,Fs,Fr,R:rd(R),discard:rd(discard),initial:rd(initial),liveR:rd(liveR),Ex:rd(Ex),Es:rd(Es),Er:rd(Er),rawEx,positiveEx,sourceChecks,cellChecks,paired,unpaired,p3Consecutive,p3Ex,maxCell:rd(maxCell),maxEffectiveCell:rd(maxEffectiveCell),weightedL:rd(weightedL),weightedR:rd(weightedR),refinedR:rd(refinedR),nonvacuous,fullGain,fullL:rd(fullL),fullR:rd(fullR),fullRefined:rd(fullRefined),firstBadEarlier,firstBadNotDisparate:rd(firstBadNotDisparate),capChecks,nonzero,synthetic}
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
