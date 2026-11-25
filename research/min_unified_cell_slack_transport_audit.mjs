// Slack-discounted cell objective and bounded overshoot/tick transport.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,P=focus?30:6,kap=2,alpha=1/8,eta=.4,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,m)=>{if(!x)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 const ov=new Map(),projected=new Map(),physical=new Map(),pCap=new Map(),tCap=new Map();
 function add(m,k,v){if(v>0)m.set(k,(m.get(k)||0)+v)}
 let N=0,events=0,hit=0,G=0,W=0,old=0,oldWord=0,newA=0,newWord=0,rawClip=0,exact=0,correction=0,overshoot=0,wait=0,root=0,badPrev=0,smallPrev=0,longPrev=0,ovRem=0,waitRem=0,cellN=0,zero=0,carryN=0,capacityChecks=0,stackChecks=0,wordChecks=0,fullA=0,fullWord=0,fullW=0,matched=0,discard=0,initial=0,finiteLower=0,finiteScore=0,finiteException=0,projectedPaid=0,tickPaid=0,overlap=0;
 let routed=[];
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],cells=[],start=0,prevB=C0-(P*Math.ceil(C0/P)-P);
  while(C-C0<T){
   let p=0,v=Infinity,r=Infinity;
   for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;
   let J=C+p-1,g=p-1,w=v-t,delta=2*w-g,D=Math.max(0,-delta),pos=Math.max(0,delta),E=Math.max(0,delta-3*g),Db=Math.max(0,g-4*r),Eb=4*(p===r?1:0),n=Math.ceil(J/P)-Math.ceil(C/P),bad=p>=kap*P&&r<alpha*g;
   ok(w<=2*r&&w<=3*g&&D>=Db&&E<=Eb&&2*t>=C&&2*v>=J&&(!n||P%p!==0),"event");
   es.push({C,J,t,v,p,r,g,w,delta,D,pos,E,Db,Eb,n,bad,gamma:0,cell:-1});events++;
   if(n){
    let i=es.length-1,seg=es.slice(start,i+1),sum=k=>seg.reduce((s,e)=>s+e[k],0),gg=sum("g"),ww=sum("w"),dd=sum("D"),pp=sum("pos"),ee=sum("E"),db=sum("Db"),eb=sum("Eb"),rs=sum("r"),l=gg-g,f=P*n,K=P*Math.ceil(C/P),last=P*(Math.ceil(J/P)-1),b=J-last,id=cells.length;
    ok(l<=P&&ee<=l+8&&b>0&&b<=P&&f-gg===prevB-b&&pp-dd===2*ww-gg&&dd<=gg,"cell geometry");
    let gam=bad?0:dd?Math.min(1,f/dd):0;
    for(let a of seg){a.cell=id;a.gamma=gam}
    if(bad)es[i].gamma=f/D;
    let fc=bad?0:Math.max(0,f-dd),A=bad?0:fc+Math.min(l,ee)/4,AW=bad?0:Math.max(0,f-db)+Math.min(l,eb)/4;
    let raw=bad?0:Math.max(0,Math.max(f,dd)-gg+ww/2);
    let Jnew=Math.min(A,raw);
    let wenv=bad?0:Math.max(0,f-gg+rs,seg.reduce((s,e)=>s+Math.max(-1.5,e.r-e.g),0));
    let word=Math.min(AW,wenv);
    ok(raw<=A+2+1e-7&&Jnew<=word+1e-7&&word<=AW+1e-7,"pointwise envelopes");
    for(let e of seg){let x=Math.max(e.g-1.5,e.r);ok(e.D+e.w/2<=x+1e-7,"endpoint convex bound");wordChecks++}
    let carry=Math.max(0,Jnew-ww/2),clock=Jnew-carry;
    ok(carry<=Math.max(0,prevB-b)+1e-7&&clock<=ww/2+1e-7,"direct transport");
    cells.push({start,i,gg,ww,dd,pp,ee,l,f,bad,fc,A,AW,raw,Jnew,word,carry,clock,b,K,last,p,r});prevB=b;start=i+1;
   }
   C=J;t=v;
  }
  let st=[[-1,6]],I=0,R=0,del=0,gm=0,src=new Map(),snk=new Map();
  for(let j=0;j<es.length;j++){
   let e=es[j];gm=Math.max(gm,e.gamma);
   if(e.delta>0)st.push([j,e.delta]);else if(e.D){let left=e.D;while(left){let a=st.at(-1),len=Math.min(left,a[1]),i=a[0],v=e.gamma*len;left-=len;a[1]-=len;if(!a[1])st.pop();if(!v)continue;
    if(i<0){I+=v;continue}R+=v;ok(es[i].cell>=0&&es[i].cell<=e.cell,"source cell");
    if(cells[es[i].cell].bad){del+=v;let s=es[i];if(j!==cells[s.cell].i||e.p<3*s.p||e.C-s.J>e.p/3)finiteException+=v;continue}
    add(src,i,v);add(snk,j,v);stackChecks++;
   }}
  }
  for(let [i,v] of src)ok(v<=gm*es[i].pos+1e-7&&!snk.has(i),"source");
  for(let [j,v] of snk)ok(v<=gm*es[j].D+1e-7,"sink");
  let gain=C-C0,ff=cells.reduce((s,c)=>s+c.fc,0),flux=cells.reduce((s,c)=>s+c.f,0),ps=cells.filter(c=>!c.bad).reduce((s,c)=>s+c.pp,0),ds=es.reduce((s,e)=>s+e.D,0);
  ok(eq(ff+R+I,flux)&&R-del<=gm*ps+1e-7&&R-del<=gm*ds+1e-7,"ledger/capacity");
  let low=(1-3*gm/4)*gain-P-I-del,score=ff+gm*(ps+3*ds-3*gain)/4;
  let clip=cells.filter(c=>!c.bad).reduce((s,c)=>s+Math.max(0,c.fc+gm*(c.pp+3*c.dd-3*c.gg)/4),0);
  ok(score>=low-1e-7&&clip>=score-1e-7,"finite signed certificate");
  let ja=0,jw=0;
  for(let [id,c] of cells.entries()){
   if(c.bad)continue;cellN++;old+=c.A;oldWord+=c.AW;rawClip+=c.raw;newA+=c.Jnew;newWord+=c.word;correction+=c.A-c.Jnew;ja+=c.Jnew;jw+=c.word;capacityChecks++;
   if(c.Jnew===0)zero++;if(c.carry>0)carryN++;overshoot+=c.carry;wait+=c.clock;
   if(c.carry){
    if(id===0)root+=c.carry;
    else {let prev=cells[id-1],pe=es[prev.i];ok(c.carry<=Math.min(P,pe.g)+1e-7,"predecessor capacity");
     if(prev.bad)badPrev+=c.carry;
     else if(prev.p<=eta*P)smallPrev+=c.carry;
     else if(prev.p>=1.5*P)longPrev+=c.carry;
     else {add(ov,[prev.last,pe.C,pe.p].join("|"),c.carry);ovRem+=c.carry;}
    }
   }
   if(c.clock){let alpha=c.clock/c.ww;ok(alpha<=.5+1e-9,"tick coefficient");
    for(let i=c.start;i<=c.i;i++){let e=es[i],pk=e.C+"|"+e.p;
     add(projected,pk,alpha*e.w);pCap.set(pk,e.r);
     for(let j=e.t;j<e.v;j++){let tk=e.C+"|"+e.p+"|"+j;add(physical,tk,alpha);tCap.set(tk,e.r);routed.push({pk,tk,w:alpha});}
    }
   }
  }
  if(gain>=T){hit++;fullA+=ja;fullWord+=jw;fullW+=es.reduce((s,e)=>s+e.w,0)}
  G+=gain;W+=es.reduce((s,e)=>s+e.w,0);matched+=R;discard+=del;initial+=I;finiteLower+=low;finiteScore+=clip;
 }
 const sum=m=>[...m.values()].reduce((s,v)=>s+v,0);
 const po=new Set(),to=new Set();
 for(let [k,v] of projected)if(v<=pCap.get(k)*(focus?.5:2)){po.add(k);projectedPaid+=v}
 for(let [k,v] of physical)if(v<=(focus?.25:1)){to.add(k);tickPaid+=v}
 for(let a of routed){if(po.has(a.pk)&&to.has(a.tk))overlap+=a.w;else if(!po.has(a.pk)&&!to.has(a.tk))waitRem+=a.w}
 ok(eq(overshoot+wait,newA)&&eq(root+badPrev+smallPrev+longPrev+ovRem,overshoot)&&eq(sum(ov),ovRem)&&eq(sum(projected),wait)&&eq(sum(physical),wait)&&eq(projectedPaid+tickPaid-overlap+waitRem,wait),"global transport");
 const rd=x=>+x.toFixed(6);
 return {X,focus,B,T,P,N,events,hit,G,W,old:rd(old),oldWord:rd(oldWord),newA:rd(newA),newWord:rd(newWord),rawClip:rd(rawClip),reduction:rd(correction),overshoot:rd(overshoot),wait:rd(wait),root:rd(root),badPrev:rd(badPrev),smallPrev:rd(smallPrev),longPrev:rd(longPrev),ovRem:rd(ovRem),waitRem:rd(waitRem),cellN,zero,carryN,capacityChecks,stackChecks,wordChecks,fullA:rd(fullA),fullWord:rd(fullWord),fullW,matched:rd(matched),discard:rd(discard),initial:rd(initial),finiteLower:rd(finiteLower),finiteScore:rd(finiteScore),finiteException:rd(finiteException),projectedPaid:rd(projectedPaid),tickPaid:rd(tickPaid),overlap:rd(overlap),ovKeys:ov.size,projectedKeys:projected.size,physicalKeys:physical.size};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
