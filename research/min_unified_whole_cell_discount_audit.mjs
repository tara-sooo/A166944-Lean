// Whole-cell negative variation and source excess certificate, finite diagnostics.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),P=focus?30:6,kap=2,alpha=1/8,kap2=1.5,eta=.4,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,s)=>{if(!x)throw Error(`${X}/${focus} ${s}`)},eq=(x,y)=>Math.abs(x-y)<=1e-7*Math.max(1,Math.abs(x),Math.abs(y)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,events=0,hit=0,G=0,oldActual=0,oldProj=0,actual=0,word=0,exactActual=0,exactWord=0,credit=0,creditWord=0,exCredit=0,cellN=0,noncrossSink=0,initial=0,matched=0,discard=0,exception=0,sourceChecks=0,capacityChecks=0,rootTrim=0,prevLongTrim=0,cheapTrim=0,cheapWordTrim=0,cheapN=0,cheapWordN=0,prevLongN=0,overshootChecks=0,remaining=0,smallN=0,largeOffsetN=0,expensiveN=0,fullActual=0,fullWord=0,fullLower=0,maxCredit=0,keys=new Map();
 function add(m,k,v){m.set(k,(m.get(k)||0)+v)}
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[],cells=[],start=0;
  while(C-C0<T){
   let p=0,v=Infinity,r=Infinity;
   for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;
   let J=C+p-1,g=p-1,w=v-t,delta=2*w-g,D=Math.max(0,-delta),Db=Math.max(0,g-4*r),E=Math.max(0,delta-3*g),Eb=4*(r===p?1:0),n=Math.ceil(J/P)-Math.ceil(C/P),bad=p>=kap*P&&r<alpha*g;
   ok(w<=2*r&&r<=p&&D>=Db&&E<=Eb&&2*t-C>=0&&2*v-J>=0&&(!n||P%p!==0),"event");
   es.push({C,J,p,r,g,w,D,Db,E,Eb,delta,n,bad,gamma:0,cell:-1});events++;
   if(n){let i=es.length-1,seg=es.slice(start,i+1),pre=seg.slice(0,-1),l=C-seg[0].C,f=P*n,
     dn=seg.reduce((s,e)=>s+e.D,0),db=seg.reduce((s,e)=>s+e.Db,0),ee=seg.reduce((s,e)=>s+e.E,0),eb=seg.reduce((s,e)=>s+e.Eb,0),
     wp=pre.reduce((s,e)=>s+e.w,0),rp=pre.reduce((s,e)=>s+e.r,0);
    ok(l<=P&&ee<=l+8&&dn>=db&&ee<=eb,"cell envelope");
    const id=cells.length;
    for(let e of seg)e.cell=id;
    let gamma=bad?0:dn?Math.min(1,f/dn):0;
    if(bad)es[i].gamma=f/D;else for(let e of seg)e.gamma=gamma;
    let fnew=bad?0:Math.max(0,f-dn),fw=bad?0:Math.max(0,f-db),a=bad?0:fnew+Math.min(l,ee)/4,b=bad?0:fw+Math.min(l,eb)/4,
       ae=bad?0:fnew+ee/4,be=bad?0:fw+Math.min(l+8,eb)/4,old=bad?0:Math.max(0,f-D)+l/4,oldp=bad?0:Math.max(0,f-Db)+l/4;
    ok(a<=b+1e-8&&a<=old+1e-8&&b<=oldp+1e-8&&ae<=be+1e-8&&ae-a<=2+1e-8&&be-b<=2+1e-8,"pointwise");
    cells.push({start,i,l,f,dn,db,ee,eb,wp,rp,fnew,fw,a,b,ae,be,old,oldp,bad,K:P*Math.ceil(C/P),last:P*(Math.ceil(J/P)-1),n,p,offset:P*Math.ceil(C/P)-C,J});
    start=i+1;
   }
   C=J;t=v;
  }
  let st=[[-1,6]],I=0,raw=0,del=0,gm=0,src=new Map(),snk=new Map(),exCell=new Map(),noncross=0;
  for(let j=0;j<es.length;j++){let b=es[j],gamma=b.gamma;gm=Math.max(gm,gamma);
   if(b.delta>0)st.push([j,b.delta]);else if(b.D){let left=b.D;while(left){let s=st.at(-1),n=Math.min(left,s[1]),i=s[0],charge=gamma*n;left-=n;s[1]-=n;if(!s[1])st.pop();if(!charge)continue;if(i<0){I+=charge;continue}raw+=charge;
    let a=es[i],k=a.cell;ok(k>=0&&k<=b.cell,"source cell");
    if(cells[k].bad){del+=charge;if(j!==cells[k].i||a.p>3*P||b.p<3*a.p||b.C-a.J>b.p/3)exception+=charge;continue}
    if(!b.n)noncross++;add(src,i,charge);add(snk,j,charge);
   }}}
  let ex=0,gs=0,gt=0;
  for(let [i,v] of src){let a=es[i],e=Math.max(0,v/gm-3*a.g);ok(v<=gm*a.delta+1e-7&&e<=a.E+1e-7&&!snk.has(i),"source packing");gs+=a.g;ex+=e;add(exCell,a.cell,e);sourceChecks++}
  for(let [j,v] of snk){ok(v<=gm*es[j].D+1e-7,"sink packing");gt+=es[j].g}
  for(let [id,v] of exCell){ok(!cells[id].bad&&v<=cells[id].ee+1e-7,"excess attribution");capacityChecks++}
  let gain=C-C0,ff=cells.reduce((s,c)=>s+c.fnew,0),grid=cells.reduce((s,c)=>s+c.f,0),a=cells.reduce((s,c)=>s+c.a,0),b=cells.reduce((s,c)=>s+c.b,0);
  ok(eq(ff+raw+I,grid)&&gs+gt<=gain&&raw-del<=gm*(3*gain+ex)/4+1e-7&&I<=6*gm+1e-7,"exact new ledger");
  let lo=(1-3*gm/4)*gain-P-I-del;ok(ff+gm*ex/4>=lo-1e-7,"weighted lower bound");
  for(let [id,c] of cells.entries()){if(c.bad)continue;cellN++;oldActual+=c.old;oldProj+=c.oldp;actual+=c.a;word+=c.b;exactActual+=c.ae;exactWord+=c.be;credit+=c.old-c.a;creditWord+=c.oldp-c.b;exCredit+=(c.l-Math.min(c.l,c.ee))/4;maxCredit=Math.max(maxCredit,c.old-c.a);
   if(c.p>=kap2*P)continue;
   if(id===0){rootTrim+=c.b;continue}
   let prev=cells[id-1],over=prev.J-prev.last;
   ok(c.K===prev.last+P&&c.l===P-c.offset-over&&over>0&&over<=prev.p-1,"adjacent cell geometry");overshootChecks++;
   if(prev.p>=kap2*P){prevLongTrim+=c.b;prevLongN++;continue}
   if(c.p<=eta*P+1){smallN++;
    if(over<=eta*P&&c.offset<=eta*P){
     ok(c.n===1&&c.l>=(1-2*eta)*P-1e-7,"small cell geometry");
     if(c.wp<=eta*P){ok(c.a<=4.5*eta*P+1+1e-7,"actual cheap cell");cheapTrim+=c.a;cheapN++;}
     else expensiveN++;
     if(2*c.rp<=eta*P){ok(c.b<=4.5*eta*P+1+1e-7,"word cheap cell");cheapWordTrim+=c.b;cheapWordN++;continue}
    }else largeOffsetN++;
   }
   remaining+=c.b;for(let K=c.K;K<=c.last;K+=P)add(keys,[K,es[c.i].C,c.p].join("|"),c.b/c.n);
  }
  G+=gain;initial+=I;matched+=raw;discard+=del;noncrossSink+=noncross;
  if(gain>=T){hit++;fullActual+=a;fullWord+=b;fullLower+=lo;}
 }
 const rd=x=>+x.toFixed(6);
 return {X,focus,B,T,P,N,events,hit,G,oldActual:rd(oldActual),oldProj:rd(oldProj),actual:rd(actual),word:rd(word),exactActual:rd(exactActual),exactWord:rd(exactWord),credit:rd(credit),creditWord:rd(creditWord),exCredit:rd(exCredit),cellN,noncrossSink,initial:rd(initial),matched:rd(matched),discard:rd(discard),exception:rd(exception),sourceChecks,capacityChecks,rootTrim:rd(rootTrim),prevLongTrim:rd(prevLongTrim),prevLongN,cheapTrim:rd(cheapTrim),cheapWordTrim:rd(cheapWordTrim),cheapN,cheapWordN,overshootChecks,smallN,largeOffsetN,expensiveN,remaining:rd(remaining),keys:keys.size,fullActual:rd(fullActual),fullWord:rd(fullWord),fullLower:rd(fullLower),maxCredit:rd(maxCredit)};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
