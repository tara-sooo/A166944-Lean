// Exact boundary-targeted deficit matching and short pair arithmetic audit.
function audit(X,stress=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=stress?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),P=stress?30:6,kap=2,alpha=1/8,cstar=4,rho=3,L=stress?8:16,top=Math.floor(B**.95),lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,m)=>{if(!x)throw Error(X+" "+m)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,events=0,hit=0,F=0,grid=0,badFlux=0,initial=0,target=0,recycled=0,shallow=0,disparate=0,shortPair=0,shortInc=0,matchChecks=0,stackChecks=0,phaseChecks=0,badSinks=0,shallowChecks=0,disparateChecks=0,persistChecks=0,rootBound=0,fullScore=0;
 const groups=new Map();
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[];
  while(C-C0<T){
   let v=Infinity,p=0,s=0,ls=fac(C-1),rs=fac(C+1),r=Math.min(...ls,...rs);
   for(let [sg,fs] of [[-1,ls],[1,rs]])for(let q of fs){let j=t+1+mod((sg===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j;s=sg}}
   if(!p||v>cut)break;
   let J=C+p-1,dp=2*t-C,d=2*v-J,w=v-t,n=Math.ceil(J/P)-Math.ceil(C/P),bad=p>=kap*P&&r<alpha*(p-1),delta=d-dp;
   ok(dp>=0&&d>=0&&w<=2*r&&w<=3*(p-1),"clock");
   if(n)ok(P%p!==0,"boundary");let cost=P*n;
   if(bad){ok(delta<0&&cost<=cstar*(-delta)+1e-9,"bad density");if(n)badSinks++;}
   es.push({C,J,t,v,p,s,r,w,dp,d,delta,bad,cost});events++;C=J;t=v;
  }
  let st=[[ -1,6]],lost=new Float64Array(es.length),paidSink=new Map(),paidSource=new Map(),targetSource=new Map(),tg=0,ig=0,ff=0,gg=0,bb=0;
  for(let j=0;j<es.length;j++){
   let b=es[j];gg+=b.cost;if(b.bad)bb+=b.cost;else ff+=b.cost;
   if(b.delta>0)st.push([j,b.delta]);
   else if(b.delta<0){
    let left=-b.delta,topLevel=b.dp,weight=b.bad?b.cost/left:0;
    while(left){ok(st.length>0,"stack underflow");let seg=st.at(-1),i=seg[0],len=Math.min(left,seg[1]),hi=topLevel,lo=hi-len;topLevel=lo;left-=len;seg[1]-=len;if(!seg[1])st.pop();
     if(i<0){ig+=weight*len;continue}
     let a=es[i];lost[i]+=len;ok(i<j&&a.delta>0&&lo>=a.dp&&hi<=a.d&&lo>=b.d&&hi<=b.dp,"level matching");matchChecks++;
     for(let h=i;h<j;h++){ok(es[h].d>=hi,"actual lifetime");persistChecks++}
     if(!weight)continue;
     let c=weight*len;tg+=c;targetSource.set(i,(targetSource.get(i)||0)+c);
     let depth=b.p/rho,low=Math.max(0,Math.min(hi,depth)-lo),c0=weight*low;shallow+=c0;shallowChecks++;
     let rem=c-c0,e=b.C-a.J;ok(e>=0&&e%2===0,"gap");
     if(rem<=1e-10)continue;
     if(b.p>=rho*a.p&&e<=b.p/rho){disparate+=rem;paidSink.set(j,(paidSink.get(j)||0)+(len-low));disparateChecks++;continue}
     if(a.p>=rho*b.p&&e<=a.p/rho){disparate+=rem;paidSource.set(i,(paidSource.get(i)||0)+(len-low));disparateChecks++;continue}
     if(a.p>L+3&&a.p<=top&&b.p<=top&&a.p<rho*b.p&&b.p<rho*a.p&&e<=L&&b.p>=kap*P){
       ok(a.p!==b.p&&a.r>(a.p-1)/4,"distinct rough source");let h=b.v-a.v;
       ok(h>0&&h<=3*e+2*b.r&&mod(a.v-(a.s===-1?0:a.p+2),2*a.p)===0&&mod(a.v+h-(b.s===-1?0:b.p+2),2*b.p)===0,"time CRT");
       ok(mod(a.C+a.s,a.p)===0&&mod(a.C+a.p-1+e+b.s,b.p)===0,"space CRT");phaseChecks++;
       let key=[a.C,a.p,a.v,b.C,b.p,b.v].join("|"),g=groups.get(key)||{A:a.C,p:a.p,q:b.p,v:a.v,V:b.v,e,n:0,charge:0};g.n++;g.charge+=rem;groups.set(key,g);shortPair+=rem;shortInc++;
     }
    }
    ok(topLevel===b.d,"stack level");
   }
  }
  let min=es.length?es.at(-1).d:6,R=0;
  for(let i=es.length-1;i>=0;i--){let a=es[i];min=Math.min(min,a.d);let b=Math.max(0,a.delta)-Math.max(0,min-a.dp);ok(eq(b,lost[i])&&(targetSource.get(i)||0)<=cstar*b+1e-9,"source domination");R+=b;min=Math.min(min,a.dp);stackChecks++}
  for(let [j,w] of paidSink)ok(w<=10*es[j].p/rho+1e-9,"sink recent gain");
  for(let [i,w] of paidSource)ok(w<=2*es[i].p/rho+1e-9,"source recent gain");
  ok(eq(tg+ig,bb)&&eq(ff+tg+ig,gg)&&ig<=6*cstar+1e-9&&tg<=cstar*R+1e-9,"exact flux");
  F+=ff;grid+=gg;badFlux+=bb;initial+=ig;target+=tg;recycled+=R;
  if(C-C0>=T){hit++;rootBound+=T-P-6*cstar;fullScore+=ff+tg;ok(ff+tg>=T-P-6*cstar,"reached certificate")}
 }
 let thin=0,heavy=0,paid=0,maxMass=0;
 for(let g of groups.values()){let n=g.charge/(5*cstar*g.p),cap=stress?2*B/g.p:B/g.p;ok(n<=g.n+1e-9,"effective mass");maxMass=Math.max(maxMass,n);if(n<=cap){thin++;paid+=g.charge}else heavy++}
 ok(target+initial+F<=grid+1e-7&&eq(target+initial+F,grid)&&shallow+disparate+shortPair<=target+1e-7&&fullScore>=rootBound,"global");
 let rnd=x=>+x.toFixed(6);
 return {X,stress,B,T,P,L,top,N,hit,events,F,grid,badFlux,initial:rnd(initial),target:rnd(target),recycled,shallow:rnd(shallow),disparate:rnd(disparate),shortPair:rnd(shortPair),paid:rnd(paid),remain:rnd(target-shallow-disparate-paid),groups:groups.size,thin,heavy,maxMass:rnd(maxMass),shortInc,matchChecks,stackChecks,phaseChecks,badSinks,shallowChecks,disparateChecks,persistChecks,rootBound,fullScore:rnd(fullScore)};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536])) console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
