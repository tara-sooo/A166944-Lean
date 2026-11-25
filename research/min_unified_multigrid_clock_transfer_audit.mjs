// Multi-primorial overshoot variation and whole-cell clock mask transfer audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],kap=2,alpha=1/8,eta=.5,K=2,eps=.35,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,m)=>{if(!x)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let paths=[],N=0,hit=0,events=0,G=0,W=0,midChecks=0,cellChecks=0,scoreChecks=0,coverChecks=0,heavyWitnessChecks=0;
 let grids=Ps.map(P=>({P,keys:new Map(),cells:[],down:0,up:0,root:0,small:0,mid:0,large:0,midGain:0,smallN:0,largeN:0,J:0,clock:0,carry:0,err:0,shortfall:0,badW:0,tailW:0,n:0,atoms:0,paid:0,covered:0,thin:0,heavy:0,zero:0}));
 function add(m,k,v){m.set(k,(m.get(k)||0)+v)}
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[];
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;
   for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;
   let g=p-1,w=v-t,J=C+g,delta=2*w-g,D=Math.max(0,-delta),E=Math.max(0,delta-3*g);
   ok(w<=2*r&&w<=3*g&&2*t>=C&&2*v>=J,"event");
   es.push({C,J,p,r,g,w,D,E,cover:0,h:[]});events++;C=J;t=v;
  }
  let gain=C-C0,clock=es.reduce((s,e)=>s+e.w,0);G+=gain;W+=clock;if(gain>=T)hit++;
  let midGain=0;
  for(let z of grids){
   let P=z.P,bprev=C0-(P*Math.ceil(C0/P)-P),b0=bprev,prev=null,start=0,tagDown=0,tagUp=0,tagMid=0,tagErr=0,tagBad=0,tagTail=0,tagCells=0,tagScore=0,tagW=0,tagAtoms=0;
   for(let i=0;i<es.length;i++){let e=es[i],n=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!n)continue;
    ok(P%e.p!==0,"strict barrier");let seg=es.slice(start,i+1),sum=k=>seg.reduce((s,e)=>s+e[k],0),gg=sum("g"),ww=sum("w"),dd=sum("D"),ee=sum("E"),l=gg-e.g,f=P*n,b=e.J-P*(Math.ceil(e.J/P)-1),dn=Math.max(0,bprev-b),up=Math.max(0,b-bprev),bad=e.p>=kap*P&&e.r<alpha*e.g;
    ok(f-gg===bprev-b&&dd<=gg&&l<=P&&ee<=l+8&&b>0&&b<=Math.min(P,e.g),"cell geometry");
    tagDown+=dn;tagUp+=up;tagCells++;tagAtoms+=n;
    if(!prev){z.root+=dn;ok(dn<=P,"root");}
    else if(prev.p<=eta*P){z.small+=dn;z.smallN++;ok(dn<=eta*P,"small");}
    else if(prev.p>=K*P){z.large+=dn;z.largeN++;ok(dn<=P&&prev.g>=K*P-1,"large");}
    else{z.mid+=dn;z.midGain+=prev.g;tagMid+=prev.g;ok(dn<=prev.g,"mid");}
    let A=bad?0:Math.max(0,f-dd)+Math.min(l,ee)/4,L=bad?0:Math.max(0,Math.max(f,dd)-gg+ww/2),J=Math.min(A,L),beta=Math.max(0,J-ww/2),omega=J-beta;
    ok(beta<=dn+1e-7&&omega<=ww/2+1e-7&&(!bad?J>=ww/2-up-2-1e-7:true),"score bounds");scoreChecks++;
    if(bad){tagBad+=ww;ok(ww<=3*P+2*alpha*e.g+1e-7,"bad wait");}
    let err=Math.abs(J-ww/2);tagErr+=err;tagScore+=J;tagW+=ww;
    z.shortfall+=ww/2-omega;z.J+=J;z.clock+=omega;z.carry+=beta;z.n++;z.atoms+=n;if(J===0)z.zero++;
    let keys=[];for(let k=P*Math.ceil(e.C/P);k<e.J;k+=P){let key=[k,e.C,e.p].join("|");keys.push(key);if(J)add(z.keys,key,J/n);}
    z.cells.push({seg,keys,J,ww,bad});prev=e;bprev=b;start=i+1;cellChecks++;
   }
   let tail=es.slice(start),tailG=tail.reduce((s,e)=>s+e.g,0);tagTail=tail.reduce((s,e)=>s+e.w,0);
   ok(tailG<=P&&tagTail<=3*P&&tagUp-tagDown===bprev-b0&&tagAtoms<=gain/P+1+1e-7,"terminal/variation");
   tagErr+=tagTail/2;ok(tagErr<=tagDown+tagUp+2*tagCells+(tagBad+tagTail)/2+1e-7,"absolute variation error");
   z.down+=tagDown;z.up+=tagUp;z.err+=tagErr;z.badW+=tagBad;z.tailW+=tagTail;z.shortfall+=tagTail/2;
   if(tail.length)z.cells.push({seg:tail,keys:[],J:0,ww:tagTail,bad:true});
   ok(eq(tagW+tagTail,clock),"clock partition");midGain+=tagMid;
  }
  ok(midGain<=gain+1e-7,"disjoint middle bands");midChecks++;paths.push(es);
 }
 for(let z of grids){
  let P=z.P,thin=new Set();
  for(let [k,v] of z.keys){if(v<=1.25*P*(focus?.5:2)){thin.add(k);z.thin++;}else z.heavy++;}
  for(let c of z.cells){let h=c.bad||!c.J?1:c.keys.filter(k=>thin.has(k)).length/c.keys.length;z.paid+=h*c.J;z.covered+=h*c.ww;
   ok(h*c.ww<=2*h*c.J+2*Math.max(0,c.ww/2-c.J)+1e-7,"fraction transfer");
   for(let e of c.seg){e.cover+=h/Ps.length;e.h.push(h);}
  }
  ok(eq(z.down,z.root+z.small+z.mid+z.large)&&z.small<=eta*P*z.smallN+1e-7&&z.large<=P*z.largeN+1e-7&&eq(z.J,z.clock+z.carry)&&eq(z.shortfall,W/2-z.clock)&&z.covered<=2*z.paid+2*z.err+1e-7,"global grid");
 }
 let cover=0,trim=0,retained=0,trimEvents=0,retainedEvents=0,goodGrids=0;
 for(let es of paths)for(let e of es){ok(e.h.length===Ps.length&&eq(e.cover,e.h.reduce((s,x)=>s+x,0)/Ps.length),"coverage");
  cover+=e.cover*e.w;coverChecks++;
  if(e.cover>eps){trim+=e.w;trimEvents++;}
  else{retained+=e.w;retainedEvents++;let good=e.h.filter(h=>h<=.5).length;ok(good>=Ps.length*(1-2*eps)-1e-7,"many good grids");goodGrids+=good;heavyWitnessChecks++;}
 }
 ok(eq(cover,grids.reduce((s,z)=>s+z.covered,0)/Ps.length)&&trim<=cover/eps+1e-7&&eq(trim+retained,W),"coverage Markov");
 ok(grids.reduce((s,z)=>s+z.midGain,0)<=G+1e-7,"middle gain global");
 const rd=x=>+x.toFixed(6);
 return {X,focus,B,T,N,hit,events,G,W,midChecks,cellChecks,scoreChecks,coverChecks,heavyWitnessChecks,cover:rd(cover),trim,retained,trimEvents,retainedEvents,goodGrids,grids:grids.map(({keys,cells,...z})=>Object.fromEntries(Object.entries(z).map(([k,v])=>[k,rd(v)])))};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
