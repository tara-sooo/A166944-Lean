// Two-sided multigrid annulus witness audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],a=2,sqrtA=Math.sqrt(a),lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(x,m)=>{if(!x)throw Error(`${X}/${focus} ${m}`)},eq=(x,y)=>Math.abs(x-y)<=1e-8*Math.max(1,Math.abs(x),Math.abs(y)),mod=(x,y)=>(x%y+y)%y;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,G=0,W=0,hit=0,events=0,paths=[],grids=Ps.map(P=>({P,counts:new Map(),left:0,right:0,thinLeft:0,thinRight:0,thinUnion:0,middleLeft:0,middleRight:0,middleFocal:0,largeNonself:0,smallSelf:0,edge:0,strip:0,paid:0,good:0,self:0,small:0,midGain:0,cellChecks:0,keys:0,thin:0,heavy:0,repeat:0}));
 function add(m,k,v){m.set(k,(m.get(k)||0)+v)}
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,cut=Math.floor((7*M-1)/4),es=[];
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g&&2*t>=C&&2*v>=J,"event");
   es.push({C,J,g,p,r,w,good:[],bad:0});C=J;t=v;events++;G+=g;W+=w;
  }
  if(C-C0>=T)hit++;paths.push(es);
  for(let z of grids){let P=z.P;for(let e of es){let n=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(n){ok(P%e.p!==0,"strict barrier");for(let K=P*Math.ceil(e.C/P);K<e.J;K+=P)add(z.counts,[K,e.C,e.p].join("|"),1)}if(e.p>P/a&&e.p<a*P)z.midGain+=e.g}}
 }
 let partitionChecks=0,annulusChecks=0,capacityChecks=0,smallEvents=0,manyGood=0,retained=0,trim=0,averageBad=0,distinctChecks=0,rawRepeatChecks=0,retainedSmall=0,smallBoth=0;
 for(let es of paths){
  for(let z of grids){
   const P=z.P,n=es.length,prev=new Int32Array(n),next=new Int32Array(n),cross=es.map(e=>Math.ceil(e.J/P)-Math.ceil(e.C/P)),isThin=e=>{let vals=[];for(let K=P*Math.ceil(e.C/P);K<e.J;K+=P)vals.push(z.counts.get([K,e.C,e.p].join("|")));ok(vals.length>0&&vals.every(v=>v===vals[0]),"same tag count on all crossed atoms");return vals[0]<=(focus?.5:2)};
   let k=-1;for(let i=0;i<n;i++){if(cross[i])k=i;prev[i]=k}k=-1;for(let i=n-1;i>=0;i--){if(cross[i])k=i;next[i]=k}
   let lw=new Map(),rw=new Map(),tagMid=0,tagLarge=0,tagSmall=0,tagStrip=0,tagEdge=0,thinL=0,thinR=0;
   for(let i=0;i<n;i++){let e=es[i];if(prev[i]>=0)add(lw,prev[i],e.w);if(next[i]>=0)add(rw,next[i],e.w)}
   for(let [i,w] of lw){let e=es[i];ok(w<=3*(e.g+P)&&w<=9*P*cross[i],"backward cell cap");capacityChecks++;z.left+=w;if(isThin(e))thinL+=w}
   for(let [i,w] of rw){let e=es[i];ok(w<=3*(e.g+P)&&w<=9*P*cross[i],"forward cell cap");capacityChecks++;z.right+=w;if(isThin(e))thinR+=w}
   z.thinLeft+=thinL;z.thinRight+=thinR;
   let count=cross.reduce((s,x)=>s+x,0),g=es.reduce((s,e)=>s+e.g,0);
   let localMid=es.filter(e=>e.p>P/a&&e.p<a*P).reduce((s,e)=>s+e.g,0);
   for(let i=0;i<n;i++){
    let e=es[i],L=prev[i],R=next[i],l=L<0?null:es[L],r=R<0?null:es[R],reason="";
    if(L<0||R<0){reason="edge";tagEdge+=e.w}
    else if(isThin(l)||isThin(r))reason="thinUnion";
    else if(l.p>P/a&&l.p<a*P){reason="middleLeft";tagMid+=e.w}
    else if(r.p>P/a&&r.p<a*P){reason="middleRight";tagMid+=e.w}
    else if(e.p>P/a&&e.p<a*P){reason="middleFocal";tagMid+=e.w}
    else if((L!==i&&l.p>=a*P)||(R!==i&&r.p>=a*P)){reason="largeNonself";tagLarge+=e.w}
    else if(cross[i]&&e.p<=P/a){reason="smallSelf";tagSmall+=e.w}
    else if(!cross[i]){
      let Kleft=P*(Math.ceil(l.J/P)-1),Kright=P*Math.ceil(r.C/P);
      ok(Kright-Kleft===P&&l.J<=e.C&&e.J<=r.C,"adjacent grid");
      if(Math.min(e.C-Kleft,Kright-e.C)<P/sqrtA){reason="strip";tagStrip+=e.w}
    }
    if(reason){e.bad++;z[reason]+=e.w;z.paid+=e.w;continue}
    z.good+=e.w;
    if(cross[i]){ok(L===i&&R===i&&e.p>=a*P,"self large");z.self+=e.w;e.good.push({P,self:true,L,R});}
    else{ok(e.p<=P/a&&l.p<=P/a&&r.p<=P/a&&L<i&&i<R,"small triple");let dL=e.C-l.C,dR=r.C-e.C;
     ok(dL>=P/sqrtA-1e-8&&dL<=P+P/a+1e-8&&dR>=P/sqrtA-P/a-1e-8&&dR<=P,"annuli");annulusChecks++;z.small+=e.w;e.good.push({P,self:false,L,R});
    }
    partitionChecks++;
   }
   ok(tagEdge<=6*P+1e-8&&tagMid<= (6*(1+2*a)+3)*localMid+1e-8&&tagSmall<=3*P/a*count+1e-8,"packing");
   // A small noncrossing event in a grid strip has all its gain in an enlarged strip.
   ok(tagStrip<=3*(g/P+2)*(2*P/sqrtA+2*P/a)+1e-8,"strip bound");
  }
  for(let e of es){let h=e.bad/Ps.length;averageBad+=h*e.w;
   if(h>1/3){trim+=e.w;continue}retained+=e.w;manyGood++;ok(e.good.length>=2,"many good");
   let small=e.good.filter(x=>!x.self);
   if(small.length){smallEvents++;if(small.length>=2)smallBoth++;if(e.p<=Math.min(...Ps)/a)retainedSmall++;}
   for(let i=0;i<small.length;i++)for(let j=i+1;j<small.length;j++){let x=small[i],y=small[j];
    // Finite grids need a larger scale ratio for these particular finite annulus constants.
    if(y.P*(1/sqrtA-1/a)>x.P*(1+1/a)){ok(x.L!==y.L&&x.R!==y.R,"distinct witnesses");distinctChecks++}
    if(x.L===y.L||x.R===y.R)rawRepeatChecks++;
   }
  }
 }
 for(let z of grids){z.keys=z.counts.size;for(let v of z.counts.values())if(v<=(focus?.5:2))z.thin++;else z.heavy++;ok(z.thinLeft<=9*z.P*(focus?.5:2)*z.thin+1e-7&&z.thinRight<=9*z.P*(focus?.5:2)*z.thin+1e-7&&z.thinUnion<=z.thinLeft+z.thinRight+1e-7&&eq(z.good+z.paid,W),"global grid")}
 ok(grids.reduce((s,z)=>s+z.midGain,0)<=G+1e-7&&eq(retained+trim,W)&&trim<=3*averageBad+1e-7,"global");
 let rd=x=>+x.toFixed(6);return {X,focus,B,T,N,events,hit,G,W,averageBad:rd(averageBad),trim,retained,manyGood,smallEvents,smallBoth,retainedSmall,annulusChecks,capacityChecks,partitionChecks,distinctChecks,rawRepeatChecks,grids:grids.map(({counts,...z})=>z)};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[256,1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
