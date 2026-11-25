// Banded high-clock focal and self-source partner capacities.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Ps=[6,30,210],Lh=Math.max(2,Math.floor(B/32)),Ll=Math.max(Lh,Math.floor(B/8)),Y=Math.max(5,Math.ceil(Math.sqrt(B))),R=8,cut=3,c=9,Q=Math.pow(B,.75),eps=.25,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(b,m)=>{if(!b)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,W=0,events=0,hit=0,paths=[],proj=new Map(),episodes=new Map(),birthCache=new Map(),pairs=new Map(),sameKeys=new Map(),merges=new Map(),cellChecks=0,excessChecks=0,smallCells=0,largeCells=0,cellOld=0,cellNew=0;
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C=2*M-2,C0=C,t=M+2,stop=Math.floor((7*M-1)/4),es=[],tag={M,es,end:0};while(C-C0<T){
   let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g,"wait");let k=C+"|"+p,o=proj.get(k)||{C,p,slots:new Map()};proj.set(k,o);let sl=o.slots.get(v)||{v,refs:[],o};o.slots.set(v,sl);
   let e={C,J,p,w,t,v,r,tag,i:es.length,sl,lo:[0,0,0],hi:[0,0,0]};es.push(e);sl.refs.push(e);W+=w;events++;C=J;t=v;
  }tag.end=C;let prev=new Map();for(let e of es){e.prevP=prev.get(e.p)??-1;e.load=Ps.map(()=>[0,0]);e.rw=Ps.map(()=>[0,0]);e.focalHigh=Ps.map(()=>0);e.band=Ps.map(()=>[0,0,0]);e.partnerBand=Ps.map(()=>[0,0]);e.partnerSrc=Ps.map(()=>new Map());e.focalSources=Ps.map(()=>new Map());e.radGap=0;let rad=6;for(let i=e.i-1;i>=0;i--){let p=es[i].p;if(p===e.p)break;if(rad%p!==0)rad*=p;if(rad>4*H)break;e.radGap=e.C-es[i].C;}prev.set(e.p,e.i)}if(C-C0>=T)hit++;paths.push(tag);
  for(let j=0;j<Ps.length;j++){let P=Ps[j],l=0,h=0,g=0,ex=0;for(let e of es){g+=e.p-1;ex+=Math.max(0,2*e.w-4*(e.p-1));if(e.p<=P/2){if(e.p<Y)l+=e.w;else if(e.w>=eps*(e.p-1))h+=e.w;}let k=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(k){ok(ex<=g+4,"local excess packing");excessChecks++;let cap=0;if(e.p<=P/2){ok(k===1&&g<=P+e.p-1,"small cell gain");cap=2.5*g+2;smallCells++;}else if(e.p>=2*P){l=e.p<Y?e.w:0;h=e.p>=Y&&e.w>=eps*(e.p-1)?e.w:0;cap=2*(e.p-1)+2;largeCells++;}else{l=h=0}
  ok(l+h<=cap+1e-7&&l+h<=c*P*k,"sharp good cell");if(l+h){cellChecks++;let old=6*P*k;ok(l+h<=old&&cap<=old+1e-7,"finite sharp comparison");cellOld+=old;cellNew+=cap}e.lo[j]=l;e.hi[j]=h;l=h=g=ex=0}}}
 }
 function word(e,L){let a=e.tag.es,i=e.i+1,s=[];while(a[i-1].J-e.J<L){let x=a[i++];ok(x,"room");s.push(x.p+":"+x.w)}return s.join(",")}
 function birth(e,f){let a=e.tag,b=f.tag,k=Math.min(a.M,b.M)+"|"+Math.max(a.M,b.M);if(birthCache.has(k))return birthCache.get(k);let i=0,j=0;while(i<a.es.length&&j<b.es.length){let x=a.es[i],y=b.es[j];if(x.C<y.C){i++;continue}if(y.C<x.C){j++;continue}if(Math.max(x.t,y.t)<Math.min(x.v,y.v)){ok(x.v===y.v&&x.p===y.p,"shared exit");let z={x,y,J:x.C,h:Math.abs(x.t-y.t),later:x.t>y.t?x:y};birthCache.set(k,z);return z}i++;j++}throw Error("missing common birth")}
 const stats=Ps.map(P=>({P,source:0,back:0,forward:0,unstable:0,diag:0,recent:0,small:0,long:0,other:0,highPaid:0,columns:0,rows:0,kernelChecks:0,defectChecks:0,longPairs:0,episodes:0,envelope:0,oldPairEnvelope:0,targetActual:0,targetBack:0,targetForward:0,unionBound:0,intersectionBound:0,targetChecks:0,treeBack:0,treeForward:0,labelForward:0,treeLabel:0,forwardNodes:0,childPairs:0,backEpisodes:0,backGroupPairs:0,radicalChecks:0,distinctCharge:0,sameCharge:0,pairKeyChecks:0,pairedCap:0,chosenCap:0,pairedImproved:0,pairRouteChecks:0,sameWaitChecks:0,sameMerge:0,sameSeparate:0,mergeChecks:0,shortLagChecks:0,predecessorChecks:0,coverChecks:0,coverFull:0,coverMinority:0,coverImproved:0,reverseGroups:0,reversePositive:0,reverseExact:0,reverseRaw:0,reversePool:0,reverseHalf:0,reverseCover:0,reverseChecks:0,reverseSlotChecks:0,stopChecks:0,stopGroups:0,stopMass:0,stopCharge:0,stopSame:0,stopBound:0,stopBudget:0,highFocalClock:0,highFocalChosen:0,highFocalOpposite:0,highFocalChecks:0,highSourceChecks:0,highSuffixChecks:0,highLabelChecks:0,highActualCap:0,highRawCap:0,highSuffixCap:0,highImproved:0,highKeys:0,bandNonself:0,bandMid:0,bandTop:0,partnerMid:0,partnerTop:0,bandCapNonself:0,bandCapMid:0,bandCapTop:0,partnerCapMid:0,partnerCapTop:0,partnerChecks:0,bandChecks:0,bandFringeChecks:0,partnerRows:0,timeChecks:0,arithmeticGroups:0,arithmeticChecks:0,recordChecks:0,budgetChecks:0,recordWeight:0,budgetWeight:0,modularUpper:0,exactForward:0,late:0,lateSmall:0,lateUpper:0,lateGroups:0,lateSmallChecks:0,radicalCapChecks:0,radicalImproved:0,radicalCapSum:0,renewalChecks:0,renewalCapChecks:0,renewalImproved:0,renewalOldCap:0,renewalNewCap:0,renewalLoad:0,jointCap:0,separateCap:0}));
 for(let o of proj.values()){let cls=new Map();for(let sl of o.slots.values()){sl.ready=sl.refs.filter(e=>e.tag.end-e.J>=Ll);if(sl.ready.length){sl.wl=word(sl.ready[0],Ll);sl.wh=word(sl.ready[0],Lh)}let c0=mod(sl.v,6),a=cls.get(c0)||[];a.push(sl);cls.set(c0,a)}
  for(let a of cls.values()){let n=a.reduce((v,s)=>v+s.refs.length,0),stable=a.reduce((v,s)=>v+s.ready.length,0),long=new Map(),short=new Map();for(let s of a)if(s.ready.length){long.set(s.wl,(long.get(s.wl)||0)+s.ready.length);short.set(s.wh,(short.get(s.wh)||0)+s.ready.length)}
   for(let j=0;j<Ps.length;j++){let z=stats[j],P=Ps[j],k=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!k)continue;let cap=c*P*k,cols=new Map(),bc=new Map(),dc=new Map(),rows=new Map(),live=[];
    const add=(m,key,v)=>m.set(key,(m.get(key)||0)+v);
    const weights=new Map();
    for(let s of a)for(let e of s.ready){let l=e.lo[j],h=e.hi[j];if(h&&short.get(s.wh)!==s.ready.length)h=0;weights.set(e,[l,h])}
    const W=(e)=>{let t=weights.get(e)||[0,0];return t[0]+t[1]};
    // Separate tries for the actual pursuit lengths. Nodes carry original source slots.
    for(let sector=0;sector<2;sector++){
     let L=sector?Lh:Ll,root={C:o.C+o.p-1,children:new Map(),slots:[],rad:6};
     function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
     function lcm(a,b){return a>4*H?a:Math.min(4*H+1,a/gcd(a,b)*b)}
     root.rad=lcm(root.rad,2*o.p);
     const arithmetic=new Map(),records=new Map(),threshold=Math.max(12,Math.floor(H/4)),kappa=.2,lateGroups=new Map();
     for(let s of a)if(s.ready.length){let e=s.ready[0],rad=root.rad,seq="",logBudget=0,seen=new Set(),i=e.i+1,lateKey=null,w=s.ready.reduce((v,f)=>v+weights.get(f)[sector],0);
      while(e.tag.es[i-1].J-e.J<L){let x=e.tag.es[i++],key=x.C+"|"+rad+"|"+(rad>4*H?s.v:mod(s.v,rad));let ar=arithmetic.get(key)||{seq,slots:[]};ok(ar.seq===seq,"arithmetic implies same prefix");ar.slots.push(s);arithmetic.set(key,ar);z.arithmeticChecks++;
       if(rad<=4*H&&rad>=threshold&&lateKey===null){lateKey=key;let g=lateGroups.get(key)||{n:0,small:0,w:0,sw:0};g.n+=s.ready.length;g.w+=w;if(s.refs.length<=kappa*n){g.small+=s.ready.length;g.sw+=w}lateGroups.set(key,g)}
       if(rad<=4*H&&rad%(2*x.p)!==0){ok(!seen.has(x.p),"record distinct");seen.add(x.p);logBudget+=Math.log(x.p);z.recordChecks++;let partnerN=0,partnerW=0;for(let t of a)if(t.ready.length&&(t.v-s.v)%rad===0&&(t.v-s.v)%(2*x.p)!==0){partnerN+=t.ready.length;partnerW+=t.ready.reduce((v,f)=>v+weights.get(f)[sector],0)}
        z.modularUpper+=(w*partnerN+s.ready.length*partnerW)/n;
       }
       rad=lcm(rad,2*x.p);seq+=","+x.p+":"+x.w;
      }
      ok(logBudget<=Math.log(4*H/root.rad)+Math.log(B)+1e-7,"log record budget");z.budgetChecks++;z.recordWeight+=w*logBudget;z.budgetWeight+=w*(Math.log(4*H/root.rad)+Math.log(B));
     }
     for(let g of lateGroups.values()){let capSlots=1+Math.floor(4*H/threshold);ok(g.small<=capSlots*kappa*n+1e-7,"late small packing");z.lateUpper+=(g.sw*g.n+g.w*g.small)/n;z.lateGroups++}
     z.arithmeticGroups+=arithmetic.size;
     for(let s of a)if(s.ready.length){let e=s.ready[0],i=e.i+1,node=root;node.slots.push(s);while(e.tag.es[i-1].J-e.J<L){let x=e.tag.es[i++],key=x.p+":"+x.w,ch=node.children.get(key);if(!ch){ch={C:x.J,p:x.p,w:x.w,slots:[],children:new Map(),rad:lcm(node.rad,2*x.p)};node.children.set(key,ch)}ch.slots.push(s);node=ch}}
     let stopMass=0,stopSq=0,stopCharge=0,stopSame=0,theta0=.25;
     const mass=node=>node.slots.reduce((v,s)=>v+s.ready.length,0);
     function stop(b){stopMass+=b;stopSq+=b*b;z.stopGroups++}
     function traverse(node,stopped=false){let bm=mass(node),nodeSmall=bm<=theta0*n;
      if(!stopped&&nodeSmall)stop(bm);let covered=stopped||nodeSmall;
      if(node.children.size){let key=node.C+"|"+node.rad+"|"+(node.rad>4*H?node.slots[0].v:mod(node.slots[0].v,node.rad)),g=arithmetic.get(key);ok(g&&g.slots.length===node.slots.length&&node.slots.every(s=>g.slots.includes(s)),"exact arithmetic node");}
      if(node.slots.length>1){let v=node.slots[0].v;for(let s of node.slots){ok(node.rad>4*H?s.v===v:(s.v-v)%node.rad===0,"prefix radical");z.radicalChecks++}}
      let ch=[...node.children.values()],labels=new Map();
      for(let x of ch)labels.set(x.p,(labels.get(x.p)||0)+mass(x));
      if(!covered)for(let b0 of labels.values())if(b0<=theta0*n)stop(b0);
      if(ch.length>1){z.forwardNodes++;for(let x of ch)for(let y of ch){if(x===y)continue;let wx=0,ny=0,rx=new Map(),ry=new Map();for(let s of x.slots){let w=s.ready.reduce((v,e)=>v+weights.get(e)[sector],0);wx+=w;add(rx,mod(s.v,2*x.p),w)}for(let s of y.slots){ny+=s.ready.length;add(ry,mod(s.v,2*x.p),s.ready.length)}
       z.exactForward+=wx*ny/n;if(x.p===y.p?labels.get(x.p)<=theta0*n:nodeSmall){stopCharge+=wx*ny/n;if(x.p===y.p)stopSame+=wx*ny/n}
       if(node.rad>=threshold){z.late+=wx*ny/n;let v=0;for(let s of x.slots)for(let t of y.slots)if(s.refs.length<=kappa*n||t.refs.length<=kappa*n)v+=s.ready.reduce((w,e)=>w+weights.get(e)[sector],0)*t.ready.length/n;z.lateSmall+=v;z.lateSmallChecks++}
       let equal=0;for(let [r,w] of rx)equal+=w*(ry.get(r)||0);let total=wx*ny;ok(equal<=total+1e-7,"residue count");if(node.rad<=4*H&&node.rad%(2*x.p)===0)ok(eq(equal,total),"periodic child");if(node.rad<=4*H&&node.rad%(2*y.p)===0&&node.rad%(2*x.p)===0)throw Error("two periodic children");
       if(node.C%10===0){z.treeForward+=total/n;z.treeLabel+=((x.p%3===1?total-equal:0)+(y.p%3===1?equal:0))/n}z.childPairs++;
      }}for(let x of ch)traverse(x,covered||labels.get(x.p)<=theta0*n)}
     traverse(root);ok(stopMass<=mass(root)&&stopSq<=theta0*n*stopMass+1e-7&&stopCharge<=cap*stopSq/n+1e-7&&cap*stopSq/n<=theta0*cap*mass(root)+1e-7,"disjoint first small prefix groups");z.stopChecks++;z.stopMass+=stopMass;z.stopCharge+=stopCharge;z.stopSame+=stopSame;z.stopBound+=cap*stopSq/n;z.stopBudget+=theta0*cap*mass(root);
    }
    // At every source physical slot, pool actual earlier episodes by arrival time.
    for(let s of a){if(s.refs.length<cut)continue;let A=long.get(s.wl)||0;if(!A)continue;let ep=new Map();for(let f of s.refs){for(let i=0;i<f.i;i++){let x=f.tag.es[i];if(x.C>o.C-2||x.C%10!==0)continue;let m=ep.get(x.sl)||new Map();ep.set(x.sl,m);let g=m.get(x.t)||{b:0,w:0,bjump:0,wjump:0};m.set(x.t,g);g.b++;g.w+=W(f);if(i>0){g.bjump++;g.wjump+=W(f)}}}
     for(let m of ep.values()){let g=[...m].sort((a,b)=>a[0]-b[0]);z.backEpisodes++;let b=0,w=0,i=0;for(let j0=0;j0<g.length;j0++){while(i<j0&&g[j0][0]-g[i][0]>R){b+=g[i][1].b;w+=g[i][1].w;i++}let t=g[j0][1];z.treeBack+=A/(n*s.refs.length)*(w*t.bjump+b*t.wjump);z.backGroupPairs+=i}}
    }
    const Bmask=new Map(),Dmask=new Map(),Bcount=new Map(),Dword=new Map();let Dtotal=0;
    for(let s of a)for(let f of s.refs){let b=f.tag.es.slice(0,f.i).some(x=>x.C<=o.C-2&&x.C%10===0),d=f.tag.end-f.J>=Ll&&f.tag.es.slice(f.i+1).some(x=>x.C<f.J+Ll&&x.C%10===0);Bmask.set(f,b);Dmask.set(f,d);if(b)add(Bcount,s,1);if(d){Dtotal++;add(Dword,s.wl,1)}}
    for(let s of a)for(let e of s.ready){let l=e.lo[j],h=e.hi[j],mass=short.get(s.wh);if(h&&mass!==s.ready.length){z.highPaid+=h;h=0}e.rw[j]=[l,h];let w=l+h;if(!w)continue;ok(w<=cap,"row clock");let A=long.get(s.wl);if(h)ok(A===s.ready.length,"positive high singleton nested");if(Bmask.get(e)||Dmask.get(e))z.unionBound+=w;
     z.intersectionBound+=w*((Bmask.get(e)?A/n*(Bcount.get(s)||0)/s.refs.length:0)+(Dmask.get(e)?(Dtotal-(Dword.get(s.wl)||0))/n:0));
     z.source+=w;z.unstable+=w*(n-stable)/n;rows.set(e,w);live.push(e);
     for(let t of a){if(!t.ready.length)continue;if(h){ok((s.wh===t.wh)===(s.wl===t.wl),"common forward kernel");z.kernelChecks++}
      if(s.wl===t.wl)continue;
      let q=w/n;for(let f of t.ready){add(cols,f,q);add(dc,f,q);z.forward+=q}
      // Long/short actual first defect comparison for each positive row sector.
      for(let [weight,L] of [[l,Ll],[h,Lh]])if(weight){let x=e.tag.es,y=t.ready[0].tag.es,i=e.i+1,b=t.ready[0].i+1,lag=t.v-s.v,found=false;while(x[i-1].J-e.J<L){let u=x[i],v=y[b];ok(u&&v&&u.C===v.C&&v.t-u.t===lag,"translated");if(u.p!==v.p||u.w!==v.w){ok(lag%(2*u.p)!==0||lag%(2*v.p)!==0,"nonperiodic");if(u.C%10===0){ok(Dmask.get(e)&&t.ready.every(f=>Dmask.get(f)),"defect target intersection");let amount=weight*t.ready.length/n;z.targetActual+=amount;z.targetForward+=amount;let chosen=lag%(2*u.p)!==0?u:v;if(chosen.p%3===1)z.labelForward+=amount;z.targetChecks++;}let sector=L===Ll?0:1,side=lag%(2*u.p)!==0?0:1;
       const p=side===0?u.p:v.p,q=side===0?v.p:u.p,amount=weight*t.ready.length/n;
       if(sector===1){
         let f=x[i];ok(f.C===u.C&&e.i<i&&f.C-e.J<Lh,"actual focal event");
         f.focalHigh[j]+=amount;let band=e.p>=2*P?(e.p<=Q?1:2):0;f.band[j][band]+=amount;z[['bandNonself','bandMid','bandTop'][band]]+=amount;if(band){ok(e.p>=Y&&e.w>=eps*(e.p-1)&&weight===e.w&&e.r>=eps*(e.p-1)/2,'self rough');for(let ff of t.ready){let d=ff.tag.es[ff.i+b-t.ready[0].i];ok(d.C===f.C&&ff.p===e.p&&ff.C===e.C&&ff.r===e.r,'partner source rough');d.partnerBand[j][band-1]+=weight/n;let map=d.partnerSrc[j],k0=ff.i;map.set(k0,(map.get(k0)||0)+weight/n);z[band===1?'partnerMid':'partnerTop']+=weight/n;z.partnerChecks++;}}let m=f.focalSources[j];m.set(e.i,(m.get(e.i)||0)+amount);
         z.highFocalClock+=amount;if(side===0)z.highFocalChosen+=amount;else z.highFocalOpposite+=amount;
         z.highFocalChecks++;
       }
       if(p===q){ok(u.w!==v.w&&(v.w-u.w)%2===0&&(lag+v.w-u.w)%(2*p)===0&&Math.abs(v.w-u.w)<2*u.r,"same label defect");z.sameWaitChecks++;z.sameCharge+=amount;
       let a0=x[i-1],b0=y[b-1],q0=a0.p;
       ok(q0===b0.p&&q0!==p&&a0.J===u.C&&b0.J===v.C&&a0.v===u.t&&b0.v===v.t,"common previous label");
       ok(lag%(2*q0)===0&&mod(u.t,6)===mod(v.t,6)&&lag%(2*p)!==0&&(u.C+2*(u.t%2))%q0===0&&(u.C%p===1||u.C%p===p-1),"predecessor CRT");z.predecessorChecks++;
       let d=Math.abs(lag),out=Math.abs(v.v-u.v);
       if(!out){z.sameMerge+=amount;let later=u.t>v.t?u:v,earlier=u.t>v.t?v:u;
        ok(earlier.t<later.t&&later.t<earlier.v,"overlap");
        let key=u.C+"|"+later.t+"|"+q0;merges.set(key,{E:u.C,t:later.t,q:q0,p});z.mergeChecks++;
       }else{ok(out%(2*p)===0&&(v.v-u.v)*lag>0&&Math.abs(out-d)<2*u.r&&Math.max(u.t,v.t)>=Math.min(u.v,v.v),"noncolliding intervals");
        if(d<2*p)ok(out===2*p&&d>2*p-2*u.r,"short lag obstruction");z.shortLagChecks++;
        z.sameSeparate+=amount;let key=u.C+"|"+p+"|"+q0+"|"+mod(u.t,6),g=sameKeys.get(key)||{E:u.C,p,q:q0,phase:mod(u.t,6),load:Ps.map(()=>[0,0])};sameKeys.set(key,g);g.load[j][sector]+=amount;
       }}
       else{let key=u.C+"|"+p+"|"+q,g=pairs.get(key)||{E:u.C,p,q,load:Ps.map(()=>[0,0])};pairs.set(key,g);g.load[j][sector]+=amount;z.distinctCharge+=amount;
       for(let [f,di] of [[e,i],...t.ready.map(f=>[f,f.i+b-t.ready[0].i])]){let d=f.tag.es[di],rad=6;ok(d.C===u.C,"paired actual event");for(let ii=f.i;ii<di;ii++){let rr=f.tag.es[ii].p;ok(rr!==p&&lag%(2*rr)===0,"bilateral suffix");}z.pairRouteChecks++}}
       
       for(let f of side===0?[e]:t.ready){let dest=f.tag.es[f.i+(side===0?i-e.i:b-t.ready[0].i)];ok(dest.p===(side===0?u.p:v.p)&&dest.C===u.C,"actual renewal destination");ok(dest.prevP<f.i,"first occurrence after source");ok(dest.C-f.C<=dest.radGap,"backward radical gap");if(dest.prevP>=0)ok(f.tag.es[dest.prevP].J<=f.C,"renewal left endpoint");dest.load[j][sector]+=side===0?weight*t.ready.length/n:weight/n;z.renewalChecks++}
       found=true;break}i++;b++}ok(found,"word defect");z.defectChecks++}
     }
     const bw=w*A/n/s.refs.length;for(let f of s.refs){add(cols,f,bw);add(bc,f,bw);z.back+=bw;if(f===e){z.diag+=bw;continue}if(s.refs.length<cut){z.small+=bw;continue}let b=birth(e,f);if(o.C-b.J<2){z.recent+=bw;continue}if(b.h>R&&b.later.i>0){z.long+=bw;z.longPairs++;if(b.J%10===0){ok(Bmask.get(e)&&Bmask.get(f),"birth target intersection");z.targetActual+=bw;z.targetBack+=bw;z.targetChecks++;}let slot=b.x.sl,ep=episodes.get(slot)||{slot,charge:[0,0,0]};episodes.set(slot,ep);ep.charge[j]+=bw;}else z.other+=bw}
    }
    for(let s of a)for(let f of s.refs){let v=cols.get(f)||0,b=bc.get(f)||0,d=dc.get(f)||0;ok(eq(v,b+d)&&v<=cap+1e-7,"combined column");if(v){z.columns++;z.jointCap+=cap;z.separateCap+=cap*((b>0?1:0)+(d>0?1:0))}}
    z.rows+=rows.size;
   }
  }
 }
 for(let ep of episodes.values()){let sl=ep.slot,J=sl.o.C,groups=new Map();for(let e of sl.refs){let a=groups.get(e.t)||[];a.push(2*e.tag.M-2+H);groups.set(e.t,a)}let g=[...groups].sort((a,b)=>a[0]-b[0]);
  for(let j=0;j<Ps.length;j++){let charge=ep.charge[j];if(!charge)continue;let z=stats[j],P=Ps[j],sum=0,old=0;
   for(let K=P*Math.ceil(J/P);K<J+H;K+=P){let a=g.map(([t,v])=>[t,v.filter(x=>x>K).length]),L=a.reduce((v,x)=>v+x[1],0);if(!L)continue;let pair=0,old0=0,max=0;for(let i=0;i<a.length;i++){let q=0;for(let k=i;k<a.length&&a[k][0]-a[i][0]<=R;k++)q+=a[k][1];max=Math.max(max,q);for(let k=i+1;k<a.length;k++)if(a[k][0]-a[i][0]>R){pair+=a[i][1]*a[k][1];old0+=a[i][1]*a[k][1]/Math.max(cut,a[i][1]+a[k][1])}}
    let out=L-max,env=Math.min(pair/cut,L/2,out-out*out/(2*L),old0);sum+=2*c*P*env;old+=2*c*P*old0;
   }ok(charge<=sum+1e-7&&sum<=old+1e-7,"episode envelope");z.episodes++;z.envelope+=sum;z.oldPairEnvelope+=old;
  }
 }
 for(let tag of paths)for(let e of tag.es)for(let j=0;j<Ps.length;j++)for(let s=0;s<2;s++){let load=e.load[j][s];if(!load)continue;let L=s?Lh:Ll,left=e.prevP<0?2*tag.M-2:tag.es[e.prevP].J,gap=e.C-left,old=2*c*(L+B+Ps[j]),nw=2*c*(Math.min(L+B,gap)+Ps[j]);ok(gap>=0&&load<=nw+1e-7,"renewal capacity");let rw=2*c*(Math.min(L+B,e.radGap)+Ps[j]);ok(load<=rw+1e-7&&rw<=nw+1e-7,"radical cap");let z=stats[j];z.radicalCapChecks++;z.radicalCapSum+=rw;if(rw<nw)z.radicalImproved++;z.renewalCapChecks++;if(nw<old)z.renewalImproved++;z.renewalOldCap+=old;z.renewalNewCap+=nw;z.renewalLoad+=load}
 for(let j=0;j<Ps.length;j++){
 const P=Ps[j],z=stats[j],keys=new Set();let sum=0;
 for(let tag of paths){let a=tag.es;for(let e of a){let load=e.focalHigh[j];if(!load)continue;keys.add(e.C+"|"+e.p);sum+=load;
   let rad=6,start=e.i,weights=0,labels=new Map(),raw=0,earliest=-1;
   for(let i=e.i-1;i>=0;i--){let f=a[i];if(e.C-f.J>=Lh)break;if(rad%f.p)rad*=f.p;if(rad>4*H)break;start=i;
     let nk=Math.ceil(f.J/P)-Math.ceil(f.C/P);if(nk){weights+=f.rw[j][1];raw+=c*P*nk;earliest=i}
   }
   ok(earliest>=0,"accepted source");
   let assigned=0;for(let [i,v] of e.focalSources[j]){ok(i>=start&&i<e.i&&v<=a[i].rw[j][1]+1e-7,"one focal row per source");assigned+=v;z.highSourceChecks++}
   ok(eq(assigned,load)&&load<=weights+1e-7&&weights<=raw+1e-7,"focal row capacity");
   let first=a[start].C,inside=0;for(let i=start;i<e.i;i++){let f=a[i];if(f.p<Y)continue;inside+=f.w;labels.set(f.p,(labels.get(f.p)||0)+f.w);ok(rad%f.p===0,"label in suffix radical");z.highLabelChecks++}
   let edge=0;for(let i=start-1;i>=0;i--){let f=a[i],nk=Math.ceil(f.J/P)-Math.ceil(f.C/P);if(nk)break;edge+=f.w}
   ok(edge<=3*P+1e-7&&weights<=inside+edge+1e-7,"high wait suffix plus cell fringe");
   ok(labels.size<=Math.log(4*H)/Math.log(Y)+1e-7&&eq([...labels.values()].reduce((v,x)=>v+x,0),inside),"high label count");
   let old=c*(Lh+B+P);ok(raw<=old+1e-7,"old one-role grid capacity");
   z.highRawCap+=old;z.highSuffixCap+=inside+edge;z.highActualCap+=Math.min(weights,old);if(weights<old)z.highImproved++;z.highSuffixChecks++;
 }}
 z.highKeys=keys.size;ok(eq(sum,z.highFocalClock)&&eq(sum,z.highFocalChosen+z.highFocalOpposite),"high focal conservation");
 }
 for(let j=0;j<Ps.length;j++){
  const P=Ps[j],z=stats[j];let fsum=[0,0,0],psum=[0,0];
  for(let tag of paths)for(let e of tag.es){let fb=e.band[j],pb=e.partnerBand[j];if(!fb.some(Boolean)&&!pb.some(Boolean))continue;
   let a=tag.es,rad=6,start=e.i,caps=[0,0,0],pcaps=[0,0],clock=0,nonselfInside=0;
   for(let i=e.i-1;i>=0;i--){let x=a[i];if(e.C-x.J>=Lh)break;if(rad%x.p)rad*=x.p;if(rad>4*H)break;start=i;
    let nk=Math.ceil(x.J/P)-Math.ceil(x.C/P);if(nk){let k=x.p>=2*P?(x.p<=Q?1:2):0;caps[k]+=x.rw[j][1];
      if(k&&x.p>=Y&&x.r>=eps*(x.p-1)/2)pcaps[k-1]+=2*x.p;
    }
    if(x.p>=Y&&x.p<=P/2&&x.w>=eps*(x.p-1))nonselfInside+=x.w;
   }
   let fringe=0;for(let i=start-1;i>=0;i--){let x=a[i];if(Math.ceil(x.J/P)>Math.ceil(x.C/P))break;fringe+=x.w;}
   ok(caps[0]<=nonselfInside+fringe+1e-7&&fringe<=3*P+1e-7,"nonself high clock fringe");z.bandFringeChecks++;
   for(let [i,load] of e.partnerSrc[j]){let x=a[i];ok(i>=start&&x.p>=2*P&&x.p>=Y&&x.r>=eps*(x.p-1)/2&&load<=2*x.p+1e-7,"partner one-column rough-source cap");z.partnerRows++}
   for(let k=0;k<3;k++){ok(fb[k]<=caps[k]+1e-7,"focal band cap");fsum[k]+=fb[k];if(fb[k]){z[['bandCapNonself','bandCapMid','bandCapTop'][k]]+=caps[k];z.bandChecks++}}
   for(let k=0;k<2;k++){ok(pb[k]<=pcaps[k]+1e-7,"partner band cap");psum[k]+=pb[k];if(pb[k])z[k?'partnerCapTop':'partnerCapMid']+=pcaps[k]}
  }
  ok(eq(fsum[0],z.bandNonself)&&eq(fsum[1],z.bandMid)&&eq(fsum[2],z.bandTop)&&eq(fsum.reduce((a,b)=>a+b,0),z.highFocalClock)&&eq(psum[0],fsum[1])&&eq(psum[1],fsum[2]),"band conservation");
 }
 function gap(e,p){let rad=6,g=0;for(let i=e.i-1;i>=0;i--){let x=e.tag.es[i];if(x.p===p)break;if(rad%x.p)rad*=x.p;if(rad>4*H)break;g=e.C-x.C}return g}
 for(let pair of pairs.values()){let a=proj.get(pair.E+"|"+pair.p),b=proj.get(pair.E+"|"+pair.q);ok(a&&b,"paired projected keys");
  for(let j=0;j<Ps.length;j++)for(let s=0;s<2;s++){let w=pair.load[j][s];if(!w)continue;let P=Ps[j],L=s?Lh:Ll,cap=o=>[...o.slots.values()].reduce((v,sl)=>v+sl.refs.reduce((t,e)=>t+2*c*(Math.min(gap(e,pair.p),L+B)+P),0),0),a0=cap(a),b0=cap(b),z=stats[j];ok(w<=Math.min(a0,b0)+1e-7,"bilateral cap");z.pairKeyChecks++;z.pairedCap+=Math.min(a0,b0);z.chosenCap+=a0;if(b0<a0)z.pairedImproved++;}
 }
 let mergeMassChecks=0;
 for(let m of merges.values()){let o=proj.get(m.E+"|"+m.p),j=proj.get((m.E-m.q+1)+"|"+m.q)?.slots.get(m.t);ok(j&&j.refs.length>0,"actual incoming jump group");
  let wait=0;for(let sl of o.slots.values())for(let e of sl.refs)if(e.t<m.t&&m.t<e.v)wait++;
  ok(wait>0,"actual waiting branch");let n=wait+j.refs.length;ok(Math.max(Math.log(n/wait),Math.log(n/j.refs.length))>=Math.log(2)-1e-12,"merge entropy lower bound");mergeMassChecks++}
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}
 for(let g of sameKeys.values()){let o=proj.get(g.E+"|"+g.p),fs=[...o.slots.values()].flatMap(s=>s.refs).filter(e=>e.i>0&&e.tag.es[e.i-1].p===g.q&&mod(e.t,6)===g.phase),times=new Map();
  for(let e of fs){let a=times.get(e.w)||new Set();a.add(e.t);times.set(e.w,a)}
  let period=6*(2*g.p)/gcd(6,2*g.p);period=period*(2*g.q)/gcd(period,2*g.q);
  for(let a of times.values()){let v=[...a].sort((a,b)=>a-b);ok(v.every(t=>(t-v[0])%period===0)&&v.length<=1+Math.floor(4*H/period),"time CRT count")}
  for(let j=0;j<Ps.length;j++)for(let s=0;s<2;s++){let w=g.load[j][s];if(!w)continue;let P=Ps[j],L=s?Lh:Ll,z=stats[j],total=0,wait=new Map(),exit=new Map();for(let e of fs){let c0=2*c*(Math.min(e.radGap,L+B)+P);total+=c0;wait.set(e.w,(wait.get(e.w)||0)+c0);exit.set(e.v,(exit.get(e.v)||0)+c0)}
   let cap=total-Math.max(0,...wait.values(),...exit.values());ok(w<=cap+1e-7,"minority cover");z.coverChecks++;z.coverFull+=total;z.coverMinority+=cap;if(cap<total)z.coverImproved++;z.timeChecks+=times.size;
   const groups=new Map(),add=(m,k,b,w)=>{let v=m.get(k)||[0,0];v[0]+=b;v[1]+=w;m.set(k,v)};
   for(let e of fs){let seq="",rad=6;for(let i=e.i-1;i>=0;i--){let a=e.tag.es[i];if(g.E-a.J>=L||a.p===g.p)break;if(rad%a.p)rad*=a.p;if(rad>4*H)break;
     let nk=Math.ceil(a.J/P)-Math.ceil(a.C/P);if(nk){let phase=mod(a.v,6),key=a.C+"|"+a.p+"|"+phase+"|"+seq,G=groups.get(key);
       if(!G){let n=[...a.sl.o.slots.values()].filter(sl=>mod(sl.v,6)===phase).reduce((v,sl)=>v+sl.refs.length,0);G={n,nk,B:0,ready:0,W:0,wait:new Map(),exit:new Map(),joint:new Map(),waitR:new Map(),exitR:new Map(),jointR:new Map()};groups.set(key,G)}
       ok(G.nk===nk,"common source atoms");G.B++;add(G.wait,e.w,1,0);add(G.exit,e.v,1,0);add(G.joint,e.w+"|"+e.v,1,0);
       if(a.tag.end-a.J>=Ll){let weight=a.rw[j][s];G.ready++;G.W+=weight;add(G.waitR,e.w,1,weight);add(G.exitR,e.v,1,weight);add(G.jointR,e.w+"|"+e.v,1,weight)}
       z.reverseSlotChecks++;
     }seq=a.p+":"+a.w+","+seq;
   }}
   let exact=0,raw=0,pool=0,half=0,localCover=0;
   const dot=m=>[...m.values()].reduce((v,[b,w])=>v+b*w,0),sq=m=>[...m.values()].reduce((v,[b])=>v+b*b,0),max=m=>Math.max(0,...[...m.values()].map(x=>x[0]));
   for(let G of groups.values()){let {n,nk,B,ready,W}=G;ok(B<=n&&ready<=B,"source group included in original class");
    let pairs=B*B-sq(G.wait)-sq(G.exit)+sq(G.joint),e0=W*ready-dot(G.waitR)-dot(G.exitR)+dot(G.jointR),k0=c*P*nk;
    ok(pairs>=0&&e0>=-1e-7,"nonnegative cut");let a=e0/n,b=k0*pairs/n,d=k0*pairs/B,h=k0*B,cv=2*k0*(B-Math.max(max(G.wait),max(G.exit)));
    ok(a<=b+1e-7&&b<=d+1e-7&&d<=h+1e-7&&d<=cv+1e-7,"quadratic pooled cut");exact+=a;raw+=b;pool+=d;half+=h;localCover+=cv;z.reverseGroups++;if(pairs)z.reversePositive++;
   }
   ok(eq(exact,w)&&raw<=pool+1e-7&&pool<=cap+1e-7&&pool<=total/2+1e-7,"reverse exact and improved cover");z.reverseExact+=exact;z.reverseRaw+=raw;z.reversePool+=pool;z.reverseHalf+=half;z.reverseCover+=localCover;z.reverseChecks++;
  }
 }
 for(let z of stats){ok(eq(z.reverseExact,z.sameSeparate),"reverse global conservation");ok(eq(z.sameCharge,z.sameMerge+z.sameSeparate),"same-label split");ok(eq(z.distinctCharge+z.sameCharge,z.forward),"pair charge conservation");ok(eq(z.exactForward,z.forward)&&z.forward<=z.modularUpper+1e-7&&z.modularUpper<=2*z.source+1e-7&&z.lateSmall<=z.lateUpper+1e-7&&z.recordWeight<=z.budgetWeight+1e-7,"global radical budget");ok(eq(z.renewalLoad,z.forward),"renewal conservation");ok(eq(z.treeBack,z.targetBack)&&eq(z.treeForward,z.targetForward)&&eq(z.treeLabel,z.labelForward),"exact tree cut targets");ok(z.treeBack+z.treeLabel<=z.targetActual+1e-7,"refined label bound");ok(z.targetActual<=z.intersectionBound+1e-7&&z.intersectionBound<=z.unionBound+1e-7&&eq(z.targetActual,z.targetBack+z.targetForward),"joint target cover");ok(eq(z.source,z.back+z.forward+z.unstable)&&eq(z.back,z.diag+z.recent+z.small+z.long+z.other),"partition");for(let k of Object.keys(z))if(typeof z[k]==="number")z[k]=+z[k].toFixed(6)}
 return {X,focus,B,T,Ll,Lh,N,W,events,hit,cellChecks,excessChecks,smallCells,largeCells,cellOld,cellNew,pairKeys:pairs.size,sameKeys:sameKeys.size,mergeKeys:merges.size,mergeMassChecks,birthCache:birthCache.size,stats};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
