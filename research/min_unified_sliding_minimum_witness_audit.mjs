// Piecewise-linear forward-minimum signed drift audit; midpoint witness samples are finite diagnostics only.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(x,m)=>(x%m+m)%m,near=(a,b)=>Math.abs(a-b)<=1e-6*Math.max(1,Math.abs(a),Math.abs(b));
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let k=p;k<=lim;k+=p)spf[k]=p;
 function smooth(path,z,cut){
  if(!path.length)return [];
  let lo=path[0].C,hi=path.at(-1).J-z;if(hi<=lo)return [];
  let knots=[...path.map(e=>e.C),path.at(-1).J],vals=[...path.map(e=>e.d),path.at(-1).dp];
  function ix(x){let a=0,b=path.length;while(a+1<b){let m=(a+b)>>1;if(knots[m]<=x)a=m;else b=m}return a}
  function d(x){let e=path[ix(x)];return e.d+(x-e.C)*e.slope}
  let breaks=[...new Set([lo,hi,...knots,...knots.map(k=>k-z)].filter(x=>lo<=x&&x<=hi))].sort((a,b)=>a-b),out=[];
  for(let k=0;k+1<breaks.length;k++){let a=breaks[k],b=breaks[k+1],mid=(a+b)/2,el=path[ix(mid)],er=path[ix(mid+z)],lines=[{s:el.slope,v:d(a),kind:"left"},{s:er.slope,v:d(a+z),kind:"right"}];
   let mv=Infinity;for(let j=0;j<knots.length;j++)if(mid<knots[j]&&knots[j]<mid+z)mv=Math.min(mv,vals[j]);if(mv<Infinity)lines.push({s:0,v:mv,kind:"inside"});
   let br=[a,b];for(let i=0;i<lines.length;i++){let x=lines[i];if(x.s){let t=a+(cut-x.v)/x.s;if(a<t&&t<b)br.push(t)}for(let j=i+1;j<lines.length;j++){let y=lines[j];if(x.s!==y.s){let t=a+(y.v-x.v)/(x.s-y.s);if(a<t&&t<b)br.push(t)}}}br.sort((a,b)=>a-b);
   for(let j=0;j+1<br.length;j++){let l=br[j],r=br[j+1];if(r-l<1e-9)continue;let q=(l+r)/2,v=x=>x.v+x.s*(q-a),line=lines.reduce((m,x)=>v(x)<v(m)?x:m),s=v(line)>cut?line.s:0,L=Math.max(0,line.v+line.s*(l-a)-cut),R=Math.max(0,line.v+line.s*(r-a)-cut);
    ok(near(R-L,s*(r-l)),"linear envelope");let m=Math.min(d(q),d(q+z),...knots.map((t,i)=>q<t&&t<q+z?vals[i]:Infinity));
    ok(near(Math.max(0,m-cut),(L+R)/2),"direct min");ok(d(q)-m<=z+1e-7,"smoothing error");
    if(s>1e-9){ok(near(m,d(q))&&near(s,el.slope),"positive left contact");ok(d(q+z)>=d(q)-1e-7,"persistence")}
    out.push({l,r,L,R,s});
   }
  }return out
 }
 const results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),D=Math.max(12,Math.floor(T/4)),z=Math.max(4,Math.floor(D/8)),cut=Math.max(12,Math.floor(B/4)),P=6,paths=[],slots=new Map(),events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C=2*M-2,C0=C,t=M+2,path=[],id=paths.length;
   while(C-C0<T){let p=0,w=Infinity,I=0;for(let j=0;j<2;j++){let q=C-1+2*j;while(q>1){let f=spf[q];while(q%f===0)q/=f;if(f*f>C+1)continue;let v=mod((j?f+2:0)-t,2*f)||2*f;if(v<w||v===w&&f<p){p=f;w=v;I=j}}}if(!p)break;let g=p-1,J=C+g,n=t+w,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;
    if(!slots.has(key))slots.set(key,{key,C,J,p,n,ids:[],next:null});let s=slots.get(key);s.ids.push(id);ok(d>=0&&dp>=0&&w<=3*g,"MIN");path.push({C,J,p,w,t,n,d,dp,g,s,slope:(dp-d)/g});C=J;t=n;events++;
   }paths.push({id,C0,F:C,path})
  }
  for(let {path} of paths)for(let i=0;i+1<path.length;i++){let a=path[i].s,b=path[i+1].s;ok(!a.next||a.next===b,"successor");a.next=b}
  let variation=0;for(let a of slots.values())if(a.next){let b=a.next,r=a.ids.filter(i=>b.ids.includes(i)).length;variation+=r*(Math.log(a.ids.length/r)+Math.log(b.ids.length/r))}
  ok(variation<=paths.length*(Math.log(paths.length)+2)+1e-6,"variation budget");
  let segments=0,pos=0,neg=0,raw=0,smoothed=0,terminalPairs=0,intervals=0,sourceMass=0,witnessMass=0,unstableMass=0,maxTick=0,maxGrid=0,maxPairTick=0,maxPairGrid=0,positiveSamples=0,negativeSamples=0,rankTests=0;
  const all=paths.map(a=>smooth(a.path,z,cut));
  segments=all.reduce((s,a)=>s+a.length,0);
  const d=(path,x)=>{let e=path.find(e=>e.C<=x&&x<=e.J);return e.d+(x-e.C)*e.slope};
  // Actual endpoint sample with full denominator; pairs start at first common exit posthorizon.
  let samples=[],maxWitnessPair=0;
  for(let l=Math.floor((2*X-2)/D)*D;l<4*X+T+B;l+=D){let e=l+D;
   for(let s of slots.values())if(s.C<e&&e<=s.J&&s.ids.length>=2){let ids=s.ids.slice(0,8),den=s.ids.length;
    for(let i=0;i<ids.length;i++)for(let j=i+1;j<ids.length;j++){
     let A=paths[ids[i]],Q=paths[ids[j]],keys=new Set(Q.path.map(x=>x.s.key)),birth=A.path.find(x=>keys.has(x.s.key)),a=Math.max(l,birth.J),b=Math.min(e,A.F-z,Q.F-z);if(b<=a)continue;intervals++;
     let sum=0,positive=0,negative=0;
     for(let seg of all[A.id]){let L=Math.max(a,seg.l),R=Math.min(b,seg.r);if(R<=L)continue;let v=seg.s*(R-L);sum+=v;if(v>0)positive+=v;else negative-=v;
      // Midpoint quadrature only for witness diagnostics, not analytic integral of witness weights.
      if(v>1e-9){let x=(L+R)/2,src=A.path.find(f=>f.C<=x&&x<f.J);let w=A.path.filter(f=>f.C>=x&&f.J<=x+z&&4*f.w>=f.g),ticks=w.reduce((s,f)=>s+f.w,0),g0=Math.ceil(x/P)*P,gs=[];for(let k=g0;k<x+z;k+=P)gs.push(k);
       let end=d(A.path,x+z);ok(end>=d(A.path,x)-1e-6,"positive witness drift");let total=A.path.reduce((s,f)=>s+Math.max(0,Math.min(f.J,x+z)-Math.max(f.C,x))*f.w/f.g,0);
       ok(total>=z/2-1e-6,"half rate");positiveSamples++;
       // Finite z often shorter than event; also use clipped expensive clock, exact continuous test.
       let ex=A.path.reduce((s,f)=>s+(4*f.w>=f.g?Math.max(0,Math.min(f.J,x+z)-Math.max(f.C,x))*f.w/f.g:0),0);ok(ex>=z/4-1e-6,"expensive integral");
       if(ticks>=z/8&&gs.length>=z/(2*P)){let wgt=2*v/den;sourceMass+=wgt;
        let vstep=0,at=A.path.indexOf(src),endIndex=A.path.findIndex(f=>f.C<x+z&&x+z<=f.J);
        for(let k=at;k<endIndex;k++){let a=A.path[k].s,b=A.path[k+1].s,r=a.ids.filter(i=>b.ids.includes(i)).length;vstep+=Math.log(a.ids.length/r)+Math.log(b.ids.length/r)}
        if(vstep>.25){unstableMass+=wgt;continue}
        for(let f of w){ok(f.s.ids.includes(Q.id),"pair shares physical tick");maxPairTick=Math.max(maxPairTick,wgt/ticks*f.s.ids.length)}
        for(let K of gs){let f=A.path.find(e=>e.C<=K&&K<e.J);ok(f&&f.s.ids.includes(Q.id),"pair shares boundary");maxPairGrid=Math.max(maxPairGrid,wgt/gs.length*f.s.ids.length/P)}
        witnessMass+=wgt;
       }
      }else if(v< -1e-9)negativeSamples++;
     }
     let dr=Math.max(0,d(A.path,b)-cut)-Math.max(0,d(A.path,a)-cut);ok(Math.abs(dr-sum)<=2*z+1e-6,"endpoint error");raw+=2*dr/den;smoothed+=2*sum/den;pos+=2*positive/den;neg+=2*negative/den;if(b===A.F-z||b===Q.F-z)terminalPairs++;
    }
   }
  }
  ok(near(smoothed,pos-neg)&&near(sourceMass,witnessMass+unstableMass),"signed and route partition");
  results.push({X,focus,B,T,D,z,cut,N:paths.length,events,segments,intervals,terminalPairs,variation,raw,smoothed,pos,neg,positiveSamples,negativeSamples,sourceMass,witnessMass,unstableMass,maxPairTick,maxPairGrid});
 }
 // Synthetic exact piecewise-linear excursion control: temporary spike disappears, persistent rise survives.
 let P=[{C:0,J:8,d:0,dp:16,slope:2},{C:8,J:24,d:16,dp:0,slope:-1},{C:24,J:32,d:0,dp:16,slope:2},{C:32,J:64,d:16,dp:16,slope:0}],S=smooth(P,24,0);let first=S.filter(s=>s.l<24&&s.s>0).reduce((a,s)=>a+s.s*(Math.min(s.r,24)-s.l),0),later=S.filter(s=>s.l>=24&&s.s>0).reduce((a,s)=>a+s.s*(s.r-s.l),0);ok(first<1e-7&&near(later,16),"excursion control");
 return {results,synthetic:{first,later}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
