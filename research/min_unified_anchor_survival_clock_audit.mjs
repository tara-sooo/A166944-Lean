// True birth and monotone anchor survival clock ledger.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},near=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(x,m)=>(x%m+m)%m;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let res=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,age=Math.max(4,Math.floor(B/16)),h=age,b0=2,tags=[],slots=new Map(),plate=new Map(),events=0,terminal=0,allWait=0,allGain=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let id=tags.length,C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let z=C-1+2*I;while(z>1){let f=spf[z];while(z%f===0)z/=f;if(f*f>C+1)continue;let v=mod((I?f+2:0)-t,2*f)||2*f;if(v<w||v===w&&f<p){p=f;w=v}}}if(!p)break;
    let n=t+w,J=C+p-1,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;if(!slots.has(key))slots.set(key,{C,J,p,n,ids:[]});let s=slots.get(key);s.ids.push(id);
    path.push({C,J,t,n,d,dp,w,g:p-1,s});allWait+=w;allGain+=p-1;events++;C=J;t=n;
   }
   for(let j=0;j<=path.length;j++){let e=path[j],v={id,a:e?e.t:t,b:e?e.n-1:t,br:j?"p"+path[j-1].s.p:"root",C:e?e.C:C};if(!plate.has(v.C))plate.set(v.C,[]);plate.get(v.C).push(v)}
   terminal+=2*t-C;tags.push({id,C0,F:C,df:2*t-C,path})
  }
  ok(2*allWait===allGain+terminal-6*tags.length,"terminal clock");
  let births=0,pairs=0,eligible=0,anchors=0,anchorGains=0,retireSteps=0,strictCredit=0,actualClock=0,birthClock=0,anchorClock=0,horizon=0,startDebit=0,endCredit=0,retirementDebit=0,sparseBirths=0,sparseClock=0,attachClock=0,maxBirth=0,slabChecks=0,slabD=Math.max(8,Math.floor(B/8)),historyChecks=0,seen=new Set();
  function at(path,x){let e=path.find(e=>e.C<=x&&x<e.J);if(!e)e=path.find(e=>e.J===x);ok(e,"path at "+x);return e}
  function d(path,x){let e=at(path,x);return e.d+(x-e.C)*(e.dp-e.d)/e.g}
  function ledger(path,a,b,ids){
   let cuts=[a,b,...ids.map(i=>tags[i].F).filter(x=>a<x&&x<b),...path.map(e=>e.J).filter(x=>a<x&&x<b)].sort((x,y)=>x-y);cuts=[...new Set(cuts)];
   let U=0,W=0,R=0,actual=0,steps=0,old=null;
   const f=x=>1/Math.max(b0,ids.filter(i=>tags[i].F>x).length);
   for(let k=0;k+1<cuts.length;k++){let l=cuts[k],r=cuts[k+1],q=(l+r)/2,z=f(q),e=at(path,q);ok(ids.filter(i=>tags[i].F>q).every(i=>e.s.ids.includes(i)),"anchor descendants");
    if(old!==null){ok(z>=old-1e-10,"monotone reciprocal");if(z>old+1e-10){R+=d(path,l)*(z-old);steps++}}
    old=z;U+=(r-l)*z;W+=(r-l)*z*e.w/e.g;actual+=(r-l)*e.w/e.g/Math.max(b0,e.s.ids.length);
   }
   let A=d(path,a)*f(a),Z=d(path,b)*f((cuts.at(-2)+b)/2);
   ok(near(2*W,U+Z-A-R),"Stieltjes ledger");ok(W+1e-8>=actual&&R>=0,"clock upper");return {U,W,R,A,Z,actual,steps}
  }
  for(let [J,rows] of plate){let starts=[...new Set(rows.map(r=>r.a))].sort((a,b)=>a-b);
   for(let t of starts){let alive=rows.filter(r=>r.a<=t&&t<=r.b),groups=new Map();
    for(let v of alive){let br=v.a===t?v.br:"wait";if(!groups.has(br))groups.set(br,[]);groups.get(br).push(v.id)}
    if(groups.size<2)continue;births++;maxBirth=Math.max(maxBirth,alive.length);
    let ids=alive.map(r=>r.id),G=[...groups.values()],rep=tags[ids.reduce((i,j)=>tags[i].F>=tags[j].F?i:j)],e=rep.path.find(e=>e.C===J&&e.t<=t&&t<e.n);
    for(let k=0;k<G.length;k++)for(let l=k+1;l<G.length;l++)for(let i of G[k])for(let j of G[l]){let key=Math.min(i,j)+"/"+Math.max(i,j);ok(!seen.has(key),"unique true birth");seen.add(key);pairs++;
     if(!e)continue;
     let a=e.J+age,b=Math.min(tags[i].F,tags[j].F)-h;if(b<=a)continue;eligible++;
     let anc=at(rep.path,e.J+age/2),A=anc.J;if(A>a)A=e.J;
     let anchorEvent=rep.path.find(z=>z.J===A);ok(anchorEvent&&A<=a,"actual anchor");
     let ai=anchorEvent.s.ids;ok(ids.filter(id=>tags[id].F>A).every(id=>ai.includes(id)),"anchor contains living birth");
     let raw=ledger(rep.path,a,b,ids),an=ledger(rep.path,a,b,ai);ok(an.W<=raw.W+1e-8&&near(an.actual,raw.actual),"anchor improves");
     if(an.W<raw.W-1e-8)anchorGains++;anchors++;retireSteps+=an.steps;if(an.R>1e-8)strictCredit++;
     birthClock+=2*raw.W;anchorClock+=2*an.W;actualClock+=2*an.actual;horizon+=2*an.U;startDebit+=2*an.A;endCredit+=2*an.Z;retirementDebit+=2*an.R;
     let s=0;for(let x=a;x<b;){let y=Math.min(b,(Math.floor(x/slabD)+1)*slabD);s+=ledger(rep.path,x,y,ai).W;x=y;slabChecks++}ok(near(s,an.W),"across slab conservation");
     // finite relative group threshold, not actual retirement-preserving historical mass.
     if(G[k].length>=3&&G[l].length>=3){sparseClock+=2*an.W;sparseBirths++}else if(Math.max(G[k].length,G[l].length)>=3)attachClock+=2*an.W;
    }
   }
  }
  ok(near(2*anchorClock,horizon+endCredit-startDebit-retirementDebit),"aggregate exact signed balance");
  res.push({X,focus,N:tags.length,events,allGain,allWait,terminal,births,pairs,eligible,anchors,anchorGains,retireSteps,strictCredit,actualClock,birthClock,anchorClock,horizon,startDebit,endCredit,retirementDebit,sparseBirths,sparseClock,attachClock,maxBirth,slabChecks});
 }
 return res
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
