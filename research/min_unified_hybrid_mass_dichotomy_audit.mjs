// Actual common-suffix finite hybrid mass and two-branch witness controls.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(x,m)=>(x%m+m)%m,near=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 const lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1),pr=[];
 for(let p=2;p<=lim;p++)if(!spf[p]){pr.push(p);for(let k=p;k<=lim;k+=p)if(!spf[k])spf[k]=p}
 const odd=pr.filter(p=>p>2),prime=x=>x>=2&&spf[x]===x;
 const res=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,L=Math.max(16,Math.floor(B/2)),tags=[],slots=new Map(),events=0;
  for(let M=X|1;M<2*X;M+=2)if(prime(M)){let id=tags.length,C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity,I=0;for(let j=0;j<2;j++){let v=C-1+2*j;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((j?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r;I=j}}}if(!p)break;let g=p-1,J=C+g,n=t+w,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;
    if(!slots.has(key))slots.set(key,{key,C,J,p,n,rows:[],next:null});let slot=slots.get(key);slot.rows.push({id,index:path.length,d,dp,w});
    ok(d>=0&&dp>=0&&w<=3*g,"MIN");path.push({C,J,p,w,I,t,n,d,dp,g,slot});C=J;t=n;events++;
   }tags.push({id,C0,F:C,path})
  }
  for(let t of tags)for(let i=0;i+1<t.path.length;i++){let a=t.path[i].slot,b=t.path[i+1].slot;ok(!a.next||a.next===b,"successor");a.next=b}
  const vmap=new Map();let variation=0;
  for(let a of slots.values())if(a.next){let b=a.next,ids=new Set(b.rows.map(r=>r.id)),r=a.rows.filter(q=>ids.has(q.id)).length;let v=Math.log(a.rows.length/r)+Math.log(b.rows.length/r);vmap.set(a.key,v);variation+=r*v}
  ok(variation<=tags.length*(Math.log(tags.length)+2)+1e-6,"variation budget");
  for(let cfg of [{S:3,R:5,V:9,A:17},{S:5,R:7,V:25,A:37},{S:7,R:11,V:49,A:67}]){
   let {S,R,V,A}=cfg,small=odd.filter(p=>p<=S),mid=odd.filter(p=>S<p&&p<=R),extra=odd.filter(p=>R<p&&p<=V),PS=small.reduce((a,p)=>a*p,1),PR=PS*mid.reduce((a,p)=>a*p,1),lam=Math.ceil(PR**(4/11)),alpha=mid.reduce((a,p)=>a*(p-1)/(2*p),1/PS),Q=extra.reduce((a,p)=>a*(1-2/p),1);
   const jmax=Math.ceil((4*X+H)/2)+lam+3,isCut=j=>{let J=2*j;return j%PS===0&&mid.every(p=>{let r=mod(J,p);return r%2===0&&r<=p-3})&&extra.every(p=>{let r=mod(J,p);return r!==1&&r!==p-1})};
   let pre=new Float64Array(jmax+1);for(let j=0;j<jmax;j++)pre[j+1]=pre[j]+Number(isCut(j));
   const cnt=(a,b)=>pre[b]-pre[a];let l2=new Float64Array(jmax-lam+2);
   for(let j=0;j<jmax-lam+1;j++){let r=cnt(j,j+lam)/(alpha*lam)-Q;l2[j+1]=l2[j]+r*r}
   let controls=0,high=0,short=0,moderate=0,unclassified=0,cutChecks=0,strictTwin=0,cheap=0,rankChecks=0,allMass=0,highMass=0,shortMass=0,stableMass=0,unstableMass=0,maxRoleTick=0,maxRoleCut=0,maxPairTick=0,maxPairCut=0,maxProjectedHigh=0,maxProjectedShort=0,thinHigh=0,thinShort=0,thinModerate=0,richRaw=0,richShort=0,highG=0,highW=0;
   const roles=new Map(),pairs=new Map(),proj=new Map(),physical=new Map(),sourceKeys=new Set(),rankGroups=new Map();
   const add=(map,k,v)=>map.set(k,(map.get(k)||0)+v);
   function merge(ints){let a=[];for(let z of ints){if(a.length&&z[0]<=a.at(-1)[1])a.at(-1)[1]=Math.max(a.at(-1)[1],z[1]);else a.push(z.slice())}return a}
   for(let s of slots.values()){
    // Finite source: common poststate of an actual positive event. Select up to four
    // actual members sharing a persistent suffix through first gain crossing L.
    let rows=s.rows.filter(r=>r.dp>r.d&&tags[r.id].F>=s.J+L).slice(0,4);if(rows.length<2)continue;
    let t=tags[rows[0].id],a=s.J,block=[],G=0;
    for(let k=rows[0].index+1;k<t.path.length;k++){let f=t.path[k];block.push(f);G+=f.g;if(G>=L)break}
    if(G<L||block.some(f=>f.d<rows[0].dp||f.dp<rows[0].dp))continue;
    let b=block.at(-1).J;rows=rows.filter(r=>tags[r.id].F>=b);if(rows.length<2)continue;
    let al=a/2,be=b/2,n=G/2,raw=cnt(al,be),big=block.filter(f=>f.p>A),gBig=big.reduce((v,f)=>v+f.g,0),bigRaw=big.reduce((v,f)=>v+cnt(f.C/2,f.J/2),0),sRaw=raw-bigRaw;
    let U=merge(big.map(f=>[f.C/2-lam+1,f.J/2])),ulen=U.reduce((v,[l,r])=>v+r-l,0);ok(ulen<=gBig/2+(lam-1)*big.length,"union fringe");
    let err=0,smoothed=0;for(let [l,r] of U){err+=l2[r]-l2[l];for(let j=l;j<r;j++)smoothed+=cnt(j,j+lam)/(alpha*lam)}
    ok(bigRaw/alpha<=smoothed+1e-6,"nonnegative smoothing");ok(smoothed<=Q*ulen+Math.sqrt(ulen*Math.max(0,err))+1e-5,"local L2");
    let E=Math.abs(raw/alpha-Q*n)+Math.sqrt(ulen*Math.max(0,err));
    ok(sRaw/alpha+1e-5>=Q*(G-gBig)/2-Q*(lam-1)*big.length-E,"cut mass complement");controls++;
    let Ws=[],cutWs=[],expTicks=big.filter(f=>8*f.w>=f.g),ticks=expTicks.reduce((v,f)=>v+f.w,0),W=block.reduce((v,f)=>v+f.w,0);
    ok(W>=G/2-1e-7,"persistent total wait");
    for(let f of block)for(let j=f.C/2;j<f.J/2;j++)if(isCut(j)){
     let J=2*j;ok(f.p>R,"R barrier");
     if(f.p<=V){ok(J>f.C,"anchor excluded");let off=J-f.C,rough=small.every(p=>mod(f.C,p)!==1&&mod(f.C,p)!==p-1);if(rough){ok(prime(off-1)&&prime(off+1)&&off-1>S,"offset twin");strictTwin++}else{ok(f.w<=2*S&&f.d-f.dp>=f.g-4*S,"cheap");cheap++}}
     cutChecks++;if(f.p<=A)cutWs.push({f,J})
    }
    ok(cutWs.length===sRaw,"cut partition");
    let mode;
    if(12*gBig>=11*G){ok(ticks>=G/8-1e-7,"high expensive clock");high++;highG+=gBig;highW+=ticks;mode="h";for(let f of expTicks)for(let j=f.t+1;j<=f.n;j++)Ws.push({f,j})}
    else if(sRaw>=alpha*Q*G/48&&sRaw>0){short++;richRaw+=raw;richShort+=sRaw;mode="c";Ws=cutWs;if(cutWs.some(z=>z.f.p<=V))moderate++}
    else{unclassified++;continue}
    let den=s.rows.length,bmass=5/den,sourceMass=0;
    for(let i=0;i<rows.length;i++)for(let j=0;j<rows.length;j++)if(i!==j){
     let ri=rows[i],rj=rows[j],tag=ri.id,partner=rj.id,sourceKey=tag+"/"+partner+"/"+a;ok(!sourceKeys.has(sourceKey),"unique pair source");sourceKeys.add(sourceKey);sourceMass+=bmass;
     let prefix=new Map(),vv=0;for(let f of block){let prev=prefix.size?block[prefix.size-1].slot:s;vv+=vmap.get(prev.key);prefix.set(f.slot.key,vv)}
     for(let z of Ws){let f=z.f,ids=f.slot.rows.map(r=>r.id);ok(ids.includes(tag)&&ids.includes(partner),"shared actual witness");let w=bmass/Ws.length,key=mode==="h"?f.slot.key+"/"+z.j:f.slot.key+"/"+z.J,projkey=mode==="h"?f.C+"/"+f.p:z.J+"/"+f.C+"/"+f.p,cat=mode==="h"?"h":f.p<=V?"m":"s",pk=cat+"/"+projkey;
      allMass+=w;if(mode==="h")highMass+=w;else shortMass+=w;
      if(prefix.get(f.slot.key)>.25){unstableMass+=w;continue}
      stableMass+=w;ok(Math.abs(Math.log(den/f.slot.rows.length))<=.25+1e-7,"denominator stability");
      add(roles,mode+"/"+key+"/"+tag,w);add(pairs,mode+"/"+key+"/"+tag+"/"+partner,w);
      let pairKey=mode+"/"+key+"/"+tag+"/"+partner,roleKey=mode+"/"+key+"/"+tag;
      if(mode==="h"){maxRoleTick=Math.max(maxRoleTick,roles.get(roleKey));maxPairTick=Math.max(maxPairTick,pairs.get(pairKey)*f.slot.rows.length)}
      else{maxRoleCut=Math.max(maxRoleCut,roles.get(roleKey)*alpha);maxPairCut=Math.max(maxPairCut,pairs.get(pairKey)*alpha*f.slot.rows.length)}
      add(proj,pk,w);if(!physical.has(pk))physical.set(pk,{p:f.p,cat,ids:new Set()});physical.get(pk).ids.add(tag);
      let rk=mode+"/"+key;if(!rankGroups.has(rk))rankGroups.set(rk,{b:f.slot.rows.length,pairs:new Set()});rankGroups.get(rk).pairs.add(tag+"/"+partner)
     }
    }
    ok(near(sourceMass,rows.length*(rows.length-1)*bmass),"source mass");
   }
   // Finite span L+B gives conservative cap; with exact length L analytic cap is absolute.
   let span=1+B/L,capH=40*span,capC=240*span/Q;
   ok(maxRoleTick<=capH+1e-6&&maxRoleCut<=capC+1e-6&&maxPairTick<=capH*Math.exp(.25)+1e-6&&maxPairCut<=capC*Math.exp(.25)+1e-6,"marginal cap");
   for(let [k,w] of proj){let {p,cat,ids}=physical.get(k),eff=cat==="h"?w/(capH*2*p):w*alpha/capC;ok(eff<=ids.size+1e-6,"projected mass");if(cat==="h"){maxProjectedHigh=Math.max(maxProjectedHigh,eff);if(eff<=1)thinHigh+=w}else{maxProjectedShort=Math.max(maxProjectedShort,eff);if(eff<=1){thinShort+=w;if(cat==="m")thinModerate+=w}}}
   for(let z of rankGroups.values()){ok(z.pairs.size<=z.b*(z.b-1),"full physical ordered pair count");rankChecks++}
   ok(near(allMass,highMass+shortMass)&&near(allMass,stableMass+unstableMass),"exact transport partition");
   res.push({X,focus,B,T,L,N:tags.length,events,S,R,V,A,lam,alpha,Q,controls,high,short,moderate,unclassified,cutChecks,strictTwin,cheap,allMass,highMass,shortMass,stableMass,unstableMass,maxRoleTick,maxRoleCut,maxPairTick,maxPairCut,maxProjectedHigh,maxProjectedShort,thinHigh,thinShort,thinModerate,richRaw,richShort,highG,highW,rankChecks})
  }
 }
 ok(res.some(r=>r.high>0)&&res.some(r=>r.short>0)&&res.some(r=>r.moderate>0),"both branches and moderate");
 return res
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
