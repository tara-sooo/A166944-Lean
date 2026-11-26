// Last-upcross and first-downcross pair-level ledger, finite actual MIN controls.
function audit(Xs=[4096,16384,65536]){
 const ok=(v,m)=>{if(!v)throw Error(m)},mod=(x,m)=>(x%m+m)%m,near=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b));
 const lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1),pr=[];
 for(let p=2;p<=lim;p++)if(!spf[p]){pr.push(p);for(let k=p;k<=lim;k+=p)if(!spf[k])spf[k]=p}
 const odd=pr.filter(p=>p>2),prime=x=>x>=2&&spf[x]===x;
 function minD(path,a,b){let m=Infinity;for(let e of path){let l=Math.max(a,e.C),r=Math.min(b,e.J);if(l<=r)m=Math.min(m,e.d+(l-e.C)*e.s,e.d+(r-e.C)*e.s)}ok(Number.isFinite(m),"minimum domain");return m}
 function pieces(path,a,b){let out=[];for(let e of path){let l=Math.max(a,e.C),r=Math.min(b,e.J);if(l<r)out.push({e,l,r,dl:e.d+(l-e.C)*e.s,dr:e.d+(r-e.C)*e.s})}return out}
 function records(path,a,b,z,cut){
  let ma=minD(path,a,a+z),mb=minD(path,b,b+z),lo=Math.max(cut,Math.min(ma,mb)),hi=Math.max(cut,Math.max(ma,mb)),pos=[],neg=[];
  if(hi>lo&&mb>ma){let floor=mb;for(let q of pieces(path,a,b).reverse()){if(q.e.s>0){let L=Math.max(lo,q.dl),R=Math.min(hi,floor,q.dr);if(L<R)pos.push({q,L,R})}floor=Math.min(floor,q.dl,q.dr)}}
  if(hi>lo&&ma>mb){let floor=ma;for(let q of pieces(path,a+z,b+z)){if(q.e.s<0){let L=Math.max(lo,q.dr),R=Math.min(hi,floor,q.dl);if(L<R)neg.push({q,L,R})}floor=Math.min(floor,q.dl,q.dr)}}
  const length=a=>a.reduce((s,x)=>s+x.R-x.L,0),signed=Math.max(0,mb-cut)-Math.max(0,ma-cut);
  ok(near(length(pos)-length(neg),signed),"net partition");
  for(let set of [pos,neg]){let v=set.slice().sort((x,y)=>x.L-y.L);for(let j=1;j<v.length;j++)ok(near(v[j-1].R,v[j].L),"adjacent levels");if(v.length)ok(near(v[0].L,lo)&&near(v.at(-1).R,hi),"full level partition")}
  return {ma,mb,lo,hi,pos,neg,signed}
 }
 function barrier(p,b){if(p===3)return true;let r=mod(b,2*p);return !(r>=2&&r<=p-3&&r%2===0||r>=8&&r<=p+3&&r%2===0)}
 const results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),D=Math.max(12,Math.floor(T/4)),z=Math.max(4,Math.floor(D/8)),L=Math.max(z,Math.floor(D/3)),cut=Math.max(12,Math.floor(B/4)),tags=[],slots=new Map(),events=0;
  for(let M=X|1;M<2*X;M+=2)if(prime(M)){let id=tags.length,C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity,I=0;for(let j=0;j<2;j++){let x=C-1+2*j;while(x>1){let f=spf[x];while(x%f===0)x/=f;if(f*f>C+1)continue;let v=mod((j?f+2:0)-t,2*f)||2*f;if(v<w||v===w&&f<p){p=f;w=v;I=j}}}if(!p)break;let g=p-1,J=C+g,n=t+w,d=2*t-C,dp=2*n-J,key=C+"/"+p+"/"+n;
    if(!slots.has(key))slots.set(key,{key,C,J,p,n,ids:[]});let slot=slots.get(key);slot.ids.push(id);ok(d>=0&&dp>=0&&w<=3*g,"MIN");path.push({C,J,p,w,I,t,n,d,dp,g,s:(dp-d)/g,slot});C=J;t=n;events++;
   }tags.push({id,C0,F:C,path})
  }
  let pairs=0,positive=0,negative=0,signed=0,posRecords=0,negRecords=0,long=0,short=0,phaseChecks=0,barrierChecks=0,nonconcChecks=0,matchedSamples=0,matchedUpDown=0,hybrid=0,twins=0,cheap=0,anchors=0,positiveHybrid=0,sourceRows=new Map(),massChecks=0;
  let examples=[];
  const cfgs=[{S:3,R:5,V:9},{S:5,R:7,V:25},{S:7,R:11,V:49}];
  for(let t of tags)for(let e of t.path)for(let {S,R,V} of cfgs){if(e.p<=R||e.p>V)continue;let P=2*odd.filter(p=>p<=S).reduce((a,b)=>a*b,1);
   for(let J=Math.ceil(e.C/P)*P;J<e.J;J+=P){if(!odd.filter(p=>p>S&&p<=R).every(p=>mod(J,p)%2===0&&mod(J,p)<=p-3))continue;
    if(!odd.filter(p=>p>R&&p<=V).every(p=>mod(J,p)!==1&&mod(J,p)!==p-1))continue;hybrid++;ok(J>e.C,"sieved anchor");let u=J-e.C,rough=odd.filter(p=>p<=S).every(p=>mod(e.C,p)!==1&&mod(e.C,p)!==p-1);
    if(rough){ok(u>=4&&prime(u-1)&&prime(u+1)&&u-1>S,"twin offset");twins++;if(e.dp>e.d)positiveHybrid++}
    else{ok(e.w<=2*S&&e.d-e.dp>=e.g-4*S,"cheap crossing");cheap++}
   }
  }
  for(let l=Math.floor((2*X-2)/D)*D;l<4*X+T+B;l+=D){let e=l+D;
   for(let slot of slots.values())if(slot.C<e&&e<=slot.J&&slot.ids.length>=2){let ids=slot.ids.slice(0,8),den=slot.ids.length;
    for(let i=0;i<ids.length;i++)for(let j=i+1;j<ids.length;j++){let A=tags[ids[i]],Q=tags[ids[j]],set=new Set(Q.path.map(x=>x.slot.key)),birth=A.path.find(x=>set.has(x.slot.key)),a=Math.max(l,birth.J),b=Math.min(e,A.F-z,Q.F-z);if(b<=a)continue;pairs++;
     let r=records(A.path,a,b,z,cut),weight=2/den;signed+=weight*r.signed;
     for(let x of r.pos){let {q,L:lo,R:hi}=x,y=(lo+hi)/2,t=q.l+(y-q.dl)/q.e.s,f=q.e,h=(f.dp-6*f.I)/(2*f.p);
      ok(t>=a-1e-7&&t<=b+1e-7&&minD(A.path,t,b+z)>=y-1e-6&&near(minD(A.path,t,t+z),y),"last upcross persistent");
      ok(Number.isInteger(h)&&mod(f.C-(1-2*f.I+f.p*(2*f.I-2*h-1)),4*f.p)===0,"phase");ok(f.dp-y<=3*f.p+1+1e-7&&f.w>f.g/2,"positive support");phaseChecks++;
      ok(set.has(f.slot.key),"shared physical source");positive+=weight*(hi-lo);posRecords++;
      let tcut=b-L,ycut=q.dl+(tcut-q.l)*f.s,keep=Math.max(0,Math.min(hi,ycut)-lo);long+=weight*keep;short+=weight*(hi-lo-keep);
      // Integer level bins: one directed ordered pair/physical slot/level at most once across slabs.
      for(let y0=Math.ceil(lo);y0<hi;y0++){let key=f.slot.key+"/"+y0+"/"+A.id+"/"+Q.id;ok(!sourceRows.has(key),"unique pair source at level");sourceRows.set(key,true);massChecks++}
     }
     for(let x of r.neg){let {q,L:lo,R:hi}=x,y=(lo+hi)/2,t=q.l+(y-q.dl)/q.e.s;
      ok(t>=a+z-1e-7&&t<=b+z+1e-7&&minD(A.path,a+z,t)>=y-1e-6&&near(minD(A.path,t-z,t),y),"first downcross record");
      ok(set.has(q.e.slot.key),"shared negative provider");negative+=weight*(hi-lo);negRecords++;
      for(let Bc=2*Math.ceil(lo/2);Bc<=hi;Bc+=2)if(q.e.dp<Bc&&Bc<=q.e.d){ok(!barrier(q.e.p,Bc),"downward cut");barrierChecks++}
     }
     for(let F of [[],[3],[5],[3,5],[5,7]]){let prod=F.reduce((a,b)=>a*b,1),theta=F.reduce((a,p)=>a*(p<=7?3:(p-3)/2)/p,1),drop=r.neg.reduce((a,x)=>a+x.R-x.L,0),out=r.neg.filter(x=>!F.includes(x.q.e.p)).reduce((a,x)=>a+x.R-x.L,0);ok(out+1e-7>=theta*Math.max(0,drop-2*prod-4),"outside record bound");nonconcChecks++}
     // Sample level crossings of the actual sliding minimum by intervals at raw knots and shifted knots.
     let knots=[a,b,...A.path.flatMap(f=>[f.C,f.J,f.C-z,f.J-z]).filter(x=>a<x&&x<b)].sort((x,y)=>x-y);
     let levels=[cut+1,(r.lo+r.hi)/2,r.hi+1];
     for(let y of levels){if(y<=cut)continue;let states=knots.map(x=>minD(A.path,x,x+z)>y?1:0),up=0,dn=0;for(let k=1;k<states.length;k++){up+=Math.max(0,states[k]-states[k-1]);dn+=Math.max(0,states[k-1]-states[k])}
      ok(up-dn===states.at(-1)-states[0],"coarea sign");matchedSamples++;matchedUpDown+=Math.min(up,dn)
     }
    }
   }
  }
  ok(near(positive-negative,signed)&&near(long+short,positive),"aggregate partition");
  results.push({X,focus,N:tags.length,events,D,z,L,cut,pairs,positive,negative,signed,long,short,posRecords,negRecords,phaseChecks,barrierChecks,nonconcChecks,massChecks,matchedSamples,matchedUpDown,hybrid,twins,cheap,positiveHybrid})
 }
 // Synthetic continuous excursion: one fully canceled rise/fall, then last lasting rise.
 const p=[{C:0,J:8,d:0,dp:16,s:2},{C:8,J:24,d:16,dp:0,s:-1},{C:24,J:32,d:0,dp:16,s:2},{C:32,J:64,d:16,dp:16,s:0}];
 let a=records(p,0,40,4,0),b=records(p,8,24,4,0);ok(near(a.signed,16)&&a.pos.length===1&&a.pos[0].q.e.C===24&&b.signed<0,"synthetic records");
 return {results,synthetic:{net:a.signed,positiveStart:a.pos[0].q.e.C,negative:b.signed}}
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
