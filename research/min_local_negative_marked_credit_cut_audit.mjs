// Wall-assisted marked-event credit: discard all sufficiently large fast events.
function audit(){
 const ck=(x,m)=>{if(!x)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p,N=2100000,spf=new Uint32Array(N+3);
 for(let p=2;p*p<=N+2;p++)if(!spf[p])for(let a=p*p;a<=N+2;a+=p)spf[a]=p;
 function fs(n){let a=[];while(n>1){let p=spf[n]||n;a.push(p);while(n%p===0)n/=p}return a}
 function next(a,v){let p=Infinity,w=Infinity;for(let [d,c] of [[a+1,0],[a-1,2]])for(let r of fs(d)){let t=mod((c===0?0:r+2)-v,2*r)||2*r;if(t<w||t===w&&r<p){p=r;w=t}}return {p,w}}
 function twin(a){return !spf[a-1]&&!spf[a+1]}
 let params=[{P:[3],M:3},{P:[3,5],M:9},{P:[3,5,7],M:54}].map(q=>{let D=2*(q.M-1),B=7*D/4+8,T=Math.ceil(8*B+1),K=9*(3+B)+D;return {...q,D,B,T,K}});
 let z={roots:0,events:0,prefixChecks:0,lowRunChecks:0,unmarkedLargeFast:0,markedMedium:0,markedLargeSlow:0,successes:0,basinCutChecks:0,pairChecks:0,rows:[]};
 for(let R of [48000,192000,480000,1000000])for(let mode of ["near","sqrt"]){
  let H=mode==="near"?4*Math.floor(Math.sqrt(R)/Math.sqrt(Math.log(R))):Math.ceil(4*Math.sqrt(2*R+1)),L=Math.floor(H/4),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6),basins=new Map(),row={R,mode,H,L,success:0,events:0,fast:[0,0,0],medium:[0,0,0],slow:[0,0,0],badEnergy:0,cut:[0,0,0],allEnergy:0};
  for(let A=lo;A<=hi;A+=6){let a=A,v=3-A/2,h=3,path=[],ss=params.map(q=>({F:0,Gm:0,Glo:0,lo:0,loW:0,nm:0,nf:0,credit:0,markWeight:0}));
   while(true){let e=next(a,v);if(h+e.w>H){let ar=basins.get(a)||[];ar.push({A,path});basins.set(a,ar);z.successes++;row.success++;break;}
    let g=e.p-1,dh=e.w-g/2;if(A-a+g>L)break;let W=[];
    for(let [i,q] of params.entries()){
     let t=ss[i],wt=0;
     if(q.P.includes(e.p)){t.Glo+=g;t.lo+=g;t.loW+=e.w;ck(t.lo<=q.D&&4*t.loW<=9*t.lo+32,"low wall/potential");z.lowRunChecks++}
     else{t.lo=0;t.loW=0;if(e.p>=q.T&&4*e.w<e.p){t.F+=g;t.nf++;z.unmarkedLargeFast++;row.fast[i]++}
      else{t.Gm+=g;t.nm++;t.credit+=q.B+Math.max(0,dh);wt=g+q.D+9*(q.B+Math.max(0,dh));t.markWeight+=wt;if(e.p<q.T){z.markedMedium++;row.medium[i]++}else{z.markedLargeSlow++;row.slow[i]++}}
     }
     ck(t.Glo<=q.D*(t.nf+t.nm+1),"low total");
     ck(t.F<=8*(3+q.B+t.credit)+1e-9,"unmarked bound");
     ck(A-a+g===t.F+t.Gm+t.Glo&&A-a+g<=q.K+t.markWeight+1e-9,"full marked bound");z.prefixChecks++;W.push(wt)
    }
    path.push({key:a+":"+(v+e.w),W,g});a-=g;v+=e.w;h+=dh;z.events++;row.events++;
   }z.roots++;
  }
  for(let [a,ar] of basins){let m=ar.length,keys=new Map();for(let r of ar)for(let e of r.path){let f=keys.get(e.key)||{m:0,W:[0,0,0]};f.m++;for(let i=0;i<3;i++)f.W[i]+=e.W[i];keys.set(e.key,f)}
   let bad=!twin(a);row.allEnergy+=m*m;if(bad)row.badEnergy+=m*m;
   for(let [i,q] of params.entries()){let cut=0;for(let f of keys.values())cut+=f.W[i]*(1-f.m/m);ck(m*m<=1+q.K*(m-1)/2+cut+1e-6,"marked cut inequality");if(bad)row.cut[i]+=cut;z.basinCutChecks++}
   if(bad||a%246===0)for(let i=0;i<m;i++)for(let j=i+1;j<m;j++){let S=new Set(ar[i].path.map(e=>e.key)),w=[0,0,0];for(let e of ar[j].path){if(S.has(e.key))break;for(let k=0;k<3;k++)w[k]+=e.W[k]}
    for(let k=0;k<3;k++){ck(ar[j].A-ar[i].A<=params[k].K+w[k]+1e-9,"pair marked charge");z.pairChecks++}
   }
  }
  z.rows.push(row)
 }
 return {params,...z}
}
console.log(JSON.stringify(audit(),null,2));
