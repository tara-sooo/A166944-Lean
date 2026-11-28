// Finite actual calendar and deficit-record checks; synthetic inequality controls are not MIN paths. No asymptotic evidence.
function audit(){
 const assert=(v,m)=>{if(!v)throw Error(m)};
 const mod=(x,m)=>((x%m)+m)%m;
 const maxR=768000, N=2*maxR+100;
 const f=new Int32Array(N+1);
 for(let p=2;p<=N;p++)if(!f[p]){f[p]=p;if(p*p<=N)for(let x=p*p;x<=N;x+=p)if(!f[x])f[x]=p;}
 function factors(x){const a=[];while(x>1){const p=f[x];assert(p>0,"factor range");a.push(p);while(x%p===0)x/=p;}return a;}
 function event(x,n){
   let wait=Infinity,p=0,s=0;
   for(const e of [1,-1])for(const q of factors(x+e)){
     let w=mod((e===1?0:q+2)-n,2*q);if(!w)w=2*q;
     if(w<wait||(w===wait&&q<p)){wait=w;p=q;s=e;}
   }
   return {w:wait,p,s};
 }
 function analyze(d0,B,records,m,checkKey){
   let low=d0,total=0,good=0,bad=0,cross=0,goodCount=0,badCount=0;
   const goodBand=new Map(), badBand=new Map(), allBand=new Map(), badKeys=new Map();
   for(const r of records){
     if(low<=B)break;
     assert(r.d<low&&r.old>=low,"record minimum");
     assert(r.p<=2*r.d+1&&r.old<=4*r.d+2,"deficit inequalities");
     const drop=Math.log(low/Math.max(B,r.d));
     assert(drop>=0&&drop<=Math.log(6)+1e-11,"bounded log drop");
     total+=drop;
     if(r.d<B){cross+=drop;low=r.d;break;}
     let j=Math.floor(Math.log2(r.d/B));
     let D=B*2**j;
     while(r.d<D){j--;D/=2;}while(r.d>=2*D){j++;D*=2;}
     assert(D<=r.d&&r.d<2*D,"band");
     allBand.set(j,(allBand.get(j)||0)+drop);
     if(r.p*m<D){
       assert(drop<=2*r.p/D+1e-11&&drop<=2/m+1e-11,"good drop");
       good+=drop;goodCount++;goodBand.set(j,(goodBand.get(j)||0)+drop);
     }else{
       bad+=drop;badCount++;badBand.set(j,(badBand.get(j)||0)+drop);
       if(!badKeys.has(j))badKeys.set(j,new Set());
       badKeys.get(j).add(r.key);
       if(checkKey)checkKey(r,j,D);
     }
     low=r.d;
   }
   const ell=Math.log(d0/B);
   assert(low<=B,"completed record descent");
   assert(Math.abs(total-ell)<1e-8&&Math.abs(total-good-bad-cross)<1e-8,"telescoping");
   assert(good<=2*goodCount/m+1e-8,"good total");
   assert(cross<=Math.log(6)+1e-11,"crossing");
   for(const v of allBand.values())assert(v<=Math.log(12)+1e-9,"per-band record capacity");
   for(const v of badBand.values())assert(v<=Math.log(12)+1e-9,"bad-band capacity");
   if(ell>=4*Math.log(6)&&m>=8*records.length/ell){
     assert(bad+1e-8>=ell/2&&badBand.size+1e-8>=ell/(2*Math.log(12)),"low-depth many bad bands");
   }
   return {ell,total,good,bad,cross,goodCount,badCount,goodBand,badBand,badKeys};
 }
 let roots=0,completed=0,successes=0,recordIncidences=0,activeWitnesses=0,profiles=0,goodSteps=0,badSteps=0,bandCharges=0,localKeyChecks=0,independentChecks=0;
 const rows=[];
 for(const R of [12000,48000,192000,768000]){
   const H=Math.floor(R**.4), Q=Math.max(2,Math.floor(H/10)), B=2*Q;
   let nr=0,ne=0,ns=0,nrec=0,na=0,ng=0,nb=0,maxDepth=0;
   const allSinks=new Set(),activeSinks=new Map(),keys=new Map(),charges=new Map();
   for(let A=6*Math.ceil(R/6);A<=2*R;A+=6){
     nr++;let x=A,h=3,n=3-A/2,g=0,low=H-3,hit=false,record=[],lastIdle=0;
     while(g<=4*H){
       const {w,p,s}=event(x,n);
       if(nr%2003===1){
         let found=0, fw=0;
         for(let j=1;j<=w;j++){
           const nt=n+j,e=mod(nt,2)===0?1:-1;
           const qs=factors(x+e).filter(q=>mod(nt,2*q)===(e===1?0:q+2));
           if(qs.length){found=qs[0];fw=j;break;}
         }
         assert(found===p&&fw===w,"literal calendar");independentChecks++;
       }
       assert(w<=2*Math.min(f[x-1],f[x+1]),"calendar bound");
       if(h+w-1>=H){lastIdle=H-h;assert(lastIdle<w,"terminal idle");hit=true;break;}
       const source=x,old=H-h;
       x-=p-1;g+=p-1;n+=w;h+=w-(p-1)/2;
       assert(h===x/2+n&&h>=0&&h<H,"height ledger");
       if(g>4*H)break;
       ne++;const d=H-h;
       assert(p<=2*d+1&&old<=4*d+2,"event deficit bounds");
       if(d<low){
         assert(w>(p-1)/2&&4*Math.min(f[source-1],f[source+1])>p-1,"record slow source");
         const key=[x,h,p,s].join(",");
         record.push({old,d,p,s,w,source,x,h,key});low=d;nrec++;
       }
     }
     if(!hit)continue;
     ns++;assert(g===A-x&&g<=4*H&&lastIdle===H-h,"first height");
     allSinks.add(x);
     const qmin=Math.min(f[x-1],f[x+1]);
     if(qmin>Q)continue;
     assert(H-h===lastIdle&&lastIdle<2*qmin&&low<=H-h&&low<=B,"active terminal");
     na++;maxDepth=Math.max(maxDepth,record.length);
     const v=activeSinks.get(x);if(v===undefined||record.length<v)activeSinks.set(x,record.length);
     for(const m of [1,2,4,8,16]){
       const a=analyze(H-3,B,record,m,(r,j,D)=>{
         assert(r.p*m>=D&&r.p<=4*D+1,"band prime range");
         assert(mod(r.x-(1-r.s),r.p)===0&&mod(r.h-(r.s===1?0:3),r.p)===0,"arrival pin");
         assert(4*Math.min(f[r.source-1],f[r.source+1])>r.p-1,"source roughness");
         const bkey=m+","+j;
         if(!keys.has(bkey))keys.set(bkey,new Set());
         keys.get(bkey).add(r.key);
         if(!charges.has(bkey))charges.set(bkey,new Set());
         charges.get(bkey).add(x);
         localKeyChecks++;
       });
       profiles++;ng+=a.goodCount;nb+=a.badCount;
     }
   }
   for(const [b,s] of charges){assert(s.size<=keys.get(b).size,"one sink per physical key");bandCharges+=s.size;}
   roots+=nr;completed+=ne;successes+=ns;recordIncidences+=nrec;activeWitnesses+=na;goodSteps+=ng;badSteps+=nb;
   rows.push({R,H,Q,B,roots:nr,completed:ne,successes:ns,distinctSinks:allSinks.size,activeWitnesses:na,activeSinks:activeSinks.size,recordIncidences:nrec,maxRecordDepth:maxDepth,minimumDepthHistogram:[...activeSinks.values()].reduce((a,k)=>(a[k]=(a[k]||0)+1,a),{}),goodSteps:ng,badSteps:nb});
 }
 // Synthetic integer deficit sequences test nonvacuous long log-span implication.
 // These obey the two deficit inequalities, but are not asserted to be actual paths.
 const synthetic=[];
 for(const [d0,B,style] of [[2**20,16,"short"],[2**19,16,"slow"],[2**18,16,"mixed"]]){
   let d=d0;const rec=[];
   while(d>B){
     let n=style==="short"?Math.max(B,Math.ceil(d/3)):style==="slow"?Math.max(B,d-3):(rec.length%7===0?Math.max(B,Math.ceil(d/2)):Math.max(B,d-3));
     let p=Math.max(3,Math.ceil((d-n)/2));if(p%2===0)p++;
     assert(p<=2*n+1&&d<=4*n+2&&d-n<=2*p,"synthetic inequalities");
     rec.push({old:d,d:n,p,key:"s"+rec.length});d=n;
   }
   const ell=Math.log(d0/B), m=Math.max(1,Math.ceil(8*rec.length/ell));
   for(const mm of [m,8]){
     const a=analyze(d0,B,rec,mm);
     synthetic.push({style,d0,B,recordCount:rec.length,m:mm,ell,goodCount:a.goodCount,badCount:a.badCount,badBands:a.badBand.size,goodBands:a.goodBand.size});
   }
 }
 assert(activeWitnesses>0&&goodSteps>0&&badSteps>0&&localKeyChecks>0&&independentChecks>0,"nonvacuity");
 return {roots,completed,successes,recordIncidences,activeWitnesses,profiles,goodSteps,badSteps,bandCharges,localKeyChecks,independentChecks,rows,synthetic};
}
console.log(JSON.stringify(audit(),null,2));
