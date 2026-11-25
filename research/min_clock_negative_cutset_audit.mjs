// Exact reverse reachability and negative-deficit cutsets.
// Run node research/min_clock_negative_cutset_audit.mjs 1024 4096 16384 65536
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,startAge=mode==='full'?0:mode==='early'?B:2*B,a=startAge,N=X/2,G=2*H+B+6,U=7*X+4,W=16*B,u=Math.log(B),ell=Math.log(u);
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>B**(1/16))break;L*=p;z=p;}}
 else {z=3;L=6;}
 const T=mode==='analytic'?Math.max(z+1,Math.ceil(B**.25)):Math.ceil(Math.sqrt(B));
 const mH=mode==='analytic'?Math.max(1,Math.floor(u**2.75)):mode==='diagnostic'||mode==='stress'?8:16;
 const mM=mode==='analytic'?Math.max(1,Math.floor(B**.625)):mode==='diagnostic'||mode==='stress'?12:24;
 const D0=mode==='analytic'?Math.ceil(40*ell)+1:4;
 const lo=X,hi=7*X/2-1,len=hi+1,r=new Int32Array(len),degrees=new Uint8Array(len);
 function fac(n,cb){while(n>1){const p=spf[n];if(p>B)break;if(p>2)cb(p);while(n%p===0)n/=p;}}
 let rare=0,maxDegree=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B)r[j]=q;for(const C of [2*j,2*j+2])fac(C,()=>degrees[j]++);maxDegree=Math.max(maxDegree,degrees[j]+1);rare+=+(degrees[j]+1>D0);}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1])fac(C+side,q=>{const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(w<v||(w===v&&w<=K&&q<p)){v=w;p=q;}});return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 const paths=[],at=new Map(),W0=new Float64Array(len),WM=new Float64Array(len),WH=new Float64Array(len);
 let R=0,RM=0,RH=0,events=0,literal=0,twins=0;
 for(let i=0;i<N;i++){const M=X+1+2*i,s=M+2,K=Math.floor((7*M-1)/4),path=[];let t=s,C=2*M-2,inc=0,rr=0;
  for(;;){const e={i,M,C,t,inc,p:0,w:0};path.push(e);let row=at.get(C);if(!row){row=[];at.set(C,row);}row.push(e);
   ok(C<=2*t&&C-(2*M-2)<=G,'prefix gain');
   if(t>=s+H)break;
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(v===vv&&p===pp,'literal');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'twin');twins++;break;}
   const q=r[C/2],cost=Math.max(0,Math.min(v,s+H)-Math.max(t,s+a))/2;
   ok(v-t<=2*q&&q<=p,'wait');e.p=p;e.w=cost/q;rr+=cost;R+=cost;W0[C/2]+=e.w;
   if(p>z&&p<=T){RM+=cost;WM[C/2]+=e.w;}if(p>T){RH+=cost;WH[C/2]+=e.w;}
   t=v;C+=p-1;inc=p;events++;
  }
  ok(rr<=(H-startAge)/2,'root cost');paths.push(path);
 }








 const P=mode==='analytic'?Math.ceil(B/u**.125):Math.max(17,Math.ceil(B/(mode==='wide'?16:8)));
 const Q=mode==='analytic'?Math.max(17,Math.ceil(B/u**.25)):Math.max(17,Math.ceil(P/2));
 const Y=Math.max(17,Math.ceil(B**.125)),eps=mode==='analytic'?u**(-.125):.125;
 const h=[mode==='analytic'?Math.floor(u**.5):2,mode==='analytic'?Math.floor(u**1.5):4],D=Math.ceil(P/4),lim=12*B+6;
 const diff=[new Int32Array(lim+3),new Int32Array(lim+3)];let envelope=[0,0];
 for(let C=2*X;C<7*X;C+=2)for(const s of [0,1])fac(C+2*s-1,p=>{
  const b=p>=Q?0:p>=Y&&2*r[C/2]>=eps*p?1:-1;
  if(b<0||p>=P||p<5)return;const J=C+p-1;if(J>=7*X)return;
  for(let k=1;6*s+2*p*k<=lim;k++){
   const d=6*s+2*p*k,t=(J+d)/2;if(t%2!==s)continue;
   const l=d+1,h0=Math.min(lim,d+p-3);if(l>h0)continue;
   envelope[b]++;diff[b][l]++;diff[b][h0+1]--;
  }
 });
 const supports=[0,0],maxSupports=[0,0],per=[new Int32Array(lim+1),new Int32Array(lim+1)];
 for(let b=0;b<2;b++){let c=0;for(let l=1;l<=lim;l++){c+=diff[b][l];per[b][l]=c;supports[b]+=c;maxSupports[b]=Math.max(maxSupports[b],c);}}
 const groups=new Map(),entries=[],byRoot=new Map(),roughFull=new Float64Array(len);
 const key=(C,t,p,l)=>C+':'+t+':'+p+':'+l;
 let blockCount=0,dropCount=0,levels=0,small=0,cheap=0,near=0,rough=0,lastChecks=0,repeat=0,lowGain=0,cheapGain=0,cheapClock=0,roughInc=0,maxDrop=0,fullCost=0;
 for(const path of paths){
  let high=-1,crossed=false;
  for(let j=1;j<path.length;j++){
   const x=path[j-1],v=path[j],p=v.inc,pre=2*x.t-x.C,post=2*v.t-v.C,w=v.t-x.t;
   fullCost+=w/2;
   if(p<Y)lowGain+=p-1;else if(p<Q&&w<eps*p){cheapGain+=p-1;cheapClock+=w/2;}
   if(p>=Y&&p<Q&&w>=eps*p&&post<pre&&post!==6*(v.t%2)){roughFull[x.C/2]+=w/(2*r[x.C/2]);roughInc++;}
   if(post===6*(v.t%2)){high=-1;crossed=false;continue;}
   if(p>=P){if(high>=0&&pre<=P){repeat++;ok(crossed,'repeat requires earlier drop');}high=j;crossed=false;blockCount++;continue;}
   if(high<0||crossed)continue;
   const start=2*path[high].t-path[high].C;
   if(post>start-D)continue;
   crossed=true;dropCount++;maxDrop=Math.max(maxDrop,start-post);
   const rec={root:v.i,small:0,cheap:0,marks:[],levels:D},last=new Map();
   for(let k=high+1;k<=j;k++){const a=path[k-1],b=path[k],d0=2*a.t-a.C,d1=2*b.t-b.C;
    for(let l=Math.max(start-D+1,d1+1);l<=Math.min(start,d0);l++)last.set(l,k);
   }
   ok(last.size===D,'complete downward cutset');
   for(const [l,k] of last){const a=path[k-1],b=path[k],p0=b.inc,d0=2*a.t-a.C,d1=2*b.t-b.C,w0=b.t-a.t;
    ok(p0<P&&d1<l&&l<=d0&&p0>=5&&d1>=2*p0&&d0-d1<=p0-3,'actual nonreset downcross');
    for(let k0=k+1;k0<=j;k0++){const aa=path[k0-1],bb=path[k0];ok(!(2*bb.t-bb.C<l&&l<=2*aa.t-aa.C),'last downcross');}lastChecks++;
    if(p0>=Q||p0>=Y&&w0>=eps*p0){
     const band=+(p0<Q),id=key(b.C,b.t,p0,l);let g=groups.get(id);
     if(!g){g={band,l,n:0,D:a.C,p:p0};groups.set(id,g);}
     g.n++;rec.marks.push(id);if(band)rough++;else near++;
    }else if(p0<Y){small++;rec.small++;}else{cheap++;rec.cheap++;}
   }
   entries.push(rec);let es=byRoot.get(rec.root);if(!es){es=[];byRoot.set(rec.root,es);}es.push(rec);levels+=D;
  }
 }
 const actual=[new Int32Array(lim+1),new Int32Array(lim+1)],second=[0,0],used=[0,0],mass=[0,0],maxMass=[0,0];
 let thin=0,thick=0;
 for(const g of groups.values()){actual[g.band][g.l]++;second[g.band]+=g.n*g.n;used[g.band]++;mass[g.band]+=g.n;maxMass[g.band]=Math.max(maxMass[g.band],g.n);if(g.n<=h[g.band])thin+=g.n;else thick+=g.n;}
 for(let l=1;l<=lim;l++)for(let b=0;b<2;b++)ok(actual[b][l]<=per[b][l],'actual downcross support');
 let Erough=0;for(let c=lo;c<=hi;c++)Erough+=r[c]*roughFull[c]**2;
 ok(second[1]<=8/eps**3*Erough+1e-6*Math.max(1,Erough),'rough descent second moment');
 ok(levels===small+cheap+near+rough&&near+rough===thin+thick&&small<=lowGain&&cheap<=cheapGain&&cheapClock<=eps*(cheapGain+cheapGain/2)/2+1e-7,'cutset partition');
 const active=new Map([...groups].map(([id,g])=>[id,g.n])),charges=new Map(),deleted=new Set();let paid=0,passes=0;
 for(;;){let n=0;for(const [root,es] of byRoot){if(deleted.has(root))continue;let ids=null;
  for(const e of es){const a=e.marks.filter(id=>active.get(id)<=h[groups.get(id).band]);if(3*a.length>=D){ids=a;break;}}
  if(!ids)continue;for(const id of ids){const c=(charges.get(id)||0)+1;charges.set(id,c);ok(c<=h[groups.get(id).band],'lifetime');paid++;}
  deleted.add(root);n++;for(const e of es)for(const id of e.marks)active.set(id,active.get(id)-1);
 }if(!n)break;passes++;}
 let remaining=0,other=0,thickRemaining=0,minThick=1;
 for(const [root,es] of byRoot)if(!deleted.has(root))for(const e of es){remaining++;const n=e.marks.filter(id=>active.get(id)<=h[groups.get(id).band]).length;ok(3*n<D,'fixed point');if(3*(e.small+e.cheap)>=D)other++;else{thickRemaining++;const k=e.marks.length-n;ok(3*k>D,'thick remainder');minThick=Math.min(minThick,k/D);}}
 ok(deleted.size*D/3<=paid&&paid<=h[0]*supports[0]+h[1]*supports[1],'peeling budget');
 return {X,B,mode,P,Q,Y,eps,D,h,N,R,events,literal,blockCount,dropCount,levels,small,cheap,near,rough,thin,thick,lastChecks,repeat,maxDrop,lowGain,cheapGain,cheapClock,roughInc,fullCost,envelope,supports,maxSupports,second,used,mass,maxMass,Erough,deleted:deleted.size,paid,passes,remaining,other,thickRemaining,minThick:thickRemaining?minThick:null};
}
function reachability(){
 const X=65536,B=Math.ceil(Math.sqrt(7*X)),H=4*B,U=7*X+4,spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a;};
 function tick(t,C){const n=gcd(t%2?t-2:t,t%2?C+1:C-1);return n>1&&spf[n]<=B?spf[n]:0;}
 function rev(t,J){const a=[];if(!tick(t,J))a.push(J);let n=gcd(t-2*(t%2),J+2*(t%2));
  while(n>1){const p=spf[n];if(p>B)break;while(n%p===0)n/=p;if(p>2&&tick(t,J-p+1)===p)a.push(J-p+1);}
  return a.filter(D=>D<=2*(t-1)&&D>=2);
 }
 function search(t0,C0,global=false){const minM=Math.max(X+1,t0-H-2),maxM=Math.min(2*X-1,t0-2),minC=2*minM-2;
  let level=new Set([C0]),states=0,arcs=0,maxWidth=0,roots=[],trace=[],brute=0;
  for(let t=t0;level.size&&(global||t>=minM+2);t--){
   const next=new Set();for(const J of level){states++;
    if(J%4===0&&t===J/2+3){const M=J/2+1;if(global||M>=minM&&M<=maxM&&t0-t<=H)roots.push(M);}
    const a=rev(t,J);
    if(global){const independent=[];for(let D=Math.max(2,J-2*Math.floor((B-1)/2));D<=J;D+=2){if(D>2*(t-1))continue;const p=tick(t,D);if(D+(p?p-1:0)===J)independent.push(D);}if(a.length!==independent.length||a.some(D=>!independent.includes(D)))throw Error('independent inverse scan');brute++;trace.push({t,J,delta:2*t-J,blocked:tick(t,J),predecessors:a});}
    for(const D of a){if(!global&&D<minC)continue;next.add(D);arcs++;}
   }maxWidth=Math.max(maxWidth,level.size);level=next;
  }
  const forward=[];
  if(!global)for(let M=minM+(minM%2===0?1:0);M<=maxM;M+=2){let C=2*M-2;for(let t=M+3;t<=t0&&C<=C0;t++){const p=tick(t,C);if(p)C+=p-1;}if(C===C0)forward.push(M);}
  if(!global&&(roots.length!==forward.length||roots.some(x=>!forward.includes(x))))throw Error('canonical reverse/forward roots');
  return {t0,C0,global,states,arcs,maxWidth,roots,forwardCount:forward.length,trace,brute};
 }
 const dead=search(97712,195362,true);if(dead.states!==7||dead.roots.length||dead.arcs!==6)throw Error('dead tree');
 const later=search(97764,195498),final=search(97957,195634);if(later.roots.length!==57||final.roots.length!==57)throw Error('later basins');
 return {B,H,dead,later,final,known:search(88113,176186)};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide'])console.log(JSON.stringify(audit(X,mode)));
console.log(JSON.stringify(reachability()));
