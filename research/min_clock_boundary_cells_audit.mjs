// Source-window boundary cell absorption and low-deficit strip transfer.
// Run node research/min_clock_boundary_cells_audit.mjs 1024 4096 16384 65536
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







 const eta=u**(-.25),rho=mode==='analytic'?Math.min(.125,u**(-.25)):mode==='wide'?.125:.0625;
 const P=mode==='analytic'?Math.max(17,Math.ceil(B/u**.125)):Math.max(17,Math.ceil(B/4));
 let nonreset=0,reset=0,firstLow=0,repeatedLow=0,charged=0,repeatGain=0,subGain=0,minimumRatio=Infinity,nonresetChecks=0;
 for(const path of paths){
  let prev=null;
  for(let j=1;j<path.length;j++){
   const e=path[j-1],v=path[j],p=v.inc,d0=2*e.t-e.C,d1=2*v.t-v.C,s=v.t%2;
   if(d1===6*s){prev=null;if(p>=P)reset++;continue;}
   if(p<P){subGain+=p-1;continue;}
   ok(d1>=2*p&&d1===6*s+2*p*Math.floor((d1-6*s)/(2*p)),'nonreset high deficit');nonreset++;nonresetChecks++;
   if(d0<=P){
    ok(v.t-e.t>=p&&2*r[e.C/2]>=p,'low-deficit nonreset long wait');
    if(prev){const gain=e.C-prev.C;ok(gain>=2*prev.inc-P&&gain>=P,'repeat low deficit charge');charged+=gain;repeatGain+=p-1;repeatedLow++;minimumRatio=Math.min(minimumRatio,gain/P);}
    else firstLow++;
   }
   prev=v;
  }
 }
 ok(charged<=subGain&&repeatGain<=(B/P)*charged,'disjoint intermediate gain charges');
 const excursions={P,nonreset,reset,firstLow,repeatedLow,charged,repeatGain,subGain,minimumRatio:Number.isFinite(minimumRatio)?minimumRatio:null,nonresetChecks};
 const results=[],overlap=(l,h,x,y)=>Math.max(0,Math.min(h,y)-Math.max(l,x));
 for(const path of paths)for(let j=0;j+1<path.length;j++){const e=path[j],v=path[j+1];e.l=Math.max(e.t,e.M+2+a);e.h=Math.min(v.t,e.M+2+H);e.v=v.t;e.cut=e.M+2+H;e.start=e.M+2+a;}
 for(const b of [0,1]){
  const f=e=>b===0?e.p>z&&e.p<=T:e.p>T;
  const D=Math.min((H-a)/2,mode==='analytic'?B**(b===0?13/16:.5)*u:mode==='wide'?B/2:Math.sqrt(B));
  const E0=mode==='analytic'?D:mode==='wide'?B/2:Math.sqrt(B);
  let E=0,Rb=0,Ec=0,Et=0,Rt=0,allTail=0,paid=0,sync=0,nearAsync=0,farAsync=0,cutPaid=0,startPaid=0,oracle=0,oracleChecks=0,maxTail=0,cellChecks=0,low=0,lowStrong=0,lowExc=0,Ex=0,Rx=0,maxExc=0,lowPaid=0,lowGain=0,exceptions=0,strongInc=0;
  let lowSync=0,nearPairs=0,allSync=0,allAsync=0,lowAndTail=0;
  for(const [C,row] of at){const q=r[C/2],tags=row.filter(e=>e.w>0&&f(e));if(!tags.length)continue;const width=q+D,cells=new Map();
   let U0=0,V=0,ex=0,st=0,tail=0;
   for(const e of tags){
    const a0=overlap(e.l,e.h,e.start,e.start+D)/(2*q),a1=overlap(e.l,e.h,e.cut-D,e.cut)/(2*q),w=a0+a1;
    ok(w<=e.w+1e-9,'disjoint window ends');e.edge=w;e.edgeCut=a1;e.edgeStart=a0;
    const id=Math.floor(e.t/width),cell=cells.get(id)||{n:0,U:0,V:0};cell.n++;cell.U+=e.w;cell.V+=w;cells.set(id,cell);e.cell=id;
    U0+=e.w;tail+=w;
    const dp=Math.min(E0,rho*e.p),end=C/2+dp;
    const v=e.p>=17?overlap(e.l,e.h,C/2,end)/(2*q):0;e.low=v;
    if(v>0){
     ok(e.t<end&&e.v>=C/2+(e.p-1)/2&&e.v-end>=e.p/4&&q>=e.p/8,'low deficit next clock');
     V+=v;lowGain+=q*v;
     if(e.cut>=end+e.p/4){const aft=overlap(e.l,e.h,end,end+e.p/4)/(2*q);ok(v<=4*rho*aft+1e-9,'strong strip ratio');st+=v;strongInc++;}
     else{ok(e.cut<e.v&&e.cut>C/2&&e.cut<C/2+3*q,'exception cutoff');ex+=v;exceptions++;}
    }
   }
   ok(st<=4*rho*U0+1e-9&&ex<=3*E0+1e-9,'strip envelope');maxExc=Math.max(maxExc,ex);
   E+=q*U0*U0;Rb+=q*U0;Rt+=q*tail;allTail+=q*(2*U0*tail-tail*tail);low+=q*V;lowStrong+=q*st;lowExc+=q*ex;Ex+=q*ex*ex;Rx+=q*ex;lowPaid+=q*(2*U0*V-V*V);
   for(const [id,c] of cells){cellChecks++;ok(c.V<=6*D+1e-9,'cell boundary cap');maxTail=Math.max(maxTail,c.V);Ec+=q*c.U*c.U;Et+=q*c.V*c.V;
    const g=cells.get(id+1);paid+=q*(2*c.U*c.V-c.V*c.V);
    if(g)paid+=2*q*(c.V*g.U+c.U*g.V-c.V*g.V);
   }
   let direct=0,ne=0;
   for(let i=0;i<tags.length;i++){const x=tags[i];const diagonal=q*(2*x.w*x.edge-x.edge*x.edge);direct+=diagonal;cutPaid+=q*(2*x.w*x.edgeCut-x.edgeCut*x.edgeCut);startPaid+=q*(2*x.w*x.edgeStart-x.edgeStart*x.edgeStart);
    for(let j=0;j<i;j++){const y=tags[j],v=2*q*(x.w*y.w-(x.w-x.edge)*(y.w-y.edge)),e=2*q*x.w*y.w;
     if(x.t===y.t)allSync+=e;else allAsync+=e;
     if(Math.abs(x.cell-y.cell)<=1){direct+=v;oracleChecks++;if(x.t===y.t)sync+=v;else nearAsync+=v;if(v>0)nearPairs++;
      const ac=2*q*(x.w*y.w-(x.w-x.edgeCut)*(y.w-y.edgeCut)),as=2*q*(x.w*y.w-(x.w-x.edgeStart)*(y.w-y.edgeStart));cutPaid+=ac;startPaid+=as;
      // union of edge and low masks, each actual interval measured.
      const endX=C/2+Math.min(E0,rho*x.p),endY=C/2+Math.min(E0,rho*y.p);
      const ix=x.low? (overlap(x.l,x.h,Math.max(C/2,x.start),Math.min(endX,x.start+D))+overlap(x.l,x.h,Math.max(C/2,x.cut-D),Math.min(endX,x.cut)))/(2*q):0;
      const iy=y.low? (overlap(y.l,y.h,Math.max(C/2,y.start),Math.min(endY,y.start+D))+overlap(y.l,y.h,Math.max(C/2,y.cut-D),Math.min(endY,y.cut)))/(2*q):0;
      const ux=x.edge+x.low-ix,uy=y.edge+y.low-iy;
      ok(ux<=x.w+1e-9&&uy<=y.w+1e-9,'union actual intervals');lowAndTail+=2*q*(x.w*y.w-(x.w-ux)*(y.w-uy));
     }else farAsync+=v;
    }
   }oracle+=direct;
  }
  const eps=1e-6*Math.max(1,E);
  ok(Math.abs(paid-oracle)<=eps&&Ec<=E+eps&&Rt<=N*D+eps&&Et<=6*D*Rt+eps&&paid<=6*Math.sqrt(Ec*Et)+eps&&paid<=eta*E+9*Et/eta+eps,'cell energy budget');
  ok(Rx<=N*E0/2+eps&&Ex<=3*E0*Rx+eps&&lowPaid<=8*rho*E+2*Math.sqrt(E*Ex)+eps&&lowPaid<=(8*rho+eta)*E+Ex/eta+eps,'low-strip absorption');
  results.push({sector:b,D,E0,E,R:Rb,Ec,Et,Rt,paid,allTail,sync,nearAsync,farAsync,cutPaid,startPaid,oracleChecks,maxTail,cellChecks,nearPairs,allSync,allAsync,low,lowStrong,lowExc,Ex,Rx,maxExc,lowPaid,lowGain,exceptions,strongInc,lowAndTail});
 }
 return {excursions,X,B,mode,a,H,eta,rho,N,R,events,literal,results};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536])for(const mode of ['analytic','diagnostic','wide','full'])console.log(JSON.stringify(audit(X,mode)));
