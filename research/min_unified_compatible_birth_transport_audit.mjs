// Backward compatible-clock pair routing to actual first-meeting branches.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,Pset=[6,30,210],lens=[2,Math.max(2,Math.floor(B/16)),Math.max(2,Math.floor(B/32))],eta=.25,cut=focus?2:3,lim=7*X+B+20,S=new Int32Array(lim);
 const ok=(b,m)=>{if(!b)throw Error(`${X}/${focus} ${m}`)},eq=(a,b)=>Math.abs(a-b)<=1e-7*Math.max(1,Math.abs(a),Math.abs(b)),mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)if(!S[n])S[n]=p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let tags=[],proj=new Map(),N=0,events=0,W=0,hit=0,degree=0;
 const mk=()=>[0,0,0],key=(C,t)=>C+"|"+t;
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C0=2*M-2,C=C0,t=M+2,stop=Math.floor((7*M-1)/4),es=[],states=[],tag={M,es,states,end:0};
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>stop)break;let J=C+p-1,g=p-1,w=v-t;ok(w<=2*r&&w<=3*g,"wait");
   let e={C,J,p,g,w,t,v,i:es.length,tag,W:mk(),load:mk()};es.push(e);for(let j=t;j<v;j++)states.push({C,t:j,k:key(C,j),e});
   let k=C+"|"+p,o=proj.get(k)||{C,p,slots:new Map()};proj.set(k,o);let s=o.slots.get(v)||{v,refs:[]};o.slots.set(v,s);s.refs.push(e);e.o=o;e.s=s;events++;W+=w;C=J;t=v;
  }states.push({C,t,k:key(C,t),e:null});tag.end=C;if(C-C0>=T)hit++;tags.push(tag);
  for(let j=0;j<Pset.length;j++){let P=Pset[j],w=0;for(let e of es){w+=e.w;let n=Math.ceil(e.J/P)-Math.ceil(e.C/P);if(!n)continue;ok(w<=9*P*n,"cell");e.W[j]=w;w=0}}
 }
 function birth(a,b){let aa=a.tag.states,bb=b.tag.states,i=0,j=0;while(i<aa.length&&j<bb.length){let x=aa[i],y=bb[j];if(x.t<y.t){i++;continue}if(y.t<x.t){j++;continue}if(x.C===y.C)return {k:x.k,C:x.C,t:x.t,i,j};i++;j++}throw Error("no birth")}
 function prior(tag,i){return i?tag.states[i-1].k:"root:"+tag.M}
 function dest(e,i){let a=e.tag.states,x=a[i];if(i&&a[i-1].C!==x.C)return {e:a[i-1].e,role:"jump"};if(i)return {e:x.e,role:"wait"};return {e:null,role:"root"}}
 const stats=Pset.map(P=>({P,compatible:0,diag:0,smallBirth:0,smallBranches:0,rootPaid:0,nearPaid:0,routed:0,jump:0,wait:0,maxLoad:0,nonzero:0,keys:0}));
 let groups=0,directChecks=0,pairChecks=0,branchChecks=0,treeChecks=0,routeChecks=0,relativeChecks=0,rootCases=0;
 for(let o of proj.values()){
  let classes=new Map();for(let s of o.slots.values()){let c=mod(s.v,6),a=classes.get(c)||[];a.push(s);classes.set(c,a)}
  for(let a of classes.values()){let n=a.reduce((x,s)=>x+s.refs.length,0);
   for(let k=0;k<Pset.length;k++){let P=Pset[k],z=stats[k],nc=Math.ceil((o.C+o.p-1)/P)-Math.ceil(o.C/P);if(!nc)continue;let words=new Map();
    for(let s of a){let ready=s.refs.filter(e=>e.tag.end-e.J>=lens[k]);s.word=null;if(!ready.length)continue;let e=ready[0],es=e.tag.es,i=e.i+1,seq=[];while(es[i-1].J-e.J<lens[k]){let x=es[i++];seq.push(x.p+":"+x.w)}s.word=seq.join(",");words.set(s.word,(words.get(s.word)||0)+ready.length)}
    for(let s of a){let b=s.refs.length;if(b<cut||!s.refs.some(e=>e.W[k]&&e.tag.end-e.J>=lens[k]))continue;groups++;let cohort=s.refs,table=new Map();
     // Build the induced reverse merge tree up through the common predeparture tick.
     for(let e of cohort){let a=e.tag.states;for(let i=0;i<a.length&&a[i].t<s.v;i++){let x=a[i],v=table.get(x.k)||{n:0,br:new Map()};v.n++;let p=prior(e.tag,i);v.br.set(p,(v.br.get(p)||0)+1);table.set(x.k,v)}}
     let d=1;for(let v of table.values()){d=Math.max(d,v.br.size);ok([...v.br.values()].reduce((a,b)=>a+b,0)===v.n,"branch partition");treeChecks++}degree=Math.max(degree,d);
     let expected=cohort.filter(e=>e.tag.end-e.J>=lens[k]).reduce((a,e)=>a+e.W[k]*(words.get(s.word)||0)/n,0),before=z.compatible;let smallCounts=new Map(),parentCounts=new Map(),bound=eta*b/d;
     for(let i=0;i<b;i++)for(let j=i+1;j<b;j++){
      let x=cohort[i],y=cohort[j],f=birth(x,y),v=table.get(f.k);ok(v&&prior(x.tag,f.i)!==prior(y.tag,f.j),"first birth branches");let bx=v.br.get(prior(x.tag,f.i)),by=v.br.get(prior(y.tag,f.j));ok(bx+by<=v.n&&v.n<=b,"branch mass");pairChecks++;
      if(v.n<=eta*b){parentCounts.set(i,(parentCounts.get(i)||0)+1);parentCounts.set(j,(parentCounts.get(j)||0)+1)}
      if(Math.max(bx,by)<=bound){smallCounts.set(i,(smallCounts.get(i)||0)+1);smallCounts.set(j,(smallCounts.get(j)||0)+1)}
      for(let [focal,partner,fi,pi,fb,pb] of [[x,y,f.i,f.j,bx,by],[y,x,f.j,f.i,by,bx]]){
       if(focal.tag.end-focal.J<lens[k]||!focal.W[k])continue;
       let c=focal.W[k]*(words.get(s.word)||0)/n/b;z.compatible+=c;
       if(v.n<=eta*b){z.smallBirth+=c;continue}
       if(Math.max(fb,pb)<=bound){z.smallBranches+=c;continue}
       let sel=fb>=pb?focal:partner,idx=fb>=pb?fi:pi,D=dest(sel,idx);if(!D.e){z.rootPaid+=c;rootCases++;continue}
       // finite recent cut (two gain units), independent of entropy.
       if(o.C-f.C<2){z.nearPaid+=c;continue}
       ok(D.e.C<=f.C&&D.e.C<=o.C&&o.C-D.e.C<H,"birth destination interval");
       let br=v.br.get(prior(sel.tag,idx));ok(br>bound&&D.e.s.refs.length>=br,"heavy actual exit slot");branchChecks++;
       D.e.load[k]+=c;z.routed+=c;z[D.role]+=c;routeChecks++;
      }
     }
     for(let i=0;i<b;i++){ok((smallCounts.get(i)||0)<=(d+1)*bound+1e-7,"small branch count");ok((parentCounts.get(i)||0)<=eta*b+1e-7,"small parent count");relativeChecks++;let e=cohort[i];if(e.tag.end-e.J>=lens[k]&&e.W[k]){let c=e.W[k]*(words.get(s.word)||0)/n/b;z.compatible+=c;z.diag+=c}}
     ok(eq(z.compatible-before,expected),"direct compatible source mass");directChecks++;
    }
   }
  }
 }
 for(let k=0;k<Pset.length;k++){let z=stats[k],sum=0,keys=new Set();for(let tag of tags)for(let e of tag.es){let x=e.load[k];if(!x)continue;ok(x<=18*(H+Pset[k])+1e-7,"linear birth capacity");z.maxLoad=Math.max(z.maxLoad,x);sum+=x;z.nonzero++;keys.add(e.C+"|"+e.p+"|"+e.v)}
  z.keys=keys.size;ok(eq(sum,z.routed)&&eq(z.compatible,z.diag+z.smallBirth+z.smallBranches+z.rootPaid+z.nearPaid+z.routed)&&eq(z.routed,z.jump+z.wait),"conservation");for(let p of Object.keys(z))if(typeof z[p]==="number")z[p]=+z[p].toFixed(6)
 }
 return {X,focus,B,T,N,events,W,hit,degree,groups,directChecks,pairChecks,treeChecks,relativeChecks,branchChecks,routeChecks,rootCases,stats};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
