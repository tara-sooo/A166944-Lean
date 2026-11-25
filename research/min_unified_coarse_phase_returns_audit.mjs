// Coarse phase class rank and primitive one-edge return obstruction audit.
function audit(X,focus=false){
 const B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),lim=7*X+B+20,S=new Int32Array(lim),wheels=[6,30,210],theta=.5;
 const ok=(b,m)=>{if(!b)throw Error(`${X}/${focus} ${m}`)},mod=(a,b)=>(a%b+b)%b;
 for(let p=2;p<lim;p++)if(!S[p]){S[p]=p;if(p*p<lim)for(let n=p*p;n<lim;n+=p)S[n]=S[n]||p}
 function fac(n){let a=[];while(n>1){let p=S[n];if(p>2&&p<=B)a.push(p);while(n%p===0)n/=p}return a}
 let N=0,events=0,hit=0,G=0,W=0,proj=new Map(),paths=[],pairs=0,primitive=0,oneMulti=0,periodic=0,signChecks=0,equalLag=0,nonperiodic=0,strictGap=0;
 const stats=wheels.map(L=>({L,y:L===6?3:L===30?5:7,classes:0,thinClasses:0,rankChecks:0,rankPaid:0,thinPaid:0,raw:0,phaseFar:0,energy:0,matchedArrivals:0,intervals:0,lagChanges:0,shortIntervals:0,shortOneMulti:0,shortNonperiodic:0,shortCommonEdge:0,nontranslated:0,translated:0,firstDefects:0,primitivePhase:0,primitiveOneMulti:0,positiveFarLower:0}));
 for(let M=X;M<2*X;M++)if(S[M]===M){
  N++;let C=2*M-2,C0=C,t=M+2,cut=Math.floor((7*M-1)/4),es=[];
  while(C-C0<T){let p=0,v=Infinity,r=Infinity;for(let s of [-1,1])for(let q of fac(C+s)){r=Math.min(r,q);let j=t+1+mod((s===-1?0:q+2)-t-1,2*q);if(j<v||(j===v&&q<p)){p=q;v=j}}
   if(!p||v>cut)break;let g=p-1,J=C+g,w=v-t;ok(w<=2*r&&w<=3*g,"wait");
   let e={C,J,p,t,v,w,g,r,i:es.length,es};es.push(e);
   let k=C+"|"+p,o=proj.get(k)||{C,p,n:0,slots:new Map()};proj.set(k,o);let a=o.slots.get(v)||{v,b:0,e};o.slots.set(v,a);a.b++;o.n++;
   G+=g;W+=w;events++;C=J;t=v;
  }es.push({C,t,i:es.length,terminal:true});if(C-C0>=T)hit++;paths.push(es);
 }
 for(let o of proj.values()){
  let ss=[...o.slots.values()].sort((a,b)=>a.v-b.v);
  for(let z of stats){
   let L=z.L,A=L/2,cl=new Map();
   for(let s of ss){let h=mod(s.v,L),a=cl.get(h)||[];a.push(s);cl.set(h,a)}
   ok(cl.size<=A,"class count");
   z.classes+=cl.size;z.raw+=o.n;
   for(let a of cl.values()){let n=a.reduce((s,x)=>s+x.b,0);
    // finite proxy for phase cap: n<= 2/A.
    if(n<=2/A){z.thinClasses++;z.thinPaid+=n;continue}
    let cum=0;a.sort((a,b)=>a.b-b.b||a.v-b.v);
    for(let s of a){cum+=s.b;z.rankChecks++;if(cum<=theta*n){z.rankPaid+=s.b;continue}
      let smaller=a.filter(t=>t.b<=s.b).reduce((v,t)=>v+t.b,0),R=o.p,step=lcm(2*o.p,L),near=Math.floor(2*R/step)+1;
      let f=a.filter(t=>t.b<=s.b&&Math.abs(t.v-s.v)>R).reduce((v,t)=>v+t.b,0);
      ok(smaller>theta*n&&f>=smaller-near*s.b,"phase rank spacing");
      if(f)z.phaseFar++;if(near*s.b<=theta*n/2){ok(f>theta*n/2,"far lower");z.positiveFarLower++}
      z.energy+=s.b*f/n;
    }
   }
  }
  for(let i=0;i<ss.length;i++)for(let j=i+1;j<Math.min(i+4,ss.length);j++){
   let aa=ss[i].e,bb=ss[j].e,a=aa.es,b=bb.es,ia=aa.i+1,ib=bb.i+1,start=aa.J,cs=[];
   while(ia<a.length&&ib<b.length&&a[ia].C-start<=2*B&&b[ib].C-start<=2*B){
    if(a[ia].C<b[ib].C){ia++;continue}if(b[ib].C<a[ia].C){ib++;continue}
    cs.push({i:ia,j:ib,C:a[ia].C,d:b[ib].t-a[ia].t});ia++;ib++;
   }
   ok(cs.length>0&&cs[0].C===start,"shared posthorizon");pairs++;
   for(let h=1;h<cs.length;h++){let x=cs[h-1],y=cs[h],g=y.C-x.C,k=y.i-x.i,l=y.j-x.j,d=y.d-x.d,ap=a[x.i],bp=b[x.j];
    ok(k>0&&l>0&&Math.abs(d)<=3*g,"primitive lag Lipschitz");primitive++;
    if(k===1&&l>1||l===1&&k>1){
      oneMulti++;let single=k===1?ap:bp,multi=k===1?bp:ap,mCount=k===1?l:k,oriented=k===1?d:-d;
      ok(single.p>multi.p,"one-edge gain");if(x.d%(2*multi.p)===0){periodic++;ok(single.w<=multi.w&&oriented>=mCount-1,"periodic first label strict return");signChecks++;if(oriented>mCount-1)strictGap++}
      else{nonperiodic++;if(d===0)equalLag++}
    }
   }
   for(let z of stats){
    let hits=cs.filter(x=>x.d%z.L===0);z.matchedArrivals+=hits.length;
    for(let h=1;h<hits.length;h++){
      let x=hits[h-1],y=hits[h],g=y.C-x.C,d=y.d-x.d,k=y.i-x.i,l=y.j-x.j;
      ok(d%z.L===0&&Math.abs(d)<=3*g,"phase return");z.intervals++;
      if(d){z.lagChanges++;ok(g>=z.L/3,"quantized change")}
      let translated=k===l;for(let m=0;translated&&m<k;m++)translated=a[x.i+m].C===b[x.j+m].C&&a[x.i+m].p===b[x.j+m].p&&a[x.i+m].w===b[x.j+m].w;
      if(translated)z.translated++;else{z.nontranslated++;
       let m=0;while(x.i+m<y.i&&x.j+m<y.j&&a[x.i+m].C===b[x.j+m].C&&a[x.i+m].p===b[x.j+m].p&&a[x.i+m].w===b[x.j+m].w)m++;
       ok(x.i+m<y.i&&x.j+m<y.j&&Math.max(a[x.i+m].p,b[x.j+m].p)>z.y,"first defect large");z.firstDefects++;
      }
      if(g<z.L/3){z.shortIntervals++;ok(d===0,"short equal lag");if(k===1&&l===1){ok(translated,"single common edge");z.shortCommonEdge++}
       if(k===1&&l>1||l===1&&k>1){z.shortOneMulti++;let p=k===1?a[x.i].p:b[x.j].p,q=k===1?b[x.j].p:a[x.i].p;ok(p>q&&q>z.y&&x.d%(2*q)!==0,"short one-edge return obstruction");z.shortNonperiodic++}
      }
    }
    for(let h=1;h<cs.length;h++)if(cs[h-1].d%z.L===0&&cs[h].d%z.L===0){z.primitivePhase++;let k=cs[h].i-cs[h-1].i,l=cs[h].j-cs[h-1].j;if(k===1&&l>1||l===1&&k>1)z.primitiveOneMulti++}
   }
  }
 }
 function gcd(a,b){while(b){let t=a%b;a=b;b=t}return a}function lcm(a,b){return a/gcd(a,b)*b}
 for(let z of stats){ok(z.rankPaid<=theta*z.raw+1e-7&&z.energy<=z.raw+1e-7,"rank/energy budget");z.energy=+z.energy.toFixed(6)}
 return {X,focus,B,T,N,events,hit,G,W,pairs,primitive,oneMulti,periodic,nonperiodic,signChecks,strictGap,equalLag,stats};
}
for(const X of (process.argv.length>2?process.argv.slice(2).map(Number):[1024,4096,16384,65536]))console.log(JSON.stringify(audit(X)));for(const X of [4096,16384,65536])console.log(JSON.stringify(audit(X,true)));
