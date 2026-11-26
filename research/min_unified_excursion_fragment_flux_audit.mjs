// Actual excursion-time fragments and nonreused height matching.
function audit(Xs=[4096,16384,65536]){
 const ok=(x,m)=>{if(!x)throw Error(m)},mod=(a,b)=>(a%b+b)%b;
 let lim=7*Math.max(...Xs)+100,spf=new Int32Array(lim+1);for(let p=2;p<=lim;p++)if(!spf[p])for(let j=p;j<=lim;j+=p)spf[j]=p;
 let results=[];
 for(let X of Xs)for(let focus of [false,true]){
  let B=Math.ceil(Math.sqrt(7*X)),T=focus?Math.floor(B/2):Math.min(8*B,Math.floor(X/2)),H=T+B,tags=[],events=0;
  for(let M=X|1;M<2*X;M+=2)if(spf[M]===M){let C0=2*M-2,C=C0,t=M+2,path=[];
   while(C-C0<T){let p=0,w=Infinity;for(let I=0;I<2;I++){let v=C-1+2*I;while(v>1){let f=spf[v];while(v%f===0)v/=f;if(f*f>C+1)continue;let r=mod((I?f+2:0)-t,2*f)||2*f;if(r<w||r===w&&f<p){p=f;w=r}}}if(!p)break;
    let J=C+p-1,n=t+w,I=n%2,d=2*t-C,dp=2*n-J;path.push({C,t,J,n,I,e:1-2*I,p,w,g:p-1,d,dp,j:path.length});events++;C=J;t=n;
   }
   // Exact last-up matching of unit height intervals, for all actual decreases above 6.
   let high=6,last=new Map(),matches=0;
   for(let e of path){e.up=[];e.exc=high;if(e.dp>e.d){for(let a=Math.max(6,e.d);a<e.dp;a++){ok(!last.has(a),"no repeated open height");last.set(a,e.j)}}
    if(e.dp<e.d){for(let a=Math.max(6,e.dp);a<e.d;a++){ok(last.has(a),"prior actual ascent");let j=last.get(a);ok(j<e.j&&path[j].d<=a&&path[j].dp>a&&path[j].exc===e.exc,"same excursion matched ascent");e.up.push(j);last.delete(a);matches++}}
    if(e.dp<=6){ok(last.size===0,"no open high level at reset");high=e.j+7}
   }
   ok(last.size===Math.max(0,2*t-C-6),"terminal unmatched heights");tags.push({M,C0,F:C,df:2*t-C,path,matches})
  }
  for(let Y of [9,17,31,61])for(let capMult of [2,8]){
   let k=Math.floor(Math.sqrt(Y)),alpha=1-2/k,L=Math.max(4*Y*Y,Math.floor(H/4)),cap=capMult*Y,R=Math.max(Y,2*cap+1),r={X,focus,N:tags.length,events,Y,k,L,cap,R,bins:0,fragments:0,nonempty:0,kept:0,wide:0,zeroEntry:0,boundaryEntry:0,selected:0,F:0,drop:0,old:0,local:0,entry:0,terminal:0,positive:0,low:0,mid:0,large:0,G:0,midLabels:0,primeChecks:0,roughChecks:0,matchChecks:0,resetChecks:0,wideGain:0,sumWidth:0,maxWidthSum:0,multiGuards:0,strictWidthSaving:0,matchedSources:0,sourceReusedUnits:0};
   for(let t of tags){
    let bins=new Map();for(let e of t.path){let b=Math.floor((e.C-t.C0)/L);if(!bins.has(b))bins.set(b,[]);bins.get(b).push(e)}
    for(let es of bins.values()){
     r.bins++;let G=es.reduce((s,e)=>s+e.g,0);r.G+=G;ok(G<=L+B,"actual bin gain");let frags=[];
     for(let e of es){if(!frags.length||frags.at(-1)[0].exc!==e.exc)frags.push([]);frags.at(-1).push(e)}
     let entry=0,term=0,drop=0,F=0,positive=0,low=0,mid=0,large=0,old=0,local=0,sumWidth=0,maxWidth=0,guards=0,primeMap=new Map(),used=new Map();
     for(let fi=0;fi<frags.length;fi++){
      let fs=frags[fi];r.fragments++;if(fi>0)ok(fs[0].d<=6,"fresh fragment starts low");
      let sel=fs.filter(e=>e.p>=Y&&e.dp>6&&k*e.w<e.g);if(!sel.length)continue;r.nonempty++;
      let u=[];for(let e of sel.slice().sort((a,b)=>a.dp-b.dp)){let a=e.dp,b=a+e.g,last=u.at(-1);if(last&&a<=last[1])last[1]=Math.max(last[1],b);else u.push([a,b])}
      let width=u.reduce((s,[a,b])=>s+b-a,0),phi=d=>u.reduce((s,[a,b])=>s+Math.max(0,Math.min(b,d)-a),0);
      if(width>cap){r.wide++;r.wideGain+=sel.reduce((s,e)=>s+e.g,0);continue}
      r.kept++;guards++;sumWidth+=width;maxWidth=Math.max(maxWidth,width);
      let pi=phi(fs[0].d),pt=phi(fs.at(-1).dp),pp=0,nn=0,dd=0,fg=0,oo=0,ll=0;
      if(fs[0].d<=6){ok(pi===0,"zero entry");r.zeroEntry++}else{ok(fi===0,"only first fragment can inherit");r.boundaryEntry++}
      for(let e of fs){let z=phi(e.dp)-phi(e.d);pp+=Math.max(z,0);nn+=Math.max(-z,0);
       if(e.dp<=6){ok(z<=0,"low arrival not a source");r.resetChecks++}
       if(z>0){ok(z<=Math.min(width,3*e.p+1)&&2*e.w>e.g,"source overlap");
        if(e.p<Y)low+=z;else if(e.p>R)large+=z;else {mid+=z;let id=e.p+"/"+e.I,q=primeMap.get(id)||{p:e.p,I:e.I,n:0,first:e.C,last:e.C};ok(q.n===0||mod(e.C-q.last,e.p)===0,"source progression");q.n++;q.last=e.C;primeMap.set(id,q);for(let f=3;4*f<e.g;f+=2)if(spf[f]===f){ok((e.C-1)%f!==0&&(e.C+1)%f!==0,"source roughness");r.roughChecks++}}
       }
      }
      for(let e of sel){r.selected++;fg+=e.g;let v=e.d-e.dp;ok(v>alpha*e.g&&phi(e.d)-phi(e.dp)===v&&e.up.length===v,"full fast drop");dd+=v;
       for(let i=0;i<e.up.length;i++){let j=e.up[i],a=e.dp+i;ok(j<e.j&&t.path[j].exc===e.exc,"matched source chronology");let key=j+"/"+a;ok(!used.has(key),"no reused source height");used.set(key,1);
        if(j<fs[0].j)oo++;else{ll++;ok(j<=fs.at(-1).j&&phi(t.path[j].dp)-phi(t.path[j].d)>0,"same fragment positive source")}
        r.matchChecks++;
       }
      }
      ok(pp-nn===pt-pi&&dd<=nn&&oo<=pi&&dd===oo+ll&&ll<=pp,"fragment exact transport");
      entry+=pi;term+=pt;drop+=dd;F+=fg;positive+=pp;old+=oo;local+=ll;
     }
     ok(entry<=cap&&old<=entry&&drop+term<=positive+entry&&positive===low+mid+large&&large<=cap*G/(R-1)+1e-7,"bin resource balance");
     ok(used.size===drop,"matched units distinct");r.matchedSources+=new Set([...used.keys()].map(x=>x.split("/")[0])).size;
     for(let q of primeMap.values()){ok(q.n<=1+L/q.p,"local prime count");r.primeChecks++}
     r.midLabels+=new Set([...primeMap.values()].map(q=>q.p)).size;
     for(let [key,v] of Object.entries({F,drop,old,local,entry,terminal:term,positive,low,mid,large,sumWidth,maxWidthSum:maxWidth}))r[key]+=v;
     if(guards>1)r.multiGuards++;if(sumWidth>cap)r.strictWidthSaving++;
    }
   }
   ok(r.drop+r.terminal<=r.positive+r.entry&&r.entry<=r.cap*r.bins&&r.old<=r.entry&&r.positive===r.low+r.mid+r.large,"global balance");
   results.push(r)
  }
 }
 return results
}
console.log(JSON.stringify(audit(process.argv.length>2?process.argv.slice(2).map(Number):undefined),null,2));
