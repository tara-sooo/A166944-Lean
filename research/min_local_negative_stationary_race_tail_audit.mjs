// Exact stationary first-clock race, finite product probabilities and tail/phase diagnostics.
function audit(){
 const ck=(v,m)=>{if(!v)throw Error(typeof m==="string"?m:JSON.stringify(m))},mod=(a,p)=>(a%p+p)%p;
 const N=8000000,comp=new Uint8Array(N+1),pr=[];
 for(let p=2;p*p<=N;p++)if(!comp[p])for(let n=p*p;n<=N;n+=p)comp[n]=1;
 for(let p=3;p<=N;p+=2)if(!comp[p])pr.push(p);
 const qs=pr.filter(p=>p>=5);
 function clock(p,side,par){let x=side===0?(p-1)/2:(p+1)/2;if(mod(x,2)!==par)x+=p;let c=side===0?0:p+2;return 3+(mod(x+c-3,2*p)||2*p)}
 function V(y){let prod=1;for(let q of qs){if(q>y)break;prod*=1-2/q}return prod}
 let out={races:0,clockEvents:0,conservationChecks:0,certificateChecks:0,tailControls:0,residueControls:0,rows:[]};
 for(let Z of [50,200])for(let par of [0,1]){
  const maxP=2000000,events=[];
  for(let p of qs){if(p>4*maxP+10)break;if(p<=Z)continue;for(let side of [0,2])events.push([clock(p,side,par),p,side])}
  events.sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2]);
  let surv=1,total=0,counts=new Uint8Array(N+1),mass=new Map(),m2=new Map();
  const controls=[1000,10000,100000,1000000].filter(Y=>Y>8*Z).map(Y=>({Y,maxP,total:0,short:0,plus:0,canonical:0,pclass:new Array(4).fill(0),unit5:new Array(5).fill(0),unit7:new Array(7).fill(0)}));
  for(let [h,p,side] of events){
   let old=counts[p];ck(old<2,"clock count");let event=surv/(p-old);surv-=event;total+=event;counts[p]++;out.clockEvents++;
   if([1009,10007,100003,1000003].includes(p)){
    let prod=1;
    for(let q of qs){if(q>2*h+7)break;if(q<=Z||q===p)continue;let nu=0;
     for(let s of [0,2]){let hh=clock(q,s,par);nu+=+(hh<h||hh===h&&q<p)}
     prod*=1-nu/q;
    }
    ck(Math.abs(event-prod/p)<1e-10*prod/p+1e-15,{p,side,h,event,expected:prod/p});out.certificateChecks++;
   }
   for(let row of controls)if(p>=row.Y&&p<=maxP){
    row.total+=event;let short=mod(p,4)===mod(2*par+1,4);if(short)row.short+=event;if(side===2)row.plus+=event;
    if(short&&side===2&&p%3===1){row.canonical+=event;row.unit5[p%5]+=event;row.unit7[p%7]+=event;}
    row.pclass[[1,5,7,11].indexOf(p%12)]+=event;
   }
  }
  ck(Math.abs(total+surv-1)<1e-9,"prob conservation");out.conservationChecks++;
  for(let row of controls){let predicted=(V(row.Y-1)-V(maxP))/V(Z);ck(predicted>0&&row.total>0,"nonzero");out.tailControls++;out.residueControls+=4+6;
   out.rows.push({Z,par,Y:row.Y,Pmax:maxP,exact:row.total,predicted,ratio:row.total/predicted,short:row.short/row.total,plus:row.plus/row.total,canonical:row.canonical/row.total,pclass:row.pclass.map(x=>x/row.total),unit5:row.unit5.map(x=>x/row.canonical),unit7:row.unit7.map(x=>x/row.canonical)});
  }
  out.races++;
 }
 return out
}
console.log(JSON.stringify(audit(),null,2));
