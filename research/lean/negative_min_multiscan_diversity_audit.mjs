// Independent finite audit of multi-successor scans. The finite thresholds
// are deliberately small; asymptotic separation Y1 > B*Ystar is NOT assumed.
function audit(Rs=[12000,48000,192000]){
 const mod=(x,p)=>(x%p+p)%p;
 const gcd=(a,b)=>{a=Math.abs(a);while(b){let t=a%b;a=b;b=t}return a};
 let checks=0;function ck(b,msg){if(!b)throw Error(JSON.stringify(msg));checks++}
 const spf=new Int32Array(2*Math.max(...Rs)+64);
 for(let p=2;p*p<spf.length;p++)if(!spf[p])for(let j=p*p;j<spf.length;j+=p)if(!spf[j])spf[j]=p;
 const lpf=n=>spf[n]||n;
 const z=5,Y=17,Yb=31,Y1=97,Ystar=47,U=4,D=2,h=2,k=4,Qz=30;
 const slow=e=>BigInt(e.w)**5n>=BigInt(e.p)**3n;
 const rough=e=>BigInt(2*e.q)**5n>=BigInt(e.p)**3n;
 function next(x,n,ps){let p=0,w=Infinity;for(let q of ps)for(let sign of [-1,1])if(mod(x-sign,q)===0){let d=mod((sign===-1?0:q+2)-n,2*q)||2*q;if(d<w||d===w&&q<p){p=q;w=d}}
 return {p,w}}
 function reconstruction(es,i,j,row){
  let a=es[i],mid=es.slice(i+1,j),qs=[...new Set(mid.filter(e=>e.p>z).map(e=>e.p))],ps=[3,5,...qs],counts=new Map(),E=0,pins=new Set();
  let x=a.x-a.p+1,n=a.n;
  for(let e of mid){
   if(e.p>z&&!pins.has(e.p)){
    let G=E+qs.reduce((sum,q)=>sum+(counts.get(q)||0)*(q-1),0);
    ck(x===a.x-a.p+1-G,'count compression');
    ck(mod(a.x,e.p)===mod(a.p-1+G+e.sign,e.p),'first use pin');pins.add(e.p);
   }
   let b=next(x,n,ps);ck(b.p===e.p&&n+b.w===e.n&&x===e.x,'restricted reconstruction');
   n=e.n;x-=e.p-1;row.reconstructed++;
   if(e.p<=z)E+=e.p-1;else counts.set(e.p,(counts.get(e.p)||0)+1);
  }
  if(j<es.length)ck(x===es[j].x,'target position');
  row.maxIntermediate=Math.max(row.maxIntermediate,mid.length);
  return {x,n,qs,G:a.x-a.p+1-x};
 }
 let rows=[];
 for(let R of Rs){
  let row={R,roots:0,ticks:0,events:0,high:{large:0,fast:0,slow:0,sat:0,end:0},medium:{narrow:0,big:0,fast:0,slow:0,end:0},reconstructed:0,maxIntermediate:0,repeatSourceInMedium:0,highSameTarget:0,joint:0,largeSaturations:0,lowChunks:0,mediumCharge:0,goodMediumCharge:0};
  let T=Math.ceil(Math.sqrt(2*R+1)),W=6*Math.floor(T/6),lo=6*Math.ceil(R/6),hi=6*Math.floor(2*R/6);
  for(let l=lo;l<=hi;l+=W)for(let A=l;A<=Math.min(hi,l+W-6);A+=6){
   row.roots++;let x=A,last=3-A/2,es=[],end=3-l/2+T;
   for(let n=last+1;n<=end;n++){
    let g=n%2===0?gcd(n,x+1):gcd(n-2,x-1),p=g>1?lpf(g):0;row.ticks++;
    if(p){let e={p,x,n,sign:n%2===0?-1:1,q:Math.min(lpf(x-1),lpf(x+1)),w:n-last};ck(e.w<=2*e.q&&e.w<=2*p,'wait cap');es.push(e);x-=p-1;last=n;row.events++}
   }
   let sat=0,low=0,largeSeen=new Set(),lowSeen=new Set(),largeBlock=0,blocks=new Map(),blockId=[],narrowStarts=new Set(),chunkGain=0,chunkEvents=0,maxLowEvents=0;
   function flush(){maxLowEvents=Math.max(maxLowEvents,chunkEvents);if(!lowSeen.size)ck(chunkGain<Qz,'empty wall');else ck(chunkGain<=chunkEvents*Y,'low gain');lowSeen.clear();chunkGain=0;chunkEvents=0}
   for(let j=0;j<es.length;j++){
    let p=es[j].p;
    if(p>=Ystar){largeSeen.clear();largeBlock++}
    blockId[j]=largeBlock;
    let b=blocks.get(largeBlock)||{broad:0,small:new Set()};blocks.set(largeBlock,b);
    if(z<p&&p<Yb)b.broad++;
    if(z<p&&p<Y){b.small.add(p);largeSeen.add(p);if(largeSeen.size>D){sat++;largeSeen.clear()}}
    if(p>=Y){flush();continue}
    chunkGain+=p-1;chunkEvents++;
    if(p>z){if(!lowSeen.size)low++;lowSeen.add(p);if(lowSeen.size>D)flush()}
   }
   flush();row.largeSaturations+=sat;row.lowChunks+=low;
   let usedSat=new Set(),usedJoint=new Set(),bad=new Map(),badWeight=0,mediumWeight=0,good=0,maxMed=0;
   for(let i=0;i<es.length;i++){
    let a=es[i],p=a.p;
    if(p>=Y1){
     let seen=new Set(),hs=new Set(),j=i+1,why='end';
     for(;j<es.length;j++){let e=es[j],r=e.p;
      if(r>=Ystar){why='large';break}
      if(z<r&&r<Y){seen.add(r);if(seen.size>D){why='sat';break}}
      if(r>=Y&&!hs.has(r)){if(!slow(e)){why='fast';break}hs.add(r);if(hs.size===h){why='slow';break}}
     }
     row.high[why]++;
     let v=reconstruction(es,i,j,row);ck(v.qs.length<=D+h-1,'high support');
     if(why==='sat'){ck(!usedSat.has(blockId[i]),'disjoint high source blocks');usedSat.add(blockId[i]);
      let j0=i+1;while(j0<es.length&&es[j0].p<Yb)j0++;
      let count=es.slice(i+1,j0).filter(e=>e.p>z&&e.p<Yb).length;
      if(j0<es.length&&count>k){let b=blocks.get(blockId[i]);ck(b.broad>k&&b.small.size>D,'joint trigger');ck(!usedJoint.has(blockId[i]),'joint injection');usedJoint.add(blockId[i]);row.joint++}
     }
     if(j<es.length&&why!=='sat'){
      let b=es[j];if(b.p===p){row.highSameTarget++;ck(v.G>=p-1,'same label relay gap')}
      if(v.G<p-1)ck(b.p!==p,'separated source target');
      if(why==='fast')ck(!v.qs.includes(b.p)&&b.p!==p,'fresh fast target');
      if(why==='slow')ck(slow(b)&&[...hs].length===h,'slow distinct count');
     }
    }
    if(Y<=p&&p<Y1&&rough(a)){
     let hs=new Set([p]),j=i+1,why='end';
     for(;j<es.length;j++){let e=es[j],r=e.p;
      if(z<r&&r<Y){why='narrow';break}
      if(r>=U*Y1){why='big';break}
      if(r>=Y&&!hs.has(r)){if(!slow(e)){why='fast';break}hs.add(r);if(hs.size===h+1){why='slow';break}}
     }
     row.medium[why]++;let v=reconstruction(es,i,j,row);maxMed=Math.max(maxMed,j-i);
     ck(v.qs.length<=h,'medium support');
     if(v.qs.includes(p))row.repeatSourceInMedium++;
     let charge=2*a.q;mediumWeight+=charge;ck(charge<=2*p,'charge cap');
     if(why==='narrow'||why==='big'||why==='end'){
      let arr=bad.get(j)||{count:0,why,weight:0};ck(arr.why===why,'same stop reason');arr.count++;arr.weight+=charge;bad.set(j,arr);badWeight+=charge;
      if(why==='narrow'){narrowStarts.add(j);ck(es[j].p>z&&es.slice(i+1,j).every(e=>e.p<=z||e.p>=Y),'first narrow')}
     }else{good+=charge;let b=es[j];ck(b.p!==p&&!v.qs.includes(b.p),'fresh medium target');
      if(why==='slow'){ck(hs.size===h+1&&slow(b),'slow stop');let positions=[a.x];let seen=new Set([p]);for(let e of es.slice(i+1,j+1))if(e.p>=Y&&!seen.has(e.p)){seen.add(e.p);ck(slow(e)&&rough(e),'slow rough');positions.push(e.x)}
       let forms=positions.flatMap(x=>[x-1,x+1]);ck(new Set(forms).size===2*(h+1),'distinct forms')}
     }
    }
   }
   ck(usedSat.size<=sat,'saturation charge');ck(narrowStarts.size<=low,'low chunk charge');
   for(let [j,b] of bad){ck(b.count<=maxMed&&b.weight<=2*Y1*maxMed,'bad source multiplicity')}
   ck(mediumWeight===good+badWeight,'medium partition');
   row.mediumCharge+=mediumWeight;row.goodMediumCharge+=good;
  }
  rows.push(row);
 }
 return {checks,rows}
}
const args=typeof process==="undefined"?[]:process.argv.slice(2).map(Number);
if(typeof console!=="undefined")console.log(JSON.stringify(audit(args.length?args:[12000,48000,192000]),null,2));
