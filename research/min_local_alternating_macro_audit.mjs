// Exhaustive finite residue classification and BigInt literal controls for alternating macro words.
function alternatingAudit(){
 const mod=(x,m)=>(x%m+m)%m,source=p=>p%4===1?0:6,allowed=(p,e)=>p%6===1?[0]:e===-1?[2]:[2,8];
 let survivors=[],tested=0;
 for(let p of [1,5,7,11])for(let r of [1,5,7,11])for(let c=-16;c<=16;c+=2)if(c&&mod(p+c,12)===r)for(let e of [-1,1])for(let f of [-1,1])for(let E of allowed(p,e))for(let F of allowed(r,f))for(let G of allowed(p,-e)){
  tested++;
  if(mod(source(p)+p-1+E,12)!==source(r)||mod(source(r)+r-1+F,12)!==source(p)||mod(source(p)+p-1+G,12)!==source(r))continue;
  if(c!==2-2*e-E-F||-c!==2-2*f-F-G)continue;
  survivors.push({p,r,c,e,f,E,F,G});
 }
 if(survivors.length!==2||survivors.some(s=>Math.abs(s.c)!==2))throw Error("table");
 const isprime=n=>{if(n<2)return false;for(let p=2;p*p<=n;p++)if(n%p===0)return false;return true};
 const gcd=(x,y)=>{while(y){let z=x%y;x=y;y=z}return x<0n?-x:x};
 // Explicitly realize a four-word for an already-known admissible twin pair.
 let examples=[];
 for(let p=37;p<500;p++)if(p%12===5&&isprime(p)&&isprime(p+2)&&(p+1)%5===0){
   let r=p+2,h=p+1;
   const qs=Array.from({length:r+8},(_,i)=>i+3).filter(isprime).filter(q=>q<=r+7);
   let conditions=[[12,0]],possible=true;
   for(let q of qs){
     if(q===3)continue;
     if(q===p){conditions.push([q,q-1]);continue}
     if(q===r){conditions.push([q,2]);continue}
     let options=Array.from({length:q},(_,x)=>x).filter(x=>[0,1,2,3].every(i=>{let t=mod(x+i*h,q);return t!==1&&t!==q-1}));
     if(q===5)options=options.filter(x=>x!==3); // third macro relay must NOT use 5
     if(!options.length){possible=false;break}
     conditions.push([q,options[0]]);
   }
   if(!possible)continue;
   // Force both neighbors composite at each macro source without affecting any earlier candidate.
   let fresh=[];for(let q=r+8;fresh.length<4;q++)if(isprime(q))fresh.push(q);
   // The selected side is composite at a sufficiently large lift. Add proper factor on opposite side.
   const signs=[-1,1,1,-1];
   for(let i=0;i<4;i++)conditions.push([fresh[i],mod(-signs[i]-i*h,fresh[i])]);
   let x=0n,M=1n;
   for(let [q,s] of conditions){
      let Q=BigInt(q),k=0n;while((x+k*M)%Q!==BigInt(s))k++;
      x+=k*M;M*=Q;
   }
   x+=M;
   let u=x,v=x/2n+3n,ticks=0,events=[];
   const word=[[p,(p-1)/2,-1],[3,1,1],[r,(r-7)/2,1],[p,(p-1)/2,1],[3,4,1],[r,(r-1+6-6)/2,-1]];
   // r fourth starts with deficit 6, plus clock (r-1)/2.
   for(let [label,w,e] of word){
     let P=BigInt(label),W=BigInt(w);
     for(let i=1n;i<=W;i++){let n=v+i,g=gcd(n%2n?n-2n:n,n%2n?u+1n:u-1n);if(i===W){if(g%P!==0n)throw Error("selected missing");for(let q of qs)if(q<label&&g%BigInt(q)===0n)throw Error("tie");if((n%2n?-1:1)!==e)throw Error("sign")}else if(g!==1n)throw Error("early");ticks++}
     events.push({shift:Number(u-x),d:Number(2n*v-u),label,w,e});
     u+=P-1n;v+=W;
   }
   for(let i=0;i<4;i++){
     let H=x+BigInt(i*h),selected=BigInt(i%2===0?p:r),opp=BigInt(fresh[i]);
     if((H-BigInt(signs[i]))%selected!==0n||(H+BigInt(signs[i]))%opp!==0n||H-1n<=selected||H-1n<=opp)throw Error("proper factors");
   }
   examples.push({p,r,X:x.toString(),M:M.toString(),ticks,events,fresh});
   if(examples.length>=3)break;
 }
 return {tested,survivors,examples}
}
console.log(JSON.stringify(alternatingAudit(),null,2));
