// General primorial block transfer and one-large-sector energy certificate.
// Run node research/min_clock_wide_low_transfer_audit.mjs 1024 4096 16384 65536 262144
function audit(X,mode){
 const B=Math.ceil(Math.sqrt(7*X)),H=4*B,a=2*B,N=X/2,U=7*X+4,G=2*H+B+6;
 const ok=(b,m)=>{if(!b)throw Error(m);};
 ok(H+2*B<=Math.floor((7*(X+1)-1)/4)-(X+3),'prefix gate');
 const spf=new Int32Array(U);
 for(let p=2;p<U;p++)if(!spf[p]){spf[p]=p;if(p*p<U)for(let j=p*p;j<U;j+=p)if(!spf[j])spf[j]=p;}
 const f=Math.max(1,Math.log(Math.log(B)))**.25;
 const limit=B**(1/3)/f;
 let z=2,L=2;
 if(mode==='analytic'){for(let p=3;p<=B;p+=2)if(spf[p]===p){if(L*p>limit)break;L*=p;z=p;}}
 else{z=mode==='fixed3'?3:mode==='fixed5'?5:7;for(let p=3;p<=z;p+=2)if(spf[p]===p)L*=p;}
 const T=Math.min(B,Math.max(z+1,mode==='analytic'?Math.ceil(B**(1/3)):Math.ceil(Math.sqrt(B))));
 const b=1.5*L,margin=3*L+2*T+2,lo=X,hi=7*X/2-1,len=hi+1;
 const r=new Int32Array(len),W=new Float64Array(len),A=new Float64Array(len),M=new Float64Array(len),F=new Float64Array(len),trans=new Float64Array(len),mass=new Int32Array(len);
 let S0=0,ST=0;
 for(let j=lo;j<=hi;j++){const q=Math.min(spf[2*j-1],spf[2*j+1]);if(q<=B){r[j]=q;S0+=q;if(q<=T)ST+=q;}}
 function hit(t,C,K){let v=K+1,p=0;for(const side of [-1,1]){let n=C+side;while(n>1){const q=spf[n];if(q>B)break;const m=2*q,res=side===-1?0:q+2,w=t+1+(res-(t+1)%m+m)%m;if(q>2&&(w<v||(w===v&&w<=K&&q<p))){v=w;p=q;}while(n%q===0)n/=q;}}return [v,p];}
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a;};
 let events=0,literal=0,twins=0,R=0,Rlow=0,Rmid=0,Rhigh=0,Rtransfer=0,Rtail=0,Rbig=0,Rtrim=0,destCost=0,destCount=0,lowBlocks=0,positiveBlocks=0,maxGain=0,maxElapsed=0,maxBlockCost=0,highHits=0,lowEvents=0,midEvents=0,postChecks=0;
 // Also test a destination-aware deterministic mask at high labels, and a separate
 // natural medium mask whose lost occupation is explicitly charged (not silently dropped).
 const Mmask=new Float64Array(len),Fmask=new Float64Array(len);
 let RmidMask=0,RhighMask=0,maskedDestCost=0,maskedTransferred=0,maskDestCount=0,RmidLost=0,RhighLost=0;
 for(let root=X+1;root<2*X;root+=2){
  const s=root+2,K=Math.floor((7*root-1)/4);
  let t=s,C=2*root-2,rootR=0,gain=0,elapsed=0,lowCost=0,lowTrim=0,lastLowEnd=0,blockStart=0;
  const rootLowStart=C;
  function reset(){gain=0;elapsed=0;lowCost=0;lowTrim=0;lastLowEnd=0;blockStart=0;}
  function closeBlock(){
   if(gain){lowBlocks++;positiveBlocks+=+(lowCost>0);maxGain=Math.max(maxGain,gain);maxElapsed=Math.max(maxElapsed,elapsed);maxBlockCost=Math.max(maxBlockCost,lowCost);}
   ok(gain<L&&elapsed<=3*gain&&lowCost<=b,'full primorial block bound');
  }
  while(t<s+H){
   const [v,p]=hit(t,C,K);
   if(X===1024){let vv=K+1,pp=0;for(let j=t+1;j<=K;j++){const n=gcd(j%2?j-2:j,j%2?C+1:C-1);if(n>1&&spf[n]<=B){vv=j;pp=spf[n];break;}}ok(vv===v&&pp===p,'literal MIN');literal++;}
   if(!p){ok(!r[C/2]&&spf[C-1]===C-1&&spf[C+1]===C+1,'terminal twin');twins++;break;}
   const q=r[C/2],D=C+p-1,cl=Math.max(t,s+a),cr=Math.min(v,s+H),dur=Math.max(0,cr-cl),cost=dur/2,w=cost/q;
   ok(q>0&&q<=p&&v-t<=2*q&&C<=2*t&&D<=2*v&&D-rootLowStart<=G,'clock and gain');
   events++;R+=cost;rootR+=cost;W[C/2]+=w;
   const keep=((root+v+p)%5)!==0;
   if(p<=z){
    lowEvents++;Rlow+=cost;A[C/2]+=w;
    if(!gain)blockStart=C;
    gain+=p-1;elapsed+=v-t;lowCost+=cost;
    const tr=Math.max(0,Math.min(v,s+H-margin)-Math.max(t,s+a))/2;
    lowTrim+=tr;if(tr>0)lastLowEnd=v;
    ok(gain<L&&elapsed<=3*gain&&lowTrim<=lowCost,'LOW barrier');
   }else{
    closeBlock();
    if(p<=T){
     midEvents++;Rmid+=cost;M[C/2]+=w;
     if(keep){RmidMask+=cost;Mmask[C/2]+=w;}else RmidLost+=cost;
     if(lowTrim>0){
      ok(lastLowEnd<=t&&t>=s+a&&v<=s+H&&cost===(v-t)/2&&cost>=.5,'natural full destination wait');
      ok(C-blockStart===gain&&C-blockStart<L,'destination gain');
      Rtransfer+=lowTrim;destCost+=cost;destCount++;mass[C/2]++;trans[C/2]+=lowTrim;postChecks++;
      if(keep){maskedDestCost+=cost;maskedTransferred+=lowTrim;maskDestCount++;}
     }
     Rtrim+=lowCost-lowTrim;
    }else{
     highHits++;Rhigh+=cost;F[C/2]+=w;Rbig+=lowCost;
     if(keep){RhighMask+=cost;Fmask[C/2]+=w;}else RhighLost+=cost;
    }
    reset();
   }
   C=D;t=v;
  }
  closeBlock();Rtail+=lowCost;ok(rootR<=B,'per root budget');
 }
 let E=0,Elow=0,Emid=0,Ehigh=0,Elarger=0,EmidMask=0,EhighMask=0,n2=0,maxMass=0,transferEnergy=0,RtransferCheck=0;
 for(let j=lo;j<=hi;j++){const q=r[j];E+=q*W[j]**2;Elow+=q*A[j]**2;Emid+=q*M[j]**2;Ehigh+=q*F[j]**2;Elarger+=q*(M[j]+F[j])**2;EmidMask+=q*Mmask[j]**2;EhighMask+=q*Fmask[j]**2;n2+=mass[j]**2;maxMass=Math.max(maxMass,mass[j]);transferEnergy+=trans[j]**2/b;RtransferCheck+=trans[j];ok(mass[j]<=2*q*M[j]+1e-7,'destination count dominated by original full waits');}
 const eps=1e-6*Math.max(1,E,R);
 ok(Math.abs(R-Rlow-Rmid-Rhigh)<=eps&&Math.abs(Rlow-Rtransfer-Rtail-Rbig-Rtrim)<=eps&&Math.abs(Rtransfer-RtransferCheck)<=eps,'linear partitions');
 ok(Rtail<=N*b+eps&&Rbig<=highHits*b+eps&&highHits*(T-1)<=N*G+eps&&Rtrim<=N*margin/2+eps,'linear losses');
 ok(Rtransfer<=2*b*destCost+eps&&destCost<=Rmid+eps&&destCount<=2*destCost+eps,'natural destination injection');
 ok(Rmid**2<=ST*Emid+1e-6*Math.max(1,Rmid**2)&&Rhigh**2<=S0*Ehigh+1e-6*Math.max(1,Rhigh**2),'energy Cauchy');
 ok(Rtransfer+Rmid<= (1+2*b)*Math.sqrt(ST*Emid)+eps,'joint low medium bound');
 ok(n2<=4*T*Emid+eps&&transferEnergy<=b*n2+eps,'transferred energy count');
 ok(Math.abs(RmidMask+RmidLost-Rmid)<=eps&&Math.abs(RhighMask+RhighLost-Rhigh)<=eps,'mask partition');
 ok(Rtransfer-maskedTransferred<=2*b*RmidLost+eps&&maskedTransferred<=2*b*maskedDestCost+eps&&maskedDestCost<=RmidMask+eps,'destination-aware mask loss');
 ok(Rlow+Rmid<=(1+2*b)*(Math.sqrt(ST*EmidMask)+RmidLost)+Rtail+Rbig+Rtrim+eps,'masked medium inequality');
 ok(RhighMask**2<=S0*EhighMask+1e-6*Math.max(1,RhighMask**2),'masked high Cauchy');
 return {X,B,mode,z,L,T,limit,margin,events,literal,twins,R,Rlow,Rmid,Rhigh,Rtransfer,Rtail,Rbig,Rtrim,destCost,destCount,lowBlocks,positiveBlocks,maxGain,maxElapsed,maxBlockCost,highHits,lowEvents,midEvents,postChecks,S0,ST,E,Elow,Emid,Ehigh,Elarger,n2,maxMass,transferEnergy,RmidMask,RhighMask,RmidLost,RhighLost,maskedTransferred,maskDestCount,EmidMask,EhighMask};
}
const args=typeof process!=='undefined'?process.argv.slice(2).map(Number):[];
for(const X of args.length?args:[1024,4096,16384,65536,262144])for(const mode of ['analytic','fixed3','fixed5','fixed7'])console.log(JSON.stringify(audit(X,mode)));
