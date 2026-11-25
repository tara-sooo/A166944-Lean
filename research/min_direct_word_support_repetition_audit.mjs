// Dense support-barrier budget between identical fixed-deficit tick words.
function audit(N=12000){
 const cap=300000,spf=new Int32Array(cap);for(let i=2;i<cap;i++)if(!spf[i]){spf[i]=i;if(i*i<cap)for(let j=i*i;j<cap;j+=i)if(!spf[j])spf[j]=i}
 const gcd=(a,b)=>{a=Math.abs(a);b=Math.abs(b);while(b)[a,b]=[b,a%b];return a};
 let st={roots:0,ticks:0,events:0,wordChecks:0,returnWords:0,repeatedWords:0,repeatedReturnWords:0,outsideEvents:0,outsideGain:0,barrierIncidences:0,multiplePeriodTests:0,maxRepeatMultiplicity:0,maxSupport:0,allSupportForbidden:0,shortJumpChecks:0};
 function support(word){let fs=[...new Set(word.filter(Boolean))],P=1n,A=1n;for(let p of fs){P*=BigInt(p);A*=BigInt((p-1)/2)}return{fs,P,A}}
 function test(rows,start,end,word,seen,key,ret=false){
  let H=rows[start].H,Hend=rows[end].H,{fs,P,A}=support(word);if(!fs.length)return;
  if(BigInt(Hend-H)>=2n*P)throw Error("support run capacity");st.wordChecks++;st.maxSupport=Math.max(st.maxSupport,fs.length);
  let v=seen.get(key);if(v){
   let D=H-v.H;if(D<=0||BigInt(D)%(4n*P)!==0n||v.end>start)throw Error("word spacing");
   let mult=BigInt(D)/(2n*P),outsideGain=0,outside=0,barriers=0;
   for(let i=v.start;i<start;i++){let row=rows[i],p=row.p;if(!p)continue;
    let g=p-1,c=0;for(let b=row.H;b<row.H+g;b+=2)if(fs.every(f=>b%f<=(f-3)&&b%f%2===0))c++;
    if(fs.includes(p)){if(c)throw Error("inside barrier")}else{
     outside++;outsideGain+=g;barriers+=c;
     if(2*c>g||BigInt(2*c)*P>A*(BigInt(g)+2n*P))throw Error("jump capacity");
     if(BigInt(g)<2n*P){if(BigInt(c)>A)throw Error("short jump");st.shortJumpChecks++}
    }
   }
   if(BigInt(barriers)!==mult*A||BigInt(outsideGain)<2n*mult*A||BigInt(outsideGain)+2n*P*BigInt(outside)<BigInt(D)||outside===0)throw Error("repetition budget");
   st.repeatedWords++;if(ret)st.repeatedReturnWords++;st.outsideEvents+=outside;st.outsideGain+=outsideGain;st.barrierIncidences+=barriers;if(mult>2n)st.multiplePeriodTests++;st.maxRepeatMultiplicity=Math.max(st.maxRepeatMultiplicity,Number(mult/2n));st.allSupportForbidden++;
  }
  seen.set(key,{H,start,end})
 }
 for(let M=5;M<=N;M+=2){
  st.roots++;let H=2*M-2,t=M+2,rows=[],evs=[];
  for(let i=0;i<4000;i++){
   let n=t+1,I=n%2,e=1-2*I,g=gcd(n-2*I,H-e),p=g>1?spf[g]:0;if(p&&p*p>H+1)p=0;
   rows.push({H,t,d:2*t-H,I:t%2,p});t=n;st.ticks++;
   if(p){H+=p-1;st.events++;evs.push(i+1)}
   if(spf[H-1]===H-1&&spf[H+1]===H+1)break;
   if(H+3>=cap)throw Error("cap");
  }
  rows.push({H,t,d:2*t-H,I:t%2,p:0});
  for(let L of [2,4,8]){
   let seen=new Map;
   for(let i=0;i+L<rows.length;i++){
    let word=rows.slice(i,i+L).map(r=>r.p);if(!word[0]&&!word.at(-1))continue;
    let r=rows[i],key=[r.d,r.I,...word].join(",");
    test(rows,i,i+L,word,seen,key)
   }
  }
  let last=new Map,seen=new Map;
  for(let j of evs){let r=rows[j],key=r.d+","+r.I,i=last.get(key);if(i!==undefined){
    let word=rows.slice(i,j).map(r=>r.p);
    if(rows[j].H-rows[i].H!==2*(j-i))throw Error("return gain");
    st.returnWords++;test(rows,i,j,word,seen,key+":"+word.join(","),true)
   }last.set(key,j)}
 }
 if(!st.repeatedReturnWords||!st.multiplePeriodTests)throw Error("coverage");
 return st
}
console.log(JSON.stringify(audit(Number(process.argv[2]||12000)),null,2));
