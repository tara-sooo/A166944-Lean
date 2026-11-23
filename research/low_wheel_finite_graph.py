from math import prod
from array import array

def audit(ps):
 P=prod(ps);L=2*P;N=P*L
 memo=array('i',[-1])*N
 status=bytearray(N)
 nxt=[0]*N; gaps=[0]*N
 def clk(t,p,r):
  g=(r-t)%(2*p)
  return g or 2*p
 def successor(s):
  t=s%L; c=2*(s//L)
  delay=0
  for p in ps:
   if (c-1)%p==0:
    v=clk(t,p,0)
    if delay==0 or v<delay:delay=v
   if (c+1)%p==0:
    v=clk(t,p,p+2)
    if delay==0 or v<delay:delay=v
  if delay==0:return -1,0
  n=(t+delay)%L
  d=prod(p for p in ps if (((c-1)%p==0 and n%(2*p)==0) or ((c+1)%p==0 and n%(2*p)==(p+2)%(2*p))))
  assert d>1, (s,t,c,delay,n,d)
  c=(c+d-1)%L
  return (c//2)*L+n,delay
 for s in range(N):
  nxt[s],gaps[s]=successor(s)
 maxv=0;arg=0;maxev=0
 for root in range(N):
  if status[root]:continue
  path=[];u=root
  while u!=-1 and status[u]==0:
   status[u]=1;path.append(u);u=nxt[u]
  if u!=-1 and status[u]==1:
   raise ValueError(f'LOW_WHEEL_CYCLE ps={ps} u={u} tail={path[-10:]}')
  while path:
   v=path.pop()
   memo[v]=gaps[v]+(memo[nxt[v]] if nxt[v]!=-1 else 0)
   status[v]=2
   if memo[v]>maxv:maxv=memo[v];arg=v
 print('LOW_GRAPH_COMPLETE',ps,'P',P,'N',N,'max_time',maxv,'arg_t',arg%L,'arg_C',2*(arg//L),'path',end=' ')
 u=arg
 while u!=-1:
  print((u%L,2*(u//L),gaps[u]),end=' ');u=nxt[u]
 print('SINK')

for x in [[3],[3,5],[3,5,7]]:
 audit(x)