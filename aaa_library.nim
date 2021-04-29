import times, strutils, sequtils, math, algorithm, tables, sets, lists, intsets
import critbits, future, strformat, deques,macros
template `max=`(x,y) = x = max(x,y)
template `min=`(x,y) = x = min(x,y)
template `mod=`(x,y) = x = x mod y
template scan2 = (scan(), scan())
template scan3 = (scan(), scan())
let read* = iterator: string {.closure.} =
    while true: (for s in stdin.readLine.split: yield s)
proc scan(): int = read().parseInt
proc scanf(): float = read().parseFloat
proc toInt(c:char): int =
    return int(c) - int('0')


macro toTuple*(rhs: seq,cnt: static[int]): auto =
  let t = genSym(); result = quote do:(let `t` = `rhs`;())
  for i in 0..<cnt: result[0][1].add(quote do:`t`[`i`])

# 最長部分増加列
proc getLIS(arr:seq[int]):seq[int]=
  var n = arr.len
  var res = newseqwith(n+2,int.high.div(2))
  res[0]=arr[0]
  proc binSearch(v:int,res:var seq[int]):int=
    var
      left = 0
      right = n+1
    if res[left]>=v:
      return left
    else:
      while left+1<right:
        var mid = (left+right).div(2)
        if res[mid]<v:
          left = mid
        else:
          right=mid
      return right
  
    
  for i in 1..<n:
    res[binSearch(arr[i])]=arr[i]
    echo res
  return res

echo getLIS(@[5,3,1,2,4,2])


# combination
# コンビネーションの計算
const
  D = 998244353
  m:int = 1E6.int
  #fac:seq[int]
  #finv:seq[int]
  #inv:seq[int]
proc comInit():(seq[int],seq[int],seq[int])=
  var
    fac = newseqwith(m,1)
    finv = newseqwith(m,1)
    inv = newseqwith(m,1)
  for i in 2..<m:
    fac[i] = fac[i-1]*i mod D
    inv[i] = D - inv[D mod i] * (D div i) mod D
    finv[i] = finv[i-1] * inv[i] mod D
  return (fac,finv,inv)

const (fac,finv,inv) = comInit()


proc com(n,k:int):int=
  if  n<k:return 0
  elif n<0 or k<0: return 0
  else:
    return fac[n] * (finv[k]*finv[n-k] mod D) mod D

proc H(n,r:int):int=
  return com(n+r-1,r)

proc primeFact(n:int):Table[int,int]=
  result = initTable[int,int]()
  var t = n
  var d = 2
  var p = 2
  while p^2 <= n:
    if  t mod p == 0:
      result.add(p,0)
    while t mod p == 0:
      t = t div p
      result[p]+=1
    p+=1
  
  if t != 1:
    result[t]=1

proc getIsPrimes(n:int):seq[bool]=
    result = newSeqWith(n+1,true)
    result[1] = false
    result[0] = false
    for i in 2..n.float.sqrt.int:
        if not result[i]:continue
        for j in countup(i*2,n,i):
            result[j] = false


    
var isPrime:seq[bool] = getIsPrimes(1E5.int)


proc getLowLink(G:seq[seq[int]],start:int=0):(seq[int],seq[(int,int)])=
  var
    N = G.len
    order = newseqwith(N,-1)
    used = newseqwith(N,false)
    loww = newseqwith(N,0)
    acP = newseq[int]()
    bridge = newseq[(int,int)]()

  proc dfs(idx, k, par:int):int=
    var
      k = k
      isA = false
      cnt = 0
    used[idx]=true
    order[idx]=k
    k+=1
    loww[idx]=order[idx]
    
    for nxt in G[idx]:
      if not used[nxt]:
        cnt+=1
        k = dfs(nxt,k,idx)
        loww[idx].min=loww[nxt]
        isA = isA or  ( par != -1 and (loww[nxt] >= order[idx]))
        if order[idx]<loww[nxt]:
          bridge.add((min(idx,nxt),max(idx,nxt)))
      elif nxt != par:
        loww[idx].min=order[nxt]

    isA = isA or (par == -1 and cnt>1)
    if isA:
      acP.add(idx)
    return k
  
  proc build()=
    var k = 0
    for i in 0..<N:
      if not used[i]:
        k = dfs(i,k,-1)

  build()
  
  return (acP, bridge)

var
  case1 = @[
    @[1],
    @[0,2],
    @[1,3],
    @[2]
  ]
  case2 = @[
    @[1,2],
    @[0,2],
    @[0,1,3],
    @[2,4,5],
    @[3,5],
    @[3,4]
  ]
  case3 = @[
    @[1,2],
    @[0,2],
    @[0,1],
    @[4,5],
    @[3,5],
    @[3,4]
  ]
  case4 = @[
    @[1,3],
    @[0,2],
    @[1,3],
    @[0,2]
  ]
  case5 = @[
    @[1,2],
    @[0,2],
    @[0,1],
    @[4,5],
    @[3,5],
    @[3,4,6],
    @[5,7,8],
    @[6,8],
    @[6,7]
  ]

echo getLowLink(case1)
echo getLowLink(case2)
echo getLowLink(case3)
echo getLowLink(case4)
    


iterator allPermutation*[T](v:openArray[T]):seq[T]=
  var v = v.sorted(SortOrder.Ascending)
  yield v
  while v.nextPermutation:
    yield v


# 境界を探す二分探索
# BinarySearch
# aは昇順にソートされているとする
# 初めて等しいか超える直前のidxを返す
proc myBinarySearch[T](a:openarray[T], key:T):int=

  var imin = -1
  var imax = a.len
  var imid:int
  while imax - imin > 1:
    imid = (imin+imax) div 2
    if a[imid] < key:
      imin = imid
    else:
      imax = imid
  return imin



# ヒープキュー
# heapqueue
# 0.13にないので……
proc pushHeap[T](arr:var seq[T], elem:T)=
  var n = arr.len
  arr.add(elem)
  while n != 0:
    var i = (n - 1) div 2
    if arr[n] > arr[i]:
      swap(arr[n],arr[i])
    n = i
proc popHeap[T](arr:var seq[T]):T=
  result = arr[0]

  var n = arr.len-1
  arr[0] = arr[n]
  arr.delete(n)
  var i = 0
  var j :int = 2*i+1
  while j < n:
    if (j != n-1) and (arr[j] < arr[j+1]):
      j+=1
    if arr[i] < arr[j]:
      swap(arr[i], arr[j])
    i=j
    j = 2*i+1

#var t:seq[int] = @[]
#for i in 1..5:
  ##t.pushHeap(i)
  #echo t
#for i in 1..5:
  #echo popHeap(t)


# modPow
# 無いので作る
# なんか畳み込んで上手いことやるやつ
proc modPow(x,b,m:int):int=
  if b == 1:
    return x
  return (modPow((x^2) mod m, b div 2, m) * x^(b mod 2)) mod m


echo modPow(2,1E9.int,1E9.int+7)




# dfsで同一グループをまとめる
# ref:abc157_D.nim
var 
  n = 50
  edges = newseqwith(n,newseq[int](0))
  blocks = newseqwith(n,newseq[int](0))
  group = newseqwith(n,-1)
proc sameGrouprec(user:int, groupNum:int)=
  if group[user] != -1:
    return
  else:
    group[user] = groupNum
    for edge in edges[user]:
      sameGrouprec(edge,groupNum)



# 拡張ユークリッド互除法

proc xgcd(a,b:int):(int,int,int)=
  var
    b = b
    x0=1
    y0=0
    x1=0
    y1=1
    q:int
    a = a
  while b!=0:
    (q,a,b) = (a.div(b),b,a.mod(b))
    (x0,x1)=(x1,x0-q*x1)
    (y0,y1)=(y1,y0-q*y1)
  return (a,x0,y0)

proc modinv(a,m:int):int=
  var (g,x,y)=xgcd(a,m)
  if g!=1:
    return -1
  else:
    return x mod m

proc crt(b:seq[int],m:seq[int]):(int,int)=
  var
    r=0
    M=1
  for i in 0..<b.len:
    var (d,p,q)=xgcd(M,m[i])
    if ((b[i]-r)mod d) != 0:return (0,-1)
    var tmp = (b[i]-r) div d * p mod (m[i] div d)
    r+=M*tmp
    M*=m[i] div d
  if r<0:
    r+=M
  r.mod=M

  return (r,M)


# セグメント木


type SegTree = object
  tree :seq[int]
  n:int

proc initSegTree(baseArr:seq[int]):SegTree=
  var n = baseArr.len
  var m = 1
  while m < n:
    m*=2
  result = SegTree()
  result.n = m
  result.tree = newseqwith(2*m-1,int.high.div(4))
  for i, v in baseArr:
    result.tree[m-1+i]=v
  for idx in countdown(m-2,0):
    result.tree[idx] = min(result.tree[idx*2+1],result.tree[idx*2+2])

proc get(segTree:SegTree,ql,qr:int,k:int=0,left:int=0,right:int= -1):int=
  var right=right
  if right<0:
    right = segTree.n
  echo ql,", ", qr, ", ",left,", ", right
  if ql>=right or qr<=left:
    return int.high
  if ql <= left and right <= qr:
    return segTree.tree[k]
  var
    vl = segTree.get(ql,qr,2*k+1,left,(left+right).div(2))
    vr = segTree.get(ql,qr,2*k+2,(left+right).div(2),right)
  return min(vl,vr)

proc set(segTree:var SegTree,idx,value:int)=
  var k = segTree.n - 1 + idx
  segTree.tree[k] = value
  while k>=1:
    k = (k-1).div(2)
    if segTree.tree[k] == min(segTree.tree[2*k+1],segTree.tree[2*k+2]):
      break
    else:
      segTree.tree[k] = min(segTree.tree[2*k+1],segTree.tree[2*k+2])


proc ford_fulkerson():int=
  var
    (v,e)=(scan(),scan())
    residual = newseqwith(n,newseqwith(n,0))
    used  = newseqwith(n,false)

  for i in 0..<n:

  proc reset_fp()=
    used.applyIt(false)

  proc dfs(now,terminal,flow:int):int=
    used[now]=true
    if now==terminal:
      return flow
    else:
      for next in 0..<n:
        if residual[now][next]>0 and used[next]!=true:
          result=dfs(next,terminal, min(flow,residual[now][next]))
          if result>0:
            residual[now][next]-=result
            residual[next][now]+=result
            return
    return     
  

  proc max_flow(s,t:int):int=
    while true:
      reset_fp()
      var f = dfs(s,t,int.high.div(4))
      if f==0:
        return
      else:
        result+=f
  
proc warshall_floyd()=
  var
    d:seq[seq[int]]
    v:int
  for k in 0..<v:
    for i in 0..<v:
      for j in 0..<v:
        d[i][j]=min(d[i][j],d[i][k]+d[k][j])


proc bellman_ford():bool=
  var
    n:int
    s:int
    dist:seq[int]
    edges:seq[seq[int]]
    costs:seq[seq[int]]
    inf:int
  dist[s]=0
  for i in 0..<n:
    for v in 0..<n:
      for nextIdx in 0..<len(edges[v]):
        var
          next=edges[v][nextIdx]
          cost = costs[v][nextIdx]

        if dist[v]!=inf and dist[next]>dist[v]+cost:
          dist[next]=dist[v]+cost
          if i==n-1:
            return true
  return false



# 行列のダブリング

const md = 10^9+7

proc `*`(x,y:seq[seq[int]]):seq[seq[int]]=
  var
    xh = x.len
    xw = x[0].len
    yh = y.len
    yw = y[0].len
  if xw != yh:
    raise
  result = newseqwith(xh,newseqwith(yw,0))
  for i in 0..<xh:
    for j in 0..<yw:
      for p in 0..<xw:
        result[i][j]+=x[i][p]*y[p][j]
        result[i][j].mod=md
  return

proc modPow(x:seq[seq[int]],n:int):seq[seq[int]]=
  var
    x = x
    n = n
    h = x.len
    w = x[0].len
  result = newseqwith(h,newseqwith(w,0))
  for i in 0..<h:
    result[i][i]=1
  while n>0:
    if (n and 1)>0:
      result = result*x
    x = x*x
    n = n shr 1
  return

# 強連結成分分解
proc solve():int=
  var
    n = scan()
    m = scan()
    es = newseqwith(n,newseq[int]())
    ies = newseqwith(n,newseq[int]())
    order = newseq[int]()
    fp = newseqwith(n,false)
  for i in 0..<m:
    var
      (a,b) = (scan()-1,scan()-1)
    es[a].add(b)
    ies[b].add(a)
  proc dfs(p:int,preorder:var seq[int])=
    fp[p]=true
    for nxt in es[p]:
      if not fp[nxt]:
        dfs(nxt,preorder)
    preorder.add(p)

  proc dfs2nd(p:int):int=
    fp[p]=true
    result = 1
    for nxt in ies[p]:
      if not fp[nxt]:
        result+=dfs2nd(nxt)

    
  for p in 0..<n:
    if not fp[p]:
      dfs(p,order)
  fp.fill(false)
  for i in countdown(n-1,0):
    if not fp[order[i]]:
      var t = dfs2nd(order[i])
      result+=(t*(t-1)).div(2)


import sequtils, math




# 有理数の近似のやつ
# 
# http://satashun.hatenablog.com/entry/2018/12/13/163524


proc sternBrocot*(generation: int): (seq[int], seq[int]) =
  var children = @[0, 1]
  var mother = @[1, 1]
  for i in 0..<generation:
    var nextChildren = newSeqWith[int](children.len*2-1, 0)
    var nextMother = newSeqWith[int](mother.len*2-1, 0)
    for i in 0..<children.len-1:
      nextChildren[2*i] = children[i]
      nextChildren[2*i+2] = children[i+1]
      nextChildren[2*i+1] = children[i]+children[i+1]
      nextMother[2*i] = mother[i]
      nextMother[2*i+2] = mother[i+1]
      nextMother[2*i+1] = mother[i]+mother[i+1]
    children = nextChildren
    mother = nextMother
  return (children, mother)



  #for left in 0..2^generation:
    #for right in 0..2^generation:
      #echo result[0][left], " / ", result[1][left], "~", result[0][right],
        #" / ", result[1][right]



if isMainModule:
  var (c,m) =  sternBrocot(3)
  echo c
  echo m


import math, sequtils, bigints


iterator iterPQD(P, Q, D: float): int =
  var
    a = floor((P+D.sqrt)/Q)
    nP = P
    nQ = Q
  while true:
    echo nP, " ", nQ, " ", a
    nP = a*nQ-nP
    nQ = (D-nP^2)/nQ
    a = floor((nP+D.sqrt)/nQ)
    yield a.int

proc getFirst(P, Q, D: float): int =
  return int(floor((P+D.sqrt)/Q))


proc generateAppr*(a0: int, an: seq[int]): (int, int) =
  (result[0], result[1]) = (1, an[^1])
  for i in countdown(len(an)-2, 0):
    (result[0], result[1]) = (result[1], an[i]*result[1]+result[0])
  (result[0], result[1]) = (a0*result[1]+result[0], result[1])


proc generateApprBigInt*(a0: int, an: seq[int]): (BigInt, BigInt) =
  var a0 = a0.initBigInt
  var an = an.mapIt(it.initBigInt)
  (result[0], result[1]) = (1.initBigInt, an[^1])
  for i in countdown(len(an)-2, 0):
    (result[0], result[1]) = (result[1], an[i]*result[1]+result[0])
  (result[0], result[1]) = (a0*result[1]+result[0], result[1])



proc continuedFraction*(P, Q, D: float): (int, seq[int]) =
  var
    a = floor((P+D.sqrt)/Q)
    nP = P
    nQ = Q
    goalP = a*nQ-nP
    goalQ = (D-goalP^2)/nQ
  result[0] = a.int
  nP = a*nQ-nP
  nQ = (D-nP^2)/nQ
  a = floor((nP+D.sqrt)/nQ)
  result[1].add(a.int)
  while true:
    nP = a*nQ-nP
    nQ = (D-nP^2)/nQ
    a = floor((nP+D.sqrt)/nQ)
    if nP == goalP and nQ == goalQ:
      break
    result[1].add(a.int)

  return

proc lagrangeSolver*(P, Q, D: float): (int, seq[int]) =
  var
    footPrint: seq[int]
  result[0] = getFirst(P, Q, D)
  var count = 0
  for v in iterPQD(P, Q, D):
    if count > 50:
      break
    footPrint.add(v)
    count+=1

  return (result[0], footPrint)


when isMainModule:
  var (a, b) = continuedFraction(0, 1, 23)
  echo a, ",", b
  echo generateAppr(a, b)
