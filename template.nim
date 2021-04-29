import times, strutils, sequtils, math, algorithm, tables, sets, lists, intsets
import critbits, future, strformat, deques
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



proc solve():int=
  var
    n = scan()
    p = newseqwith(n,(scanf(),scanf(),1.0))
    m = scan()
    ops = newseq[array[3,array[3,int]]](M+1)
  ops.add(
    [
      [1,0,0],
      [0,1,0],
      [0,0,1]
    ])
  )
  for i in 1..m:
    var v = stdin.readLine.split()
    if v[0]=="1":
      ops[i]=ops[i-1] * [
        [0,1,0],
        [-1,0,0],
        [0,0,1]
      ]
    elif v[0]=="2":
      ops[i]=ops[i-1] * [
        [0,-1,0],
        [1,0,0],
        [0,0,1]
      ]))
    elif v.len==2:
      var p = v[1].parseInt
      if v[0]=="3":
        ops[i]=ops[i-1] * [
          [-2,0,2.0*p],
          [0,1,0.0],
          [0,0,1.0]
        ]))
      if v[0]=="4":
        ops[i]=ops[i-1] * [
          @[1.0,0,0],
          @[0.0,-2,2*p],
          @[0.0,0,1.0]
        ]))
  var q = scan()
  for i in 0..<q:
    var (a,b)=(scan(),scan())
    echo ops[b]*p[a]
  
      
      

  

  
echo solve()