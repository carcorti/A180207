#!/usr/bin/env python3
"""Exact independent unrestricted-initial-triple window DP, one n per process.
Copyright (c) 2026 Carlo Corti. No producer import, zero split or convolution.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import resource
import time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--n',type=int,required=True,choices=range(1,23))
parser.add_argument('--out',type=Path,required=True)
parser.add_argument('--memory-gib',type=int,default=8)
a=parser.parse_args()
if not 1<=a.memory_gib<=44:parser.error('memory ceiling must be1..44GiB')
if a.out.exists():parser.error('refusing existing result')
resource.setrlimit(resource.RLIMIT_AS,(a.memory_gib<<30,a.memory_gib<<30))
n=a.n;start=time.monotonic()
current={(0,x,y,z):1 for x in range(n) for y in range(n-x) for z in range(n-x-y)}
layers=[]
try:
    for t in range(n):
        following=defaultdict(int)
        for (mask,x,y,z),weight in current.items():
            lower=x+y+z
            for v in range(lower,n):
                if not (mask>>v)&1:
                    following[(mask|(1<<v),y,z,v-lower)]+=weight
        row={'layer':t+1,'input_states':len(current),'output_states':len(following),'elapsed_seconds':time.monotonic()-start}
        layers.append(row);print(json.dumps(row),flush=True)
        current=following
    total=sum(current.values())
    obj={'status':'COMPLETE','method':'unrestricted initial-triple DP, Python arbitrary integers','n':n,'count':total,'layers':layers,'wall_seconds':time.monotonic()-start,'rss_kib_linux':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'memory_ceiling_bytes':a.memory_gib<<30}
    with a.out.open('x') as f:json.dump(obj,f,indent=2);f.write('\n')
    print(json.dumps(obj),flush=True)
except MemoryError:
    print(json.dumps({'status':'INCOMPLETE_MEMORY','n':n,'last_finished_layer':len(layers)}),flush=True)
    raise SystemExit(3)
