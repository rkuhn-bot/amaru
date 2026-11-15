# What-if residual SCCs: pass-4 'after' discharges plus the extra edges listed in the given file (one discharge-row key per line). Run from /workspace/deadlock-research.
import json,sys
import os
g=json.load(open(os.environ.get('GRAPH','wait-graph-v4.json')));d=json.load(open(os.environ.get('DIS','wait-graph-v4-discharge.json')))
after={r['edge'] for r in d['rows'] if r['after']=='discharged'}
def key(e): return f"{e['from']} -> {e['to']} [{e['message']}]"
extra=[l.strip() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')] if len(sys.argv)>1 else []
dis=after|set(extra)
E=[(e['from'],e['to']) for e in g['edges'] if e['blocking'] and key(e) not in dis]
missing=[x for x in extra if x not in {key(e) for e in g['edges']}]
if missing: print("UNKNOWN",missing)
V=sorted({x for e in E for x in e})
adj={v:[] for v in V}
for a,b in E: adj[a].append(b)
idx={};low={};st=[];on=set();out=[];c=[0]
sys.setrecursionlimit(10000)
def sc(v):
    idx[v]=low[v]=c[0];c[0]+=1;st.append(v);on.add(v)
    for w in adj[v]:
        if w not in idx: sc(w);low[v]=min(low[v],low[w])
        elif w in on: low[v]=min(low[v],idx[w])
    if low[v]==idx[v]:
        comp=[]
        while True:
            w=st.pop();on.discard(w);comp.append(w)
            if w==v:break
        out.append(comp)
for v in V:
    if v not in idx: sc(v)
print("after-mode discharged:",len(dis))
for comp in out:
    if len(comp)>1: print(len(comp),sorted(comp))
print("selfloops",[a for a,b in E if a==b])
