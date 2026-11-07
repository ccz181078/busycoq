#!/usr/bin/env python3
# Writes one Rocq job per verified checkpoint interval of the c273 run, the final halting job, and Chain.v composing them into
# `halts tm c0`. usage: gen_jobs.py CKPT_LOG HALT_FILE OUTDIR, here gen/gen_jobs.py gen/ckpt.txt gen/halt.txt .
import sys,os
ck=[l.split() for l in open(sys.argv[1]) if l.strip()]
halt={k:v for k,v in (l.split(None,1) for l in open(sys.argv[2]) if l.strip())}
hn=int(halt['map_steps_done']); hs=[int(x) for x in halt['state'].split()]
out=sys.argv[3]; os.makedirs(out+'/jobs',exist_ok=True)
pts=[(int(f[0]),int(f[1]),int(f[2]),int(f[3])) for f in ck]
assert pts[0]==(0,0,1,0)
jobs=[]
for i in range(len(pts)-1):
    n0,a,b,c=pts[i]; n1,a2,b2,c2=pts[i+1]
    jobs.append(('ok',n1-n0,(a,b,c),(a2,b2,c2),n0,n1))
n0,a,b,c=pts[-1]
jobs.append(('halt',hn-n0+1,(a,b,c),None,n0,hn))
H='From BusyCoq.LopsidedCamper Require Import Kernel273.\nFrom Coq Require Import Uint63 ZArith.\nOpen Scope uint63_scope.\n'
for i,(kind,p,s,e,n0,n1) in enumerate(jobs):
    name=f'J{i:04d}'
    if kind=='ok':
        body=(f'(* map steps {n0} to {n1} *)\nLemma {name} : job_ok {p} {s[0]} {s[1]} {s[2]} {e[0]} {e[1]} {e[2]}.\n'
              f'Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go {e[0]} {e[1]} {e[2]}))]. Qed.\n')
    else:
        body=(f'(* map steps {n0} to the halt at {n1}: the step from map step {n1} returns Halt *)\nLemma {name} : job_halt {p} {s[0]} {s[1]} {s[2]}.\n'
              f'Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl Halt)]. Qed.\n')
    open(f'{out}/jobs/{name}.v','w').write(H+body)
# Chain.v: nested from the last job outward
imp=''.join(f'From BusyCoq.LopsidedCamper.jobs Require {f"J{i:04d}"}.\n' for i in range(len(jobs)))
term=f'(ch_halt _ _ _ _ J{len(jobs)-1:04d}.J{len(jobs)-1:04d})'
for i in range(len(jobs)-2,-1,-1):
    term=f'(ch_step _ _ _ _ _ _ _ J{i:04d}.J{i:04d}\n {term})'
open(f'{out}/Chain.v','w').write(H+imp+f'\nTheorem c273_chain : chain i0 i1 i0.\nProof. exact {term}. Qed.\n')
# The final statement lives apart from Chain.v: BusyCoq's notations clash with Uint63's once both are imported in one file.
open(f'{out}/Halts273.v','w').write('From BusyCoq Require Import Individual62.\nFrom BusyCoq.LopsidedCamper Require Import Rules273 Final273.\nFrom BusyCoq.LopsidedCamper Require Chain.\n\n'
  'Theorem c273_halts : halts tm c0.\nProof. apply halts_of_chain. exact Chain.c273_chain. Qed.\nCheck c273_halts.\nPrint Assumptions c273_halts.\n')
print(len(jobs),'jobs; total map steps',sum(j[1] for j in jobs))
