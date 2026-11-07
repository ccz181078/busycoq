#!/usr/bin/env python3
"""Generate the proof files for `halts tm c0`: Cuts.v, one jobs/Jnnnn.v per job, jobs/JHalt.v, Final.v.
usage: gen_final.py CHUNKS_TSV OUTDIR CHUNKS_PER_JOB, here gen/gen_final.py chunks.tsv . 1024
The cut points are untrusted: a wrong one only makes a job fail."""
import sys, os
tsv, out, per = sys.argv[1], sys.argv[2], int(sys.argv[3])
A_HALT = 1083197534374707740536733690
P63 = 2**63
rows = [l.split() for l in open(tsv) if l.strip()]
assert rows[-1][4] == 'H'
assert rows[0][2:4] == ['6', '1']
for x, y in zip(rows, rows[1:]):
    assert x[4:6] == y[2:4]

def w(x):
    x = int(x)
    return f"(mkW {x // P63}%uint63 {x % P63}%uint63)"

# cuts: job i runs rows[i*per] .. rows[(i+1)*per-1]; the last row, ending in the halt, is its own job
body = rows[:-1]
cuts = [(body[0][2], body[0][3])]
for i in range(per, len(body), per):
    cuts.append((body[i][2], body[i][3]))
cuts.append((rows[-1][2], rows[-1][3]))
os.makedirs(f"{out}/jobs", exist_ok=True)
with open(f"{out}/Cuts.v", "w") as f:
    f.write("From Coq Require Import Uint63.\nFrom BusyCoq.Halt_1RB0LF_1RC1RA Require Import Num.\n\n")
    for i, (z, b) in enumerate(cuts):
        f.write(f"Definition z{i} : int := {z}%uint63.\nDefinition b{i} : W := {w(b)}.\n")
    f.write(f"Definition a_halt : W := {w(A_HALT)}.\nDefinition y_end : W := {w(2**100)}.\n")
njobs = len(cuts) - 1
for i in range(njobs):
    with open(f"{out}/jobs/J{i:04d}.v", "w") as f:
        f.write(f"""From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z{i} Cuts.b{i} Cuts.z{i+1} Cuts.b{i+1} = true.
Proof. native_cast_no_check (eq_refl true). Qed.
""")
last = njobs
with open(f"{out}/jobs/JHalt.v", "w") as f:
    f.write(f"""From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_halt_at Cuts.z{last} Cuts.b{last} Cuts.y_end Cuts.a_halt = true.
Proof. native_cast_no_check (eq_refl true). Qed.
""")
with open(f"{out}/Final.v", "w") as f:
    f.write("""(** [halts tm c0] for the holdout 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA, from the checker's runs over the whole orbit. *)
From Coq Require Import ZArith.
From Coq Require Uint63.
From BusyCoq Require Import Individual62.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Rules Map Num.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HCore HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts. From BusyCoq.Halt_1RB0LF_1RC1RA.jobs Require JHalt.
""")
    for i in range(njobs):
        f.write(f"From BusyCoq.Halt_1RB0LF_1RC1RA.jobs Require J{i:04d}.\n")
    f.write("Local Open Scope Z_scope.\n\n")
    f.write(f"Lemma k0 : Rch (Uint63.to_Z Cuts.z0) (val Cuts.b0) (Uint63.to_Z Cuts.z1) (val Cuts.b1).\n")
    f.write(f"Proof. exact (run_seg_sound Cuts.z0 Cuts.b0 Cuts.z1 Cuts.b1 eq_refl J0000.seg). Qed.\n")
    for i in range(1, njobs):
        f.write(f"Lemma k{i} : Rch (Uint63.to_Z Cuts.z0) (val Cuts.b0) (Uint63.to_Z Cuts.z{i+1}) (val Cuts.b{i+1}).\n")
        f.write(f"Proof. exact (Rch_trans _ _ _ _ _ _ k{i-1} (run_seg_sound Cuts.z{i} Cuts.b{i} Cuts.z{i+1} Cuts.b{i+1} eq_refl J{i:04d}.seg)). Qed.\n")
    f.write(f"""
Lemma orbit : Rch 6 1 (val Cuts.a_halt) (val Cuts.a_halt + 3).
Proof.
  exact (Rch_trans _ _ _ _ _ _ k{njobs-1} (run_halt_at_sound Cuts.z{njobs} Cuts.b{njobs} Cuts.y_end Cuts.a_halt eq_refl JHalt.seg)).
Qed.

Theorem bb6_holdout_halts : halts tm c0.
Proof.
  destruct orbit as (n & r & H). destruct (halts_of_Reach _ _ _ H) as (st & Hst & _). exists st. exact Hst.
Qed.

Print Assumptions bb6_holdout_halts.
""")
print(njobs, "jobs +1 halt job;", len(body), "chunks")
