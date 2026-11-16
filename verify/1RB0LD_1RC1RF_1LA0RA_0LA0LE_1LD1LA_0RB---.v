From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.


Definition S0 a b c :=
  const 0 <* [1] <* [0;1]^^a {{A}}> [0]^^b *> [1;0]^^c *> [0;1] *> const 0.

Lemma init:
  c0 -->* S0 1 1 0.
Proof.
  es.
Qed.

Lemma Inc a b c:
  S0 a (3+b) c -->* S0 (2+a) b c.
Proof.
  es.
Qed.

Lemma Rst0 a c:
  S0 a 0 (1+c) -->* S0 1 (3+a*2) c.
Proof.
  es.
Qed.

Lemma Rst1 a c:
  S0 (1+a) 1 c -->* S0 1 (2+a*2) (4+c).
Proof.
  es.
Qed.

Lemma Rst2 a c:
  S0 a 2 (1+c) -->* S0 1 (4+a*2) (7+c).
Proof.
  es.
Qed.

Lemma Incs a b c n:
  S0 a (n*3+b) c -->* S0 (n*2+a) b c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Lemma R0 b c:
  S0 1 (b*3+0) (1+c) -->* S0 1 (b*4+5) c.
Proof.
  follow Incs.
  follow Rst0.
  finish.
Qed.

Lemma R1 b c:
  S0 1 (b*3+1) c -->* S0 1 (b*4+2) (4+c).
Proof.
  follow Incs.
  replace (b*2+1) with (1+b*2) by lia.
  follow Rst1.
  finish.
Qed.

Lemma R2 b c:
  S0 1 (b*3+2) (1+c) -->* S0 1 (b*4+6) (7+c).
Proof.
  follow Incs.
  follow Rst2.
  finish.
Qed.

Definition S1 a b c :=
  const 0 <* [1] <* [0;1]^^a {{A}}> [0]^^b *> c *> const 0.

Lemma R0_0 b:
  S0 1 (b*3+0) 0 -->* S1 5 (b*4) [1;0;1].
Proof.
  follow Incs.
  es.
Qed.

Lemma S1_Inc a b c:
  S1 a (3+b) c -->* S1 (2+a) b c.
Proof.
  es.
Qed.

Lemma S1_Incs a b c n:
  S1 a (n*3+b) c -->* S1 (n*2+a) b c.
Proof.
  gen a b.
  ind n S1_Inc.
Qed.

Lemma Rst0_101 a:
  S1 (1+a) 0 [1;0;1] -->* S0 1 (4+a*2) 0.
Proof.
  es.
Qed.

Lemma Rst1_101 a:
  S1 (1+a) 1 [1;0;1] -->* S1 1 (6+a*2) [1;0;0;0;1].
Proof.
  es.
Qed.

Lemma Rst0_10001 a:
  S1 (1+a) 0 [1;0;0;0;1] -->* S0 1 (6+a*2) 0.
Proof.
  es.
Qed.

Lemma Rst1_10001 a:
  S1 (1+a) 1 [1;0;0;0;1] -->* S1 1 (6+a*2) [1;0;1;1].
Proof.
  es.
Qed.

Lemma Halt1_1011 a:
  halts tm (S1 (1+a) 1 [1;0;1;1]).
Proof.
  eapply halts_evstep.
  2:{
    repeat step1.
    constructor.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma MayHalt b:
  halts tm (S0 1 ((((b*3+2)*3+1)*3+1)*3+0) 0).
Proof.
  eapply halts_evstep.
  2:{
    follow R0_0.
    remember (b*3+2) as b2.
    remember (b2*3+1) as b1.
    replace ((b1*3+1)*4) with ((b1*4+1)*3+1) by lia.
    follow S1_Incs.
    replace ((b1*4+1)*2+5) with (1+(b1*8+6)) by lia.
    follow Rst1_101.
    replace (6+(b1*8+6)*2) with ((b2*16+11)*3+1) by lia.
    follow S1_Incs.
    rewrite Nat.add_comm.
    follow Rst1_10001.
    replace (6+(b2*16+11)*2*2) with ((b*64+59)*3+1) by lia.
    follow S1_Incs.
    rewrite Nat.add_comm.
    constructor.
  }
  apply Halt1_1011.
Qed.

Check init.
Check R0.
Check R1.
Check R2.
Check MayHalt.
Print S0.

(*

start: (1,0)
(3b+0,c+1) --> (4b+5,c)
(3b+1,c) --> (4b+2,c+4)
(3b+2,c+1) --> (4b+6,c+7)
(3(3(3(3b+2)+1)+1)+0,0) --> halt

(b,c) := 0^inf 110 A> 0^b 10^c 01 0^inf

*)


