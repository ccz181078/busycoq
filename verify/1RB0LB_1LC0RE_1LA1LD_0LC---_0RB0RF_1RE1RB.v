From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

Definition S0 a b c :=
  const 0 <* <[1;0] <* <[0;1]^^a <* [0]^^b <{{A}} [1] *> [1;0]^^c *> [1;1] *> const 0.

Lemma Inc a b c:
  S0 a (3+b) c -->* S0 a b (2+c).
Proof.
  es.
Qed.

Lemma Incs a b c n:
  S0 a (n*3+b) c -->* S0 a b (n*2+c).
Proof.
  gen a b c.
  ind n Inc.
Qed.

Lemma Ov0 a c:
  S0 (1+a) 0 c -->*
  S0 (7+a) (c*2+2) 1.
Proof.
  es.
Qed.

Lemma Ov1 a c:
  S0 (1+a) 1 c -->*
  S0 a (c*2+5) 1.
Proof.
  es.
Qed.

Lemma Ov2 a c:
  S0 a 2 c -->*
  S0 (4+a) (c*2+2) 1.
Proof.
  es.
Qed.

Definition S1 b c :=
  const 0 <* <[1;0;1] <* [0]^^b <{{A}} [1] *> [1;0]^^c *> [1;1] *> const 0.

Lemma Ov1' c:
  S0 0 1 c -->*
  S1 (c*2+6) 1.
Proof.
  es.
Qed.

Lemma Inc1 b c:
  S1 (3+b) c -->* S1 b (2+c).
Proof.
  es.
Qed.

Lemma Incs1 b c n:
  S1 (n*3+b) c -->* S1 b (n*2+c).
Proof.
  gen b c.
  ind n Inc1.
Qed.

Definition S2 b c :=
  const 0 <* <[1;0;0;0;1] <* [0]^^b <{{A}} [1] *> [1;0]^^c *> [1;1] *> const 0.

Lemma S1_Ov2 c:
  S1 2 c -->*
  S2 (c*2+6) 1.
Proof.
  es.
Qed.

Lemma Inc2 b c:
  S2 (3+b) c -->* S2 b (2+c).
Proof.
  es.
Qed.

Lemma Incs2 b c n:
  S2 (n*3+b) c -->* S2 b (n*2+c).
Proof.
  gen b c.
  ind n Inc2.
Qed.

Definition S3 b c :=
  const 0 <* <[1;1;0;1] <* [0]^^b <{{A}} [1] *> [1;0]^^c *> [1;1] *> const 0.

Lemma S2_Ov2 c:
  S2 2 c -->*
  S3 (c*2+6) 1.
Proof.
  es.
Qed.

Lemma Inc3 b c:
  S3 (3+b) c -->* S3 b (2+c).
Proof.
  es.
Qed.

Lemma Incs3 b c n:
  S3 (n*3+b) c -->* S3 b (n*2+c).
Proof.
  gen b c.
  ind n Inc3.
Qed.

Lemma S3_Ov2_halt c:
  halts tm (S3 2 c).
Proof.
  eapply halts_evstep.
  2:{
    unfold S3.
    repeat step1.
    sr.
    repeat step1.
    sr.
    repeat step1.
    finish.
  }
  apply halted_halts.
  constructor.
Qed.

Lemma Halt c:
  halts tm (S0 0 1 (c*27+16)).
Proof.
  replace (c*27+16) with (((c*3+1)*3+2)*3+1) by lia.
  eapply halts_evstep.
  2:{
  remember (c*3+1) as c2.
  remember (c2*3+2) as c1.
  follow Ov1'.
  replace ((c1*3+1)*2+6) with ((c1*2+2)*3+2) by lia.
  follow Incs1.
  follow S1_Ov2.
  replace (((c1 * 2 + 2) * 2 + 1) * 2 + 6) with ((c2*8+10)*3+2) by lia.
  follow Incs2.
  follow S2_Ov2.
  replace (((c2 * 8 + 10) * 2 + 1) * 2 + 6) with ((c*32+26)*3+2) by lia.
  follow Incs3.
  finish.
  }
  apply S3_Ov2_halt.
Qed.

Lemma init:
  c0 -->*
  S0 4 124 1.
Proof.
  unfold S0.
  solve_init.
Qed.

Lemma R0 a n:
  S0 (1+a) (n*3+0) 1 -->*
  S0 (7+a) (n*4+4) 1.
Proof.
  follow Incs.
  follow Ov0.
  finish.
Qed.

Lemma R1 a n:
  S0 (1+a) (n*3+1) 1 -->*
  S0 (0+a) (n*4+7) 1.
Proof.
  follow Incs.
  follow Ov1.
  finish.
Qed.

Lemma R2 a n:
  S0 (1+a) (n*3+2) 1 -->*
  S0 (5+a) (n*4+4) 1.
Proof.
  follow Incs.
  follow Ov2.
  finish.
Qed.

Lemma Halt' n:
  halts tm (S0 0 ((n*27+21)*3+1) 1).
Proof.
  eapply halts_evstep.
  2:{
    follow Incs.
    replace ((n*27+21)*2+1) with ((n*2+1)*27+16) by lia.
    finish.
  }
  apply Halt.
Qed.


Check init.
Check R0.
Check R1.
Check R2.
Check Halt'.
(*
   classic cryptid #5
   (a,n) := 0^inf 10 01^a 0^n <A 11011 0^inf
   start: (4,124)
   (a+1,3n+0) --> (a+7,4n+4)
   (a+1,3n+1) --> (a+0,4n+7)
   (a+1,3n+2) --> (a+5,4n+4)
   (0,3(27n+21)+1) --> halt
*)

