From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Module TC_Example1.

Definition tm := (TM_from_str "1RB---_0RA---_------_------_------_------").

(*
  a -->* b means b is reachable from a by >=0 steps of TM execution
  a -->+ b means b is reachable from a by >0 steps of TM execution
 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(*
  S0(l) is defined as l A> 0^inf
 *)
Definition S0 (l:side) := l {{A}}> const 0.

(*
  l A> 0^inf -->+ l 10 A> 0^inf
 *)
Lemma Inc l:
  S0 l -->+ S0 (l <* <[1;0]).
Proof.
  es. (* trivial TM execution *)
Qed.

(*
  0^inf A> 0^inf -->* 0^inf A> 0^inf
 *)
Lemma init:
  c0 -->* S0 (const 0).
Proof.
  es.
Qed.

(* prove nonhalt staring from 0^inf A> 0^inf *)
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt. (* to prove A nonhalt, we can prove B-->*A and B nonhalt *)
  1: apply init.
  eapply progress_nonhalt_simple. (* to prove f(x) nonhalt, we can prove forall x, exists y, f(x)-->+f(y) *)
  intros i.
  eexists.
  apply Inc.
Qed.

End TC_Example1.


Module Bouncer_Example1.

Definition tm := (TM_from_str "1LB1RA_1RA1LB_------_------_------_------").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(*
  S0(n) := 0^inf 1^n A> 0^inf
 *)
Definition S0 n := const 0 <* [1]^^n {{A}}> const 0.

Lemma Inc n:
  S0 n -->+ S0 (2+n).
Proof.
  es. (* es also support executing shift rule *)
Qed.

Lemma init:
  c0 -->* S0 0.
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply Inc.
Qed.

End Bouncer_Example1.


Module Counter_Example1.

Definition tm := (TM_from_str "1RB1LA_0LA0RB_------_------_------_------").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 (l:side) n := l {{B}}> [1]^^n *> const 0.
Definition S1 (l:side) n := l <{{A}} [1]^^n *> const 0.

Lemma S0_to_S1 l n:
  S0 l n -->* S1 l n.
Proof.
  gen l.
  induction n; intros. (* prove by induction on n *)
  - es.
  - mid (S0 (l<*[0]) n). (* we can prove A-->*C by specifying B and then prove A-->*B and B-->*C *)
    1: es.
    follow IHn. (* we can prove B-->*C by specifying a rule B-->*D and then prove D-->*C *)
    mid (S0 (l<*[1]) n).
    1: es.
    follow IHn.
    es.
Qed.

Lemma Inc n:
  S1 (const 0) n -->+
  S1 (const 0) (1+n).
Proof.
  mid10 (S0 (const 0<*[1]) n). (* similar to mid, but split A-->+C as A-->+B and B-->*C *)
  1: es.
  follow S0_to_S1.
  es.
Qed.

Lemma init:
  c0 -->* S1 (const 0) 0.
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply Inc.
Qed.

End Counter_Example1.


Module CubicBell_Example1.

Definition tm := (TM_from_str "1RB0RB_0LC1RB_1RA1LC_------_------_------").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b := const 0 <* [1]^^a <* [0] <{{C}} [1]^^b *> const 0.

Lemma Inc0 a b:
  S0 a (1+b) -->*
  S0 (1+a) b.
Proof.
  es.
Qed.

Lemma Incs0 a b:
  S0 a b -->*
  S0 (b+a) 0.
Proof.
  gen a.
  ind b Inc0. (* prove by induction on b, and Inc0 is one induction step *)
Qed.

Lemma Inc1 n:
  S0 0 n -->+
  S0 0 (2+n).
Proof.
  follow Incs0.
  es.
Qed.

Lemma init:
  c0 -->* S0 0 1.
Proof.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply Inc1.
Qed.

End CubicBell_Example1.


Module Bell_Example1.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RA_1RA0LB_------_------_------").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 a b := const 0 <* [1]^^a <* <[0;1]^^b {{B}}> const 0.

Lemma Inc0 a b:
  S0 (2+a) b -->*
  S0 a (2+b).
Proof.
  es.
Qed.

Lemma Incs0 a b:
  S0 (a*2) b -->*
  S0 0 (a*2+b).
Proof.
  gen b.
  ind a Inc0.
Qed.

Definition config n := S0 (n*2) 0.

Lemma Inc1 n:
  config n -->+
  config (n*2+2).
Proof.
  unfold config.
  follow Incs0.
  es.
Qed.

Lemma init:
  c0 -->* config 3.
Proof.
  unfold config.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros i.
  eexists.
  apply Inc1.
Qed.

End Bell_Example1.


