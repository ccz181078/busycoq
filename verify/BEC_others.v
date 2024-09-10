From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Ltac solve_LInc L:=
  intros;
  apply LInc';
  execute_with_shift_rule.

Ltac solve_RInc R:=
  unfold R;
  intros;
  execute_with_shift_rule.

Ltac solve_RIncs k n m LInc RInc :=
  gen k m;
  induction n as [|n IHn]; intros;
  [ finish
  | follow100 RInc;
    follow100 LInc;
    follow IHn;
    finish ].

Ltac solve_ROv L R LInc:=
  intros;
  unfold L,R;
  cbn[BinaryCounter];
  repeat (
  execute_with_shift_rule;
  execute_with_rotate;
  follow100 LInc).

Module test1.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC1LF_0RD0RC_1LD1RE_0LB0LB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [1;0;0] ([1] *> const 0) n.

Definition R n m := [1;1;1;0]^^(1+n) *> [0] *> [1;1;1;1]^^m *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ n) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (1+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test1.

Module test2.

Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC0LC_1RD0LB_0RE0LE_1LF0RE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0;0] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(1+n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0;1;1;0;1;1;1;0;1] *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ (Pos.succ n)) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test2.

Module test3.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0LC0RF_---1LD_1LE1LF_1RA0LC_0LE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0;0;0] {{F}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [0;1;1]^^(n) *> [0] *> [0;1;1]^^(1+m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv00:
  forall n m,
    L (n~0~0) |> R 0 m -->+
    L (n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv11:
  forall n m,
    L (n~1~1) |> R 0 m -->+
    L (n) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~0) |> R 0 (1+(Pos.to_nat n)*3).


Lemma BigStep n:
  config n -->+
  config (1+n).
Proof.
  unfold config.
  mid10 (L (n~1~1) |> R 0 (2+(Pos.to_nat n)*3)).
  { follow10 ROv00.
    follow100 LInc.
    follow RIncs.
    finish. }
  mid (L (n~1~1) |> R 0 (3+(Pos.to_nat n)*3)).
  { follow100 ROv11.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv11.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L (n~1~1) |> R 0 (2+(Pos.to_nat n)*3)).
  { follow10 ROv00.
    follow100 LInc.
    follow RIncs.
    finish. }
  mid (L (n~1~1) |> R 0 (3+(Pos.to_nat n)*3)).
  { follow100 ROv11.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv11.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test3.

Module test4.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1RD---_0LE0LF_1LA1LF_0LD0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1;0;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;0;0] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [1;0;0]^^(n) *> [0;0;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv0:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv1:
  forall n m,
    L (n~1~1) |> R 0 m -->+
    L (n~1) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~0) |> R 0 (1+(Pos.to_nat n)*2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L (n~1~1) |> R 0 (2+(Pos.to_nat n)*2)).
  { follow10 ROv0.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv1.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test4.

Module test5.

Definition tm := Eval compute in (TM_from_str "1LB0LF_0LC1LF_1RD0LC_0RD0RE_1RA---_0LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [0;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;0;0] {{A}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [1;1;0]^^(n) *> [0] *> [0;1;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv0:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv1:
  forall n m,
    L (n~1~1) |> R 0 m -->+
    L (n~1) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~0) |> R 0 (1+(Pos.to_nat n)*2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L (n~1~1) |> R 0 (2+(Pos.to_nat n)*2)).
  { follow10 ROv0.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv1.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test5.

Module test6.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LF_1RD1LC_---0RE_1RA0RE_0LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;0;0] {{A}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [1;1;0]^^(n) *> [0] *> [0;1;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv0:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv1:
  forall n m,
    L (n~1~1) |> R 0 m -->+
    L (n~1) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~0) |> R 0 (1+(Pos.to_nat n)*2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L (n~1~1) |> R 0 (2+(Pos.to_nat n)*2)).
  { follow10 ROv0.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv1.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test6.


Module test7.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC1LB_---0RD_1RE0RD_1LA0LF_0LE0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;0;0] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [1;1;0]^^(n) *> [0] *> [0;1;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv0:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv1:
  forall n m,
    L (n~1~1) |> R 0 m -->+
    L (n~1) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~0) |> R 0 (1+(Pos.to_nat n)*2).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L (n~1~1) |> R 0 (2+(Pos.to_nat n)*2)).
  { follow10 ROv0.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv1.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test7.

Module test8. (* similar to test2 *)

Definition tm := Eval compute in (TM_from_str "1LB0RB_0LC0LE_1LD0LB_1RE1LF_0RA0RE_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0;0] {{A}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [1;0;0] ([1] *> const 0) n.

Definition R n m := [1] *> [1;1;1;0;1]^^(n) *> [0;0] *> [1;1;1;0;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ (Pos.succ n)) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test8.

Module test9.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RB_0LD1LA_0RE1LC_1RF0RA_1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;1;0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [1;1;0] [0;1;0] ([] *> const 0) n.

Definition R n m := [1] *> [1;1;0;1]^^(n) *> [1;1;1;0;0] *> [1;1;0;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ (Pos.succ n)) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L ((n+1)~1) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test9.


Module test10.

Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1LF_1RD0RC_0LA0LE_0LA0RB_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;0] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [1;0;1;0;0] [1;0;0;0;0] ([1] *> const 0) n.

Definition R n m := [1;0]^^(n) *> [0] *> [1;0]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (n) <| R (3+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L ((2+n*3)~0) |> R 0 (4+(Pos.to_nat n)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test10.

Module test11.

Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC0RB_0LD1LC_1RA1LE_---1LF_0RF0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test11.

Module test12.

Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC0RB_0LD1LC_1RA1LE_---1LF_1RC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test12.

Module test13.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC0RB_0LD1LC_1RA1LA_1RC0LF_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test13.

Module test14.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC1LB_1RD0LF_---1RE_1LC0RE_0LB1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test14.

Module test15. (* similar to test2 *)

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC1LA_0RD0RC_0RE1RB_1RF0LA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Definition R n m := [1;0;0] *> [1;1;0;1;0;0]^^(n) *> [0;0;1;0] *> [1;1;0;1;0;0]^^(m) *> [1] *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ (Pos.succ n)) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test15.

Module test16.

Definition tm := Eval compute in (TM_from_str "1LB1LF_0RC0LE_1LA1LD_1RE1RB_1LA0RD_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [1;0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [1;1;0] [1;0;0] ([1] *> const 0) n.

Definition R n m := [1;1;0;1;1]^^(1+n) *> [0;0;1;1] *> [0;1;1;1;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L ((n+1)~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test16.

Module test17.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RD_0LB1LE_1LC0RD_0LF1RB_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [0;0] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0;0] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;1;1;0;0] [1;1;1;1;0;0] ([1;1;1;1] *> const 0) n.

Definition R n m := [1;1] *> [1;0;1;1;1]^^(n) *> [0;0] *> [1;1;1;0;1]^^(m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (2+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1~0) |> R 0 ((Pos.to_nat (n~1))).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test17.

Module test18.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0LC0RB_1RA1LD_0RB0LE_1LC0LF_---1LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0;0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [1;0]^^(n) *> [0] *> [1;0]^^(2+m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv0:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv01:
  forall n m,
    L (n~0~1) |> R 0 m -->+
    L (n~0) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~1) |> R 0 ((Pos.to_nat (n~0))).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L n~1~0 |> R 0 (Pos.to_nat n~1)).
  { follow10 ROv01.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv0.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test18.

Module test19.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0LC1RD_---1LD_1LE1LF_1RA0LC_0LE0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [1;1;1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0;0;0] {{F}}> r) (at level 30).

Definition L n := BinaryCounter [0] [1] ([1] *> const 0) n.

Definition R n m := [0;1;1]^^(n) *> [0] *> [0;1;1]^^(1+m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv00:
  forall n m,
    L (n~0~0) |> R 0 m -->+
    L (n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma ROv11:
  forall n m,
    L (n~1~1) |> R 0 m -->+
    L (n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0~0) |> R 0 (1+(Pos.to_nat n)*3).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  mid10 (L n~1~1 |> R 0 (2+(Pos.to_nat n)*3)).
  { follow10 ROv00.
    follow100 LInc.
    follow RIncs.
    finish. }
  mid (L n~1~1 |> R 0 (3+(Pos.to_nat n)*3)).
  { follow100 ROv11.
    follow100 LInc.
    follow RIncs.
    finish. }
  follow100 ROv11.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test19.

Module test20.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC0LD_1LD0RC_0RE0LA_1LA1RB_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Definition R n m := [0;0] *> [1;0;0]^^(m) *> [1;0;1]^^(n) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 2).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test20.

Module test21.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LE_1RA0LB_0RF1RC_1LC1LA_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Definition R n m := [1;0] *> [1;1;0]^^(m) *> [1;1;1]^^(n) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ n) <| R (1+m) 0.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test21.

Module test22.

Definition tm := Eval compute in (TM_from_str "1LB0RA_0RC0LE_1LE1RD_1RA0LB_1LD1LF_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{D}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{A}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Definition R0 n m := [1;0;0]^^(1+m) *> [1;0;1]^^(n) *> const 0.
Definition R1 n m := [1;0;0]^^(n) *> [0] *> [1;0;1]^^(1+m) *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc0:
  forall l n m,
    l |> R0 (1+n) m -->+
    l <| R0 n (1+m).
Proof.
  solve_RInc R0.
Qed.

Lemma RInc1:
  forall l n m,
    l |> R1 (1+n) m -->+
    l <| R1 n (1+m).
Proof.
  solve_RInc R1.
Qed.

Lemma ROv0:
  forall n m,
    L n |> R0 0 m -->*
    L n <| R1 m 0.
Proof.
  unfold R1.
  solve_ROv L R0 LInc.
Qed.

Lemma ROv1:
  forall n m,
    L (n~1) |> R1 0 m -->+
    L (Pos.succ n) <| R0 (1+m) 0.
Proof.
  unfold R0.
  solve_ROv L R1 LInc.
Qed.

Lemma RIncs0 k n m:
  L k |> R0 n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R0 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc0.
Qed.

Lemma RIncs1 k n m:
  L k |> R1 n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R1 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc1.
Qed.

Definition config n :=
  L (n~0~1) |> R1 0 ((Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv1.
  follow100 LInc.
  follow RIncs0.
  follow ROv0.
  follow100 LInc.
  follow RIncs1.
  finish.
Qed.

End test22.

Module test23.

Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC0RB_0LD1LC_1RA1LE_---1LF_1LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test23.

Module test24.

Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC0RB_0LF0RD_---1LE_1LC0LA_1RA1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test24.

Module test25.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC0RB_0LE0RA_1LC0LF_1RA1LA_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test25.

Module test26.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC0RB_0LD1LC_1RA1LA_1LC0LF_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{C}} [1] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;1] ([1;1] *> const 0) n.

Definition R n m := [1;1;0;1]^^(n) *> [0;0] *> [1;1;0;1]^^(1+m) *> [0] *> [1;1;0;1]^^3 *> [0] *> [1;1;0;1]^^2 *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~0) |> R 0 m -->+
    L (Pos.succ n) <| R (m) 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~0) |> R 0 (0+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test26.

Module test27.

Definition tm := Eval compute in (TM_from_str "1RB1LE_0RC0RB_1LC1RD_0LA0LC_1LF---_1LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [1;0;0] ([1] *> const 0) n.

Definition R n m := [1;1;1;0]^^(1+n) *> [0] *> [1;1;1;1]^^m *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ n) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (1+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test27.

Module test28.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC1LF_0RD0RC_1LD1RE_1LD0LB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{B}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [1;0;0] ([1] *> const 0) n.

Definition R n m := [1;1;1;0]^^(1+n) *> [0] *> [1;1;1;1]^^m *> const 0.

Lemma LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.
Proof.
  solve_LInc L.
Qed.

Lemma RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).
Proof.
  solve_RInc R.
Qed.

Lemma ROv:
  forall n m,
    L (n~1) |> R 0 m -->+
    L (Pos.succ n) <| R m 1.
Proof.
  solve_ROv L R LInc.
Qed.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
Proof.
  solve_RIncs k n m LInc RInc.
Qed.

Definition config n :=
  L (n~1) |> R 0 (1+(Pos.to_nat n)).

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config 1).
  1: unfold config; cbn; solve_init.
  apply progress_nonhalt_simple.
  intro n.
  exists (1+n)%positive.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

End test28.
