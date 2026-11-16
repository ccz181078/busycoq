
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Section RGRv1.
Hypothesis tm:TM.
Hypothesis QR:Q.
Definition S0 n1 n2 n3 n4 :=
  const 0 <* [1]^^n1 <* [0] <* [1]^^n2 {{QR}}> [0;1]^^n3 *> [0;0;0] *> [1;0]^^n4 *> const 0.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

Hypothesis Inc:
  forall n1 n2 n3 n4,
    S0 n1 (2+n2) (2+n3) n4 -->+
    S0 (1+n1) (1+n2) (1+n3) (1+n4).

Hypothesis ROv:
  forall n1 n2 n4,
    S0 n1 (1+n2) 1 n4 -->+
    S0 (2+n1) (1+n2) (1+n4) 0.

Hypothesis LOv:
  forall n1 n3 n4,
    S0 (4+n1) 1 (2+n3) n4 -->+
    S0 3 (1+n1) (2+n3) (1+n4).

Hypothesis init:
  c0 -->* S0 4 5 2 1.

Definition S1 n :=
  let '(n1,n2,n3,n4):=n in
  S0 (4+n1-n2) (1+n2) (1+n3) (1+n4-n3).

Definition WF (n:nat*nat*nat*nat):Prop :=
  let '(n1,n2,n3,n4):=n in
  4+n1>=n2 /\ n3<=1+n4 /\ (n3 <= n2 /\ n1>=n4+1 \/ n3>n2 /\ n1>=n4+3).

Theorem nonhalt:
  ~halts tm c0.
Proof.
  Search halts.
  apply (multistep_nonhalt _ _ (S1 (4,4,1,1)%nat)).
  1: apply init.
  apply progress_nonhalt_cond with (P:=WF).
  all: unfold WF.
  2: lia.
  unfold S1.
  intro i.
  destruct i as [[[n1 n2] n3] n4].
  intro H.
  destruct n3 as [|n3].
  - exists (2+n1,n2,1+n4,n4).
    split. 2: lia.
    follow10 ROv. finish.
  - destruct n2 as [|n2].
    + exists (n1-1,n1,1+n3,1+n4).
      split. 2: lia.
      follow10 LOv. finish.
    + exists (n1,n2,n3,n4).
      split. 2: lia.
      follow10 Inc. finish.
Qed.

End RGRv1.


Inductive Cert :=
| cert1
  (QR : Q).

Ltac solve_cert cert :=
match cert with
  (cert1 ?QR) =>
  eapply (nonhalt _ QR);
  [ unfold S0;
    try (execute_with_shift_rule || fail)
  | unfold S0;
    try (execute_with_shift_rule || fail)
  | unfold S0;
    try (execute_with_shift_rule || fail)
  | unfold S0;
    try (solve_init || fail)
  ]
end.


Definition tm0 := Eval compute in (TM_from_str "1RB1LA_0LC0RE_---1LD_1LA0LF_1RB1RE_1RB0LB").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 E).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB0RC_1RB0LB").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 A).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB0RC_0LC0RE_---1LD_1LA0LF_1RB1RE_1LD0LB").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 E).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB1LA_0LC0RE_---1LD_1RA0LF_1RB1RE_1RB0LB").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 E).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1LB0LD_1RC0LA_1RD1LC_1LF0RE_1RD1RE_---0RB").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 E).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB1LA_0LC0RE_---1LD_1RA0LF_1RB1RE_1LD0LB").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 E).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB1RA_1LC0RA_---0RD_1LF0LE_1LD0LB_1RB1LF").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 A).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1RB1RA_0LC0RA_---1LD_1LE0LF_1RB1LE_1LD0LB").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 A).
Qed.



(*
```
1RB1LA_0LC0RE_---1LD_1LA0LF_1RB1RE_1RB0LB

start: (4, 4, 1, 1)
(n1, 1+n2, 1+n3, n4) -> (n1, n2, n3, n4)
(n1, n2, 0, n4) -> (2+n1, n2, 1+n4, n4)
(1+n1, 0, 1+n3, n4) -> (n1, 1+n1, 1+n3, 1+n4)

(n1, n2, n3, n4) := 0^inf 1^(4+n1-n2) 0 1^(1+n2) E> 01^(1+n3) 000 10^(1+n4-n3) 0^inf, if 4+n1>=n2 and n3<=1+n4 and (if n2>=n3 then n1>=n4+1 else n1>=n4+3)
```

*)


