
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0LC0RE_---1LD_1LA0LF_1RB1RE_1RB0LB").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.




Lemma AL l r n:
  l <* [1]^^n <{{A}} r -->*
  l <{{A}} [1]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma ER l r n:
  l {{E}}> [1]^^n *> r -->*
  l <* [1]^^n {{E}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma ER' l r n:
  l {{E}}> [0;1]^^n *> r -->*
  l <* [0;1]^^n {{E}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma BR l r n:
  l {{B}}> [1;0]^^n *> r -->*
  l <* [1;0]^^n {{B}}> r.
Proof.
  shift_rule.
  execute.
Qed.

Lemma FL l r n:
  l <* [0;1]^^n <{{F}} [0] *> r -->*
  l <{{F}} [0] *> [1;0]^^n *> r.
Proof.
  shift_rule.
  execute.
Qed.

Definition S0 n1 n2 n3 n4 :=
  const 0 <* [1]^^n1 <* [0] <* [1]^^n2 {{E}}> [0;1]^^n3 *> [0;0;0] *> [1;0]^^n4 *> const 0.

Ltac execute10 :=
  eapply progress_evstep_trans; execute.

Lemma Inc n1 n2 n3 n4:
  S0 n1 (2+n2) (2+n3) n4 -->+
  S0 (1+n1) (1+n2) (1+n3) (1+n4).
Proof.
  unfold S0.
  follow ER'.
  execute10.
  follow FL.
  execute.
  follow AL.
  do 2 rewrite lpow_shift1.
  execute.
  follow ER.
  rewrite lpow_shift1.
  rewrite lpow_shift21.
  finish.
Qed.

Lemma ROv n1 n2 n4:
  S0 n1 (1+n2) 1 n4 -->+
  S0 (2+n1) (1+n2) (1+n4) 0.
Proof.
  unfold S0.
  execute10.
  follow AL.
  do 2 rewrite lpow_shift1.
  execute.
  follow ER.
  rewrite lpow_shift1.
  execute.
  follow AL.
  do 2 rewrite lpow_shift1.
  execute.
  follow ER.
  repeat rewrite lpow_shift1.
  rewrite <-lpow_shift21.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma LOv n1 n3 n4:
  S0 (4+n1) 1 (2+n3) n4 -->+
  S0 3 (1+n1) (2+n3) (1+n4).
Proof.
  unfold S0.
  follow ER'.
  execute10.
  follow FL.
  execute.
  follow AL.
  do 2 rewrite lpow_shift1.
  execute.
  follow ER.
  execute.
  follow AL.
  execute.
  follow ER.
  execute.
  follow AL.
  do 2 rewrite lpow_shift1.
  execute.
  follow ER.
  repeat rewrite lpow_shift1.
  rewrite lpow_shift21.
  finish.
Qed.


Lemma init:
  c0 -->* S0 4 5 2 1.
Proof.
  unfold S0.
  steps.
Qed.

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


