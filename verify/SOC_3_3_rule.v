From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0LF_1LD0LC_1RA0RB_1RD---_0RA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Notation "l <1| r" := (l <{{D}} [1;0;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1] {{B}}> r) (at level 30).

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |1> rd0^^m *> [1;0] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n m:
  l |1> rd1^^n *> [1;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <1| rd0^^(2+n+m) *> [1;0] *> r.
Proof.
  es.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RF_0LD0LC_0RE0RB_1LA---_1RA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <| rd0^^(2+n+m) *> [1] *> r.
Proof.
  es.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0LB_1RE0RD_1RA1RE_1LB1RF_1RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_1 l r n:
  l |> rd1^^n *> [1] *> rd1^^2 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> rd0 *> r.
Proof.
  es.
Qed.

Lemma ROv_0 l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <| [1] *> r.
Proof.
  es.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RF_0LD0LC_1RE0RB_1RF---_1RA1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <| rd0^^(2+n+m) *> [1] *> r.
Proof.
  es.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LA---_1LC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Notation "l <1| r" := (l <{{D}} [1;0;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1] {{B}}> r) (at level 30).

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |1> rd0^^m *> [1;0] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n m:
  l |1> rd1^^n *> [1;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <1| rd0^^(2+n+m) *> [1;0] *> r.
Proof.
  es.
Qed.
End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0LA_1LD0LC_1RA0RF_1RD---_1LC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Notation "l <1| r" := (l <{{D}} [1;0;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1] {{B}}> r) (at level 30).

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |1> rd0^^m *> [1;0] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n m:
  l |1> rd1^^n *> [1;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <1| rd0^^(2+n+m) *> [1;0] *> r.
Proof.
  es.
Qed.
End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1RD---_1LC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Notation "l <1| r" := (l <{{D}} [1;0;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1] {{B}}> r) (at level 30).

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |1> rd0^^m *> [1;0] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n m:
  l |1> rd1^^n *> [1;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <1| rd0^^(2+n+m) *> [1;0] *> r.
Proof.
  es.
Qed.
End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1LF---_1LC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Notation "l <1| r" := (l <{{D}} [1;0;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1] {{B}}> r) (at level 30).

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |1> rd0^^m *> [1;0] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n m:
  l |1> rd1^^n *> [1;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <1| rd0^^(2+n+m) *> [1;0] *> r.
Proof.
  es.
Qed.
End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_0RD1RA_1LA---_1LF0RC_1RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1RD1RA_1LB---_1LF0RC_1RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0LB_1RD1RA_1LE---_1RC1LE_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RE_1RD1LC_1LF1RB_0RA0RD_0LB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LD0LC_1RD1RE_0LE0RB_1RA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM13.


Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_0LE0LD_1LB0LD_1RA0RF_1LC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LB_0LD1RB_1RF0RE_1LC1RA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LB_0LD0RD_1RE0RF_1RA---_1LC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM17.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC0RE_0LB1RA_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0LE1LC_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM19.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC0RE_0LB1RA_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM20.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1RF_1LD1RA_0RE0LD_1LF1RC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_0LE0RD_1RA---_1RD0RF_1LC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM22.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RE_1LD1RA_1RE0LD_0LA---_1LE1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM23.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA---_0LA1RF_1LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM24.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM25.


Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_1RD1RE_1LB---_0LA1RF_1LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM26.


Module TM27.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{B}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

End TM27.


Module TM28.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM28.


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM29.


Module TM30.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_1RD0LC_1LE1RB_0LF1LE_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM30.


Module TM31.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_0LD---_1LE1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM31.


Module TM32.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_0LD0RC_1LE1RB_0LF0LE_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> rd0 *> r -->+
  l <| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{F}} [0;1;1;1] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).
Notation "l <2| r" := (l <{{F}} [0;1;1;0] *> r) (at level 30).

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma ROv_O l r:
  l |> [1;1;0] *> r -->+
  l <* ld0 <* ld1 |1> r.
Proof.
  es.
Qed.

Lemma ROv' l r n:
  l |> rd1^^n *> [0;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <1| r.
Proof.
  es.
Qed.


Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> rd0 *> r -->+
  l <2| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Lemma LInc2 l r n:
  l <* ld0 <* ld1^^n <2| r -->+
  l <* ld1 <* ld0^^n <1| r.
Proof.
  es.
Qed.

Lemma ROv1' l r n:
  l |1> rd1^^n *> [0;1;0] *> r -->+
  l <* ld1 <* ld0^^n <1| r.
Proof.
  es.
Qed.

End TM32.


Module TM33.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_0LD1LE_1LE1RB_0LF0LE_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> rd0 *> r -->+
  l <| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{F}} [0;1;1;1] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).
Notation "l <2| r" := (l <{{F}} [0;1;1;0] *> r) (at level 30).

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma ROv_O l r:
  l |> [1;1;0] *> r -->+
  l <* ld0 <* ld1 |1> r.
Proof.
  es.
Qed.

Lemma ROv' l r n:
  l |> rd1^^n *> [0;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <1| r.
Proof.
  es.
Qed.


Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> rd0 *> r -->+
  l <2| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Lemma LInc2 l r n:
  l <* ld0 <* ld1^^n <2| r -->+
  l <* ld1 <* ld0^^n <1| r.
Proof.
  es.
Qed.

Lemma ROv1' l r n:
  l |1> rd1^^n *> [0;1;0] *> r -->+
  l <* ld1 <* ld0^^n <1| r.
Proof.
  es.
Qed.

End TM33.


Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_0RB---").
(* similar to TM27 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

End TM34.


Module TM35.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_1RC---").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM35.


Module TM36.
Definition tm := Eval compute in (TM_from_str "1RB1RE_0RC---_1RD1LC_0RE1RA_1LF0RD_1RC0LF").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

End TM36.


Module TM37.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC---_1LD1RA_0LE0LD_1RE1RF_0LF0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM37.


Module TM38.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_0RF1RA_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^n <* ld0^^m <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.
End TM38.


Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_1RD---").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^n <* ld0^^m <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

End TM39.


Module TM40.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_1LE---").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^n <* ld0^^m <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

End TM40.


Module TM41.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC0RE_0RB1RA_---1RA").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^n <* ld0^^m <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

End TM41.


Module TM42.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA1LC_---1RA").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^n <* ld0^^m <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

End TM42.


Module TM43.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC0RE_0RB1RA_---1LD").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^n <* ld0^^m <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

End TM43.


Module TM44.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RD_1LD1RA_1RE0LD_0LA---_1LE1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM44.

Module TM45.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LB_1LE1RD_1LB1RF_0LF1LE_0RA0RC").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.
End TM45.


Module TM46.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD1RA_0LE1LD_1RF0RC_1RA---").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.
End TM46.


Module TM47.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RE_1LD1RA_1LA0LD_0LA---_1LE1RC").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.
End TM47.


Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD---_1RA0LD_1RD1RF_1LD0RB").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r:
  l |2> rd0 *> r -->+
  l <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM48.


Module TM49.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1RA---").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r:
  l |2> rd0 *> r -->+
  l <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM49.


Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RD_1LA---_1RF1RE_1LF0RB_1RA0LF").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r:
  l |2> rd0 *> r -->+
  l <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM50.


Module TM51.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_0RC---").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

End TM51.

Module TM52.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM52.


Module TM53.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_1RC---_1RA0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM53.


Module TM54.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1LC1RD_0LD0LC_1RE0RF_1RB---_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM54.


Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_0RD1RF_1LE0RC_1RB0LE_1RA1RD").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM55.


Module TM56.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA---_1RA1RF_1LA0RC").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM56.


Module TM57.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_1RD1RE_1LB---_1RA1RF_1LA0RC").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(2+m+n) |2> r.
Proof.
  es.
Qed.

End TM57.


Module TM58.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0RA_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM58.


Module TM59.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0RA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM59.


Module TM60.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0LD_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM60.


Module TM61.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0LD_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM61.


Module TM62.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_1RB0RA_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM62.


Module TM63.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_1LD0RA_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM63.


Module TM64.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC1RE_0RA0RA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM64.


Module TM65.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC1RE_1LD0RA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM65.


Module TM66.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0LB_1RE1RD_---0LA_1LB1RF_1RC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM66.


Module TM67.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RD_1RE1RA_1LF1RE_1LF1RB_0LB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{B}} [0;1;1;1;1;1;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;0;1;1;1;1;1] {{E}}> r) (at level 30).

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^(1+n) |1> [1] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1_S l r n:
  l |1> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1_O l r n:
  l <* ld0 <* ld1^^n |1> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |1> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM67.


Module TM68.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0RE_1RF1RD_0LB---_1LD1RF_1LA1RB").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.
End TM68.


Module TM69.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM69.


Module TM70.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB0RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM70.


Module TM71.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB1RF_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM71.


Module TM72.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB1RF_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM72.


Module TM73.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC0LE_1LD0LC_1RE0RA_1RB1RF_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM73.


Module TM74.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RE_0LD0LC_1RD0RA_1RF0RA_1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM74.


Module TM75.
Definition tm := Eval compute in (TM_from_str "1LB1LB_1LC1RD_0LD0LC_1RE0RF_1RB---_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM75.


Module TM76.
Definition tm := Eval compute in (TM_from_str "1RB1RC_0LA---_1LD1RF_1LE0LD_1RC0RA_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM76.


Module TM77.
Definition tm := Eval compute in (TM_from_str "1LB1LC_0RA1RC_1LD1RE_0LE0LD_1RF0RB_1RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM77.


Module TM78.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RE_0RF1RB_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM78.


Module TM79.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LA---_1RB1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM79.


Module TM80.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC---_1LD0LC_1RE0RA_1LC1RF_1RD0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM80.


Module TM81.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_0LB---").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld1 <* ld0^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <* ld1 <* ld0^^n <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^m |2> r.
Proof.
  es.
Qed.

End TM81.


Module TM82.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_1LE1RD_1RB1RF_0LF0LE_1RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_SS l r n m:
  l |> rd1^^(2+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r m:
  l |> rd1^^1 *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld0^^(1+m) <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

End TM82.

Module TM83.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC0LB_1RD1LC_1LB1RE_1RF1RA_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM83.


Module TM84.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_0RF0RA_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM84.


Module TM85.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_0RF0RA_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM85.


Module TM86.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_1RF0RA_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM86.


Module TM87.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_1RF0RA_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM87.


Module TM88.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_0RA0RA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM88.


Module TM89.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_0RA0LD_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM89.


Module TM90.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_1LD0RA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM90.


Module TM91.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_0RD0RA_1LE---_1RF1RC_1RA1LF").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_SS l r n m:
  l |> rd1^^(2+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r m:
  l |> rd1^^1 *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld0^^(1+m) <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

End TM91.


Module TM92.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RA_0LE0LD_1RF0RC_1LB---").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_SS l r n m:
  l |> rd1^^(2+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r m:
  l |> rd1^^1 *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld0^^(1+m) <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

End TM92.


Module TM93.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1RF_0LD1LC_0RE0RB_1LA---_1LA1RD").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM93.


Module TM94.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1RF_0LD1LC_1RE0RB_1RF---_1LA1RD").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM94.


Module TM95.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RF_1RD0LC_1LE---_1RA1LE_0RD0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.
Proof.
  es.
Qed.

End TM95.


Module TM96.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_0RF0RA_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^n *> [1] *> rd1^^(2+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <| rd1 *> rd0^^m *> [0] *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <| [1] *> r.
Proof.
  es.
Qed.

End TM96.


Module TM97.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0RA_1RE1RB_1LF1RC_1LC0LF").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM97.


Module TM98.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RE_1RD1LC_1LF1RB_0RA0RD_0RA0LF").
(* similar to TM12 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM98.


Module TM99.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RD1LC_1LF1RE_1RC1RA_0LE0LF").
(* similar to TM12 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM99.


Module TM100.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1RC_0LD1RD_1RE0RB_1RF---_1LA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m:
  ldh <* ld1^^(1+n) <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^2 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma LOv_O r n:
  ldh <* ld1^^(1+n) <| rd0 *> r -->+
  ldh <* ld0^^n <| rd0^^2 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^(1+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma ROv_O_S l r n m k:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m+n) <* ld1^^3 <* ld0^^k <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma ROv_O_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m+n) <* ld1 <| rd0^^2 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

End TM100.


Module TM101.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0LC1LB_0RD0RA_1LE---_1RA0LE_1LE1RC").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM101.


Module TM102.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(1+m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM102.


Module TM103.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_0RD---").
(* simular to TM102 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(1+m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM103.


Module TM104.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RE_1RD1LC_1LF1RB_0RA0RD_0LE0LF").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_SS l r n m:
  l |> rd1^^(2+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r m:
  l |> rd1^^1 *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld0^^(1+m) <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

End TM104.


Module TM105.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RD1LC_1LF1RE_1RC1RA_0LA0LF").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_SS l r n m:
  l |> rd1^^(2+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r m:
  l |> rd1^^1 *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld0^^(1+m) <| rd1 *> [1] *> r.
Proof.
  es.
Qed.

End TM105.


Module TM106.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC1LB_1RD0RA_1RE---_1LF1RC_1RA0LF").
(* similar to TM31 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

End TM106.


Module TM107.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD1RD_0LE1RE_1RF0RC_1RA---").
(* similar to TM100 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m:
  ldh <* ld1^^(1+n) <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^2 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma LOv_O r n:
  ldh <* ld1^^(1+n) <| rd0 *> r -->+
  ldh <* ld0^^n <| rd0^^2 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^(1+n) *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma ROv_O_S l r n m k:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m+n) <* ld1^^3 <* ld0^^k <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma ROv_O_O l r n m:
  l <* ld0 <* ld1^^n |> [1] *> rd1^^(1+m) *> rd0 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m+n) <* ld1 <| rd0^^2 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

End TM107.


Module TM108.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC---_1LD1RF_1LE0LD_1RC1LE_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.



Notation "l <1| r" := (l <{{E}} [1;1;1;1] *> r) (at level 30).
Notation "l |1> r" := (l <* [0;1;1;1] {{C}}> r) (at level 30).

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> rd0 *> r -->+
  l <1| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^n *> [1] *> rd1^^(2+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) |1> rd0^^m *> rd1 *> r.
Proof.
  es.
Qed.



Lemma ROv_SS l r n m:
  l |> rd1^^n *> [1] *> rd1^^(3+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd1 *> rd0^^m *> rd1 *> r.
Proof.
  follow11 (ROv_S l r n (1+m)).
  replace (rd0^^(1+m) *> rd1 *> r) with (rd1^^0 *> rd0 *> rd0^^m *> rd1 *> r) by (simpl_tape; reflexivity).
  follow11 RInc1.
  follow10 LInc1.
  finish.
Qed.

Lemma ROv_SO l r n m:
  l |> rd1^^n *> [1] *> rd1^^2 *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd0^^(1+m) *> rd1 *> r.
Proof.
  follow11 (ROv_S l (rd1^^m *> rd0 *> r) n 0).
  replace (rd0^^0*>rd1*>rd1^^m*>rd0*>r) with (rd1^^(1+m)*>rd0*>r) by (simpl_tape; reflexivity).
  follow11 RInc1.
  follow10 LInc1.
  finish.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <| [1] *> r.
Proof.
  es.
Qed.

End TM108.


Module TM109.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC---_1RD1LC_1LA1RE_1RC1RF_1RB0RD").
(* similar to TM12 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^(1+m) <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <* ld1^^m <| [1] *> r.
Proof.
  es.
Qed.

End TM109.


Module TM110.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_1RA1RD_1RE1RF_1RB0LE_1LE0RC").
(* simular to TM81 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [0;1;1;0;1;1;1;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^(n) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r:
  l |2> rd0 *> r -->+
  l <* ld1 <| [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m+n) |2> r.
Proof.
  es.
Qed.

End TM110.


Module TM111.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC0RE_1RF0LE_0RA---").
(* similar to TM108 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.



Notation "l <1| r" := (l <{{C}} [1;1;1;1] *> r) (at level 30).
Notation "l |1> r" := (l <* [0;1;1;1] {{A}}> r) (at level 30).

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |> [1] *> r.
Proof.
  solve_LOverflow.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> rd0 *> r -->+
  l <1| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^n *> [1] *> rd1^^(2+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) |1> rd0^^m *> rd1 *> r.
Proof.
  es.
Qed.



Lemma ROv_SS l r n m:
  l |> rd1^^n *> [1] *> rd1^^(3+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd1 *> rd0^^m *> rd1 *> r.
Proof.
  follow11 (ROv_S l r n (1+m)).
  replace (rd0^^(1+m) *> rd1 *> r) with (rd1^^0 *> rd0 *> rd0^^m *> rd1 *> r) by (simpl_tape; reflexivity).
  follow11 RInc1.
  follow10 LInc1.
  finish.
Qed.

Lemma ROv_SO l r n m:
  l |> rd1^^n *> [1] *> rd1^^2 *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd0^^(1+m) *> rd1 *> r.
Proof.
  follow11 (ROv_S l (rd1^^m *> rd0 *> r) n 0).
  replace (rd0^^0*>rd1*>rd1^^m*>rd0*>r) with (rd1^^(1+m)*>rd0*>r) by (simpl_tape; reflexivity).
  follow11 RInc1.
  follow10 LInc1.
  finish.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <| [1] *> r.
Proof.
  es.
Qed.

End TM111.
