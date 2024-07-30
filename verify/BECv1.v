
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Set Default Goal Selector "!".





Section BECv1.

Hypothesis tm:TM.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Hypothesis QL QR QL' QR': Q.
Hypothesis d0 d1 d1' d d': list Sym.
Hypothesis w0 w0' w1 w w': list Sym.
Hypothesis m0 m1 m2 m3: list Sym.
Hypothesis a k0 k1:nat.

(*

bell eats counter
typical behavior version 1:

Ls(1) := 0^inf d1
Ls(2i) := Ls(i) d0
Ls(2i+1) := Ls(i) d1

0^inf A> 0^inf --> Ls(2*(k0+1)) m0 w' QR> w1 w0^(k1+1) 0^inf
k1+1=k0+a

HR1~HR3
w' QR> w0 --> w0' w' QR>
w' QR> w0 w1 w0 --> <QL w w1 w0 w0
w0' <QL w --> <QL w w0

HL2~HL4
d1 <QL' d' --> <QL' d' d1'
d0 <QL' d' --> d1 d QR'>
d QR'> d1' --> d0 d QR'>

HL1,HL5
m0 <QL w --> <QL' d' m1
d QR'> m1 --> m0 w' QR>

d0 m0 w' QR> w1 w0 --> <QL' d' m2   (HE0)
d QR'> m2 --> m3 w0' w' QR>         (HE1)
w0' w' QR> 0^inf --> <QL w w1 w0 0^inf  (HE2)
m3 <QL w --> <QL' d' m1 w0^a   (HE3)

*)

Hypothesis HL0:
  forall r,
    const 0 <{{QL'}} d' *> r -->*
    const 0 <* d0 <{{QL'}} d' *> r.

Hypothesis HL1:
  forall l r,
    l <* m0 <{{QL}} w *> r -->*
    l <{{QL'}} d' *> m1 *> r.

Hypothesis HL2:
  forall l r,
    l <* d1 <{{QL'}} d' *> r -->*
    l <{{QL'}} d' *> d1' *> r.

Hypothesis HL3:
  forall l r,
    l <* d0 <{{QL'}} d' *> r -->+
    l <* d1 <* d {{QR'}}> r.

Hypothesis HL4:
  forall l r,
    l <* d {{QR'}}> d1' *> r -->*
    l <* d0 <* d {{QR'}}> r.

Hypothesis HL5:
  forall l r,
    l <* d {{QR'}}> m1 *> r -->*
    l <* m0 <* w' {{QR}}> r.


Fixpoint LeftBinaryCounter (n:positive) :=
match n with
| xH => d1 *> const 0
| xI n0 => d1 *> (LeftBinaryCounter n0)
| xO n0 => d0 *> (LeftBinaryCounter n0)
end.

Lemma LInc n r:
  (LeftBinaryCounter n) <{{QL'}} d' *> r -->+
  (LeftBinaryCounter (n+1)) <* d {{QR'}}> r.
Proof.
  gen r.
  induction n; intro r.
  - cbn.
    follow HL2.
    follow10 IHn.
    follow HL4.
    finish.
  - apply HL3.
  - cbn.
    follow HL2.
    follow HL0.
    follow10 HL3.
    follow HL4.
    finish.
Qed.



Definition RightUnaryCounter n m :=
  w0^^n *> w1 *> w0^^m *> const 0.

Hypothesis HR1:
  forall l r,
  l <* w' {{QR}}> w0 *> r -->*
  l <* w0' <* w' {{QR}}> r.

Hypothesis HR2:
  forall l r,
  l <* w' {{QR}}> w0 *> w1 *> w0 *> r -->*
  l <{{QL}} w *> w1 *> w0 *> w0 *> r.

Hypothesis HR3:
  forall l r,
  l <* w0' <{{QL}} w *> r -->*
  l <{{QL}} w *> w0 *> r.

Lemma HR1' n l r:
  l <* w' {{QR}}> w0^^n *> r -->*
  l <* w0'^^n <* w' {{QR}}> r.
Proof.
  shift_rule.
  apply HR1.
Qed.

Lemma HR3' n l r:
  l <* w0'^^n <{{QL}} w *> r -->*
  l <{{QL}} w *> w0^^n *> r.
Proof.
  shift_rule.
  apply HR3.
Qed.

Lemma lpow_1:
  forall {A} (ls:list A), ls^^1 = ls.
Proof.
  intros. cbn.
  apply List.app_nil_r.
Qed.

Lemma RDec n m l:
  l <* w' {{QR}}> RightUnaryCounter (n+1) (m+1) -->*
  l <{{QL}} w *> RightUnaryCounter n (m+2).
Proof.
  unfold RightUnaryCounter.
  rewrite lpow_add,Str_app_assoc.
  follow HR1'.
  rewrite lpow_1.
  replace (m+1) with (1+m) by lia.
  rewrite lpow_add,Str_app_assoc.
  rewrite lpow_1.
  follow HR2.
  replace (m+2) with (2+m) by lia.
  simpl_tape.
  follow HR3'.
  finish.
Qed.



Hypothesis HE0:
  forall l r,
    l <* d0 <* m0 <* w' {{QR}}> w1 *> w0 *> r -->*
    l <{{QL'}} d' *> m2 *> r.

Hypothesis HE1:
  forall l r,
    l <* d {{QR'}}> m2 *> r -->*
    l <* m3 <* w0' <* w' {{QR}}> r.

Hypothesis HE2:
  forall l,
    l <* w0' <* w' {{QR}}> const 0 -->*
    l <{{QL}} w *> w1 *> w0 *> const 0.

Hypothesis HE3:
  forall l r,
    l <* m3 <{{QL}} w *> r -->*
    l <{{QL'}} d' *> m1 *> w0^^a *> r.


Lemma EatDigit k m:
  LeftBinaryCounter (2*k) <* m0 <* w' {{QR}}> RightUnaryCounter 0 (1+m) -->*
  LeftBinaryCounter (k+1) <{{QL'}} d' *> m1 *> RightUnaryCounter (a+m) 1.
Proof.
  cbn.
  rewrite Str_app_assoc.
  follow HE0.
  apply progress_evstep.
  follow10 LInc.
  follow HE1.
  follow HR1'.
  rewrite lpow_shift'.
  follow HE2.
  follow HR3'.
  follow HE3.
  unfold RightUnaryCounter.
  simpl_tape.
  finish.
Qed.

Lemma Inc k n m:
  LeftBinaryCounter (k) <* m0 <* w' {{QR}}> RightUnaryCounter (n+1) (m+1) -->+
  LeftBinaryCounter (k+1) <* m0 <* w' {{QR}}> RightUnaryCounter n (m+2).
Proof.
  follow RDec.
  follow HL1.
  follow10 LInc.
  follow HL5.
  finish.
Qed.

Lemma Incs k n m c:
  LeftBinaryCounter (k) <* m0 <* w' {{QR}}> RightUnaryCounter (n+(S c)) (m+1) -->+
  LeftBinaryCounter (k+(Pos.of_succ_nat c)) <* m0 <* w' {{QR}}> RightUnaryCounter n (m+1+(S c)).
Proof.
  gen k n m.
  induction c; intros k n m.
  - cbn.
    replace (m+1+1) with (m+2) by lia.
    apply Inc.
  - replace (n+(S(S c))) with ((n+(S c))+1) by lia.
    follow11 Inc.
    replace (m+2) with (m+1+1) by lia.
    follow10 IHc.
    finish.
Qed.

Lemma BigStep k m:
  LeftBinaryCounter (2*k) <* m0 <* w' {{QR}}> RightUnaryCounter 0 (m+1) -->+
  LeftBinaryCounter (k+1+(Pos.of_succ_nat (a+m))) <* m0 <* w' {{QR}}> RightUnaryCounter 0 (a+m+1).
Proof.
  replace (m+1) with (1+m) by lia.
  follow EatDigit.
  follow10 LInc.
  follow HL5.
  remember (a+m) as c.
  destruct c.
  - finish.
  - follow100 (Incs (k+1+1) 0 0 c).
    finish.
Qed.


Definition to_config(x:nat) :=
  LeftBinaryCounter (2*(Pos.of_succ_nat (k0+a*x))) <* m0 <* w' {{QR}}> RightUnaryCounter 0 (k1+a*x+1).

Hypothesis init:
  c0 -->*
  to_config 0.

Hypothesis H_a_k0_k1:
  k1+1=k0+a.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  apply progress_nonhalt_simple.
  intro i.
  exists (S i).
  unfold to_config.
  follow10 BigStep.
  finish.
Qed.

End BECv1.

Inductive BEC_cert_v1 :=
| Build_BEC_cert_v1
  (QL QR QL' QR' : Q)
  (d0 d1 d1' d d' : list Sym)
  (w0 w0' w1 w w' : list Sym)
  (m0 m1 m2 m3 : list Sym)
  (a k0 k1 : nat).


Ltac steps := cbn; intros;
  repeat ((try apply evstep_refl); step).

Ltac solve_BECv1 tm cert :=
match cert with
  (Build_BEC_cert_v1
  ?QL ?QR ?QL' ?QR'
  ?d0 ?d1 ?d1' ?d ?d'
  ?w0 ?w0' ?w1 ?w ?w'
  ?m0 ?m1 ?m2 ?m3
  ?a ?k0 ?k1) =>
  apply (nonhalt tm
    QL QR QL' QR'
    d0 d1 d1' d d'
    w0 w0' w1 w w'
    m0 m1 m2 m3
    a k0 k1);
  [ simpl_tape; steps |
    steps |
    steps |
    execute |
    steps |
    steps |
    steps |
    steps |
    steps |
    steps |
    steps |
    steps |
    steps |
    unfold to_config; steps |
    reflexivity ]
end.





