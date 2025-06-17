From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.


Module UC1.
Section UnaryCounter1.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis w0 w1 w1':list Sym.
Hypothesis Inc:
  segRL tm hR hL w0 w1.
Hypothesis Ov:
  segRR tm hR hR w1 w1'.
Hypothesis Rst:
  segLL tm hL hL w1' w1.

Lemma Incs n m:
  segRLs tm ([(hR,hL)]^^(n+m)) ([(hR,hL)]^^m) (w0^^n) (w1^^n).
Proof.
  induction n.
  1: apply segRLs_nil.
  cbn.
  eapply segRLs_S.
  - intros l r.
    rewrite Str_app_assoc.
    follow10 Inc.
    rewrite <-Str_app_assoc.
    finish.
  - eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall; eauto.
Qed.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n)) [] (w0^^n) (w1^^n).
Proof.
  applys_eq (Incs n O).
  f_equal; lia.
Qed.

End UnaryCounter1.
End UC1.

Module BCR.
Section BinaryCounter.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis d0 d1 d1':list Sym.
Hypothesis LR:
  segLR tm hL hR d0 d1.
Hypothesis Carry:
  segLL tm hL hL d1 d1'.
Hypothesis Ret:
  segRR tm hR hR d1' d0.

Lemma Incs n:
  segRLs tm ([(hR,hL)]^^n) ([(hR,hL)]^^(n*2)) d1' d1'.
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  cbn[app].
  replace (S n * 2) with (2+n*2) by lia.
  rewrite lpow_add.
  change ([(hR,hL)]^^2) with (lrcons hR [(hL,hR)] hL).
  eapply segRLs_lrcons; eauto.
  econstructor; eauto.
  econstructor.
Qed.
End BinaryCounter.
End BCR.

Module BC.
Section BinaryCounter.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis d0 d1 d1':list Sym.
Hypothesis RL:
  segRL tm hR hL d0 d1.
Hypothesis Carry:
  segRR tm hR hR d1 d1'.
Hypothesis Ret:
  segLL tm hL hL d1' d0.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n*2+1)) ([(hR,hL)]^^n) d0 d1.
Proof.
  induction n.
  1: {
    eapply segRLs_S; eauto.
    econstructor.
  }
  replace (S n * 2 + 1) with (2+(n*2+1)) by lia.
  cbn[lpow].
  rewrite lpow_add.
  eapply segRLs_trans.
  2: apply IHn.
  eapply segRLs_S; eauto.
  cbn.
  eapply segRLs_S'; eauto.
  econstructor.
Qed.

Lemma IncsOvs n m:
  segRLs tm ([(hR,hL)]^^((n+1)*2^m-1)) ([(hR,hL)]^^n) (d0^^m) (d1^^m).
Proof.
  gen n.
  induction m; intros.
  - cbn.
    replace ((n+1)*1-1) with n by lia.
    eapply segRLs_nil.
  - cbn[lpow].
    cbn[Nat.pow].
    eapply segRLs_concat.
    2: apply IHm.
    epose proof (Nat.pow_nonzero 2 m).
    replace ((n+1)*(2*2^m)-1) with (((n+1)*2^m-1)*2+1) by lia.
    eapply Incs'.
Qed.

Lemma Mul2 n:
  segRLs tm ([(hR,hL)]^^(n*2)) ([(hR,hL)]^^n) d1 d1.
Proof.
  induction n.
  1: constructor.
  cbn.
  eapply segRLs_S'; eauto.
  eapply segRLs_S; eauto.
Qed.

Lemma Ovs n m:
  segRLs tm ([(hR,hL)]^^(n*2^m)) ([(hR,hL)]^^n) (d1^^m) (d1^^m).
Proof.
  gen n.
  induction m; intros.
  - cbn.
    replace (n*1) with n by lia.
    eapply segRLs_nil.
  - cbn[lpow].
    cbn[Nat.pow].
    eapply segRLs_concat.
    2: apply IHm.
    epose proof (Nat.pow_nonzero 2 m).
    replace (n*(2*2^m)) with ((n*2^m)*2) by lia.
    eapply Mul2.
Qed.

Lemma Incs n:
  segRLs tm ([(hR,hL)]^^((2^n)-1)) [] (d0^^n) (d1^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  cbn[Nat.pow].
  epose proof (Nat.pow_nonzero 2 n).
  replace (2*2^n-1) with ((2^n-1)*2+1) by lia.
  eapply segRLs_concat.
  1: apply Incs'.
  apply IHn.
Qed.

Lemma IncsMul2 n:
  segRLs tm ([(hR,hL)]^^((2^n*2)-2)) [] (d1 ++ d0^^n) (d1 ++ d1^^n).
Proof.
  replace (2^n*2-2) with ((2^n-1)*2) by lia.
  eapply segRLs_concat.
  1: apply Mul2.
  apply Incs.
Qed.
End BinaryCounter.
End BC.

Ltac solve_LOverflow :=
  intros;
  simpl_tape; cbn; step1s;
  use_shift_rule; cbn;
  step1s;
  use_shift_rule; cbn;
  simpl_rotate;
  step1s.

Lemma Str_app_assoc_1{A} a (b:A) c:
  a *> [b] *> c =
  (a ++ [b]) *> c.
Proof.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lrcons_lpow1 h1 h2 n:
  n<>O ->
  lrcons h1 ([(h2,h1)]^^(n-1)) h2 = ([(h1,h2)]^^n).
Proof.
  intros H.
  destruct n.
  1: lia.
  replace (S n - 1) with n by lia.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn. 2: lia.
  reflexivity.
Qed.


Module UC2.
Section UnaryCounter2.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis w0 w1 w2 w2':list Sym.
Hypothesis Inc0:
  segRL tm hR hL w0 w1.
Hypothesis Inc1:
  segRL tm hR hL w1 w2.
Hypothesis Ov:
  segRR tm hR hR w2 w2'.
Hypothesis Rst:
  segLL tm hL hL w2' w2.

Lemma Incs n m:
  segRLs tm ([(hR,hL)]^^(n*2+m)) ([(hR,hL)]^^m) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: apply segRLs_nil.
  cbn.
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc0.
    rewrite <-Str_app_assoc.
    finish.
  }
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc1.
    rewrite <-Str_app_assoc.
    finish.
  }
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall; eauto.
Qed.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n*2)) [] (w0^^n) (w2^^n).
Proof.
  applys_eq (Incs n O).
  f_equal; lia.
Qed.

End UnaryCounter2.
End UC2.


Module UC3.
Section UnaryCounter3.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis w0 w1 w2 w3 w3':list Sym.
Hypothesis Inc0:
  segRL tm hR hL w0 w1.
Hypothesis Inc1:
  segRL tm hR hL w1 w2.
Hypothesis Inc2:
  segRL tm hR hL w2 w3.
Hypothesis Ov:
  segRR tm hR hR w3 w3'.
Hypothesis Rst:
  segLL tm hL hL w3' w3.

Lemma Incs n m:
  segRLs tm ([(hR,hL)]^^(n*3+m)) ([(hR,hL)]^^m) (w0^^n) (w3^^n).
Proof.
  induction n.
  1: apply segRLs_nil.
  cbn.
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc0.
    rewrite <-Str_app_assoc.
    finish.
  }
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc1.
    rewrite <-Str_app_assoc.
    finish.
  }
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc2.
    rewrite <-Str_app_assoc.
    finish.
  }
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall; eauto.
Qed.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n*3)) [] (w0^^n) (w3^^n).
Proof.
  applys_eq (Incs n O).
  f_equal; lia.
Qed.

End UnaryCounter3.
End UC3.

