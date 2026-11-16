From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require ES_v2.
From BusyCoq Require Import NatMod.
From BusyCoq Require NatMod_v2.

Ltac es_v2 := ES_v2.es.
Ltac flia := repeat (lia || f_equal).


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC1RA_0LD1RF_1RE0RB_1LA0LC_0RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh0 := (0inf <* [1]^^5).
Notation lh1 := (0inf <* [1;0;1;1;0;1;0;1;0;1;0;1;0;1]).

Definition S1 lh a b c :=
  lh <* <[0;1;0;0]^^a <* <[0;1;0;1;1] <* [1;1]^^b <* <[0;1]^^c {{E}}> 0inf.

Lemma Inc1 lh a b c:
  S1 lh a (1+b) c -->*
  S1 lh a b (2+c).
Proof.
  es.
Qed.

Lemma Incs1 lh a b c:
  S1 lh a b c -->*
  S1 lh a 0 (b*2+c).
Proof.
  gen c.
  ind b Inc1.
Qed.

Definition S2 lh a b c :=
  lh <* <[0;1;0;0]^^a <* <[1;1] <* [1;1]^^b <* <[0;1]^^c {{E}}> 0inf.

Lemma Inc2 lh a b c:
  S2 lh a (1+b) c -->*
  S2 lh a b (2+c).
Proof.
  es.
Qed.

Lemma Incs2 lh a b c:
  S2 lh a b c -->*
  S2 lh a 0 (b*2+c).
Proof.
  gen c.
  ind b Inc2.
Qed.

Lemma Rst1 lh a c:
  S1 lh a 0 c -->*
  S2 lh a (3+c) 0.
Proof.
  es.
Qed.

Lemma Rst2 lh a c:
  S2 lh (4+a) 0 c -->*
  S1 lh a (12+c) 0.
Proof.
  es.
Qed.

Definition S3 lh b c :=
  lh <* [1;1]^^(1+b) <* <[0;1]^^c {{E}}> 0inf.

Lemma Inc3 lh b c:
  S3 lh (1+b) c -->*
  S3 lh b (2+c).
Proof.
  es.
Qed.

Lemma Incs3 lh b c:
  S3 lh b c -->*
  S3 lh 0 (b*2+c).
Proof.
  gen c.
  ind b Inc3.
Qed.

Lemma Rst3 c:
  S3 0inf 0 ((1+c)*2) -->*
  S1 lh0 c 3 0.
Proof.
  es.
Qed.

Lemma Ov3 c:
  S2 lh0 3 0 c -->*
  S3 0inf (17+c) 0.
Proof.
  es.
Qed.

Lemma Ov3' c:
  S2 lh0 3 0 c -->*
  S1 lh0 (16+c) 3 0.
Proof.
  follow Ov3.
  follow Incs3.
  replace ((17+c)*2+0) with ((1+(16+c))*2) by lia.
  follow Rst3.
  finish.
Qed.

Lemma Ov2 c:
  S2 lh0 2 0 ((1+c)*2) -->*
  S1 lh1 c 3 0.
Proof.
  es.
Qed.

Notation lh2 := (0inf <* <[1;0;1]).

Lemma Rst3_2 c:
  S3 lh2 0 c -->*
  S3 0inf (5+c) 0.
Proof.
  es.
Qed.

Lemma Ov2_1' c:
  S2 lh1 2 0 c -->*
  S1 lh0 (c*2+40) 3 0.
Proof.
  mid (S3 lh2 (18+c) 0).
  1: es.
  follow Incs3.
  follow Rst3_2.
  follow Incs3.
  mid (S3 0inf 0 ((1+(c*2+40))*2)).
  1: finish.
  follow Rst3.
  finish.
Qed.

Notation lh3 := (0inf <* <[1]).

Lemma Rst3_3 c:
  S3 lh3 0 c -->*
  S3 0inf (4+c) 0.
Proof.
  es.
Qed.

Lemma Ov0 c:
  S2 lh0 0 0 c -->*
  S1 lh0 (c+7) 3 0.
Proof.
  mid (S3 lh3 1 (2+c)).
  1: es.
  follow Incs3.
  follow Rst3_3.
  follow Incs3.
  mid (S3 0inf 0 ((1+(c+7))*2)).
  1: finish.
  follow Rst3.
  finish.
Qed.

Lemma Ov1 c:
  halts tm (S2 lh0 1 0 c).
Proof.
  unfold S2.
  esx.
Qed.

Lemma init:
  c0 -->*
  S1 lh0 7 3 0.
Proof.
  unfold S1.
  esx.
Qed.

Lemma Incs12 lh n a:
  S1 lh (a+n*4) 3 0 -->*
  S2 lh a 0 ((1+(4^n*18-10))*2).
Proof.
  follow Incs1.
  follow Rst1.
  follow Incs2.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (4+a)).
  follow Rst2.
  follow Incs1.
  follow Rst1.
  follow Incs2.
  cbn[Nat.pow].
  finish.
Qed.

Ltac R_mod :=
match goal with
| |- S1 _ ?b _ _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 4 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.
  R_mod.
  follow Incs12.
  follow Ov3'.
  simpl_small_nat 200.
  R_mod.
  follow Incs12.
  follow Ov2.
  simpl_small_nat 200.
  R_mod.
  follow Incs12.
  follow Ov2_1'.
  R_mod.
  follow Incs12.
  follow Ov0.
  R_mod.
  follow Incs12.
  finish.
  }
  apply Ov1.
  Unshelve.
  all: solve_ge.
Qed.

End TM1.


Lemma pow4sub1_mod3 a:
  (4^a-1) mod 3 = O.
Proof.
  destruct a.
  cbn; trivial.
  change 4 with (2^2).
  rewrite <-Nat.pow_mul_r.
  replace (2*(S a)) with (a*2+2) by lia.
  rw_mod_1.
  Unshelve.
  all: solve_ge.
Qed.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LA_1LD0RB_1RE1LC_---1RA_1RA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* <[0;1;1]^^a <* [0] <* <[0;1]^^b <* [0] <* <[0;1]^^c <* <[0;1;1;0;1;1;0] {{F}}> 0inf.

Lemma Inc1 a b c:
  S1 a (1+b) c -->*
  S1 a b (4+c).
Proof.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b c -->*
  S1 a 0 (b*4+c).
Proof.
  gen c.
  ind b Inc1.
Qed.

Lemma Rst1 a c:
  S1 (3+a) 0 c -->*
  S1 a (13+c) 3.
Proof.
  es.
Qed.

Lemma Ov_1 c:
  S1 1 0 (0+c*3) -->*
  S1 (c*2+9) 0 15.
Proof.
  mid (S1 (c*2+9) 3 3).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma init:
  c0 -->*
  S1 1 0 (0+81*3).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Incs1s n a:
  S1 (a+n*3) 0 15 -->*
  S1 a 0 ((4^n-1)/3*100+15).
Proof.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (3+a)).
  follow Rst1.
  follow Incs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Ov_0 c:
  S1 0 0 (0+c*3) -->*
  S1 (c*2+4) 0 47.
Proof.
  mid (S1 (c*2+4) 11 3).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Incs1s_1 n a:
  S1 (a+n*3) 0 47 -->*
  S1 a 0 ((4^n-1)/3*196+47).
Proof.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (3+a)).
  follow Rst1.
  follow Incs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Ov_1_2 c:
  halts tm (S1 1 0 (2+c*3)).
Proof.
  unfold S1.
  esx.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?b _ _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_mod_c :=
match goal with
| |- S1 _ _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.
  follow Ov_1.
  R_mod.
  follow Incs1s.
  R_mod_c.
  follow Ov_0.
  R_mod.
  follow Incs1s_1.
  R_mod_c.
  finish.
  }
  apply Ov_1_2.
  Unshelve.
  all: solve_ge.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0RE_1RC1LA_1LE0RD_1RC1RF_1RA0LC_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1] <* <[0;1;1]^^a <* [0] <* <[0;1]^^b <* [0] <* <[0;1]^^c <* <[0;1;1;0;1;1;0] {{D}}> 0inf.

Lemma Inc1 a b c:
  S1 a (1+b) c -->*
  S1 a b (4+c).
Proof.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b c -->*
  S1 a 0 (b*4+c).
Proof.
  gen c.
  ind b Inc1.
Qed.

Lemma Rst1 a c:
  S1 (3+a) 0 c -->*
  S1 a (13+c) 3.
Proof.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 (2+2*3) 0 47.
Proof.
  unfold S1.
  esx.
Qed.

Lemma Incs1s n a:
  S1 (a+n*3) 0 15 -->*
  S1 a 0 ((4^n-1)/3*100+15).
Proof.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (3+a)).
  follow Rst1.
  follow Incs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Incs1s_1 n a:
  S1 (a+n*3) 0 47 -->*
  S1 a 0 ((4^n-1)/3*196+47).
Proof.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (3+a)).
  follow Rst1.
  follow Incs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Ov_2 c:
  S1 2 0 (1+c*3) -->*
  S1 (c*2+13) 0 15.
Proof.
  mid (S1 (c*2+13) 3 3).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Ov_1 c:
  S1 1 0 (1+c*3) -->*
  S1 (c*2+10) 0 47.
Proof.
  mid (S1 (c*2+10) 11 3).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Ov_0 c:
  halts tm (S1 0 0 (1+c*3)).
Proof.
  unfold S1.
  esx.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?b _ _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_mod_c :=
match goal with
| |- S1 _ _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.
  follow Incs1s_1.
  R_mod_c.
  follow Ov_2.
  R_mod.
  simpl_small_nat 200.
  follow Incs1s.
  R_mod_c.
  follow Ov_1.
  R_mod.
  follow Incs1s_1.
  R_mod_c.
  finish.
  }
  apply Ov_0.
  Unshelve.
  all: solve_ge.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC1RF_1LD0RB_1RE0LC_1LA0RD_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1] <* <[0;1;1]^^a <* [0] <* <[0;1]^^b <* [0] <* <[0;1]^^c <* <[0;1;1;0;1;1;0] {{B}}> 0inf.

Lemma Inc1 a b c:
  S1 a (1+b) c -->*
  S1 a b (4+c).
Proof.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b c -->*
  S1 a 0 (b*4+c).
Proof.
  gen c.
  ind b Inc1.
Qed.

Lemma Rst1 a c:
  S1 (3+a) 0 c -->*
  S1 a (13+c) 3.
Proof.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 (1+5*3) 0 15.
Proof.
  unfold S1.
  esx.
Qed.

Lemma Incs1s n a:
  S1 (a+n*3) 0 15 -->*
  S1 a 0 ((4^n-1)/3*100+15).
Proof.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (3+a)).
  follow Rst1.
  follow Incs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Incs1s_1 n a:
  S1 (a+n*3) 0 47 -->*
  S1 a 0 ((4^n-1)/3*196+47).
Proof.
  gen a.
  induction n; intros.
  1: finish.
  follow (IHn (3+a)).
  follow Rst1.
  follow Incs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Ov_1 c:
  S1 1 0 (2+c*3) -->*
  S1 (c*2+11) 0 47.
Proof.
  mid (S1 (c*2+11) 11 3).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Ov_0 c:
  S1 0 0 (1+c*3) -->*
  S1 (c*2+5) 0 47.
Proof.
  mid (S1 (c*2+5) 11 3).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Ov_2 c:
  halts tm (S1 2 0 (1+c*3)).
Proof.
  unfold S1.
  esx.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?b _ _ -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_mod_c :=
match goal with
| |- S1 _ _ ?b -->* _ =>
  eassert (X:_) by (eapply (div_mod' b 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Import NatMod_v2.
Import NatModTactics.

Ltac follow' H :=
  eapply evstep_trans; [eapply Peq; [|apply H]; match_Nexpr |].

Ltac followh H :=
  eapply Peq; [|apply H]; match_Nexpr.

Lemma halt: halts tm c0.
Proof with rw_all.
  eapply halts_evstep.
  2:{
  follow init.
  follow Incs1s...
  follow' Ov_1...
  follow' Incs1s_1...
  follow' Ov_1...
  follow' Incs1s_1...
  follow' Ov_0...
  follow' Incs1s_1...
  follow' Ov_0...
  follow' Incs1s_1...
  finish.
  }
  followh Ov_2.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1LC1LA_0LE---_1LF0RB_0RC0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c :=
  0inf <* [1] <* [0]^^a <* [1] <* [0]^^b <* <[1;0] <* [0;0;0]^^c {{F}}> 0inf.

Lemma Inc1 a b c:
  S1 a (1+b) c -->*
  S1 a b (1+c).
Proof.
  es.
Qed.

Lemma Incs1 a b c:
  S1 a b c -->*
  S1 a 0 (b+c).
Proof.
  gen c.
  ind b Inc1.
Qed.

Lemma Rst1 a c:
  S1 (4+a) 0 c -->*
  S1 a (c*3+7) 0.
Proof.
  es.
Qed.

Lemma Ov0 c:
  halts tm (S1 0 0 c).
Proof.
  unfold S1.
  esx.
Qed.

Lemma Ov1 c:
  S1 1 0 c -->*
  S1 (c*3+5) 0 1.
Proof.
  es.
Qed.

Lemma Ov2 c:
  S1 2 0 c -->*
  S1 (c*3+5) 0 1.
Proof.
  es.
Qed.

Lemma Ov3 c:
  S1 3 0 c -->*
  S1 (c*3+11) 0 1.
Proof.
  es.
Qed.

Lemma pow3mod2 k:
  3^k mod 2 = 1%nat.
Proof.
  induction k.
  - reflexivity.
  - cbn[Nat.pow].
    rewrite Nat.Div0.mul_mod.
    rewrite IHk.
    reflexivity.
Qed.

Lemma IncsRst1s n a:
  S1 (a+n*4) 0 1 -->*
  S1 a 0 ((3^n*9-7)/2).
Proof.
  gen a.
  induction n; intros.
  - finish.
  - follow (IHn (4+a)).
    follow Rst1.
    follow Incs1.
    cbn[Nat.pow].
    pose proof (pow3mod2 n).
    finish.
Qed.

Definition S' (x:nat*nat) := let '(a,b):=x in S1 b 0 1.

Local Opaque Nat.div Nat.modulo.
Close Scope sym.
Import NatMod_v2.
Import PairIter.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep with (c':=S' (0,5)).
  2: unfold S',S1; esx.
  eapply halts_if_simple with
    (C:=S')
    (f:=fun '(a,b0) =>
    let b:=b0/4 in
    match b0 mod 4 with
    | 1 => Some (a,((3^b*9-7)/2)*3+5)
    | 2 => Some (a,((3^b*9-7)/2)*3+5)
    | 3 => Some (a,((3^b*9-7)/2)*3+11)
    | _ => None
    end).
  - intros [a b0].
    epose proof (div_mod' b0 4 (b0 mod 4) (eq_refl)) as I1.
    remember (b0/4) as b.
    unfold S'.
    destruct (b0 mod 4) as [|[|[|[|]]]]; subst b0.
    + eapply halts_evstep.
      2: apply IncsRst1s.
      apply Ov0.
    + follow IncsRst1s.
      apply Ov1.
    + follow IncsRst1s.
      apply Ov2.
    + follow IncsRst1s.
      apply Ov3.
    + lia.
  - eapply pair_iter_halts_if with (g:=fun ls =>
    let a := Nvar 0 in
    let b0 := Nvar 1 in
    let b:=(b0/4)%Nexpr in
    match Nmod'' (2^30) b0 ls 4 with
    | None => Some ls
    | Some b1 =>
      (match b1 with
      | 1 => cons2 (a,((3^b*9-7)/2)*3+5) ls
      | 2 => cons2 (a,((3^b*9-7)/2)*3+5) ls
      | 3 => cons2 (a,((3^b*9-7)/2)*3+11) ls
      | _ => None
      end)%Nexpr
    end).
    2:{
      apply iter_halts_c_spec with (T:=16).
      vm_compute; reflexivity.
    }
    solve_v1.
    destruct (z mod 4) as [|[|[|[|]]]].
    5: lia.
    all: solve_v2.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB---_0LC0LD_1LD1LC_1RE1LB_1RF1RD_0LD0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{C}} [0;1]^^a *> [1]^^b *> [0;1;0;0] *> [1;0]^^c *> r.

Lemma Inc1 a b c r:
  S1 a (1+b) c r -->*
  S1 (2+a) b c r.
Proof.
  es.
Qed.

Lemma Incs1 a b c r:
  S1 a b c r -->*
  S1 (b*2+a) 0 c r.
Proof.
  gen a.
  ind b Inc1.
Qed.

Lemma OvIncs1 a c r:
  S1 a 0 (2+c) r -->*
  S1 (a*4+12) 0 c r.
Proof.
  mid (S1 0 (6+a*2) c r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Rst_0 a:
  S1 a 0 0 0inf -->*
  S1 4 0 (1+a) 0inf.
Proof.
  es.
Qed.

Notation rh1 := ([1;1;1]*>0inf).

Lemma Rst_1 a:
  S1 a 0 1 0inf -->*
  S1 4 0 a rh1.
Proof.
  es.
Qed.

Lemma Incss1 n c r:
  S1 4 0 (n*2+c) r -->*
  S1 (4^n*8-4) 0 c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (2+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  finish.
Qed.

Lemma init:
  c0 -->* S1 4 0 (1*2+0) 0inf.
Proof.
  unfold S1.
  esx.
Qed.

Lemma Rst1_0 a:
  halts tm (S1 a 0 0 rh1).
Proof.
  esx.
Qed.

Import NatMod_v2.
Import NatModTactics.

Ltac R_mod :=
match goal with
| |- S1 _ _ ?x _ -->* _ => R_mod'' x 2
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.

  follow Incss1.
  follow Rst_0.
  simpl_small_nat 100.
  R_mod.

  follow Incss1.
  follow Rst_1.
  simpl_small_nat 100.
  R_mod.

  follow Incss1.
  finish.
  }
  apply Rst1_0.
  Unshelve.
  all: solve_ge.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1RC1LE_0RD1RB_1RA0LA_0LA0LB_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{E}} [1;0]^^a *> [0] *> [1;0]^^b *> [1;1;1] *> [0;0;1]^^c *> r.

Notation rh1 := ([0;1;1]*>0inf).

Lemma Inc1 a b c r:
  S1 a (1+b) c r -->*
  S1 (4+a) b c r.
Proof.
  es.
Qed.

Lemma Incs1 a b c r:
  S1 a b c r -->*
  S1 (b*4+a) 0 c r.
Proof.
  gen a.
  ind b Inc1.
Qed.

Lemma OvIncs1 a c r:
  S1 a 0 (2+c) r -->*
  S1 (a*4+47) 0 c r.
Proof.
  mid (S1 3 (11+a) c r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Incss1 n c r:
  S1 19 0 (n*2+c) r -->*
  S1 ((4^n*104-47)/3) 0 c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (2+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Rst_2_1 a:
  S1 (2+a*3) 0 1 rh1 -->*
  S1 19 0 (a*2+11) rh1.
Proof.
  mid (S1 3 4 (11+a*2) rh1).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Rst_0_1 a:
  S1 (0+a*3) 0 1 rh1 -->*
  S1 39 0 (a*2+9) rh1.
Proof.
  mid (S1 3 9 (9+a*2) rh1).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Incss1' n c r:
  S1 39 0 (n*2+c) r -->*
  S1 ((4^n*164-47)/3) 0 c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (2+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Rst_1_1 a:
  halts tm (S1 (1+a*3) 0 1 rh1).
Proof.
  unfold S1.
  esx.
Qed.

Lemma init:
  c0 -->* S1 19 0 (2*2+1) rh1.
Proof.
  unfold S1.
  esx.
Qed.

Import NatMod_v2.
Import NatModTactics.

Ltac R_mod :=
match goal with
| |- S1 ?x _ _ _ -->* _ => R_mod' x 3
end.

Ltac R_mod_c :=
match goal with
| |- S1 _ _ ?x _ -->* _ => R_mod'' x 2
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.

  follow Incss1.
  R_mod.
  follow Rst_2_1.
  simpl_small_nat 100.
  R_mod_c.

  follow Incss1.
  R_mod.
  follow Rst_0_1.
  R_mod_c.

  follow Incss1'.
  R_mod.
  finish.
  }
  apply Rst_1_1.
  Unshelve.
  all: solve_ge.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1LF_0LD0LC_0LE0LB_1RE0RA_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{C}} [0]^^a *> [1]^^(1+b) *> [0;1;1]^^c *> r.

Notation rh1 := ([0;0;0;1;0;1]*>0inf).

Lemma Inc1 a b c r:
  S1 a (1+b) c r -->*
  S1 (4+a) b c r.
Proof.
  es.
Qed.

Lemma Incs1 a b c r:
  S1 a b c r -->*
  S1 (b*4+a) 0 c r.
Proof.
  gen a.
  ind b Inc1.
Qed.

Lemma OvIncs1 a c r:
  S1 a 0 (1+c) r -->*
  S1 (a*4+19) 0 c r.
Proof.
  mid (S1 3 (4+a) c r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Incss1_0 n c r:
  S1 19 0 (n+c) r -->*
  S1 ((4^n*76-19)/3) 0 c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (1+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Incss1 c r:
  S1 19 0 c r -->*
  S1 ((4^c*76-19)/3) 0 0 r.
Proof.
  follow (Incss1_0 c 0 r).
  finish.
Qed.

Notation rh2 := ([0;0;0;1;0;1;0;1]*>0inf).

Lemma Rst1_1 a:
  S1 (1+a*3) 0 0 rh1 -->*
  S1 19 0 a rh2.
Proof.
  mid (S1 3 4 a rh2).
  1: es.
  follow Incs1.
  finish.
Qed.

Notation rh3 := ([0;0;0;1;0;1;0;1;0;1]*>0inf).

Lemma Rst2_0 a:
  S1 (0+a*3) 0 0 rh2 -->*
  S1 3 0 a rh3.
Proof.
  es.
Qed.

Lemma Incss2_0 n c r:
  S1 3 0 (n+c) r -->*
  S1 ((4^n*28-19)/3) 0 c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (1+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  pose proof (pow4sub1_mod3 n).
  finish.
Qed.

Lemma Incss2 c r:
  S1 3 0 c r -->*
  S1 ((4^c*28-19)/3) 0 0 r.
Proof.
  follow (Incss2_0 c 0 r).
  finish.
Qed.

Notation rh4 := ([0;0;0;1;0;1;0;1;0;1;0;1]*>0inf).

Lemma Rst3_0 a:
  S1 (0+a*3) 0 0 rh3 -->*
  S1 3 0 a rh4.
Proof.
  es.
Qed.

Notation rh5 := ([0;0;0;1;0;1;0;1;0;1;0;1;0;1]*>0inf).

Lemma Rst4_1 a:
  S1 (1+a*3) 0 0 rh4 -->*
  S1 19 0 a rh5.
Proof.
  mid (S1 3 4 a rh5).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Rst5_2 a:
  halts tm (S1 (2+a*3) 0 0 rh5).
Proof.
  unfold S1.
  esx.
Qed.

Lemma init:
  c0 -->* S1 19 0 6 rh1.
Proof.
  unfold S1.
  esx.
Qed.

Import NatMod_v2.
Import NatModTactics.

Ltac R_mod :=
match goal with
| |- S1 ?x _ _ _ -->* _ => R_mod' x 3
end.

Ltac R_mod_c :=
match goal with
| |- S1 _ _ ?x _ -->* _ => R_mod'' x 2
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.

  follow Incss1.
  R_mod.
  follow Rst1_1.

  follow Incss1.
  R_mod.
  follow Rst2_0.

  follow Incss2.
  R_mod.
  follow Rst3_0.

  follow Incss2.
  R_mod.
  follow Rst4_1.

  follow Incss1.
  R_mod.
  finish.
  }
  apply Rst5_2.
  Unshelve.
  all: solve_ge.
Qed.

End TM8.


Lemma pow3_mod2 a:
  (3^a) mod 2 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RF_1LD1LC_1LE0RE_0RB0LC_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{C}} [1]^^a *> [0;1;1;0;0] *> [1]^^b *> [0;1;1;1] *> [0]^^c *> r.

Notation rh1 := ([1;1;1;0;0;1;1;1]*>0inf).

Lemma Inc1 a b c r:
  S1 (1+a) b c r -->*
  S1 a (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 a b c r:
  S1 a b c r -->*
  S1 0 (a*3+b) c r.
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma OvIncs1 b c r:
  S1 0 b (2+c) r -->*
  S1 0 (b*3+15) c r.
Proof.
  mid (S1 (5+b) 0 c r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Incss1 n c r:
  S1 0 6 (n*2+c) r -->*
  S1 0 ((3^n*27-15)/2) c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (2+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  pose proof (pow3_mod2 n).
  finish.
Qed.

Notation rh2 := (1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0inf).

Lemma Rst1_1 b:
  S1 0 b 1 rh1 -->*
  S1 0 6 b rh2.
Proof.
  es.
Qed.

Notation rh3 := (1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0inf).

Lemma Rst2_0 b:
  S1 0 b 0 rh2 -->*
  S1 0 6 b rh3.
Proof.
  es.
Qed.

Notation rh4 := (1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0inf).

Lemma Rst3_1 b:
  S1 0 b 1 rh3 -->*
  S1 0 (b*3+15) 1 rh4.
Proof.
  mid (S1 (5+b) 0 1 rh4).
  1: es.
  follow Incs1.
  finish.
Qed.

Notation rh5 := (1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0inf).

Lemma Rst4_1 b:
  S1 0 b 1 rh4 -->*
  S1 0 6 b rh5.
Proof.
  es.
Qed.

Notation rh6 := (0 >> 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0inf).

Definition S2 a b :=
  0inf <{{C}} [1]^^a *> [0;1;1;0;0] *> [1]^^b *> rh6.

Lemma Inc2 a b:
  S2 (1+a) b -->*
  S2 a (3+b).
Proof.
  es.
Qed.

Lemma Incs2 a b:
  S2 a b -->*
  S2 0 (a*3+b).
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst5_1 b:
  halts tm (S1 0 b 1 rh5).
Proof.
  eapply halts_evstep.
  2:{
  mid (S2 (5+b) 0).
  1: es.
  follow Incs2.
  finish.
  }
  esx.
Qed.

Lemma init:
  c0 -->* S1 0 6 (16*2+1) rh1.
Proof.
  unfold S1.
  esx.
Qed.

Import NatMod_v2.
Import NatModTactics.

Ltac R_mod_c :=
match goal with
| |- S1 _ _ ?x _ -->* _ => R_mod'' x 2
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.

  follow Incss1.
  follow Rst1_1.
  R_mod_c.

  follow Incss1.
  follow Rst2_0.
  R_mod_c.

  follow Incss1.
  follow Rst3_1.
  follow Rst4_1.
  R_mod_c.

  follow Incss1.
  finish.
  }
  apply Rst5_1.
  Unshelve.
  all: solve_ge.
Qed.

End TM9.


Lemma pow9_mod4 a:
  (9^a) mod 4 = 1%nat.
Proof.
  induction a; cbn[Nat.pow]; lia.
Qed.

Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0LC1LD_1RC0RA_1RE0LB_0LD0LF_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{E}} [0;0]^^a *> [1;1] *> [0;1]^^b *> [1;1;1;1] *> [0;1]^^c *> r.

Definition S2 a b c r :=
  0inf <{{E}} [0;0]^^a *> [1;1] *> [0;1]^^b *> [1;1] *> [0;1]^^c *> r.

Notation rh1 := ([1;1;0;1;0;1;1]*>0inf).

Lemma Inc1 a b c r:
  S1 a (1+b) c r -->*
  S1 (3+a) b c r.
Proof.
  es.
Qed.

Lemma Incs1 a b c r:
  S1 a b c r -->*
  S1 (b*3+a) 0 c r.
Proof.
  gen a.
  ind b Inc1.
Qed.

Lemma Inc2 a b c r:
  S2 a (1+b) c r -->*
  S2 (3+a) b c r.
Proof.
  es.
Qed.

Lemma Incs2 a b c r:
  S2 a b c r -->*
  S2 (b*3+a) 0 c r.
Proof.
  gen a.
  ind b Inc2.
Qed.

Lemma Ov1Incs2 a c r:
  S1 a 0 (2+c) r -->*
  S2 (a*3+20) 0 c r.
Proof.
  mid (S2 2 (6+a) c r).
  1: es.
  follow Incs2.
  finish.
Qed.

Lemma Ov2Incs1 a c r:
  S2 a 0 (2+c) r -->*
  S1 (a*3+14) 0 c r.
Proof.
  mid (S1 2 (4+a) c r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma OvIncs21 a c r:
  S2 a 0 (4+c) r -->*
  S2 (a*9+62) 0 c r.
Proof.
  follow Ov2Incs1.
  follow Ov1Incs2.
  finish.
Qed.

Lemma Incss2 n c r:
  S2 14 0 (n*4+c) r -->*
  S2 ((9^n*87-31)/4) 0 c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (4+c)).
  follow OvIncs21.
  cbn[Nat.pow].
  pose proof (pow9_mod4 n).
  finish.
Qed.

Notation rh2 := (1>>0inf).

Lemma Rst1_0 a:
  S2 a 0 0 rh1 -->*
  S2 (a*3+20) 0 0 rh2.
Proof.
  mid (S2 2 (6+a) 0 (1>>0inf)).
  1: es.
  follow Incs2.
  finish.
Qed.

Notation rh3 := (1>>1>>0>>1>>1>>0inf).

Lemma Rst2_0 a:
  a>=2 ->
  S2 a 0 0 rh2 -->*
  S2 14 0 (a-2) rh3.
Proof.
  remember (a-2) as a'.
  intros.
  replace a with (2+a') by lia.
  mid (S2 2 4 a' rh3).
  1: es.
  follow Incs2.
  finish.
Qed.

Lemma Rst3_0 a:
  S1 a 0 0 rh3 -->*
  S1 (a*3+17) 0 0 rh2.
Proof.
  mid (S1 2 (5+a) 0 rh2).
  1: es.
  follow Incs1.
  finish.
Qed.

Notation rh5 := (1>>1>>0>>1>>0>>1>>1>>0inf).

Lemma Rst4_0 a:
  a>=2 ->
  S1 a 0 0 rh2 -->*
  S2 14 0 (a-2) rh5.
Proof.
  remember (a-2) as a'.
  intros.
  replace a with (2+a') by lia.
  mid (S2 2 4 a' rh5).
  1: es.
  follow Incs2.
  finish.
Qed.

Lemma Rst5_1 a:
  S1 a 0 1 rh5 -->*
  S2 (a*3+23) 0 1 rh2.
Proof.
  mid (S2 2 (7+a) 1 rh2).
  1: es.
  follow Incs2.
  finish.
Qed.

Lemma Rst6_0 a:
  halts tm (S2 a 0 1 rh2).
Proof.
  esx.
Qed.

Lemma init:
  c0 -->* S2 14 0 (3*4+0) rh1.
Proof.
  unfold S2.
  esx.
Qed.

Import NatMod_v2.
Import NatModTactics.

Ltac R_mod_c :=
match goal with
| |- S2 _ _ ?x _ -->* _ => R_mod'' x 4
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.

  follow Incss2.
  follow Rst1_0.
  follow Rst2_0.
  1: solve_ge.
  R_mod_c.

  follow Incss2.
  follow Ov2Incs1.
  follow Rst3_0.
  eapply evstep_trans; [apply Rst4_0|].
  1: solve_ge.
  R_mod_c.

  follow Incss2.
  follow Ov2Incs1.
  follow Rst5_1.

  finish.
  }
  apply Rst6_0.
  Unshelve.
  all: solve_ge.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1LB_0RE0LD_0LC0LB_0RA1RE_0RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{B}} [1]^^a *> [0;0;1] *> [1]^^b *> [0;0;1;1;1;1]^^c *> r.

Notation rh1 := ([0;0;0;0;1;1;0;1;0;1]*>0inf).

Lemma Inc1 a b c r:
  S1 (1+a) b c r -->*
  S1 a (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 a b c r:
  S1 a b c r -->*
  S1 0 (a*2+b) c r.
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma OvIncs1 b c r:
  S1 0 b (1+c) r -->*
  S1 0 (b*2+11) c r.
Proof.
  mid (S1 (4+b) 3 c r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Incss1_0 n c r:
  S1 0 5 (n+c) r -->*
  S1 0 (2^n*16-11) c r.
Proof.
  gen c.
  induction n; intros.
  1: finish.
  follow (IHn (1+c)).
  follow OvIncs1.
  cbn[Nat.pow].
  finish.
Qed.

Lemma Incss1 c r:
  S1 0 5 c r -->*
  S1 0 (2^c*16-11) 0 r.
Proof.
  follow (Incss1_0 c 0 r).
  finish.
Qed.

Definition S2 a b r :=
  0inf <{{B}} [1]^^a *> [0;0;0] *> [0;1]^^b *> r.

Lemma Inc2 a b r:
  S2 (1+a) b r -->*
  S2 a (1+b) r.
Proof.
  es.
Qed.

Lemma Incs2 a b r:
  S2 a b r -->*
  S2 0 (a+b) r.
Proof.
  gen b.
  ind a Inc2.
Qed.

Lemma Rst_000 b r:
  S1 0 b 0 (0>>0>>0>>r) -->*
  S2 0 (4+b) r.
Proof.
  mid (S2 (4+b) 0 r).
  1: es.
  follow Incs2.
  finish.
Qed.

Notation rh2 := (1 >> 0 >> 0 >> 1 >> 1 >> 0 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0inf).

Lemma Rst_001 b r:
  S1 0 b 0 (0>>0>>1>>r) -->*
  S1 0 (b*2+8) 0 r.
Proof.
  mid (S1 (4+b) 0 0 r).
  1: es.
  follow Incs1.
  finish.
Qed.

Lemma Rst_1 b r:
  S1 0 b 0 (1>>r) -->*
  S1 0 (b+1) 0 r.
Proof.
  es.
Qed.


Lemma Rst1_0 b:
  S1 0 (0+b*3) 0 rh1 -->*
  S1 0 5 (b+1) rh2.
Proof.
  cbn[Str_app].
  follow Rst_000.
  es.
Qed.


Notation rh3 := (0 >> 0 >> 0 >> 0 >> 0 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0inf).

Lemma Rst2 b:
  S1 0 b 0 rh2 -->*
  S1 0 (b*2+11) 0 rh3.
Proof.
  follow Rst_1.
  follow Rst_001.
  follow Rst_1.
  finish.
Qed.

Notation rh4 := ([0;0;1;1;0;0;1;1;1;1]*>rh3).

Lemma Rst3_0 b:
  S1 0 (0+b*3) 0 rh3 -->*
  S1 0 5 b rh4.
Proof.
  follow Rst_000.
  es.
Qed.

Notation rh5 := ([0;0;0;0;1;1;1;1;1;1]*>rh3).

Lemma Rst3_2 b:
  S1 0 (2+b*3) 0 rh3 -->*
  S1 0 5 (b+1) rh5.
Proof.
  follow Rst_000.
  es.
Qed.

Lemma Rst5_2 b:
  halts tm (S1 0 (2+b*3) 0 rh5).
Proof.
  cbn[Str_app].
  eapply halts_evstep.
  2: apply Rst_000.
  unfold S2.
  esx.
Qed.

Lemma init:
  c0 -->* S1 0 5 39 rh1.
Proof.
  unfold S1.
  esx.
Qed.

Import NatMod_v2.
Import NatModTactics.

Ltac R_mod :=
match goal with
| |- S1 _ ?x _ _ -->* _ => R_mod' x 3
end.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.

  follow Incss1.
  R_mod.
  follow Rst1_0.

  follow Incss1.
  follow Rst2.
  R_mod.
  follow Rst3_0.

  follow Incss1.
  cbn[Str_app].
  follow Rst_001.
  follow Rst_1.
  follow Rst_001.
  do 3 follow Rst_1.
  R_mod.
  follow Rst3_2.

  follow Incss1.
  R_mod.
  finish.
  }
  apply Rst5_2.
  Unshelve.
  all: solve_ge.
Qed.

End TM11.


