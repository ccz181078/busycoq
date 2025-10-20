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

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2:{
  follow init.
  follow Incs1s.
  R_mod_c.
  follow Ov_1.
  R_mod.
  follow Incs1s_1.
  R_mod_c.
  follow Ov_1.
  R_mod.
  follow Incs1s_1.
  R_mod_c.
  follow Ov_0.
  R_mod.
  follow Incs1s_1.
  R_mod_c.
  follow Ov_0.
  R_mod.
  follow Incs1s_1.
  R_mod_c.
  finish.
  }
  apply Ov_2.
  Unshelve.
  all: solve_ge.
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


