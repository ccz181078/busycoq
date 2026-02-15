From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require Import DivModCases.
Require Import String List PeanoNat NArith Lia.
Open Scope sym.

Ltac stepn' n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Lemma LBC_IncsOv tm h w n:
  segRLs tm h (h^^2) w w ->
  segRLs tm h (h^^(2^n)) (w^^n) (w^^n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    apply segRLs_nil.
  - cbn.
    rewrite Nat.add_0_r,lpow_add.
    eapply segRLs_concat.
    1: apply H.
    cbn.
    rewrite app_nil_r.
    eapply segRLs_trans; apply IHn.
Qed.

Lemma RBC_IncsOv tm h w n:
  segRLs tm (h^^2) h w w ->
  segRLs tm (h^^(2^n)) h (w^^n) (w^^n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    apply segRLs_nil.
  - cbn[lpow Nat.pow].
    eapply segRLs_concat.
    2: apply IHn.
    applys_eq (segRLs_addmul_v2 2 1 (2^n) 0 0).
    1,2: flia.
    1: constructor.
    1: applys_eq H; cbn; rewrite app_nil_r; trivial.
Qed.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0LF_1LD1RC_1RA1LE_1LB0LD_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (0%nat,[0;1;1]*>0inf)).
  1: esx.
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC0LF_1LD1RC_1RE1LA_1RB0RE_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,_)).
  1: stepn' (7833%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC1LE_1RD0RC_1LA0LF_1LD0LB_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hR' := (A,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,_)).
  1: stepn' (5028%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RB_1LD0LF_1LA1RD_1LC0LA_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hR' := (D,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,_)).
  1: stepn' (408%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RF_1LD0LE_1LA1RD_1LC0LA_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hR' := (D,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,_)).
  1: stepn' (408%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0LE_1LD1RC_1RA1LE_1LB0LD_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,_)).
  1: stepn' (4919%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC---_1LD1RC_1RE1LA_1RF0RE_1LC0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,_)).
  1: stepn' (7833%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RB_1LD0LE_1LA1RD_1LF0LA_1LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hR' := (D,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,_)).
  1: stepn' (408%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0LE_1LD1RC_1RA1LE_1LF0LD_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (O,_)).
  1: stepn' (96%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB1RA_1RC1LE_1RD0RC_1LA0LE_1LF0LB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hR' := (A,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (6,_)).
  1: stepn' (5028%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB0LD_1LC---_1LD1RC_1RE1LA_1RF0RE_0RA0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1;0;1].
Notation m1 := [1;1;1;1;0;0;0;1].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (3+b*2*2,rd0*>rd1^^(2+b*2)*>rd0*>rd1^^(2+b)*>[0;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  remember (rd1^^(1+b)*>[0;1;1]*>r) as r0.
  mid (S1 0inf 0 0 (2+b*2) false ([1;0;0;1]*>r0)).
  1: subst r0; ut; es.
  follow Incs1'.
  remember (1+b*2) as b'.
  replace (2+b*2) with (1+b') by lia.
  mid (S1 (0inf<*[1]) (b'+1+0) 0 (b'+1+0) true ([1;0;1]*>r0)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0]) (b'+0) 0 (b'+2) false (rd1*>r0)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (2+b'*2) true ([1;0]*>rd0*>rd1^^(1+b')*>rd0*>rd1*>r0)).
  1: ut; es.
  follow Incs1'.
  subst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (3,_)).
  1: stepn' (1067%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC1RB_1RD1LF_1RE0RD_0RF0LF_1LA0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,[]).
Notation hR' := (B,[]).
Notation hL := (C,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1;0;1].
Notation m1 := [1;1;1;1;0;0;0;1].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (3+b*2*2,rd0*>rd1^^(2+b*2)*>rd0*>rd1^^(2+b)*>[0;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  remember (rd1^^(1+b)*>[0;1;1]*>r) as r0.
  mid (S1 0inf 0 0 (2+b*2) false ([1;0;0;1]*>r0)).
  1: subst r0; ut; es.
  follow Incs1'.
  remember (1+b*2) as b'.
  replace (2+b*2) with (1+b') by lia.
  mid (S1 (0inf<*[1]) (b'+1+0) 0 (b'+1+0) true ([1;0;1]*>r0)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0]) (b'+0) 0 (b'+2) false (rd1*>r0)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (2+b'*2) true ([1;0]*>rd0*>rd1^^(1+b')*>rd0*>rd1*>r0)).
  1: ut; es.
  follow Incs1'.
  subst.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (1%nat,_)).
  1: stepn' (359%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RB_1RF1LD_1LE0LC_1LB---_1RA0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[]).
Notation hR' := (B,[]).
Notation hL := (C,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1].
Notation ld0 := [0;0;0;0].
Notation m0 := [1;1;1;1;0;1].
Notation m1 := [1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,r) :=
  S1 0inf 0 (1+n) 0 true ([1;0]*>r).

Lemma BigStep b r:
  S' (b,r) -->+
  S' (6+b*2*2,rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0]) (b+0) 0 (b+2) false ([1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (3+b*2) false ([1;0]*>rd1^^(1+b)*>[0;1;1]*>r)).
  1: ut; es.
  follow Incs1'.
  remember (3+b*2+0) as b'.
  mid (S1 (0inf<*[1]) (b'+0) 0 (b'+0) true (rd1^^(1+b)*>[1;0;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  subst b'.
  mid (S1 (0inf<*<[1;1;0;0]) (2+b*2+0) 0 (2+b*2+1) false (rd0^^(2+b)*>[1;1;1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*2*2) true ([1;0]*>rd1^^(3+b*2)*>rd0^^(2+b)*>[1;1;1]*>r)).
  ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (4,_)).
  1: stepn' (1296%N).
  eapply progress_nonhalt_simple.
  intros [b r].
  eexists _; apply BigStep.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LF_1LD1RC_1RE1LF_1RB0RE_1LA0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1;1].
Notation ld0 := [0;0;0;0;0].
Notation m0 := [1;1;1;1;1;0;1].
Notation m1 := [1;1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,m,tp,r) :=
  S1 0inf 0 (2+n) 0 tp ([1;0]*>rd1^^m*>[0]*>r).

Lemma BigStep0 b m r:
  S' (b*2,m,false,r) -->+
  S' (5+b*5,2+b*2,false,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+2+0) 0 (b*2+2+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*5) false ([1;0]*>rd1^^(2+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep1 b m r:
  S' (1+b*2,m,false,r) -->+
  S' (7+b*5,3+b*2,true,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+3+0) 0 (b*2+3+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) true ([1;0]*>rd1^^(3+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep2 b m r:
  S' (b*2,m,true,r) -->+
  S' (4+b*5,2+b*2,true,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (6+b*5) true ([1;0]*>rd1^^(2+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep3 b m r:
  S' (1+b*2,m,true,r) -->+
  S' (7+b*5,3+b*2,false,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) false ([1;0]*>rd1^^(3+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,1%nat,false,_)).
  1: stepn' (964%N).
  eapply progress_nonhalt_simple.
  intros [[[b m] tp] r].
  destruct tp;
  destruct (mod2 b); subst; eexists.
  - apply BigStep2.
  - apply BigStep3.
  - apply BigStep0.
  - apply BigStep1.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC0RB_1LD0LE_1LA1RD_1LF0LA_1LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hR' := (D,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1;1].
Notation ld0 := [0;0;0;0;0].
Notation m0 := [1;1;1;1;1;0;1].
Notation m1 := [1;1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,m,tp,r) :=
  S1 0inf 0 (2+n) 0 tp ([1;0]*>rd1^^m*>[0]*>r).

Lemma BigStep0 b m r:
  S' (b*2,m,false,r) -->+
  S' (5+b*5,2+b*2,false,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+2+0) 0 (b*2+2+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*5) false ([1;0]*>rd1^^(2+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep1 b m r:
  S' (1+b*2,m,false,r) -->+
  S' (7+b*5,3+b*2,true,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+3+0) 0 (b*2+3+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) true ([1;0]*>rd1^^(3+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep2 b m r:
  S' (b*2,m,true,r) -->+
  S' (4+b*5,2+b*2,true,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (6+b*5) true ([1;0]*>rd1^^(2+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep3 b m r:
  S' (1+b*2,m,true,r) -->+
  S' (7+b*5,3+b*2,false,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) false ([1;0]*>rd1^^(3+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,1%nat,false,_)).
  1: stepn' (682%N).
  eapply progress_nonhalt_simple.
  intros [[[b m] tp] r].
  destruct tp;
  destruct (mod2 b); subst; eexists.
  - apply BigStep2.
  - apply BigStep3.
  - apply BigStep0.
  - apply BigStep1.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0LE_1LD1RC_1RA1LE_1LF0LD_1LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hR' := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1;1].
Notation ld0 := [0;0;0;0;0].
Notation m0 := [1;1;1;1;1;0;1].
Notation m1 := [1;1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,m,tp,r) :=
  S1 0inf 0 (2+n) 0 tp ([1;0]*>rd1^^m*>[0]*>r).

Lemma BigStep0 b m r:
  S' (b*2,m,false,r) -->+
  S' (5+b*5,2+b*2,false,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+2+0) 0 (b*2+2+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*5) false ([1;0]*>rd1^^(2+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep1 b m r:
  S' (1+b*2,m,false,r) -->+
  S' (7+b*5,3+b*2,true,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+3+0) 0 (b*2+3+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) true ([1;0]*>rd1^^(3+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep2 b m r:
  S' (b*2,m,true,r) -->+
  S' (4+b*5,2+b*2,true,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (6+b*5) true ([1;0]*>rd1^^(2+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep3 b m r:
  S' (1+b*2,m,true,r) -->+
  S' (7+b*5,3+b*2,false,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) false ([1;0]*>rd1^^(3+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (5,2,false,_)).
  1: stepn' (4988%N).
  eapply progress_nonhalt_simple.
  intros [[[b m] tp] r].
  destruct tp;
  destruct (mod2 b); subst; eexists.
  - apply BigStep2.
  - apply BigStep3.
  - apply BigStep0.
  - apply BigStep1.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1LC---_1LD0LA_1LE1RD_1RF1LA_1RC0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[]).
Notation hR' := (D,[]).
Notation hL := (E,[]).
Notation hRL := [(hR,hL)].
Notation hRL' := [(hR',hL)].

Notation ld := [1;1;1;1;1].
Notation ld0 := [0;0;0;0;0].
Notation m0 := [1;1;1;1;1;0;1].
Notation m1 := [1;1;1;1;1;0;0].
Notation rd0 := [0;1].
Notation rd1 := [1;1].

Definition R1 a b c (tp:bool) r := ld^^a *> (if tp then m0 else m1) *> rd1^^b *> rd0^^c *> r.

Lemma R1_Inc a c tp r:
  sideRLs tm hRL (R1 a a (1+c) tp r) (R1 a (a+1) c tp r).
Proof.
  unfold R1.
  do 2 rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply LBC_IncsOv; esc.
  eapply segRLs_sideRLs_concat.
  1: eapply @segRLs_wall'' with (h2:=hRL'); destruct tp; esc.
  eapply segRLs_sideRLs_concat.
  1: apply RBC_IncsOv; esc.
  esc.
Qed.

Definition S1 l a b c tp r := l <* ld0^^a <* [1] {{{ (hR,R) }}} R1 b b c tp r.

Ltac R1_Inc :=
  epose proof (R1_Inc _ _ _ _) as I1;
  eapply sideRLs_1 in I1;
  follow100 I1; clear I1.

Lemma Inc1 l a b c tp r:
  S1 l (1+a) b (1+c) tp r -->*
  S1 l a (1+b) c tp r.
Proof.
  unfold S1.
  R1_Inc.
  ut; er.
Qed.

Lemma Incs1 n l a b c tp r:
  S1 l (n+a) b (n+c) tp r -->*
  S1 l a (n+b) c tp r.
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Lemma Incs1' b c tp r:
  S1 0inf 0 b c tp r -->*
  S1 0inf 0 (c+b) 0 tp r.
Proof.
  mid (S1 0inf (c+0) b (c+0) tp r).
  2: apply Incs1.
  ut.
  rewrite lpow_all0 by solve_const0_eq.
  finish.
Qed.

Definition S' '(n,m,tp,r) :=
  S1 0inf 0 (2+n) 0 tp ([1;0]*>rd1^^m*>[0]*>r).

Lemma BigStep0 b m r:
  S' (b*2,m,false,r) -->+
  S' (5+b*5,2+b*2,false,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+2+0) 0 (b*2+2+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (7+b*5) false ([1;0]*>rd1^^(2+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep1 b m r:
  S' (1+b*2,m,false,r) -->+
  S' (7+b*5,3+b*2,true,[1;0]^^m*>rd1*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1]) (b*2+3+0) 0 (b*2+3+0) true (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  mid (S1 (0inf<*<[1;1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd0^^m*>[1]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) true ([1;0]*>rd1^^(3+b*2)*>[0]*>[1;0]^^m*>rd1*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep2 b m r:
  S' (b*2,m,true,r) -->+
  S' (4+b*5,2+b*2,true,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+1+0) 0 (b*2+1+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (6+b*5) true ([1;0]*>rd1^^(2+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma BigStep3 b m r:
  S' (1+b*2,m,true,r) -->+
  S' (7+b*5,3+b*2,false,rd1^^(1+m)*>[0]*>r).
Proof.
  unfold S'.
  mid10 (S1 (0inf<*<[1;0;0;0]) (b*2+2+0) 0 (b*2+2+2) false (rd1^^m*>[1;0]*>r)).
  1: ut; es.
  follow Incs1.
  R1_Inc.
  mid (S1 0inf 0 0 (9+b*5) false ([1;0]*>rd1^^(3+b*2)*>[0]*>rd1^^(1+m)*>[0]*>r)).
  1: ut; es.
  follow Incs1'.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,1%nat,false,_)).
  1: stepn' (665%N).
  eapply progress_nonhalt_simple.
  intros [[[b m] tp] r].
  destruct tp;
  destruct (mod2 b); subst; eexists.
  - apply BigStep2.
  - apply BigStep3.
  - apply BigStep0.
  - apply BigStep1.
Qed.

End TM17.


