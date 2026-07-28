From BusyCoq Require Import Individual62 Longitudinal DivModCases ES_v3.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0LE_1RD1RF_1LE0LD_0RC1RA_0RE---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h1 := [((C,<[0;0]),(E,[1;0;1]))].
Notation h2 := [((F,<[0;1]),(E,[1;0;1]))].
Notation d0 := [0;0;0;1;0;1].
Notation d1 := [0;1;0;1;0;1].

Definition P1 n := segRLs tm (h1^^(2^n)) (h1^^(2^n-1)++h2) (d0^^(2^n)) (d0^^(2^n)).
Definition P2 n := segRLs tm (h1^^(2^n-1)++h2) (h1^^(2^n)) (d0^^(2^n)) (d1^^(2^n)).

Lemma h1s_d1s k n:
  segRLs tm (h1^^k) (h1^^k) (d1^^n) (d1^^n).
Proof.
  eapply segRLs_wall''.
  esx.
Qed.

Lemma h1sh2_d1s k n:
  segRLs tm (h1^^k++h2) (h1^^k++h2) (d1^^n) (d0^^n).
Proof.
  eapply segRLs_trans.
  1: apply h1s_d1s.
  esx.
Qed.

Lemma P12_n n:
  P1 n /\ P2 n.
Proof.
  unfold P1,P2.
  induction n.
  - split; esx.
  - destruct IHn as [I1 I2].
    cbn[Nat.pow].
    split.
    all:
    replace (2*2^n-1) with (2^n+(2^n-1)) by lia;
    replace (2*2^n) with (2^n+2^n) by lia;
    repeat rewrite lpow_add;
    rewrite <-app_assoc.
    + eapply segRLs_trans.
      * eapply segRLs_concat; [apply I1|apply I2].
      * eapply segRLs_concat; [apply I1|apply h1sh2_d1s].
    + eapply segRLs_trans.
      * eapply segRLs_concat; [apply I1|apply I2].
      * eapply segRLs_concat; [apply I2|apply h1s_d1s].
Qed.

Notation hR := (A,<[1]).
Notation hL := (D,@nil Sym).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation ld := [0;0;1;0;1].
Notation lh := (0inf<*<[1;0]).
Notation hL' := (D,ld).
Notation hRL' := [(hR,hL')].
Notation hRL3 := (hRL^^2++hRL').
Notation hLR3 := (hLR^^2++[(hL',hR)]).

Definition P3 n := segRLs tm (hRL3^^(2^n)) (h1^^(2^n*2-1)++h2) (d0^^(2^n*2-1)) (d0^^(2^n*2-1)).

Lemma P3_n n:
  P3 n.
Proof.
  unfold P3.
  induction n.
  - esx.
  - replace (d0^^(2^S n*2-1)) with (d0^^((2^n*2-1)+(2^(S n)))) by (cbn; flia).
    replace (hRL3^^(2^S n)) with (hRL3^^(2^n+2^n)) by (cbn; flia).
    replace (2^S n*2-1) with (2^n*2+(2^n*2-1)) by (cbn; lia).
    repeat rewrite lpow_add.
    rewrite <-app_assoc.
    epose proof (P12_n (S n)) as [I1 I2].
    unfold P1,P2 in *.
    eapply segRLs_trans.
    + eapply segRLs_concat; [apply IHn|].
      applys_eq I2; cbn; flia.
    + eapply segRLs_concat; [apply IHn|].
      apply h1sh2_d1s.
Qed.

Definition LC n := lh <* <[1;1;0;1;0]^^n.
Definition tm' := flip tm.

Lemma LIncs k n:
  sideRLs tm' (hLR3^^k) (LC n) (LC (k+n)).
Proof.
  unfold LC.
  induction k.
  1: esx.
  replace (S k) with (k+1) by lia.
  eapply sideRLs_trans_add.
  1: eapply IHk.
  es' k n.
Qed.

Definition S' '(m,n,r) := LC m {{{ (hR,R) }}} d0^^n *> r.




Definition h1s' i n r n' r' := sideRLs tm (h1^^i) (d1^^n*>r) (d1^^n'*>r').
Definition h1sh2' i n r n' r' := sideRLs tm (h1^^i++h2) (d1^^n*>r) (d0^^n'*>r').
Definition P1' i n r n' r' := sideRLs tm (h1^^(2^i)) (d0^^n*>r) (d0^^n'*>r').
Definition P2' i n r n' r' := sideRLs tm (h1^^(2^i-1)++h2) (d0^^n*>r) (d1^^n'*>r').
Definition P3' i n r n' r' := sideRLs tm (hRL3^^(2^i)) (d0^^n*>r) (d0^^n'*>r').

Ltac uf := unfold P1,P2,P3,P1',P2',P3',h1s',h1sh2' in *.

Lemma BigStep m i n r n' r':
  P3' i n r n' r' ->
  S' (m,n,r) -->+
  S' (2^i+m,n',r').
Proof.
  unfold S',P3'.
  intros.
  eapply sideRLs_concat_v2.
  3: apply (LIncs).
  2: replace (2^i) with (S(2^i-1)) by lia; cbn; congruence.
  2: apply H.
  generalize (2^i).
  clear.
  induction n; cbn in *; trivial.
  rewrite IHn; trivial.
Qed.


Lemma h1s'_S i n r c r' n'' r'':
  sideRLs tm h1 r (d1^^c*>r') ->
  h1s' i (n+c) r' n'' r'' ->
  h1s' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  cbn[lpow].
  eapply sideRLs_trans.
  2: eauto 1.
  st.
  eapply segRLs_sideRLs_concat.
  2: eauto 1.
  esx.
Qed.

Lemma h1sh2'_S i n r c r' n'' r'':
  sideRLs tm h1 r (d1^^c*>r') ->
  h1sh2' i (n+c) r' n'' r'' ->
  h1sh2' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  cbn[lpow].
  rewrite <-app_assoc.
  eapply sideRLs_trans.
  2: eauto 1.
  st.
  eapply segRLs_sideRLs_concat.
  2: eauto 1.
  esx.
Qed.

Lemma h1s'_6n_0 i j n:
  h1s' (i*6) n ([0;1]^^j*>0inf) (n+i*2) ([0;1]^^j*>0inf).
Proof.
  uf.
  induction i.
  1: esx.
  replace (S i*6) with (i*6+6) by lia.
  eapply sideRLs_trans_add.
  1: eapply IHi.
  replace (i*2) with (i+i) by lia.
  replace ((S i)*2) with (i+i+2) by lia.
  es' i j n.
Qed.

Lemma h1s'_6n_1 i j n:
  h1s' (i*6) n ([0;1]^^j*>ld*>0inf) (n+i*2) ([0;1]^^j*>ld*>0inf).
Proof.
  uf.
  induction i.
  1: esx.
  replace (S i*6) with (i*6+6) by lia.
  eapply sideRLs_trans_add.
  1: eapply IHi.
  replace (i*2) with (i+i) by lia.
  replace ((S i)*2) with (i+i+2) by lia.
  es' i j n.
Qed.

Lemma h1sh2'_spec i n r n' r' c r'':
  h1s' i n r n' r' ->
  sideRLs tm h2 r' (d0^^c*>r'') ->
  h1sh2' i n r (n'+c) r''.
Proof.
  uf.
  intros.
  eapply sideRLs_trans; [eauto 1|].
  st.
  eapply segRLs_sideRLs_concat.
  2: eauto 1.
  esx.
Qed.

Lemma P1'_1 i n r n' r' n'' r'':
  P1' i n r n' r' ->
  P1' i n' r' n'' r'' ->
  P1' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  replace (2^S i) with (2^i+2^i) by (cbn; lia).
  rewrite lpow_add.
  eapply sideRLs_trans; eauto 1.
Qed.

Lemma P1'_2 i n r n' r' n'' r'':
  P2' i n r n' r' ->
  h1sh2' (2^i-1) n' r' n'' r'' ->
  P1' (S i) (2^i+n) r (2^i+n'') r''.
Proof.
  epose proof (P12_n i) as [I1 I2].
  uf.
  intros.
  replace (2^S i) with (2^i+2^i) by (cbn; lia).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  eapply sideRLs_trans;
  eapply segRLs_sideRLs_concat; eauto 1.
Qed.

Lemma P2'_1 i n r n' r' n'' r'':
  P1' i n r n' r' ->
  P2' i n' r' n'' r'' ->
  P2' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  replace (2^S i-1) with (2^i+(2^i-1)) by (cbn; lia).
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans; eauto 1.
Qed.

Lemma P2'_2 i n r n' r' n'' r'':
  P2' i n r n' r' ->
  h1s' (2^i) n' r' n'' r'' ->
  P2' (S i) (2^i+n) r (2^i+n'') r''.
Proof.
  epose proof (P12_n i) as [I1 I2].
  uf.
  intros.
  replace (2^S i-1) with (2^i+(2^i-1)) by (cbn; lia).
  rewrite lpow_add,<-app_assoc.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  eapply sideRLs_trans;
  eapply segRLs_sideRLs_concat; eauto 1.
Qed.

Lemma P3'_2 i n r n' r' n'' r'':
  i<>O ->
  P2' i n r n' r' ->
  h1sh2' (2^i-1) n' r' n'' r'' ->
  P3' i (2^i-1+n) r (2^i-1+n'') r''.
Proof.
  intro Hi.
  destruct i. 1: lia.
  epose proof (P3_n i) as I3.
  uf.
  intros.
  replace (hRL3^^(2^S i)) with (hRL3^^(2^i+2^i)) by (cbn; flia).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  eapply sideRLs_trans;
  eapply segRLs_sideRLs_concat.
  - applys_eq I3; cbn; flia.
  - applys_eq H; cbn; flia.
  - applys_eq I3; cbn; flia.
  - applys_eq H0; cbn; flia.
Qed.

Definition q01 : list Sym := [0;1].

Definition rr0 := 0inf.
Definition rr10 := q01 *> 0inf.
Definition rr1010 := q01^^2 *> 0inf.
Definition rr10100 := ld *> 0inf.
Definition rr1010010 := q01 *> ld *> 0inf.
Definition rr101001010 := q01^^2 *> ld *> 0inf.
Definition rr1010010100 := ld^^2 *> 0inf.
Definition rr101001010010 := q01 *> ld^^2 *> 0inf.
Definition rr10001000 := ([0;0;0;1;0;0;0;1] : list Sym) *> 0inf.

Local Open Scope nat_scope.

Lemma pow8_mod3 q:
  ((2 ^ (q * 8)) mod 3 = 1)%nat.
Proof.
  induction q.
  - reflexivity.
  - replace (S q * 8) with (q * 8 + 8) by lia.
    rewrite Nat.pow_add_r.
    rewrite Nat.mul_mod by lia.
    rewrite IHq.
    reflexivity.
Qed.

Ltac unfold_rr :=
  unfold rr0, rr10, rr1010, rr10100, rr1010010,
    rr101001010, rr1010010100, rr101001010010, rr10001000, q01.

Ltac solve_h1_const :=
  unfold_rr; esx.

Lemma h1_rr0_0:
  sideRLs tm h1 rr0 (d1^^0 *> rr10100).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr10_0:
  sideRLs tm h1 rr10 (d1^^0 *> rr1010010).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr1010_0:
  sideRLs tm h1 rr1010 (d1^^0 *> rr101001010).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr10100_0:
  sideRLs tm h1 rr10100 (d1^^0 *> rr1010).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr1010010_1:
  sideRLs tm h1 rr1010010 (d1^^1 *> rr0).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr101001010_1:
  sideRLs tm h1 rr101001010 (d1^^1 *> rr10).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr0_0:
  sideRLs tm h2 rr0 (d0^^0 *> rr1010010).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr10_0:
  sideRLs tm h2 rr10 (d0^^0 *> rr10100).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr1010_1:
  sideRLs tm h2 rr1010 (d0^^1 *> rr0).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr10100_0:
  sideRLs tm h2 rr10100 (d0^^0 *> rr101001010010).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr1010010_0:
  sideRLs tm h2 rr1010010 (d0^^0 *> rr1010010100).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr101001010_0:
  sideRLs tm h2 rr101001010 (d0^^0 *> rr10001000).
Proof.
  solve_h1_const.
Qed.

Lemma h1sh2'_6n_rr0 i n:
  h1sh2' (i*6) n rr0 (n+i*2+0) rr1010010.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr0) (c:=0).
  - applys_eq (h1s'_6n_0 i 0 n); lia.
  - apply h2_rr0_0.
Qed.

Lemma h1sh2'_6n_rr10 i n:
  h1sh2' (i*6) n rr10 (n+i*2+0) rr10100.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr10) (c:=0).
  - applys_eq (h1s'_6n_0 i 1 n); lia.
  - apply h2_rr10_0.
Qed.

Lemma h1sh2'_6n_rr1010 i n:
  h1sh2' (i*6) n rr1010 (n+i*2+1) rr0.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr1010) (c:=1).
  - applys_eq (h1s'_6n_0 i 2 n); lia.
  - apply h2_rr1010_1.
Qed.

Lemma h1sh2'_6n_rr10100 i n:
  h1sh2' (i*6) n rr10100 (n+i*2+0) rr101001010010.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr10100) (c:=0).
  - applys_eq (h1s'_6n_1 i 0 n); lia.
  - apply h2_rr10100_0.
Qed.

Lemma h1sh2'_6n_rr1010010 i n:
  h1sh2' (i*6) n rr1010010 (n+i*2+0) rr1010010100.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr1010010) (c:=0).
  - applys_eq (h1s'_6n_1 i 1 n); lia.
  - apply h2_rr1010010_0.
Qed.

Lemma h1sh2'_6n_rr101001010 i n:
  h1sh2' (i*6) n rr101001010 (n+i*2+0) rr10001000.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr101001010) (c:=0).
  - applys_eq (h1s'_6n_1 i 2 n); lia.
  - apply h2_rr101001010_0.
Qed.

Ltac pow8_lia :=
  repeat match goal with
  | |- context [2 ^ (S ?q * 8 + ?c)] =>
      replace (S q * 8 + c) with (q * 8 + (c + 8)) by lia
  | H : context [2 ^ (S ?q * 8 + ?c)] |- _ =>
      replace (S q * 8 + c) with (q * 8 + (c + 8)) in H by lia
  end;
  match goal with
  | |- context [2 ^ (?q * 8 + _)] => pose proof (pow8_mod3 q)
  | H : context [2 ^ (?q * 8 + _)] |- _ => pose proof (pow8_mod3 q)
  | q : nat |- _ => pose proof (pow8_mod3 q)
  end;
  repeat match goal with
  | |- context [2 ^ (?q * 8 + ?c)] =>
      rewrite (Nat.pow_add_r 2 (q * 8) c)
  | H : context [2 ^ (?q * 8 + ?c)] |- _ =>
      rewrite (Nat.pow_add_r 2 (q * 8) c) in H
  end;
  cbn [Nat.pow] in *;
  lia.

Ltac solve_loop_P1_1 :=
  match goal with
  | HP1: P1' ?i ?n ?r ?n' ?r',
    HP1': P1' ?i ?n' ?r' ?n'' ?r'' |-
      P1' ?j ?n0 ?r ?n0' ?r'' =>
      applys_eq (P1'_1 i n r n' r' n'' r'' HP1 HP1');
      pow8_lia
  end.

Ltac solve_loop_P1_2 :=
  match goal with
  | HP2: P2' ?i ?n ?r ?n' ?r',
    HH: h1sh2' _ ?n' ?r' ?n'' ?r'' |-
      P1' ?j ?n0 ?r ?n0' ?r'' =>
      applys_eq (P1'_2 i n r n' r' n'' r'' HP2 HH);
      pow8_lia
  end.

Ltac solve_loop_P2_1 :=
  match goal with
  | HP1: P1' ?i ?n ?r ?n' ?r',
    HP2: P2' ?i ?n' ?r' ?n'' ?r'' |-
      P2' ?j ?n ?r ?n'' ?r'' =>
      applys_eq (P2'_1 i n r n' r' n'' r'' HP1 HP2);
      pow8_lia
  end.

Ltac solve_loop_P2_2 :=
  match goal with
  | HP2: P2' ?i ?n ?r ?n' ?r',
    HS: h1s' (2 ^ ?i) ?n' ?r' ?n'' ?r'' |-
      P2' ?j ?n0 ?r ?n0' ?r'' =>
      applys_eq (P2'_2 i n r n' r' n'' r'' HP2 HS);
      pow8_lia
  end.

Ltac solve_loop_P3_2 :=
  match goal with
  | HP2: P2' ?i ?n ?r ?n' ?r',
    HH: h1sh2' _ ?n' ?r' ?n'' ?r'' |-
      P3' ?i ?n0 ?r ?n0' ?r'' =>
      let Hnz := fresh "Hnz" in
      assert (Hnz : i <> O) by lia;
      applys_eq (P3'_2 i n r n' r' n'' r'' Hnz HP2 HH);
      pow8_lia
  end.

Ltac solve_loop_P :=
  first [
    solve_loop_P1_1 |
    solve_loop_P1_2 |
    solve_loop_P2_1 |
    solve_loop_P2_2 |
    solve_loop_P3_2
  ].

Ltac solve_phase_shift :=
  match goal with
  | H: P1' ?i ?n ?r ?n' ?r' |- P1' ?j ?n0 ?r ?n0' ?r' =>
      applys_eq H; pow8_lia
  | H: P2' ?i ?n ?r ?n' ?r' |- P2' ?j ?n0 ?r ?n0' ?r' =>
      applys_eq H; pow8_lia
  end.

Ltac solve_h1_step :=
  first [
    apply h1_rr0_0 |
    apply h1_rr10_0 |
    apply h1_rr1010_0 |
    apply h1_rr10100_0 |
    apply h1_rr1010010_1 |
    apply h1_rr101001010_1
  ].

Ltac peel_h1 :=
  eapply h1s'_S; [solve_h1_step|].

Ltac peel_h1s_to_6 :=
  lazymatch goal with
  | |- h1s' (2 ^ (?q * 8 + ?c)) _ _ _ _ =>
      let even_c := eval cbv in (Nat.even c) in
      lazymatch even_c with
      | true =>
          replace (2 ^ (q * 8 + c))
            with (S (S (S (S (2 ^ (q * 8 + c) - 4))))) by pow8_lia;
          peel_h1; peel_h1; peel_h1; peel_h1
      | false =>
          replace (2 ^ (q * 8 + c))
            with (S (S (2 ^ (q * 8 + c) - 2))) by pow8_lia;
          peel_h1; peel_h1
      end
  | |- h1s' (2 ^ (?q * 8 + ?c) - 1) _ _ _ _ =>
      let even_c := eval cbv in (Nat.even c) in
      lazymatch even_c with
      | true =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (S (S (2 ^ (q * 8 + c) - 4)))) by pow8_lia;
          peel_h1; peel_h1; peel_h1
      | false =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (2 ^ (q * 8 + c) - 2)) by pow8_lia;
          peel_h1
      end
  end.

Ltac finish_h1s_base t :=
  lazymatch goal with
  | |- h1s' _ ?n rr0 _ rr0 =>
      applys_eq (h1s'_6n_0 t 0 n); pow8_lia
  | |- h1s' _ ?n rr10 _ rr10 =>
      applys_eq (h1s'_6n_0 t 1 n); pow8_lia
  | |- h1s' _ ?n rr1010 _ rr1010 =>
      applys_eq (h1s'_6n_0 t 2 n); pow8_lia
  | |- h1s' _ ?n rr10100 _ rr10100 =>
      applys_eq (h1s'_6n_1 t 0 n); pow8_lia
  | |- h1s' _ ?n rr1010010 _ rr1010010 =>
      applys_eq (h1s'_6n_1 t 1 n); pow8_lia
  | |- h1s' _ ?n rr101001010 _ rr101001010 =>
      applys_eq (h1s'_6n_1 t 2 n); pow8_lia
  end.

Ltac finish_h1s :=
  lazymatch goal with
  | |- h1s' (2 ^ (?q * 8 + ?c) - 2) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1s_base ((2 ^ (q * 8 + cm1) - 1) / 3)
  | |- h1s' (2 ^ (?q * 8 + ?c) - 4) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1s_base ((2 ^ (q * 8 + cm1) - 2) / 3)
  end.

Ltac solve_h1s :=
  peel_h1s_to_6;
  finish_h1s.

Ltac solve_h2_const :=
  unfold_rr; esx.

Ltac peel_h1sh2 :=
  eapply h1sh2'_S; [solve_h1_step|].

Ltac peel_h1sh2_to_6 :=
  lazymatch goal with
  | |- h1sh2' (2 ^ (?q * 8 + ?c) - 1) _ _ _ _ =>
      let even_c := eval cbv in (Nat.even c) in
      lazymatch even_c with
      | true =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (S (S (2 ^ (q * 8 + c) - 4)))) by pow8_lia;
          peel_h1sh2; peel_h1sh2; peel_h1sh2
      | false =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (2 ^ (q * 8 + c) - 2)) by pow8_lia;
          peel_h1sh2
      end
  end.

Ltac finish_h1sh2_base t :=
  lazymatch goal with
  | |- h1sh2' _ ?n rr0 _ rr1010010 =>
      applys_eq (h1sh2'_6n_rr0 t n); pow8_lia
  | |- h1sh2' _ ?n rr10 _ rr10100 =>
      applys_eq (h1sh2'_6n_rr10 t n); pow8_lia
  | |- h1sh2' _ ?n rr1010 _ rr0 =>
      applys_eq (h1sh2'_6n_rr1010 t n); pow8_lia
  | |- h1sh2' _ ?n rr10100 _ rr101001010010 =>
      applys_eq (h1sh2'_6n_rr10100 t n); pow8_lia
  | |- h1sh2' _ ?n rr1010010 _ rr1010010100 =>
      applys_eq (h1sh2'_6n_rr1010010 t n); pow8_lia
  | |- h1sh2' _ ?n rr101001010 _ rr10001000 =>
      applys_eq (h1sh2'_6n_rr101001010 t n); pow8_lia
  end.

Ltac finish_h1sh2 :=
  lazymatch goal with
  | |- h1sh2' (2 ^ (?q * 8 + ?c) - 2) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1sh2_base ((2 ^ (q * 8 + cm1) - 1) / 3)
  | |- h1sh2' (2 ^ (?q * 8 + ?c) - 4) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1sh2_base ((2 ^ (q * 8 + cm1) - 2) / 3)
  end.

Ltac solve_h1sh2 :=
  peel_h1sh2_to_6;
  finish_h1sh2.

Lemma h1sh2_rr0_5 q:
  h1sh2' (2 ^ (q * 8 + 5) - 1) ((2 ^ (q * 8 + 6) + 2) / 3)
    rr0 (2 ^ (q * 8 + 5)) rr101001010010.
Proof.
  replace (2 ^ (q * 8 + 5) - 1)
    with (S (((2 ^ (q * 8 + 4) + 2) / 3 - 1) * 6)).
  2:{
    pow8_lia.
  }
  replace (2 ^ (q * 8 + 5))
    with (((2 ^ (q * 8 + 6) + 2) / 3) +
          (((2 ^ (q * 8 + 4) + 2) / 3 - 1) * 2) + 0).
  2:{
    pow8_lia.
  }
  eapply h1sh2'_spec with
    (n':=(((2 ^ (q * 8 + 6) + 2) / 3) +
          (((2 ^ (q * 8 + 4) + 2) / 3 - 1) * 2)))
    (r':=rr10100) (c:=0%nat).
  - eapply h1s'_S.
    + apply h1_rr0_0.
    + replace (((2 ^ (q * 8 + 6) + 2) / 3 + 0))
        with ((2 ^ (q * 8 + 6) + 2) / 3) by lia.
      unfold rr10100.
      exact (h1s'_6n_1 ((2 ^ (q * 8 + 4) + 2) / 3 - 1) 0
        ((2 ^ (q * 8 + 6) + 2) / 3)).
  - unfold_rr; esx.
Qed.

Inductive LoopPhase (q : nat) : nat -> Prop :=
| LoopPhase_5 :
    P2' (q*8+5) ((2 ^ (q * 8 + 5) + 1) / 3) rr0
      ((2 ^ (q * 8 + 6) + 2) / 3) rr0 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr101001010010
      ((2 ^ (q * 8 + 7) + 1) / 3) rr1010 ->
    P1' (q*8+5) ((2 ^ (q * 8 + 6) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 5)) rr10100 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr10100
      ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr1010010
      ((2 ^ (q * 8 + 7) + 1) / 3) rr10100 ->
    P2' (q*8+5) ((2 ^ (q * 8 + 5) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 6) - 1) / 3) rr101001010 ->
    P1' (q*8+5) ((2 ^ (q * 8 + 6) + 2) / 3) rr0
      (2 ^ (q * 8 + 5)) rr101001010010 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr1010010100
      ((2 ^ (q * 8 + 7) + 1) / 3) rr10 ->
    P2' (q*8+5) ((2 ^ (q * 8 + 5) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 6) + 2) / 3) rr10 ->
    P1' (q*8+5) ((2 ^ (q * 8 + 6) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 5)) rr1010010100 ->
    LoopPhase q 5
| LoopPhase_6 :
    P2' (q*8+6) ((2 ^ (q * 8 + 6) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr1010010
      ((2 ^ (q * 8 + 8) - 1) / 3) rr101001010 ->
    P1' (q*8+6) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 6)) rr10100 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr10100
      ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010 ->
    P2' (q*8+6) ((2 ^ (q * 8 + 6) + 2) / 3) rr0
      ((2 ^ (q * 8 + 7) + 1) / 3) rr1010 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr1010010100
      ((2 ^ (q * 8 + 8) + 2) / 3) rr0 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr101001010010
      ((2 ^ (q * 8 + 8) + 2) / 3) rr10 ->
    P1' (q*8+6) ((2 ^ (q * 8 + 7) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 6)) rr1010010100 ->
    P2' (q*8+6) ((2 ^ (q * 8 + 6) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 7) + 1) / 3) rr10 ->
    P1' (q*8+6) ((2 ^ (q * 8 + 7) + 1) / 3) rr0
      (2 ^ (q * 8 + 6)) rr101001010010 ->
    P3' (q*8+5) ((2 ^ (q * 8 + 7) - 2) / 3) rr0
      (2 ^ (q * 8 + 6) - 1) rr101001010010 ->
    P3' (q*8+5) (2 ^ (q * 8 + 6) - 1) rr101001010010
      ((2 ^ (q * 8 + 8) - 1) / 3 - 1) rr10001000 ->
    LoopPhase q 6
| LoopPhase_7 :
    P2' (q*8+7) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr1010010
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10100 ->
    P1' (q*8+7) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
      (2 ^ (q * 8 + 7)) rr1010010100 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr1010010100
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr101001010010
      ((2 ^ (q * 8 + 9) + 1) / 3) rr1010 ->
    P2' (q*8+7) ((2 ^ (q * 8 + 7) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 8) + 2) / 3) rr0 ->
    P1' (q*8+7) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 7)) rr101001010010 ->
    P1' (q*8+7) ((2 ^ (q * 8 + 8) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 7)) rr1010010 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr10100
      ((2 ^ (q * 8 + 9) - 2) / 3) rr101001010 ->
    P2' (q*8+7) ((2 ^ (q * 8 + 7) + 1) / 3) rr0
      ((2 ^ (q * 8 + 8) + 2) / 3) rr10 ->
    P3' (q*8+6) ((2 ^ (q * 8 + 8) - 1) / 3 - 1) rr10001000
      (2 ^ (q * 8 + 7) - 1) rr1010010 ->
    P3' (q*8+6) (2 ^ (q * 8 + 7) - 1) rr1010010
      ((2 ^ (q * 8 + 9) - 2) / 3) rr1010010 ->
    LoopPhase q 7
| LoopPhase_8 :
    P2' (q*8+8) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr101001010010
      ((2 ^ (q * 8 + 10) + 2) / 3) rr10 ->
    P1' (q*8+8) ((2 ^ (q * 8 + 9) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 8)) rr101001010010 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr1010010100
      ((2 ^ (q * 8 + 10) + 2) / 3) rr0 ->
    P2' (q*8+8) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 9) + 1) / 3) rr1010 ->
    P2' (q*8+8) ((2 ^ (q * 8 + 8) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10100 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr10100
      ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr1010010
      ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010 ->
    P1' (q*8+8) ((2 ^ (q * 8 + 9) + 1) / 3) rr0
      (2 ^ (q * 8 + 8)) rr1010010100 ->
    P1' (q*8+8) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 8)) rr1010010 ->
    P3' (q*8+7) ((2 ^ (q * 8 + 9) - 2) / 3) rr1010010
      (2 ^ (q * 8 + 8) - 1) rr1010010 ->
    P3' (q*8+7) (2 ^ (q * 8 + 8) - 1) rr1010010
      ((2 ^ (q * 8 + 10) - 1) / 3) rr0 ->
    LoopPhase q 8
| LoopPhase_9 :
    P2' (q*8+9) ((2 ^ (q * 8 + 9) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 10) + 2) / 3) rr10 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr1010010100
      ((2 ^ (q * 8 + 11) + 1) / 3) rr10 ->
    P1' (q*8+9) ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 9)) rr1010010100 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr101001010010
      ((2 ^ (q * 8 + 11) + 1) / 3) rr1010 ->
    P1' (q*8+9) ((2 ^ (q * 8 + 10) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 9)) rr10100 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr10100
      ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr1010010
      ((2 ^ (q * 8 + 11) + 1) / 3) rr10100 ->
    P2' (q*8+9) ((2 ^ (q * 8 + 9) + 1) / 3) rr0
      ((2 ^ (q * 8 + 10) + 2) / 3) rr0 ->
    P2' (q*8+9) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010 ->
    P1' (q*8+9) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
      (2 ^ (q * 8 + 9)) rr101001010010 ->
    P3' (q*8+8) ((2 ^ (q * 8 + 10) - 1) / 3) rr0
      (2 ^ (q * 8 + 9) - 1) rr101001010010 ->
    P3' (q*8+8) (2 ^ (q * 8 + 9) - 1) rr101001010010
      ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010010 ->
    LoopPhase q 9
| LoopPhase_10 :
    P2' (q*8+10) ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 11) + 1) / 3) rr10 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr101001010010
      ((2 ^ (q * 8 + 12) + 2) / 3) rr10 ->
    P1' (q*8+10) ((2 ^ (q * 8 + 11) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 10)) rr1010010100 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr1010010100
      ((2 ^ (q * 8 + 12) + 2) / 3) rr0 ->
    P2' (q*8+10) ((2 ^ (q * 8 + 10) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr1010010
      ((2 ^ (q * 8 + 12) - 1) / 3) rr101001010 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr10100
      ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010 ->
    P1' (q*8+10) ((2 ^ (q * 8 + 11) + 1) / 3) rr0
      (2 ^ (q * 8 + 10)) rr101001010010 ->
    P1' (q*8+10) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 10)) rr10100 ->
    P2' (q*8+10) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
      ((2 ^ (q * 8 + 11) + 1) / 3) rr1010 ->
    P3' (q*8+9) ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010010
      (2 ^ (q * 8 + 10) - 1) rr1010010100 ->
    P3' (q*8+9) (2 ^ (q * 8 + 10) - 1) rr1010010100
      ((2 ^ (q * 8 + 12) - 1) / 3 - 1) rr1010010100 ->
    LoopPhase q 10
| LoopPhase_11 :
    P2' (q*8+11) ((2 ^ (q * 8 + 11) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 12) + 2) / 3) rr0 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr101001010010
      ((2 ^ (q * 8 + 13) + 1) / 3) rr1010 ->
    P1' (q*8+11) ((2 ^ (q * 8 + 12) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 11)) rr1010010 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr1010010
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10100 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr10100
      ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010 ->
    P2' (q*8+11) ((2 ^ (q * 8 + 11) + 1) / 3) rr0
      ((2 ^ (q * 8 + 12) + 2) / 3) rr10 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr1010010100
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10 ->
    P2' (q*8+11) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010 ->
    P1' (q*8+11) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
      (2 ^ (q * 8 + 11)) rr1010010100 ->
    P1' (q*8+11) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 11)) rr101001010010 ->
    P3' (q*8+10) ((2 ^ (q * 8 + 12) - 1) / 3 - 1) rr1010010100
      (2 ^ (q * 8 + 11) - 1) rr101001010010 ->
    P3' (q*8+10) (2 ^ (q * 8 + 11) - 1) rr101001010010
      ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010010 ->
    LoopPhase q 11
| LoopPhase_12 :
    P2' (q*8+12) ((2 ^ (q * 8 + 12) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10100 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr10100
      ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010 ->
    P1' (q*8+12) ((2 ^ (q * 8 + 13) + 1) / 3) rr0
      (2 ^ (q * 8 + 12)) rr1010010100 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr1010010100
      ((2 ^ (q * 8 + 14) + 2) / 3) rr0 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr101001010010
      ((2 ^ (q * 8 + 14) + 2) / 3) rr10 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr1010010
      ((2 ^ (q * 8 + 14) - 1) / 3) rr101001010 ->
    P1' (q*8+12) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 12)) rr1010010 ->
    P2' (q*8+12) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10 ->
    P1' (q*8+12) ((2 ^ (q * 8 + 13) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 12)) rr101001010010 ->
    P2' (q*8+12) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 13) + 1) / 3) rr1010 ->
    P3' (q*8+11) ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010010
      (2 ^ (q * 8 + 12) - 1) rr101001010010 ->
    P3' (q*8+11) (2 ^ (q * 8 + 12) - 1) rr101001010010
      ((2 ^ (q * 8 + 14) - 1) / 3 - 1) rr10001000 ->
    LoopPhase q 12
| LoopPhase_13 :
    P2' (q*8+13) ((2 ^ (q * 8 + 13) + 1) / 3) rr0
      ((2 ^ (q * 8 + 14) + 2) / 3) rr0 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr101001010010
      ((2 ^ (q * 8 + 15) + 1) / 3) rr1010 ->
    P1' (q*8+13) ((2 ^ (q * 8 + 14) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 13)) rr10100 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr10100
      ((2 ^ (q * 8 + 15) - 2) / 3) rr101001010 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr1010010
      ((2 ^ (q * 8 + 15) + 1) / 3) rr10100 ->
    P2' (q*8+13) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 14) - 1) / 3) rr101001010 ->
    P1' (q*8+13) ((2 ^ (q * 8 + 14) + 2) / 3) rr0
      (2 ^ (q * 8 + 13)) rr101001010010 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr1010010100
      ((2 ^ (q * 8 + 15) + 1) / 3) rr10 ->
    P2' (q*8+13) ((2 ^ (q * 8 + 13) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 14) + 2) / 3) rr10 ->
    P1' (q*8+13) ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 13)) rr1010010100 ->
    P3' (q*8+12) ((2 ^ (q * 8 + 14) - 1) / 3 - 1) rr10001000
      (2 ^ (q * 8 + 13) - 1) rr10100 ->
    P3' (q*8+12) (2 ^ (q * 8 + 13) - 1) rr10100
      ((2 ^ (q * 8 + 15) - 2) / 3) rr0 ->
    LoopPhase q 13.

Ltac esc :=
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Lemma loop_phase0_5:
  LoopPhase 0 5.
Proof.
  econstructor.
  all: uf; cbn[Nat.add Nat.sub Nat.mul Nat.pow Nat.div Nat.divmod fst]; unfold_rr; esc.
Qed.

Lemma loop_phase5_to_6 q:
  LoopPhase q 5 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 8) - 1) / 3 - 2 ^ (q * 8 + 5)) rr101001010 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 8) - 1) / 3 - 2 ^ (q * 8 + 5)) rr1010010 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) + 1) / 3) rr10
    ((2 ^ (q * 8 + 8) + 2) / 3 - 2 ^ (q * 8 + 5)) rr0 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 8) + 2) / 3 - 2 ^ (q * 8 + 5)) rr10 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 6) - 1) / 3) rr101001010
    (2 ^ (q * 8 + 5)) rr10100 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 6) + 2) / 3) rr10
    (2 ^ (q * 8 + 5)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 6) + 2) / 3) rr0
    (2 ^ (q * 8 + 5)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 8) - 1) / 3 - 2 ^ (q * 8 + 5)) rr10001000 ->
  LoopPhase q 6.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase9_to_10 q:
  LoopPhase q 9 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 12) + 2) / 3 - 2 ^ (q * 8 + 9)) rr10 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) + 1) / 3) rr10
    ((2 ^ (q * 8 + 12) + 2) / 3 - 2 ^ (q * 8 + 9)) rr0 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 12) - 1) / 3 - 2 ^ (q * 8 + 9)) rr101001010 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 12) - 1) / 3 - 2 ^ (q * 8 + 9)) rr1010010 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 10) + 2) / 3) rr10
    (2 ^ (q * 8 + 9)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
    (2 ^ (q * 8 + 9)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010
    (2 ^ (q * 8 + 9)) rr10100 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 11) + 1) / 3) rr10
    ((2 ^ (q * 8 + 12) - 1) / 3 - 2 ^ (q * 8 + 9)) rr1010010100 ->
  LoopPhase q 10.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase10_to_11 q:
  LoopPhase q 10 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) + 2) / 3) rr10
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr1010 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr10100 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 13) - 2) / 3 - 2 ^ (q * 8 + 10)) rr101001010 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr10 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010
    (2 ^ (q * 8 + 10)) rr1010010 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010
    (2 ^ (q * 8 + 10)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 11) + 1) / 3) rr10
    (2 ^ (q * 8 + 10)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 12) + 2) / 3) rr10
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr101001010010 ->
  LoopPhase q 11.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase11_to_12 q:
  LoopPhase q 11 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 14) - 1) / 3 - 2 ^ (q * 8 + 11)) rr1010010 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) + 1) / 3) rr10
    ((2 ^ (q * 8 + 14) + 2) / 3 - 2 ^ (q * 8 + 11)) rr0 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 14) + 2) / 3 - 2 ^ (q * 8 + 11)) rr10 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 14) - 1) / 3 - 2 ^ (q * 8 + 11)) rr101001010 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 12) + 2) / 3) rr10
    (2 ^ (q * 8 + 11)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010
    (2 ^ (q * 8 + 11)) rr1010010 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
    (2 ^ (q * 8 + 11)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 14) - 1) / 3 - 2 ^ (q * 8 + 11)) rr10001000 ->
  LoopPhase q 12.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase12_to_13 q:
  LoopPhase q 12 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) + 2) / 3) rr10
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr1010 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 15) - 2) / 3 - 2 ^ (q * 8 + 12)) rr101001010 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr10100 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) + 2) / 3) rr0
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr10 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr10100
    (2 ^ (q * 8 + 12)) rr10100 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr10
    (2 ^ (q * 8 + 12)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010
    (2 ^ (q * 8 + 12)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr0 ->
  LoopPhase q 13.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase13_to_next5 q:
  LoopPhase q 13 ->
  LoopPhase (S q) 5.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_phase_shift.
Qed.

Lemma loop_phase8_to_9 q:
  LoopPhase q 8 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr10 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) + 2) / 3) rr10
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr1010 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 11) - 2) / 3 - 2 ^ (q * 8 + 8)) rr101001010 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr10100 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010
    (2 ^ (q * 8 + 8)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr10100
    (2 ^ (q * 8 + 8)) rr10100 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr10
    (2 ^ (q * 8 + 8)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 10) + 2) / 3) rr10
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr101001010010 ->
  LoopPhase q 9.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase7_to_8 q:
  LoopPhase q 7 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 10) + 2) / 3 - 2 ^ (q * 8 + 7)) rr10 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) + 1) / 3) rr10
    ((2 ^ (q * 8 + 10) + 2) / 3 - 2 ^ (q * 8 + 7)) rr0 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 10) - 1) / 3 - 2 ^ (q * 8 + 7)) rr1010010 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 10) - 1) / 3 - 2 ^ (q * 8 + 7)) rr101001010 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
    (2 ^ (q * 8 + 7)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 8) + 2) / 3) rr10
    (2 ^ (q * 8 + 7)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010
    (2 ^ (q * 8 + 7)) rr1010010 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 10) + 2) / 3 - 2 ^ (q * 8 + 7)) rr0 ->
  LoopPhase q 8.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase6_to_7 q:
  LoopPhase q 6 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr10100 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr10 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) + 2) / 3) rr10
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr1010 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 9) - 2) / 3 - 2 ^ (q * 8 + 6)) rr101001010 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010
    (2 ^ (q * 8 + 6)) rr1010010 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010
    (2 ^ (q * 8 + 6)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 7) + 1) / 3) rr10
    (2 ^ (q * 8 + 6)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 8) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr1010010 ->
  LoopPhase q 7.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Ltac solve_loop_h :=
  first [solve_h1s | solve_h1sh2].

Lemma loop_phase5_to_6_closed q:
  LoopPhase q 5 ->
  LoopPhase q 6.
Proof.
  intro H.
  refine (loop_phase5_to_6 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase6_to_7_closed q:
  LoopPhase q 6 ->
  LoopPhase q 7.
Proof.
  intro H.
  refine (loop_phase6_to_7 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase7_to_8_closed q:
  LoopPhase q 7 ->
  LoopPhase q 8.
Proof.
  intro H.
  refine (loop_phase7_to_8 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase8_to_9_closed q:
  LoopPhase q 8 ->
  LoopPhase q 9.
Proof.
  intro H.
  refine (loop_phase8_to_9 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase9_to_10_closed q:
  LoopPhase q 9 ->
  LoopPhase q 10.
Proof.
  intro H.
  refine (loop_phase9_to_10 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase10_to_11_closed q:
  LoopPhase q 10 ->
  LoopPhase q 11.
Proof.
  intro H.
  refine (loop_phase10_to_11 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase11_to_12_closed q:
  LoopPhase q 11 ->
  LoopPhase q 12.
Proof.
  intro H.
  refine (loop_phase11_to_12 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase12_to_13_closed q:
  LoopPhase q 12 ->
  LoopPhase q 13.
Proof.
  intro H.
  refine (loop_phase12_to_13 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase5_cycle q:
  LoopPhase q 5 ->
  LoopPhase (S q) 5.
Proof.
  intro H.
  apply loop_phase13_to_next5.
  apply loop_phase12_to_13_closed.
  apply loop_phase11_to_12_closed.
  apply loop_phase10_to_11_closed.
  apply loop_phase9_to_10_closed.
  apply loop_phase8_to_9_closed.
  apply loop_phase7_to_8_closed.
  apply loop_phase6_to_7_closed.
  apply loop_phase5_to_6_closed.
  exact H.
Qed.

Ltac clear_loop_non_p3 :=
  repeat match goal with
  | H: P1' _ _ _ _ _ |- _ => clear H
  | H: P2' _ _ _ _ _ |- _ => clear H
  end.

Ltac solve_p3_step :=
  eapply BigStep;
  eassumption.

Ltac chain_p3_steps :=
  first [
    solve_p3_step |
    eapply progress_trans; [solve_p3_step|chain_p3_steps]
  ].

Lemma loop_phase5_progress q m:
  LoopPhase q 5 ->
  exists m',
    S' (m, (2 ^ (q * 8 + 7) - 2) / 3, rr0) -->+
    S' (m', (2 ^ (q * 8 + 15) - 2) / 3, rr0).
Proof.
  intro H5.
  pose proof (loop_phase5_to_6_closed q H5) as H6.
  pose proof (loop_phase6_to_7_closed q H6) as H7.
  pose proof (loop_phase7_to_8_closed q H7) as H8.
  pose proof (loop_phase8_to_9_closed q H8) as H9.
  pose proof (loop_phase9_to_10_closed q H9) as H10.
  pose proof (loop_phase10_to_11_closed q H10) as H11.
  pose proof (loop_phase11_to_12_closed q H11) as H12.
  pose proof (loop_phase12_to_13_closed q H12) as H13.
  inversion H6; subst; clear H6.
  inversion H7; subst; clear H7.
  inversion H8; subst; clear H8.
  inversion H9; subst; clear H9.
  inversion H10; subst; clear H10.
  inversion H11; subst; clear H11.
  inversion H12; subst; clear H12.
  inversion H13; subst; clear H13.
  clear_loop_non_p3.
  eexists.
  chain_p3_steps.
Qed.

Lemma LoopPhase_n q:
  LoopPhase q 5.
Proof.
  induction q.
  - apply loop_phase0_5.
  - apply loop_phase5_cycle,IHq.
Qed.

Definition S0 '(m,q) := S' (m,(2^(q*8+7)-2)/3,rr0).

Definition BigStep0 m q:
  exists m',
  S0 (m,q) -->+
  S0 (m',S q).
Proof.
  unfold S0.
  epose proof (LoopPhase_n q) as I1.
  eapply loop_phase5_progress in I1.
  destruct I1 as [m' I1].
  eexists.
  applys_eq I1; flia.
Qed.

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; simpl_tape; try reflexivity.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (62,0)).
  1: stepn 168995%N.
  eapply progress_nonhalt_simple.
  intros [m q].
  epose proof (BigStep0 m q) as [m' I1].
  eexists (_,_); apply I1.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LE_0LB1RC_0RD1RA_1RE1RF_1LC0LE_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation h1 := [((D,<[0;0]),(C,[1;0;1]))].
Notation h2 := [((F,<[0;1]),(C,[1;0;1]))].
Notation d0 := [0;0;0;1;0;1].
Notation d1 := [0;1;0;1;0;1].

Definition P1 n := segRLs tm (h1^^(2^n)) (h1^^(2^n-1)++h2) (d0^^(2^n)) (d0^^(2^n)).
Definition P2 n := segRLs tm (h1^^(2^n-1)++h2) (h1^^(2^n)) (d0^^(2^n)) (d1^^(2^n)).

Lemma h1s_d1s k n:
  segRLs tm (h1^^k) (h1^^k) (d1^^n) (d1^^n).
Proof.
  eapply segRLs_wall''.
  esx.
Qed.

Lemma h1sh2_d1s k n:
  segRLs tm (h1^^k++h2) (h1^^k++h2) (d1^^n) (d0^^n).
Proof.
  eapply segRLs_trans.
  1: apply h1s_d1s.
  esx.
Qed.

Lemma P12_n n:
  P1 n /\ P2 n.
Proof.
  unfold P1,P2.
  induction n.
  - split; esx.
  - destruct IHn as [I1 I2].
    cbn[Nat.pow].
    split.
    all:
    replace (2*2^n-1) with (2^n+(2^n-1)) by lia;
    replace (2*2^n) with (2^n+2^n) by lia;
    repeat rewrite lpow_add;
    rewrite <-app_assoc.
    + eapply segRLs_trans.
      * eapply segRLs_concat; [apply I1|apply I2].
      * eapply segRLs_concat; [apply I1|apply h1sh2_d1s].
    + eapply segRLs_trans.
      * eapply segRLs_concat; [apply I1|apply I2].
      * eapply segRLs_concat; [apply I2|apply h1s_d1s].
Qed.

Notation hR := (A,<[1]).
Notation hL := (E,@nil Sym).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation ld := [0;0;1;0;1].
Notation lh := (0inf<*<[1;0]).
Notation hL' := (E,ld).
Notation hRL' := [(hR,hL')].
Notation hRL3 := (hRL^^2++hRL').
Notation hLR3 := (hLR^^2++[(hL',hR)]).

Definition P3 n := segRLs tm (hRL3^^(2^n)) (h1^^(2^n*2-1)++h2) (d0^^(2^n*2-1)) (d0^^(2^n*2-1)).

Lemma P3_n n:
  P3 n.
Proof.
  unfold P3.
  induction n.
  - esx.
  - replace (d0^^(2^S n*2-1)) with (d0^^((2^n*2-1)+(2^(S n)))) by (cbn; flia).
    replace (hRL3^^(2^S n)) with (hRL3^^(2^n+2^n)) by (cbn; flia).
    replace (2^S n*2-1) with (2^n*2+(2^n*2-1)) by (cbn; lia).
    repeat rewrite lpow_add.
    rewrite <-app_assoc.
    epose proof (P12_n (S n)) as [I1 I2].
    unfold P1,P2 in *.
    eapply segRLs_trans.
    + eapply segRLs_concat; [apply IHn|].
      applys_eq I2; cbn; flia.
    + eapply segRLs_concat; [apply IHn|].
      apply h1sh2_d1s.
Qed.

Definition LC n := lh <* <[1;1;0;1;0]^^n.
Definition tm' := flip tm.

Lemma LIncs k n:
  sideRLs tm' (hLR3^^k) (LC n) (LC (k+n)).
Proof.
  unfold LC.
  induction k.
  1: esx.
  replace (S k) with (k+1) by lia.
  eapply sideRLs_trans_add.
  1: eapply IHk.
  es' k n.
Qed.

Definition S' '(m,n,r) := LC m {{{ (hR,R) }}} d0^^n *> r.




Definition h1s' i n r n' r' := sideRLs tm (h1^^i) (d1^^n*>r) (d1^^n'*>r').
Definition h1sh2' i n r n' r' := sideRLs tm (h1^^i++h2) (d1^^n*>r) (d0^^n'*>r').
Definition P1' i n r n' r' := sideRLs tm (h1^^(2^i)) (d0^^n*>r) (d0^^n'*>r').
Definition P2' i n r n' r' := sideRLs tm (h1^^(2^i-1)++h2) (d0^^n*>r) (d1^^n'*>r').
Definition P3' i n r n' r' := sideRLs tm (hRL3^^(2^i)) (d0^^n*>r) (d0^^n'*>r').

Ltac uf := unfold P1,P2,P3,P1',P2',P3',h1s',h1sh2' in *.

Lemma BigStep m i n r n' r':
  P3' i n r n' r' ->
  S' (m,n,r) -->+
  S' (2^i+m,n',r').
Proof.
  unfold S',P3'.
  intros.
  eapply sideRLs_concat_v2.
  3: apply (LIncs).
  2: replace (2^i) with (S(2^i-1)) by lia; cbn; congruence.
  2: apply H.
  generalize (2^i).
  clear.
  induction n; cbn in *; trivial.
  rewrite IHn; trivial.
Qed.


Lemma h1s'_S i n r c r' n'' r'':
  sideRLs tm h1 r (d1^^c*>r') ->
  h1s' i (n+c) r' n'' r'' ->
  h1s' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  cbn[lpow].
  eapply sideRLs_trans.
  2: eauto 1.
  st.
  eapply segRLs_sideRLs_concat.
  2: eauto 1.
  esx.
Qed.

Lemma h1sh2'_S i n r c r' n'' r'':
  sideRLs tm h1 r (d1^^c*>r') ->
  h1sh2' i (n+c) r' n'' r'' ->
  h1sh2' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  cbn[lpow].
  rewrite <-app_assoc.
  eapply sideRLs_trans.
  2: eauto 1.
  st.
  eapply segRLs_sideRLs_concat.
  2: eauto 1.
  esx.
Qed.

Lemma h1s'_6n_0 i j n:
  h1s' (i*6) n ([0;1]^^j*>0inf) (n+i*2) ([0;1]^^j*>0inf).
Proof.
  uf.
  induction i.
  1: esx.
  replace (S i*6) with (i*6+6) by lia.
  eapply sideRLs_trans_add.
  1: eapply IHi.
  replace (i*2) with (i+i) by lia.
  replace ((S i)*2) with (i+i+2) by lia.
  es' i j n.
Qed.

Lemma h1s'_6n_1 i j n:
  h1s' (i*6) n ([0;1]^^j*>ld*>0inf) (n+i*2) ([0;1]^^j*>ld*>0inf).
Proof.
  uf.
  induction i.
  1: esx.
  replace (S i*6) with (i*6+6) by lia.
  eapply sideRLs_trans_add.
  1: eapply IHi.
  replace (i*2) with (i+i) by lia.
  replace ((S i)*2) with (i+i+2) by lia.
  es' i j n.
Qed.

Lemma h1sh2'_spec i n r n' r' c r'':
  h1s' i n r n' r' ->
  sideRLs tm h2 r' (d0^^c*>r'') ->
  h1sh2' i n r (n'+c) r''.
Proof.
  uf.
  intros.
  eapply sideRLs_trans; [eauto 1|].
  st.
  eapply segRLs_sideRLs_concat.
  2: eauto 1.
  esx.
Qed.

Lemma P1'_1 i n r n' r' n'' r'':
  P1' i n r n' r' ->
  P1' i n' r' n'' r'' ->
  P1' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  replace (2^S i) with (2^i+2^i) by (cbn; lia).
  rewrite lpow_add.
  eapply sideRLs_trans; eauto 1.
Qed.

Lemma P1'_2 i n r n' r' n'' r'':
  P2' i n r n' r' ->
  h1sh2' (2^i-1) n' r' n'' r'' ->
  P1' (S i) (2^i+n) r (2^i+n'') r''.
Proof.
  epose proof (P12_n i) as [I1 I2].
  uf.
  intros.
  replace (2^S i) with (2^i+2^i) by (cbn; lia).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  eapply sideRLs_trans;
  eapply segRLs_sideRLs_concat; eauto 1.
Qed.

Lemma P2'_1 i n r n' r' n'' r'':
  P1' i n r n' r' ->
  P2' i n' r' n'' r'' ->
  P2' (S i) n r n'' r''.
Proof.
  uf.
  intros.
  replace (2^S i-1) with (2^i+(2^i-1)) by (cbn; lia).
  rewrite lpow_add,<-app_assoc.
  eapply sideRLs_trans; eauto 1.
Qed.

Lemma P2'_2 i n r n' r' n'' r'':
  P2' i n r n' r' ->
  h1s' (2^i) n' r' n'' r'' ->
  P2' (S i) (2^i+n) r (2^i+n'') r''.
Proof.
  epose proof (P12_n i) as [I1 I2].
  uf.
  intros.
  replace (2^S i-1) with (2^i+(2^i-1)) by (cbn; lia).
  rewrite lpow_add,<-app_assoc.
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  eapply sideRLs_trans;
  eapply segRLs_sideRLs_concat; eauto 1.
Qed.

Lemma P3'_2 i n r n' r' n'' r'':
  i<>O ->
  P2' i n r n' r' ->
  h1sh2' (2^i-1) n' r' n'' r'' ->
  P3' i (2^i-1+n) r (2^i-1+n'') r''.
Proof.
  intro Hi.
  destruct i. 1: lia.
  epose proof (P3_n i) as I3.
  uf.
  intros.
  replace (hRL3^^(2^S i)) with (hRL3^^(2^i+2^i)) by (cbn; flia).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  eapply sideRLs_trans;
  eapply segRLs_sideRLs_concat.
  - applys_eq I3; cbn; flia.
  - applys_eq H; cbn; flia.
  - applys_eq I3; cbn; flia.
  - applys_eq H0; cbn; flia.
Qed.

Definition q01 : list Sym := [0;1].

Definition rr0 := 0inf.
Definition rr10 := q01 *> 0inf.
Definition rr1010 := q01^^2 *> 0inf.
Definition rr10100 := ld *> 0inf.
Definition rr1010010 := q01 *> ld *> 0inf.
Definition rr101001010 := q01^^2 *> ld *> 0inf.
Definition rr1010010100 := ld^^2 *> 0inf.
Definition rr101001010010 := q01 *> ld^^2 *> 0inf.
Definition rr10001000 := ([0;0;0;1;0;0;0;1] : list Sym) *> 0inf.

Local Open Scope nat_scope.

Lemma pow8_mod3 q:
  ((2 ^ (q * 8)) mod 3 = 1)%nat.
Proof.
  induction q.
  - reflexivity.
  - replace (S q * 8) with (q * 8 + 8) by lia.
    rewrite Nat.pow_add_r.
    rewrite Nat.mul_mod by lia.
    rewrite IHq.
    reflexivity.
Qed.

Ltac unfold_rr :=
  unfold rr0, rr10, rr1010, rr10100, rr1010010,
    rr101001010, rr1010010100, rr101001010010, rr10001000, q01.

Ltac solve_h1_const :=
  unfold_rr; esx.

Lemma h1_rr0_0:
  sideRLs tm h1 rr0 (d1^^0 *> rr10100).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr10_0:
  sideRLs tm h1 rr10 (d1^^0 *> rr1010010).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr1010_0:
  sideRLs tm h1 rr1010 (d1^^0 *> rr101001010).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr10100_0:
  sideRLs tm h1 rr10100 (d1^^0 *> rr1010).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr1010010_1:
  sideRLs tm h1 rr1010010 (d1^^1 *> rr0).
Proof.
  solve_h1_const.
Qed.

Lemma h1_rr101001010_1:
  sideRLs tm h1 rr101001010 (d1^^1 *> rr10).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr0_0:
  sideRLs tm h2 rr0 (d0^^0 *> rr1010010).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr10_0:
  sideRLs tm h2 rr10 (d0^^0 *> rr10100).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr1010_1:
  sideRLs tm h2 rr1010 (d0^^1 *> rr0).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr10100_0:
  sideRLs tm h2 rr10100 (d0^^0 *> rr101001010010).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr1010010_0:
  sideRLs tm h2 rr1010010 (d0^^0 *> rr1010010100).
Proof.
  solve_h1_const.
Qed.

Lemma h2_rr101001010_0:
  sideRLs tm h2 rr101001010 (d0^^0 *> rr10001000).
Proof.
  solve_h1_const.
Qed.

Lemma h1sh2'_6n_rr0 i n:
  h1sh2' (i*6) n rr0 (n+i*2+0) rr1010010.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr0) (c:=0).
  - applys_eq (h1s'_6n_0 i 0 n); lia.
  - apply h2_rr0_0.
Qed.

Lemma h1sh2'_6n_rr10 i n:
  h1sh2' (i*6) n rr10 (n+i*2+0) rr10100.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr10) (c:=0).
  - applys_eq (h1s'_6n_0 i 1 n); lia.
  - apply h2_rr10_0.
Qed.

Lemma h1sh2'_6n_rr1010 i n:
  h1sh2' (i*6) n rr1010 (n+i*2+1) rr0.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr1010) (c:=1).
  - applys_eq (h1s'_6n_0 i 2 n); lia.
  - apply h2_rr1010_1.
Qed.

Lemma h1sh2'_6n_rr10100 i n:
  h1sh2' (i*6) n rr10100 (n+i*2+0) rr101001010010.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr10100) (c:=0).
  - applys_eq (h1s'_6n_1 i 0 n); lia.
  - apply h2_rr10100_0.
Qed.

Lemma h1sh2'_6n_rr1010010 i n:
  h1sh2' (i*6) n rr1010010 (n+i*2+0) rr1010010100.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr1010010) (c:=0).
  - applys_eq (h1s'_6n_1 i 1 n); lia.
  - apply h2_rr1010010_0.
Qed.

Lemma h1sh2'_6n_rr101001010 i n:
  h1sh2' (i*6) n rr101001010 (n+i*2+0) rr10001000.
Proof.
  eapply h1sh2'_spec with (n':=n+i*2) (r':=rr101001010) (c:=0).
  - applys_eq (h1s'_6n_1 i 2 n); lia.
  - apply h2_rr101001010_0.
Qed.

Ltac pow8_lia :=
  repeat match goal with
  | |- context [2 ^ (S ?q * 8 + ?c)] =>
      replace (S q * 8 + c) with (q * 8 + (c + 8)) by lia
  | H : context [2 ^ (S ?q * 8 + ?c)] |- _ =>
      replace (S q * 8 + c) with (q * 8 + (c + 8)) in H by lia
  end;
  match goal with
  | |- context [2 ^ (?q * 8 + _)] => pose proof (pow8_mod3 q)
  | H : context [2 ^ (?q * 8 + _)] |- _ => pose proof (pow8_mod3 q)
  | q : nat |- _ => pose proof (pow8_mod3 q)
  end;
  repeat match goal with
  | |- context [2 ^ (?q * 8 + ?c)] =>
      rewrite (Nat.pow_add_r 2 (q * 8) c)
  | H : context [2 ^ (?q * 8 + ?c)] |- _ =>
      rewrite (Nat.pow_add_r 2 (q * 8) c) in H
  end;
  cbn [Nat.pow] in *;
  lia.

Ltac solve_loop_P1_1 :=
  match goal with
  | HP1: P1' ?i ?n ?r ?n' ?r',
    HP1': P1' ?i ?n' ?r' ?n'' ?r'' |-
      P1' ?j ?n0 ?r ?n0' ?r'' =>
      applys_eq (P1'_1 i n r n' r' n'' r'' HP1 HP1');
      pow8_lia
  end.

Ltac solve_loop_P1_2 :=
  match goal with
  | HP2: P2' ?i ?n ?r ?n' ?r',
    HH: h1sh2' _ ?n' ?r' ?n'' ?r'' |-
      P1' ?j ?n0 ?r ?n0' ?r'' =>
      applys_eq (P1'_2 i n r n' r' n'' r'' HP2 HH);
      pow8_lia
  end.

Ltac solve_loop_P2_1 :=
  match goal with
  | HP1: P1' ?i ?n ?r ?n' ?r',
    HP2: P2' ?i ?n' ?r' ?n'' ?r'' |-
      P2' ?j ?n ?r ?n'' ?r'' =>
      applys_eq (P2'_1 i n r n' r' n'' r'' HP1 HP2);
      pow8_lia
  end.

Ltac solve_loop_P2_2 :=
  match goal with
  | HP2: P2' ?i ?n ?r ?n' ?r',
    HS: h1s' (2 ^ ?i) ?n' ?r' ?n'' ?r'' |-
      P2' ?j ?n0 ?r ?n0' ?r'' =>
      applys_eq (P2'_2 i n r n' r' n'' r'' HP2 HS);
      pow8_lia
  end.

Ltac solve_loop_P3_2 :=
  match goal with
  | HP2: P2' ?i ?n ?r ?n' ?r',
    HH: h1sh2' _ ?n' ?r' ?n'' ?r'' |-
      P3' ?i ?n0 ?r ?n0' ?r'' =>
      let Hnz := fresh "Hnz" in
      assert (Hnz : i <> O) by lia;
      applys_eq (P3'_2 i n r n' r' n'' r'' Hnz HP2 HH);
      pow8_lia
  end.

Ltac solve_loop_P :=
  first [
    solve_loop_P1_1 |
    solve_loop_P1_2 |
    solve_loop_P2_1 |
    solve_loop_P2_2 |
    solve_loop_P3_2
  ].

Ltac solve_phase_shift :=
  match goal with
  | H: P1' ?i ?n ?r ?n' ?r' |- P1' ?j ?n0 ?r ?n0' ?r' =>
      applys_eq H; pow8_lia
  | H: P2' ?i ?n ?r ?n' ?r' |- P2' ?j ?n0 ?r ?n0' ?r' =>
      applys_eq H; pow8_lia
  end.

Ltac solve_h1_step :=
  first [
    apply h1_rr0_0 |
    apply h1_rr10_0 |
    apply h1_rr1010_0 |
    apply h1_rr10100_0 |
    apply h1_rr1010010_1 |
    apply h1_rr101001010_1
  ].

Ltac peel_h1 :=
  eapply h1s'_S; [solve_h1_step|].

Ltac peel_h1s_to_6 :=
  lazymatch goal with
  | |- h1s' (2 ^ (?q * 8 + ?c)) _ _ _ _ =>
      let even_c := eval cbv in (Nat.even c) in
      lazymatch even_c with
      | true =>
          replace (2 ^ (q * 8 + c))
            with (S (S (S (S (2 ^ (q * 8 + c) - 4))))) by pow8_lia;
          peel_h1; peel_h1; peel_h1; peel_h1
      | false =>
          replace (2 ^ (q * 8 + c))
            with (S (S (2 ^ (q * 8 + c) - 2))) by pow8_lia;
          peel_h1; peel_h1
      end
  | |- h1s' (2 ^ (?q * 8 + ?c) - 1) _ _ _ _ =>
      let even_c := eval cbv in (Nat.even c) in
      lazymatch even_c with
      | true =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (S (S (2 ^ (q * 8 + c) - 4)))) by pow8_lia;
          peel_h1; peel_h1; peel_h1
      | false =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (2 ^ (q * 8 + c) - 2)) by pow8_lia;
          peel_h1
      end
  end.

Ltac finish_h1s_base t :=
  lazymatch goal with
  | |- h1s' _ ?n rr0 _ rr0 =>
      applys_eq (h1s'_6n_0 t 0 n); pow8_lia
  | |- h1s' _ ?n rr10 _ rr10 =>
      applys_eq (h1s'_6n_0 t 1 n); pow8_lia
  | |- h1s' _ ?n rr1010 _ rr1010 =>
      applys_eq (h1s'_6n_0 t 2 n); pow8_lia
  | |- h1s' _ ?n rr10100 _ rr10100 =>
      applys_eq (h1s'_6n_1 t 0 n); pow8_lia
  | |- h1s' _ ?n rr1010010 _ rr1010010 =>
      applys_eq (h1s'_6n_1 t 1 n); pow8_lia
  | |- h1s' _ ?n rr101001010 _ rr101001010 =>
      applys_eq (h1s'_6n_1 t 2 n); pow8_lia
  end.

Ltac finish_h1s :=
  lazymatch goal with
  | |- h1s' (2 ^ (?q * 8 + ?c) - 2) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1s_base ((2 ^ (q * 8 + cm1) - 1) / 3)
  | |- h1s' (2 ^ (?q * 8 + ?c) - 4) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1s_base ((2 ^ (q * 8 + cm1) - 2) / 3)
  end.

Ltac solve_h1s :=
  peel_h1s_to_6;
  finish_h1s.

Ltac solve_h2_const :=
  unfold_rr; esx.

Ltac peel_h1sh2 :=
  eapply h1sh2'_S; [solve_h1_step|].

Ltac peel_h1sh2_to_6 :=
  lazymatch goal with
  | |- h1sh2' (2 ^ (?q * 8 + ?c) - 1) _ _ _ _ =>
      let even_c := eval cbv in (Nat.even c) in
      lazymatch even_c with
      | true =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (S (S (2 ^ (q * 8 + c) - 4)))) by pow8_lia;
          peel_h1sh2; peel_h1sh2; peel_h1sh2
      | false =>
          replace (2 ^ (q * 8 + c) - 1)
            with (S (2 ^ (q * 8 + c) - 2)) by pow8_lia;
          peel_h1sh2
      end
  end.

Ltac finish_h1sh2_base t :=
  lazymatch goal with
  | |- h1sh2' _ ?n rr0 _ rr1010010 =>
      applys_eq (h1sh2'_6n_rr0 t n); pow8_lia
  | |- h1sh2' _ ?n rr10 _ rr10100 =>
      applys_eq (h1sh2'_6n_rr10 t n); pow8_lia
  | |- h1sh2' _ ?n rr1010 _ rr0 =>
      applys_eq (h1sh2'_6n_rr1010 t n); pow8_lia
  | |- h1sh2' _ ?n rr10100 _ rr101001010010 =>
      applys_eq (h1sh2'_6n_rr10100 t n); pow8_lia
  | |- h1sh2' _ ?n rr1010010 _ rr1010010100 =>
      applys_eq (h1sh2'_6n_rr1010010 t n); pow8_lia
  | |- h1sh2' _ ?n rr101001010 _ rr10001000 =>
      applys_eq (h1sh2'_6n_rr101001010 t n); pow8_lia
  end.

Ltac finish_h1sh2 :=
  lazymatch goal with
  | |- h1sh2' (2 ^ (?q * 8 + ?c) - 2) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1sh2_base ((2 ^ (q * 8 + cm1) - 1) / 3)
  | |- h1sh2' (2 ^ (?q * 8 + ?c) - 4) _ _ _ _ =>
      let cm1 := eval cbv in (c - 1) in
      finish_h1sh2_base ((2 ^ (q * 8 + cm1) - 2) / 3)
  end.

Ltac solve_h1sh2 :=
  peel_h1sh2_to_6;
  finish_h1sh2.

Lemma h1sh2_rr0_5 q:
  h1sh2' (2 ^ (q * 8 + 5) - 1) ((2 ^ (q * 8 + 6) + 2) / 3)
    rr0 (2 ^ (q * 8 + 5)) rr101001010010.
Proof.
  replace (2 ^ (q * 8 + 5) - 1)
    with (S (((2 ^ (q * 8 + 4) + 2) / 3 - 1) * 6)).
  2:{
    pow8_lia.
  }
  replace (2 ^ (q * 8 + 5))
    with (((2 ^ (q * 8 + 6) + 2) / 3) +
          (((2 ^ (q * 8 + 4) + 2) / 3 - 1) * 2) + 0).
  2:{
    pow8_lia.
  }
  eapply h1sh2'_spec with
    (n':=(((2 ^ (q * 8 + 6) + 2) / 3) +
          (((2 ^ (q * 8 + 4) + 2) / 3 - 1) * 2)))
    (r':=rr10100) (c:=0%nat).
  - eapply h1s'_S.
    + apply h1_rr0_0.
    + replace (((2 ^ (q * 8 + 6) + 2) / 3 + 0))
        with ((2 ^ (q * 8 + 6) + 2) / 3) by lia.
      unfold rr10100.
      exact (h1s'_6n_1 ((2 ^ (q * 8 + 4) + 2) / 3 - 1) 0
        ((2 ^ (q * 8 + 6) + 2) / 3)).
  - unfold_rr; esx.
Qed.

Inductive LoopPhase (q : nat) : nat -> Prop :=
| LoopPhase_5 :
    P2' (q*8+5) ((2 ^ (q * 8 + 5) + 1) / 3) rr0
      ((2 ^ (q * 8 + 6) + 2) / 3) rr0 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr101001010010
      ((2 ^ (q * 8 + 7) + 1) / 3) rr1010 ->
    P1' (q*8+5) ((2 ^ (q * 8 + 6) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 5)) rr10100 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr10100
      ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr1010010
      ((2 ^ (q * 8 + 7) + 1) / 3) rr10100 ->
    P2' (q*8+5) ((2 ^ (q * 8 + 5) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 6) - 1) / 3) rr101001010 ->
    P1' (q*8+5) ((2 ^ (q * 8 + 6) + 2) / 3) rr0
      (2 ^ (q * 8 + 5)) rr101001010010 ->
    P2' (q*8+5) (2 ^ (q * 8 + 5)) rr1010010100
      ((2 ^ (q * 8 + 7) + 1) / 3) rr10 ->
    P2' (q*8+5) ((2 ^ (q * 8 + 5) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 6) + 2) / 3) rr10 ->
    P1' (q*8+5) ((2 ^ (q * 8 + 6) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 5)) rr1010010100 ->
    LoopPhase q 5
| LoopPhase_6 :
    P2' (q*8+6) ((2 ^ (q * 8 + 6) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr1010010
      ((2 ^ (q * 8 + 8) - 1) / 3) rr101001010 ->
    P1' (q*8+6) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 6)) rr10100 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr10100
      ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010 ->
    P2' (q*8+6) ((2 ^ (q * 8 + 6) + 2) / 3) rr0
      ((2 ^ (q * 8 + 7) + 1) / 3) rr1010 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr1010010100
      ((2 ^ (q * 8 + 8) + 2) / 3) rr0 ->
    P2' (q*8+6) (2 ^ (q * 8 + 6)) rr101001010010
      ((2 ^ (q * 8 + 8) + 2) / 3) rr10 ->
    P1' (q*8+6) ((2 ^ (q * 8 + 7) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 6)) rr1010010100 ->
    P2' (q*8+6) ((2 ^ (q * 8 + 6) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 7) + 1) / 3) rr10 ->
    P1' (q*8+6) ((2 ^ (q * 8 + 7) + 1) / 3) rr0
      (2 ^ (q * 8 + 6)) rr101001010010 ->
    P3' (q*8+5) ((2 ^ (q * 8 + 7) - 2) / 3) rr0
      (2 ^ (q * 8 + 6) - 1) rr101001010010 ->
    P3' (q*8+5) (2 ^ (q * 8 + 6) - 1) rr101001010010
      ((2 ^ (q * 8 + 8) - 1) / 3 - 1) rr10001000 ->
    LoopPhase q 6
| LoopPhase_7 :
    P2' (q*8+7) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr1010010
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10100 ->
    P1' (q*8+7) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
      (2 ^ (q * 8 + 7)) rr1010010100 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr1010010100
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr101001010010
      ((2 ^ (q * 8 + 9) + 1) / 3) rr1010 ->
    P2' (q*8+7) ((2 ^ (q * 8 + 7) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 8) + 2) / 3) rr0 ->
    P1' (q*8+7) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 7)) rr101001010010 ->
    P1' (q*8+7) ((2 ^ (q * 8 + 8) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 7)) rr1010010 ->
    P2' (q*8+7) (2 ^ (q * 8 + 7)) rr10100
      ((2 ^ (q * 8 + 9) - 2) / 3) rr101001010 ->
    P2' (q*8+7) ((2 ^ (q * 8 + 7) + 1) / 3) rr0
      ((2 ^ (q * 8 + 8) + 2) / 3) rr10 ->
    P3' (q*8+6) ((2 ^ (q * 8 + 8) - 1) / 3 - 1) rr10001000
      (2 ^ (q * 8 + 7) - 1) rr1010010 ->
    P3' (q*8+6) (2 ^ (q * 8 + 7) - 1) rr1010010
      ((2 ^ (q * 8 + 9) - 2) / 3) rr1010010 ->
    LoopPhase q 7
| LoopPhase_8 :
    P2' (q*8+8) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr101001010010
      ((2 ^ (q * 8 + 10) + 2) / 3) rr10 ->
    P1' (q*8+8) ((2 ^ (q * 8 + 9) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 8)) rr101001010010 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr1010010100
      ((2 ^ (q * 8 + 10) + 2) / 3) rr0 ->
    P2' (q*8+8) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 9) + 1) / 3) rr1010 ->
    P2' (q*8+8) ((2 ^ (q * 8 + 8) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 9) + 1) / 3) rr10100 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr10100
      ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010 ->
    P2' (q*8+8) (2 ^ (q * 8 + 8)) rr1010010
      ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010 ->
    P1' (q*8+8) ((2 ^ (q * 8 + 9) + 1) / 3) rr0
      (2 ^ (q * 8 + 8)) rr1010010100 ->
    P1' (q*8+8) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 8)) rr1010010 ->
    P3' (q*8+7) ((2 ^ (q * 8 + 9) - 2) / 3) rr1010010
      (2 ^ (q * 8 + 8) - 1) rr1010010 ->
    P3' (q*8+7) (2 ^ (q * 8 + 8) - 1) rr1010010
      ((2 ^ (q * 8 + 10) - 1) / 3) rr0 ->
    LoopPhase q 8
| LoopPhase_9 :
    P2' (q*8+9) ((2 ^ (q * 8 + 9) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 10) + 2) / 3) rr10 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr1010010100
      ((2 ^ (q * 8 + 11) + 1) / 3) rr10 ->
    P1' (q*8+9) ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 9)) rr1010010100 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr101001010010
      ((2 ^ (q * 8 + 11) + 1) / 3) rr1010 ->
    P1' (q*8+9) ((2 ^ (q * 8 + 10) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 9)) rr10100 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr10100
      ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010 ->
    P2' (q*8+9) (2 ^ (q * 8 + 9)) rr1010010
      ((2 ^ (q * 8 + 11) + 1) / 3) rr10100 ->
    P2' (q*8+9) ((2 ^ (q * 8 + 9) + 1) / 3) rr0
      ((2 ^ (q * 8 + 10) + 2) / 3) rr0 ->
    P2' (q*8+9) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010 ->
    P1' (q*8+9) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
      (2 ^ (q * 8 + 9)) rr101001010010 ->
    P3' (q*8+8) ((2 ^ (q * 8 + 10) - 1) / 3) rr0
      (2 ^ (q * 8 + 9) - 1) rr101001010010 ->
    P3' (q*8+8) (2 ^ (q * 8 + 9) - 1) rr101001010010
      ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010010 ->
    LoopPhase q 9
| LoopPhase_10 :
    P2' (q*8+10) ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 11) + 1) / 3) rr10 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr101001010010
      ((2 ^ (q * 8 + 12) + 2) / 3) rr10 ->
    P1' (q*8+10) ((2 ^ (q * 8 + 11) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 10)) rr1010010100 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr1010010100
      ((2 ^ (q * 8 + 12) + 2) / 3) rr0 ->
    P2' (q*8+10) ((2 ^ (q * 8 + 10) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr1010010
      ((2 ^ (q * 8 + 12) - 1) / 3) rr101001010 ->
    P2' (q*8+10) (2 ^ (q * 8 + 10)) rr10100
      ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010 ->
    P1' (q*8+10) ((2 ^ (q * 8 + 11) + 1) / 3) rr0
      (2 ^ (q * 8 + 10)) rr101001010010 ->
    P1' (q*8+10) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 10)) rr10100 ->
    P2' (q*8+10) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
      ((2 ^ (q * 8 + 11) + 1) / 3) rr1010 ->
    P3' (q*8+9) ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010010
      (2 ^ (q * 8 + 10) - 1) rr1010010100 ->
    P3' (q*8+9) (2 ^ (q * 8 + 10) - 1) rr1010010100
      ((2 ^ (q * 8 + 12) - 1) / 3 - 1) rr1010010100 ->
    LoopPhase q 10
| LoopPhase_11 :
    P2' (q*8+11) ((2 ^ (q * 8 + 11) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 12) + 2) / 3) rr0 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr101001010010
      ((2 ^ (q * 8 + 13) + 1) / 3) rr1010 ->
    P1' (q*8+11) ((2 ^ (q * 8 + 12) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 11)) rr1010010 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr1010010
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10100 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr10100
      ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010 ->
    P2' (q*8+11) ((2 ^ (q * 8 + 11) + 1) / 3) rr0
      ((2 ^ (q * 8 + 12) + 2) / 3) rr10 ->
    P2' (q*8+11) (2 ^ (q * 8 + 11)) rr1010010100
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10 ->
    P2' (q*8+11) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010 ->
    P1' (q*8+11) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
      (2 ^ (q * 8 + 11)) rr1010010100 ->
    P1' (q*8+11) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 11)) rr101001010010 ->
    P3' (q*8+10) ((2 ^ (q * 8 + 12) - 1) / 3 - 1) rr1010010100
      (2 ^ (q * 8 + 11) - 1) rr101001010010 ->
    P3' (q*8+10) (2 ^ (q * 8 + 11) - 1) rr101001010010
      ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010010 ->
    LoopPhase q 11
| LoopPhase_12 :
    P2' (q*8+12) ((2 ^ (q * 8 + 12) - 1) / 3) rr10001000
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10100 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr10100
      ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010 ->
    P1' (q*8+12) ((2 ^ (q * 8 + 13) + 1) / 3) rr0
      (2 ^ (q * 8 + 12)) rr1010010100 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr1010010100
      ((2 ^ (q * 8 + 14) + 2) / 3) rr0 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr101001010010
      ((2 ^ (q * 8 + 14) + 2) / 3) rr10 ->
    P2' (q*8+12) (2 ^ (q * 8 + 12)) rr1010010
      ((2 ^ (q * 8 + 14) - 1) / 3) rr101001010 ->
    P1' (q*8+12) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010010
      (2 ^ (q * 8 + 12)) rr1010010 ->
    P2' (q*8+12) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
      ((2 ^ (q * 8 + 13) + 1) / 3) rr10 ->
    P1' (q*8+12) ((2 ^ (q * 8 + 13) + 1) / 3) rr101001010010
      (2 ^ (q * 8 + 12)) rr101001010010 ->
    P2' (q*8+12) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010100
      ((2 ^ (q * 8 + 13) + 1) / 3) rr1010 ->
    P3' (q*8+11) ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010010
      (2 ^ (q * 8 + 12) - 1) rr101001010010 ->
    P3' (q*8+11) (2 ^ (q * 8 + 12) - 1) rr101001010010
      ((2 ^ (q * 8 + 14) - 1) / 3 - 1) rr10001000 ->
    LoopPhase q 12
| LoopPhase_13 :
    P2' (q*8+13) ((2 ^ (q * 8 + 13) + 1) / 3) rr0
      ((2 ^ (q * 8 + 14) + 2) / 3) rr0 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr101001010010
      ((2 ^ (q * 8 + 15) + 1) / 3) rr1010 ->
    P1' (q*8+13) ((2 ^ (q * 8 + 14) - 1) / 3) rr10001000
      (2 ^ (q * 8 + 13)) rr10100 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr10100
      ((2 ^ (q * 8 + 15) - 2) / 3) rr101001010 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr1010010
      ((2 ^ (q * 8 + 15) + 1) / 3) rr10100 ->
    P2' (q*8+13) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010010
      ((2 ^ (q * 8 + 14) - 1) / 3) rr101001010 ->
    P1' (q*8+13) ((2 ^ (q * 8 + 14) + 2) / 3) rr0
      (2 ^ (q * 8 + 13)) rr101001010010 ->
    P2' (q*8+13) (2 ^ (q * 8 + 13)) rr1010010100
      ((2 ^ (q * 8 + 15) + 1) / 3) rr10 ->
    P2' (q*8+13) ((2 ^ (q * 8 + 13) + 1) / 3) rr101001010010
      ((2 ^ (q * 8 + 14) + 2) / 3) rr10 ->
    P1' (q*8+13) ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010100
      (2 ^ (q * 8 + 13)) rr1010010100 ->
    P3' (q*8+12) ((2 ^ (q * 8 + 14) - 1) / 3 - 1) rr10001000
      (2 ^ (q * 8 + 13) - 1) rr10100 ->
    P3' (q*8+12) (2 ^ (q * 8 + 13) - 1) rr10100
      ((2 ^ (q * 8 + 15) - 2) / 3) rr0 ->
    LoopPhase q 13.

Ltac esc :=
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Lemma loop_phase0_5:
  LoopPhase 0 5.
Proof.
  econstructor.
  all: uf; cbn[Nat.add Nat.sub Nat.mul Nat.pow Nat.div Nat.divmod fst]; unfold_rr; esc.
Qed.

Lemma loop_phase5_to_6 q:
  LoopPhase q 5 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 8) - 1) / 3 - 2 ^ (q * 8 + 5)) rr101001010 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 8) - 1) / 3 - 2 ^ (q * 8 + 5)) rr1010010 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) + 1) / 3) rr10
    ((2 ^ (q * 8 + 8) + 2) / 3 - 2 ^ (q * 8 + 5)) rr0 ->
  h1s' (2 ^ (q*8+5)) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 8) + 2) / 3 - 2 ^ (q * 8 + 5)) rr10 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 6) - 1) / 3) rr101001010
    (2 ^ (q * 8 + 5)) rr10100 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 6) + 2) / 3) rr10
    (2 ^ (q * 8 + 5)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 6) + 2) / 3) rr0
    (2 ^ (q * 8 + 5)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+5) - 1) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 8) - 1) / 3 - 2 ^ (q * 8 + 5)) rr10001000 ->
  LoopPhase q 6.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase9_to_10 q:
  LoopPhase q 9 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 12) + 2) / 3 - 2 ^ (q * 8 + 9)) rr10 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) + 1) / 3) rr10
    ((2 ^ (q * 8 + 12) + 2) / 3 - 2 ^ (q * 8 + 9)) rr0 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 12) - 1) / 3 - 2 ^ (q * 8 + 9)) rr101001010 ->
  h1s' (2 ^ (q*8+9)) ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 12) - 1) / 3 - 2 ^ (q * 8 + 9)) rr1010010 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 10) + 2) / 3) rr10
    (2 ^ (q * 8 + 9)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
    (2 ^ (q * 8 + 9)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010
    (2 ^ (q * 8 + 9)) rr10100 ->
  h1sh2' (2 ^ (q*8+9) - 1) ((2 ^ (q * 8 + 11) + 1) / 3) rr10
    ((2 ^ (q * 8 + 12) - 1) / 3 - 2 ^ (q * 8 + 9)) rr1010010100 ->
  LoopPhase q 10.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase10_to_11 q:
  LoopPhase q 10 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) + 2) / 3) rr10
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr1010 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr10100 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 13) - 2) / 3 - 2 ^ (q * 8 + 10)) rr101001010 ->
  h1s' (2 ^ (q*8+10)) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr10 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 11) - 2) / 3) rr101001010
    (2 ^ (q * 8 + 10)) rr1010010 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 11) + 1) / 3) rr1010
    (2 ^ (q * 8 + 10)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 11) + 1) / 3) rr10
    (2 ^ (q * 8 + 10)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+10) - 1) ((2 ^ (q * 8 + 12) + 2) / 3) rr10
    ((2 ^ (q * 8 + 13) + 1) / 3 - 2 ^ (q * 8 + 10)) rr101001010010 ->
  LoopPhase q 11.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase11_to_12 q:
  LoopPhase q 11 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 14) - 1) / 3 - 2 ^ (q * 8 + 11)) rr1010010 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) + 1) / 3) rr10
    ((2 ^ (q * 8 + 14) + 2) / 3 - 2 ^ (q * 8 + 11)) rr0 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 14) + 2) / 3 - 2 ^ (q * 8 + 11)) rr10 ->
  h1s' (2 ^ (q*8+11)) ((2 ^ (q * 8 + 13) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 14) - 1) / 3 - 2 ^ (q * 8 + 11)) rr101001010 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 12) + 2) / 3) rr10
    (2 ^ (q * 8 + 11)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 12) - 1) / 3) rr1010010
    (2 ^ (q * 8 + 11)) rr1010010 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 12) + 2) / 3) rr0
    (2 ^ (q * 8 + 11)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+11) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 14) - 1) / 3 - 2 ^ (q * 8 + 11)) rr10001000 ->
  LoopPhase q 12.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase12_to_13 q:
  LoopPhase q 12 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) + 2) / 3) rr10
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr1010 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 15) - 2) / 3 - 2 ^ (q * 8 + 12)) rr101001010 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr10100 ->
  h1s' (2 ^ (q*8+12)) ((2 ^ (q * 8 + 14) + 2) / 3) rr0
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr10 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr10100
    (2 ^ (q * 8 + 12)) rr10100 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr10
    (2 ^ (q * 8 + 12)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 13) + 1) / 3) rr1010
    (2 ^ (q * 8 + 12)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+12) - 1) ((2 ^ (q * 8 + 14) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 15) + 1) / 3 - 2 ^ (q * 8 + 12)) rr0 ->
  LoopPhase q 13.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase13_to_next5 q:
  LoopPhase q 13 ->
  LoopPhase (S q) 5.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_phase_shift.
Qed.

Lemma loop_phase8_to_9 q:
  LoopPhase q 8 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) + 2) / 3) rr0
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr10 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) + 2) / 3) rr10
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr1010 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 11) - 2) / 3 - 2 ^ (q * 8 + 8)) rr101001010 ->
  h1s' (2 ^ (q*8+8)) ((2 ^ (q * 8 + 10) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr10100 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010
    (2 ^ (q * 8 + 8)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr10100
    (2 ^ (q * 8 + 8)) rr10100 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr10
    (2 ^ (q * 8 + 8)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+8) - 1) ((2 ^ (q * 8 + 10) + 2) / 3) rr10
    ((2 ^ (q * 8 + 11) + 1) / 3 - 2 ^ (q * 8 + 8)) rr101001010010 ->
  LoopPhase q 9.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase7_to_8 q:
  LoopPhase q 7 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) + 1) / 3) rr1010
    ((2 ^ (q * 8 + 10) + 2) / 3 - 2 ^ (q * 8 + 7)) rr10 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) + 1) / 3) rr10
    ((2 ^ (q * 8 + 10) + 2) / 3 - 2 ^ (q * 8 + 7)) rr0 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) - 2) / 3) rr101001010
    ((2 ^ (q * 8 + 10) - 1) / 3 - 2 ^ (q * 8 + 7)) rr1010010 ->
  h1s' (2 ^ (q*8+7)) ((2 ^ (q * 8 + 9) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 10) - 1) / 3 - 2 ^ (q * 8 + 7)) rr101001010 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
    (2 ^ (q * 8 + 7)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 8) + 2) / 3) rr10
    (2 ^ (q * 8 + 7)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010
    (2 ^ (q * 8 + 7)) rr1010010 ->
  h1sh2' (2 ^ (q*8+7) - 1) ((2 ^ (q * 8 + 9) + 1) / 3) rr10100
    ((2 ^ (q * 8 + 10) + 2) / 3 - 2 ^ (q * 8 + 7)) rr0 ->
  LoopPhase q 8.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Lemma loop_phase6_to_7 q:
  LoopPhase q 6 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr10100 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) + 2) / 3) rr0
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr10 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) + 2) / 3) rr10
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr1010 ->
  h1s' (2 ^ (q*8+6)) ((2 ^ (q * 8 + 8) - 1) / 3) rr1010010
    ((2 ^ (q * 8 + 9) - 2) / 3 - 2 ^ (q * 8 + 6)) rr101001010 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 7) - 2) / 3) rr101001010
    (2 ^ (q * 8 + 6)) rr1010010 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 7) + 1) / 3) rr1010
    (2 ^ (q * 8 + 6)) rr1010010100 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 7) + 1) / 3) rr10
    (2 ^ (q * 8 + 6)) rr101001010010 ->
  h1sh2' (2 ^ (q*8+6) - 1) ((2 ^ (q * 8 + 8) - 1) / 3) rr101001010
    ((2 ^ (q * 8 + 9) + 1) / 3 - 2 ^ (q * 8 + 6)) rr1010010 ->
  LoopPhase q 7.
Proof.
  intro H.
  inversion H; subst; clear H.
  econstructor.
  all: solve_loop_P.
Qed.

Ltac solve_loop_h :=
  first [solve_h1s | solve_h1sh2].

Lemma loop_phase5_to_6_closed q:
  LoopPhase q 5 ->
  LoopPhase q 6.
Proof.
  intro H.
  refine (loop_phase5_to_6 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase6_to_7_closed q:
  LoopPhase q 6 ->
  LoopPhase q 7.
Proof.
  intro H.
  refine (loop_phase6_to_7 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase7_to_8_closed q:
  LoopPhase q 7 ->
  LoopPhase q 8.
Proof.
  intro H.
  refine (loop_phase7_to_8 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase8_to_9_closed q:
  LoopPhase q 8 ->
  LoopPhase q 9.
Proof.
  intro H.
  refine (loop_phase8_to_9 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase9_to_10_closed q:
  LoopPhase q 9 ->
  LoopPhase q 10.
Proof.
  intro H.
  refine (loop_phase9_to_10 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase10_to_11_closed q:
  LoopPhase q 10 ->
  LoopPhase q 11.
Proof.
  intro H.
  refine (loop_phase10_to_11 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase11_to_12_closed q:
  LoopPhase q 11 ->
  LoopPhase q 12.
Proof.
  intro H.
  refine (loop_phase11_to_12 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase12_to_13_closed q:
  LoopPhase q 12 ->
  LoopPhase q 13.
Proof.
  intro H.
  refine (loop_phase12_to_13 q H _ _ _ _ _ _ _ _);
  solve_loop_h.
Qed.

Lemma loop_phase5_cycle q:
  LoopPhase q 5 ->
  LoopPhase (S q) 5.
Proof.
  intro H.
  apply loop_phase13_to_next5.
  apply loop_phase12_to_13_closed.
  apply loop_phase11_to_12_closed.
  apply loop_phase10_to_11_closed.
  apply loop_phase9_to_10_closed.
  apply loop_phase8_to_9_closed.
  apply loop_phase7_to_8_closed.
  apply loop_phase6_to_7_closed.
  apply loop_phase5_to_6_closed.
  exact H.
Qed.

Ltac clear_loop_non_p3 :=
  repeat match goal with
  | H: P1' _ _ _ _ _ |- _ => clear H
  | H: P2' _ _ _ _ _ |- _ => clear H
  end.

Ltac solve_p3_step :=
  eapply BigStep;
  eassumption.

Ltac chain_p3_steps :=
  first [
    solve_p3_step |
    eapply progress_trans; [solve_p3_step|chain_p3_steps]
  ].

Lemma loop_phase5_progress q m:
  LoopPhase q 5 ->
  exists m',
    S' (m, (2 ^ (q * 8 + 7) - 2) / 3, rr0) -->+
    S' (m', (2 ^ (q * 8 + 15) - 2) / 3, rr0).
Proof.
  intro H5.
  pose proof (loop_phase5_to_6_closed q H5) as H6.
  pose proof (loop_phase6_to_7_closed q H6) as H7.
  pose proof (loop_phase7_to_8_closed q H7) as H8.
  pose proof (loop_phase8_to_9_closed q H8) as H9.
  pose proof (loop_phase9_to_10_closed q H9) as H10.
  pose proof (loop_phase10_to_11_closed q H10) as H11.
  pose proof (loop_phase11_to_12_closed q H11) as H12.
  pose proof (loop_phase12_to_13_closed q H12) as H13.
  inversion H6; subst; clear H6.
  inversion H7; subst; clear H7.
  inversion H8; subst; clear H8.
  inversion H9; subst; clear H9.
  inversion H10; subst; clear H10.
  inversion H11; subst; clear H11.
  inversion H12; subst; clear H12.
  inversion H13; subst; clear H13.
  clear_loop_non_p3.
  eexists.
  chain_p3_steps.
Qed.

Lemma LoopPhase_n q:
  LoopPhase q 5.
Proof.
  induction q.
  - apply loop_phase0_5.
  - apply loop_phase5_cycle,IHq.
Qed.

Definition S0 '(m,q) := S' (m,(2^(q*8+7)-2)/3,rr0).

Definition BigStep0 m q:
  exists m',
  S0 (m,q) -->+
  S0 (m',S q).
Proof.
  unfold S0.
  epose proof (LoopPhase_n q) as I1.
  eapply loop_phase5_progress in I1.
  destruct I1 as [m' I1].
  eexists.
  applys_eq I1; flia.
Qed.

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; simpl_tape; try reflexivity.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (62,0)).
  1: stepn 179829%N.
  eapply progress_nonhalt_simple.
  intros [m q].
  epose proof (BigStep0 m q) as [m' I1].
  eexists (_,_); apply I1.
Qed.

End TM2.



