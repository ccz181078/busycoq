From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require Import DivModCases.
From BusyCoq Require Import BinaryCounter_v2.

Open Scope list.

Lemma sideRLs_wall tm h n l l' w:
  segRLs tm h h w w ->
  sideRLs tm (h^^n) l l' ->
  sideRLs tm (h^^n) (l<*w) (l'<*w).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  2: apply H0.
  apply segRLs_wall'',H.
Qed.

Notation "a ^^^ b" := (flat_map a b) (at level 20).


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC0LB_1LD0RE_---1LB_1RF1RF_1RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hL := (B,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;1;0].
Notation d := [0;1;1].
Notation w' := [0;0;1;1;0].
Notation w := [0;0;0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> r =
  0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_wall''; esx.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (0>>0>>1>>0inf).
Notation rh1 := (0>>1>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd;Dd;Dd;Dw],rh1).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(1+n)) rh1 (d*>w^^n*>0>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>0>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  1: rewrite const_unfold; finish.
  1: er.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(3+n*2)) rh0 (w^^(n)*>0>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  1: rewrite const_unfold; finish.
  1: er.
  1: er.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (1+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (3+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 2<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rw [Dd;Dd;Dd]).
    1: do 3 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-1).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1RB_1RC0RE_1RD1LB_1RE0LD_1LF0RA_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;1;0].
Notation d := [0;1;1].
Notation w' := [0;0;1;1;0].
Notation w := [0;0;0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> r =
  0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_wall''; esx.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (0>>0>>1>>0inf).
Notation rh1 := (0>>1>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^4++[Dw]^^3,rh0).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(1+n)) rh1 (d*>w^^n*>0>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>0>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  1: rewrite const_unfold; finish.
  1: er.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(3+n*2)) rh0 (w^^(n)*>0>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  1: rewrite const_unfold; finish.
  1: er.
  1: er.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (1+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (3+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 2<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 4 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-1).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LA_1RD1RC_1RA0RF_1LD1LA_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;0;1;0].
Notation d := [1;0;1;0].
Notation w' := [0;1;0].
Notation w := [1;0;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> r =
  1 >> 0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (0inf).
Notation rh1 := (0>>0>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1;1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^3++[Dw]^^2,rh0).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3+n)) rh1 (d*>w^^n*>1>>0>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>1>>0>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(3+n*2)) rh0 (w^^(n)*>1>>0>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (3+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (3+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 3 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-3).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RB_1RD0RF_1LA0LE_1LC1LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;0;1;0].
Notation d := [1;0;1;0].
Notation w' := [0;1;0].
Notation w := [1;0;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> r =
  1 >> 0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (0inf).
Notation rh1 := (0>>0>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1;1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^3++[Dw]^^1,rh0).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3+n)) rh1 (d*>w^^n*>1>>0>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>1>>0>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(3+n*2)) rh0 (w^^(n)*>1>>0>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (3+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (3+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 3 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-3).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0LF_1RD0LB_1RA1RD_0RD---_1LA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hL := (B,[]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;0;1;0].
Notation d := [1;0;1;0].
Notation w' := [0;1;0].
Notation w := [1;0;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> r =
  1 >> 0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (0inf).
Notation rh1 := (0>>0>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1;1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^3++[Dw]^^2,rh1).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3+n)) rh1 (d*>w^^n*>1>>0>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>1>>0>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(3+n*2)) rh0 (w^^(n)*>1>>0>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (3+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (3+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 3 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-3).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC0RF_0RD0LD_0LB1RE_0RA---_0LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;0;1;0].
Notation d := [1;0;1;0].
Notation w' := [0;1;0;0;1;0].
Notation w := [1;0;0;1;0;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> r =
  1 >> 0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh1 := (0>>1>>0inf).
Notation dx := [0; 1;0;1;0; 1;0].

Lemma Incs_dx n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*2+2)) dx (d++[1;0;0]).
Proof.
  destruct n.
  1: esx.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^5++[Dw]^^4,rh1).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3+n)) rh1 (1>>0>>dx*>w'^^n*>rh1).
Proof.
  sideRLs_ind n.
Qed.

Lemma Incs_ws n m:
  segRLs tm (hRL^^(n+m+1)) (hRL^^(m+1)) (w'^^n) (w^^n).
Proof.
  induction n.
  - eapply segRLs_wall''; esx.
  - cbn[lpow].
    eapply segRLs_concat.
    2: apply IHn.
    applys_eq (Incs_w (n+m)); flia.
Qed.

Lemma RIncs2 n m:
  n+1<=m*2 ->
  sideRLs tm (hRL^^(m*1+2)) (dx*>w'^^(n)*>rh1) ((d++[1;0;0])*>w^^(n)*>1>>0>>dx*>w'^^(m*2-1-n)*>rh1).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  1: apply (Incs_dx).
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws (n) (m*2+1-n)); flia.
  applys_eq (RIncs1 (m*2-1-n)); flia.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (3+n) ->
  S' (ls,rh1) -->+
  S' (Dd::ls,dx*>w'^^n*>rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1' ls i m n:
  P ls i m ->
  n+5<=m*2 ->
  S' (ls,dx*>w'^^n*>rh1) -->+
  S' (Dd::ls++Dd::[Dw]^^(1+n)++Dd::[Dw]^^((m-2)*2-1-n),rh1).
Proof.
  unfold P,S'.
  intros HP Hm.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    applys_eq (RIncs2 n (m-2)); flia.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep ls i n:
  P ls i n ->
  3<=n ->
  S' (ls,rh1) -->+
  S' ((((((Dd::Dd::ls)++[Dd])++[Dw]^^(n-2))++[Dd])++[Dw]^^(2^i*2+n-2)),rh1).
Proof.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep1 with (n:=n-3).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1'.
  1: apply HP.
  1: lia.
  repeat rewrite <-app_assoc.
  cbn[app].
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 5 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [Hr [i [n [I1 I2]]]].
  subst r.
  eexists (_,_); repeat split.
  + eapply BigStep; eauto 1.
  + eexists _,_; split.
    1:{
      apply P_Rws.
      1: apply P_Rd.
      1: apply P_Rws.
      1: apply P_Rd.
      do 2 apply P_Ld.
      1: apply I1.
      all: lia.
    }
    lia.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0RF_0RC0LC_0LA1RD_0RE---_1RA0RE_0LE0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[1]).
Notation hL := (C,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;0;1;0].
Notation d := [1;0;1;0].
Notation w' := [0;1;0;0;1;0].
Notation w := [1;0;0;1;0;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> r =
  1 >> 0 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh1 := (0>>1>>0inf).
Notation dx := [0; 1;0;1;0; 1;0].

Lemma Incs_dx n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*2+2)) dx (d++[1;0;0]).
Proof.
  destruct n.
  1: esx.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ((([Dd]^^5++[Dw]^^2)++[Dd])++[Dw]^^10,rh1).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(3+n)) rh1 (1>>0>>dx*>w'^^n*>rh1).
Proof.
  sideRLs_ind n.
Qed.

Lemma Incs_ws n m:
  segRLs tm (hRL^^(n+m+1)) (hRL^^(m+1)) (w'^^n) (w^^n).
Proof.
  induction n.
  - eapply segRLs_wall''; esx.
  - cbn[lpow].
    eapply segRLs_concat.
    2: apply IHn.
    applys_eq (Incs_w (n+m)); flia.
Qed.

Lemma RIncs2 n m:
  n+1<=m*2 ->
  sideRLs tm (hRL^^(m*1+2)) (dx*>w'^^(n)*>rh1) ((d++[1;0;0])*>w^^(n)*>1>>0>>dx*>w'^^(m*2-1-n)*>rh1).
Proof.
  intros.
  eapply segRLs_sideRLs_concat.
  1: apply (Incs_dx).
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws (n) (m*2+1-n)); flia.
  applys_eq (RIncs1 (m*2-1-n)); flia.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (3+n) ->
  S' (ls,rh1) -->+
  S' (Dd::ls,dx*>w'^^n*>rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1' ls i m n:
  P ls i m ->
  n+5<=m*2 ->
  S' (ls,dx*>w'^^n*>rh1) -->+
  S' (Dd::ls++Dd::[Dw]^^(1+n)++Dd::[Dw]^^((m-2)*2-1-n),rh1).
Proof.
  unfold P,S'.
  intros HP Hm.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    applys_eq (RIncs2 n (m-2)); flia.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep ls i n:
  P ls i n ->
  3<=n ->
  S' (ls,rh1) -->+
  S' ((((((Dd::Dd::ls)++[Dd])++[Dw]^^(n-2))++[Dd])++[Dw]^^(2^i*2+n-2)),rh1).
Proof.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep1 with (n:=n-3).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1'.
  1: apply HP.
  1: lia.
  repeat rewrite <-app_assoc.
  cbn[app].
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply P_Rws.
    1: apply P_Rd.
    1: apply P_Rws.
    1: do 5 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros [ls r] [Hr [i [n [I1 I2]]]].
  subst r.
  eexists (_,_); repeat split.
  + eapply BigStep; eauto 1.
  + eexists _,_; split.
    1:{
      apply P_Rws.
      1: apply P_Rd.
      1: apply P_Rws.
      1: apply P_Rd.
      do 2 apply P_Ld.
      1: apply I1.
      all: lia.
    }
    lia.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC0LB_1LD0RF_1LE---_1RA1RB_0RE1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[0;0;1]).
Notation hL := (B,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1;0;1;0;1].
Notation w := [0;1;1;0;1;0;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (1>>0>>1>>0inf).
Notation rh1 := (1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0;1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^3++[Dw]^^0,rh0).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(2+n)) rh1 (d*>w^^n*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>0>>1>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(1+n*2)) rh0 (w^^(n)*>0>>1>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (2+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (1+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 3 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-2).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1RC0RA_0RD0LC_1LE0RF_1LA---_0RA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[0;0;1]).
Notation hL := (C,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1;0;1;0;1].
Notation w := [0;1;1;0;1;0;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (1>>0>>1>>0inf).
Notation rh1 := (1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0;1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^3++[Dw]^^1,rh1).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(2+n)) rh1 (d*>w^^n*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>0>>1>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(1+n*2)) rh0 (w^^(n)*>0>>1>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (2+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (1+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 3 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-2).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1LC---_1RD1RE_1RE0RC_0RA0LE_0RC1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;0;1]).
Notation hL := (E,[0;0;1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1;0;1;0;1].
Notation w := [0;1;1;0;1;0;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+1)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n+1 ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (1>>0>>1>>0inf).
Notation rh1 := (1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0;1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^4++[Dw]^^2,rh0).
Proof.
  esx.
Qed.

Lemma RIncs1 n:
  sideRLs tm (hRL^^(2+n)) rh1 (d*>w^^n*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n*2)) rh0 (w^^(n)*>0>>1>>rh0).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(1+n*2)) rh0 (w^^(n)*>0>>1>>rh1).
Proof.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n:
  P ls i (2+n) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (1+n*2) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1) /\ exists i n, P ls i n /\ 3<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 4 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|Hr] [i [n [I1 I2]]]].
  - subst r.
    destruct (mod2 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - subst r.
    eexists (_,_); repeat split.
    + eapply BigStep1 with (n:=n-2).
      applys_eq I1; flia.
    + tauto.
    + eexists _,_; split.
      1:{
        apply P_Ld.
        apply P_Rws.
        1: apply P_Rd.
        1: apply I1.
        1,2: lia.
      }
      lia.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RE_0RA0RB_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR'' := (C,<[0;1;1;0;1;0;1]).
Notation hR' := (C,<[0;1;1;0;0;1]).
Notation hR := (E,<[0;1;1;0]).
Notation hL := (C,[0;1;0;1]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [1;1;0;1].
Notation w := [1;0;1;0;1].

Lemma LIncs i:
  segRLs tm hRL' (hRL^^(2^i-1)++hRL') (d^^i) (d^^i).
Proof.
  induction i.
  - esx.
  - cbn[Nat.pow].
    rewrite <-(Nat.add_1_r i).
    rewrite lpow_add.
    eapply segRLs_concat.
    1: apply IHi.
    replace (2*2^i-1) with ((2^i-1)*2+1) by lia.
    rewrite lpow_add,<-app_assoc.
    eapply @segRLs_trans with (w2:=d).
    2: esx.
    applys_eq (segRLs_addmul_v2 1 2 (2^i-1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL''++hRL^^(n+b)) (hRL^^a++hRL''++hRL^^b) (w^^n) (w^^n).
Proof.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  2: eapply segRLs_wall''; esx.
  clear.
  induction n.
  1: esx.
  cbn[lpow].
  rewrite app_assoc.
  eapply segRLs_concat.
  2: apply IHn.
  eapply segRLs_trans.
  2: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL''++hRL^^(1+b)) (hRL^^(a*2+1)++hRL''++hRL^^(b*2)) (d++w) (w++d).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: applys_eq (segRLs_addmul_v2 1 2 a 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  applys_eq (segRLs_addmul_v2 1 2 b 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL''++hRL^^(n+(1+b))) (hRL^^(a*2+1)++hRL''++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  apply Incs_dw.
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Definition P ls i n n0 :=
  forall c,
  segRLs tm (hRL''++hRL^^(c+n)) (hRL^^(2^i-1)++hRL''++hRL^^(c*2^i+n0)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 0 0.
Proof.
  unfold P.
  intros.
  rewrite app_assoc.
  rewrite Nat.mul_1_r.
  apply segRLs_nil.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 n c':
  P ls i m m0 ->
  n+1<=c'*2^i+m0 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0-(n+1))*2).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (2^i-1) ((c+c')*2^i+m0-(n+1)) n); flia.
Qed.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  rw_flat_map.
  rewrite IHls.
  unfold Rmp,Rmp'; st.
  simpl_rotate.
  reflexivity.
Qed.

Definition RC0 n := w^^n *> [1] *> 0inf.
Definition RC1 n := w^^n *> [1;0;1] *> 0inf.

Lemma RIncs0 k n:
  sideRLs tm (hRL^^(1+k*2)) (RC0 n) (RC1 (k+n)).
Proof.
  unfold RC0,RC1.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs1 k n:
  sideRLs tm (hRL^^(1+k*2)) (RC1 n) (RC0 (1+k+n)).
Proof.
  unfold RC0,RC1.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs0' k n:
  sideRLs tm (hRL''++hRL^^(n+(1+k))) (RC0 n) (w^^n*>w*>d*>RC0 k).
Proof.
  unfold RC0.
  eapply segRLs_sideRLs_concat.
  1: apply (Incs_ws 0).
  rewrite lpow_add.
  do 2 rewrite app_assoc.
  eapply sideRLs_trans.
  1: esx.
  sideRLs_ind k.
Qed.

Lemma RIncs1'_0 k n:
  sideRLs tm (hRL''++hRL^^(n+k*2)) (RC1 n) (RC0 (n+(1+k))).
Proof.
  unfold RC1,RC0.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply (Incs_ws 0).
  rewrite app_assoc.
  eapply sideRLs_trans.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs1'_1 k n:
  sideRLs tm (hRL''++hRL^^(n+k*2+1)) (RC1 n) (RC1 (n+(1+k))).
Proof.
  rewrite lpow_add,app_assoc.
  eapply sideRLs_trans.
  1: apply RIncs1'_0.
  unfold RC1,RC0.
  esx.
Qed.

Definition RC k ls (tp:bool) n :=
  d^^k *> w *> [1;0;1] *> (Rmp'^^^ls) *> (if tp then RC1 n else RC0 n).

Definition S' '(k,ls,tp,n) := 0inf <* <[1] {{{ (hR',R) }}} RC (k+1) ls tp n.

Lemma BigStep k ls tp n k' ls' tp' n':
  sideRLs tm hRL' (RC (k+1) ls tp n) (RC (k'+1) ls' tp' n') ->
  S' (k,ls,tp,n) -->+ S' (k',ls',tp',n').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL''++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL' (d^^(k+1) *> w *> [1;0;1] *> r) (d^^(k+1+1) *> w *> [1;0;1] *> r').
Proof.
  intros.
  remember (k+1) as k'.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  subst k'.
  rewrite Nat.pow_add_r.
  eapply sideRLs_trans.
  1:{
    remember (2^k*2-2) as v1.
    replace (2^k*2^1-1) with (1+v1) by lia.
    rewrite lpow_add.
    rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply H.
    eapply segRLs_trans.
    1: esx.
    eapply segRLs_wall''; esx.
  }
  esx.
Qed.

Lemma BigStep1 k ls n i m m0:
  P ls (S i) m m0 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2*2^i)+m0 in
  (2^i+n+2) <= v1 ->
  S' (k,ls,true,n) -->+
  S' (k+1,ls++[2^i+n],false,v1-(2^i+n+2)) /\
  P (ls++[2^i+n]) (S (S i)) (2^k*2-2) ((v1-(2^i+n+1))*2).
Proof.
  intros HP Hm Hv1 Hm'.
  split.
  2: {
    epose proof (P_S _ _ _ _ (2^i+n) (2^k*2-2-m) HP).
    applys_eq H; cbn[Nat.pow]; flia.
  }
  unfold P.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 (2^i-1) n); flia.
  unfold Rmp.
  do 2 rewrite Str_app_assoc.
  applys_eq (RIncs0' (1+((2^k*2-2-m)*(2*2^i)+m0-(2^i+n+2))) (2^i+n)); flia.
Qed.

Lemma RC0_w n:
  w *> RC0 n = RC0 (1+n).
Proof.
  reflexivity.
Qed.

Lemma RC1_w n:
  w *> RC1 n = RC1 (1+n).
Proof.
  reflexivity.
Qed.

Lemma BigStep0 k ls n i m m0:
  P ls (S i) m m0 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2*2^i)+m0 in
  (2^i-1+n) <= v1 ->
  S' (k,ls,false,n) -->+
  S' (k+1,ls,(v1-(2^i-1+n)) mod 2 =? 1,((2^i-1+n)+v1)/2) /\
  P ls (S i) m m0.
Proof.
  unfold P.
  intros HP Hm Hm'.
  split.
  2: apply HP.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  eapply sideRLs_trans.
  1: applys_eq (RIncs0 (2^i-1) n); flia.
  remember ((2^k*2-2-m)*(2*2^i)+m0) as v1.
  remember (2^i-1+n) as v2.
  destruct (Nat.eqb_spec ((v1-v2) mod 2) 1).
  - applys_eq (RIncs1'_1 ((v1-v2)/2) (v2)).
    1: flia.
    rewrite RC1_w.
    flia.
  - applys_eq (RIncs1'_0 ((v1-v2)/2) (v2)).
    1: flia.
    rewrite RC0_w.
    flia.
Qed.

Lemma init:
  c0 -->*
  S' (5,[8],false,20) /\
  P [8] 1 9 0.
Proof.
  split.
  1: esx.
  apply (P_S [] _ _ _ 8 9 P_O); lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,tp,n) => exists i m m0, P ls (S i) m m0 /\ m<=2^k*2-2 /\ 2^i+n+2<=(2^k*2-2-m)*(2*2^i)+m0 /\ True).
  2:{
    eexists _,_,_; repeat split.
    1: apply init.
    all: lia.
  }
  intros [[[k ls] []] n] [i [m [m0 [I1 [I2 [I3 I4]]]]]].
  - eexists (_,_,_,_); split.
    1: apply BigStep1.
    1: apply I1.
    1,2: lia.
    eexists _,_,_; split.
    + apply BigStep1.
      1: apply I1.
      1: apply I2.
      lia.
    + cbn[Nat.pow].
      rewrite Nat.pow_add_r.
      repeat split.
      1: lia.
      zify_pow2sub1; lia.
  - eexists (_,_,_,_); split.
    1: apply BigStep0.
    1: apply I1.
    1,2: lia.
    eexists _,_,_; split.
    + apply I1.
    + rewrite Nat.pow_add_r.
      repeat split.
      1: lia.
      replace (2^k*2^1*2-2-m) with ((2^k*2-2-m)+(2^k*2)) by lia.
      zify_pow2sub1; lia.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_1RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR'' := (A,<[0;1;1;0;1;0;1]).
Notation hR' := (A,<[0;1;1;0;0;1]).
Notation hR := (E,<[0;1;1;0]).
Notation hL := (A,[0;1;0;1]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [1;1;0;1].
Notation w := [1;0;1;0;1].

Lemma LIncs i:
  segRLs tm hRL' (hRL^^(2^i-1)++hRL') (d^^i) (d^^i).
Proof.
  induction i.
  - esx.
  - cbn[Nat.pow].
    rewrite <-(Nat.add_1_r i).
    rewrite lpow_add.
    eapply segRLs_concat.
    1: apply IHi.
    replace (2*2^i-1) with ((2^i-1)*2+1) by lia.
    rewrite lpow_add,<-app_assoc.
    eapply @segRLs_trans with (w2:=d).
    2: esx.
    applys_eq (segRLs_addmul_v2 1 2 (2^i-1) 0 0); unfold DH0.
    1,2: flia.
    1,2: esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL''++hRL^^(n+b)) (hRL^^a++hRL''++hRL^^b) (w^^n) (w^^n).
Proof.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  2: eapply segRLs_wall''; esx.
  clear.
  induction n.
  1: esx.
  cbn[lpow].
  rewrite app_assoc.
  eapply segRLs_concat.
  2: apply IHn.
  eapply segRLs_trans.
  2: eapply segRLs_wall''; esx.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL''++hRL^^(1+b)) (hRL^^(a*2+1)++hRL''++hRL^^(b*2)) (d++w) (w++d).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: applys_eq (segRLs_addmul_v2 1 2 a 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  applys_eq (segRLs_addmul_v2 1 2 b 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL''++hRL^^(n+(1+b))) (hRL^^(a*2+1)++hRL''++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  apply Incs_dw.
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Definition P ls i n n0 :=
  forall c,
  segRLs tm (hRL''++hRL^^(c+n)) (hRL^^(2^i-1)++hRL''++hRL^^(c*2^i+n0)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 0 0.
Proof.
  unfold P.
  intros.
  rewrite app_assoc.
  rewrite Nat.mul_1_r.
  apply segRLs_nil.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 n c':
  P ls i m m0 ->
  n+1<=c'*2^i+m0 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0-(n+1))*2).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (2^i-1) ((c+c')*2^i+m0-(n+1)) n); flia.
Qed.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  rw_flat_map.
  rewrite IHls.
  unfold Rmp,Rmp'; st.
  simpl_rotate.
  reflexivity.
Qed.

Definition RC0 n := w^^n *> [1] *> 0inf.
Definition RC1 n := w^^n *> [1;0;1] *> 0inf.

Lemma RIncs0 k n:
  sideRLs tm (hRL^^(1+k*2)) (RC0 n) (RC1 (k+n)).
Proof.
  unfold RC0,RC1.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs1 k n:
  sideRLs tm (hRL^^(1+k*2)) (RC1 n) (RC0 (1+k+n)).
Proof.
  unfold RC0,RC1.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs0' k n:
  sideRLs tm (hRL''++hRL^^(n+(1+k))) (RC0 n) (w^^n*>w*>d*>RC0 k).
Proof.
  unfold RC0.
  eapply segRLs_sideRLs_concat.
  1: apply (Incs_ws 0).
  rewrite lpow_add.
  do 2 rewrite app_assoc.
  eapply sideRLs_trans.
  1: esx.
  sideRLs_ind k.
Qed.

Lemma RIncs1'_0 k n:
  sideRLs tm (hRL''++hRL^^(n+k*2)) (RC1 n) (RC0 (n+(1+k))).
Proof.
  unfold RC1,RC0.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: apply (Incs_ws 0).
  rewrite app_assoc.
  eapply sideRLs_trans.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind k.
Qed.

Lemma RIncs1'_1 k n:
  sideRLs tm (hRL''++hRL^^(n+k*2+1)) (RC1 n) (RC1 (n+(1+k))).
Proof.
  rewrite lpow_add,app_assoc.
  eapply sideRLs_trans.
  1: apply RIncs1'_0.
  unfold RC1,RC0.
  esx.
Qed.

Definition RC k ls (tp:bool) n :=
  d^^k *> w *> [1;0;1] *> (Rmp'^^^ls) *> (if tp then RC1 n else RC0 n).

Definition S' '(k,ls,tp,n) := 0inf <* <[1] {{{ (hR',R) }}} RC (k+1) ls tp n.

Lemma BigStep k ls tp n k' ls' tp' n':
  sideRLs tm hRL' (RC (k+1) ls tp n) (RC (k'+1) ls' tp' n') ->
  S' (k,ls,tp,n) -->+ S' (k',ls',tp',n').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL''++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL' (d^^(k+1) *> w *> [1;0;1] *> r) (d^^(k+1+1) *> w *> [1;0;1] *> r').
Proof.
  intros.
  remember (k+1) as k'.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  subst k'.
  rewrite Nat.pow_add_r.
  eapply sideRLs_trans.
  1:{
    remember (2^k*2-2) as v1.
    replace (2^k*2^1-1) with (1+v1) by lia.
    rewrite lpow_add.
    rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: apply H.
    eapply segRLs_trans.
    1: esx.
    eapply segRLs_wall''; esx.
  }
  esx.
Qed.

Lemma BigStep1 k ls n i m m0:
  P ls (S i) m m0 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2*2^i)+m0 in
  (2^i+n+2) <= v1 ->
  S' (k,ls,true,n) -->+
  S' (k+1,ls++[2^i+n],false,v1-(2^i+n+2)) /\
  P (ls++[2^i+n]) (S (S i)) (2^k*2-2) ((v1-(2^i+n+1))*2).
Proof.
  intros HP Hm Hv1 Hm'.
  split.
  2: {
    epose proof (P_S _ _ _ _ (2^i+n) (2^k*2-2-m) HP).
    applys_eq H; cbn[Nat.pow]; flia.
  }
  unfold P.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 (2^i-1) n); flia.
  unfold Rmp.
  do 2 rewrite Str_app_assoc.
  applys_eq (RIncs0' (1+((2^k*2-2-m)*(2*2^i)+m0-(2^i+n+2))) (2^i+n)); flia.
Qed.

Lemma RC0_w n:
  w *> RC0 n = RC0 (1+n).
Proof.
  reflexivity.
Qed.

Lemma RC1_w n:
  w *> RC1 n = RC1 (1+n).
Proof.
  reflexivity.
Qed.

Lemma BigStep0 k ls n i m m0:
  P ls (S i) m m0 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2*2^i)+m0 in
  (2^i-1+n) <= v1 ->
  S' (k,ls,false,n) -->+
  S' (k+1,ls,(v1-(2^i-1+n)) mod 2 =? 1,((2^i-1+n)+v1)/2) /\
  P ls (S i) m m0.
Proof.
  unfold P.
  intros HP Hm Hm'.
  split.
  2: apply HP.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  eapply sideRLs_trans.
  1: applys_eq (RIncs0 (2^i-1) n); flia.
  remember ((2^k*2-2-m)*(2*2^i)+m0) as v1.
  remember (2^i-1+n) as v2.
  destruct (Nat.eqb_spec ((v1-v2) mod 2) 1).
  - applys_eq (RIncs1'_1 ((v1-v2)/2) (v2)).
    1: flia.
    rewrite RC1_w.
    flia.
  - applys_eq (RIncs1'_0 ((v1-v2)/2) (v2)).
    1: flia.
    rewrite RC0_w.
    flia.
Qed.

Lemma init:
  c0 -->*
  S' (4,[O],false,15) /\
  P [O] 1 1 0.
Proof.
  split.
  1: esx.
  apply (P_S [] _ _ _ 0 1 P_O); lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,tp,n) => exists i m m0, P ls (S i) m m0 /\ m<=2^k*2-2 /\ 2^i+n+2<=(2^k*2-2-m)*(2*2^i)+m0 /\ True).
  2:{
    eexists _,_,_; repeat split.
    1: apply init.
    all: lia.
  }
  intros [[[k ls] []] n] [i [m [m0 [I1 [I2 [I3 I4]]]]]].
  - eexists (_,_,_,_); split.
    1: apply BigStep1.
    1: apply I1.
    1,2: lia.
    eexists _,_,_; split.
    + apply BigStep1.
      1: apply I1.
      1: apply I2.
      lia.
    + cbn[Nat.pow].
      rewrite Nat.pow_add_r.
      repeat split.
      1: lia.
      zify_pow2sub1; lia.
  - eexists (_,_,_,_); split.
    1: apply BigStep0.
    1: apply I1.
    1,2: lia.
    eexists _,_,_; split.
    + apply I1.
    + rewrite Nat.pow_add_r.
      repeat split.
      1: lia.
      replace (2^k*2^1*2-2-m) with ((2^k*2-2-m)+(2^k*2)) by lia.
      zify_pow2sub1; lia.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0LD_1RA0RE_1LB1RA_1RF0RD_---0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;1;1;1].
Notation d := [1;1;1;1].
Notation w' := [0;1;0;1;1].
Notation w := [1;1;0;1;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 1 >> r =
  1 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n*2 ->
  P (ls++[Dw]^^n) i (c-n*2).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (1>>0inf).
Notation rh1 := (0>>1>>1>>1>>0inf).
Notation rh2 := (0>>1>>0>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^4++[Dw]^^2,rh1).
Proof.
  esx.
Qed.

Ltac solve_v1 n :=
  eapply sideRLs_trans_add; [solve[esx]|];
  rewrite lpow_mul;
  sideRLs_ind n.

Lemma RIncs0_0 n:
  sideRLs tm (hRL^^(1+n*3)) rh0 (w^^(n)*>1>>1>>rh0).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(2+n*3)) rh0 (w^^(n)*>1>>1>>rh1).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs0_2 n:
  sideRLs tm (hRL^^(3+n*3)) rh0 (w^^(n)*>1>>1>>rh2).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs2_0 n:
  sideRLs tm (hRL^^(2+n*3)) rh2 (w^^(n)*>1>>1>>rh2).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs2_1 n:
  sideRLs tm (hRL^^(3+n*3)) rh2 (w^^(1+n)*>1>>1>>rh0).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs2_2 n:
  sideRLs tm (hRL^^(4+n*3)) rh2 (w^^(1+n)*>1>>1>>rh1).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs1_0 n:
  sideRLs tm (hRL^^(2+n*3)) rh1 (d*>w^^(n*2)*>1>>1>>rh0).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs1_1 n:
  sideRLs tm (hRL^^(3+n*3)) rh1 (d*>w^^(n*2)*>1>>1>>rh2).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs1_2 n:
  sideRLs tm (hRL^^(4+n*3)) rh1 (d*>w^^(1+n*2)*>1>>1>>rh1).
Proof.
  solve_v1 n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep0_0 ls i n:
  P ls i (1+n*3) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (2+n*3) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_2 ls i n:
  P ls i (3+n*3) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh2).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_2.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep2_0 ls i n:
  P ls i (2+n*3) ->
  S' (ls,rh2) -->+
  S' (Dd::ls++[Dw]^^n,rh2).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs2_0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep2_1 ls i n:
  P ls i (3+n*3) ->
  S' (ls,rh2) -->+
  S' (Dd::ls++[Dw]^^(1+n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs2_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep2_2 ls i n:
  P ls i (4+n*3) ->
  S' (ls,rh2) -->+
  S' (Dd::ls++[Dw]^^(1+n),rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs2_2.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1_0 ls i n:
  P ls i (2+n*3) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^(n*2)),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1_0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1_1 ls i n:
  P ls i (3+n*3) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^(n*2)),rh2).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1_2 ls i n:
  P ls i (4+n*3) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^(1+n*2)),rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1_2.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1\/r=rh2) /\ exists i n, P ls i n /\ 2<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    1: apply (P_Rws).
    1: do 4 apply P_Ld.
    1: apply P_O.
    1,2: lia.
  }
  intros [ls r] [[Hr|[Hr|Hr]] [i [n [I1 I2]]]]; subst r.
  - destruct (mod3 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0_2 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_0 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - destruct (mod3 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep1_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply P_Rd.
          1: apply I1.
          all: lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep1_2 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply P_Rd.
          1: apply I1.
          all: lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep1_0 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply P_Rd.
          1: apply I1.
          all: lia.
        }
        lia.
  - destruct (mod3 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep2_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep2_2 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep2_0 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RA_1RB0LD_1LC1RB_1RF0RD_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[1]).
Notation hL := (D,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation d' := [1;1;1;1].
Notation d := [1;1;1;1].
Notation w' := [0;1;0;1;1].
Notation w := [1;1;0;1;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 1 >> r =
  1 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+2)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  eapply @segRLs_wall with (w':=[]).
  1,2: solve_seg.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=2 ->
  P (ls++[Dw]) i (c-2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-2)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n*2 ->
  P (ls++[Dw]^^n) i (c-n*2).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (1>>0inf).
Notation rh1 := (0>>1>>1>>1>>0inf).
Notation rh2 := (0>>1>>0>>1>>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma init:
  c0 -->* S' ([Dd]^^5++[Dw]++[Dd]++[Dw]^^8,rh0).
Proof.
  esx.
Qed.

Ltac solve_v1 n :=
  eapply sideRLs_trans_add; [solve[esx]|];
  rewrite lpow_mul;
  sideRLs_ind n.

Lemma RIncs0_0 n:
  sideRLs tm (hRL^^(1+n*3)) rh0 (w^^(n)*>1>>1>>rh0).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs0_1 n:
  sideRLs tm (hRL^^(2+n*3)) rh0 (w^^(n)*>1>>1>>rh1).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs0_2 n:
  sideRLs tm (hRL^^(3+n*3)) rh0 (w^^(n)*>1>>1>>rh2).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs2_0 n:
  sideRLs tm (hRL^^(2+n*3)) rh2 (w^^(n)*>1>>1>>rh2).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs2_1 n:
  sideRLs tm (hRL^^(3+n*3)) rh2 (w^^(1+n)*>1>>1>>rh0).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs2_2 n:
  sideRLs tm (hRL^^(4+n*3)) rh2 (w^^(1+n)*>1>>1>>rh1).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs1_0 n:
  sideRLs tm (hRL^^(2+n*3)) rh1 (d*>w^^(n*2)*>1>>1>>rh0).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs1_1 n:
  sideRLs tm (hRL^^(3+n*3)) rh1 (d*>w^^(n*2)*>1>>1>>rh2).
Proof.
  solve_v1 n.
Qed.

Lemma RIncs1_2 n:
  sideRLs tm (hRL^^(4+n*3)) rh1 (d*>w^^(1+n*2)*>1>>1>>rh1).
Proof.
  solve_v1 n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep0_0 ls i n:
  P ls i (1+n*3) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_1 ls i n:
  P ls i (2+n*3) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep0_2 ls i n:
  P ls i (3+n*3) ->
  S' (ls,rh0) -->+
  S' (Dd::ls++[Dw]^^n,rh2).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs0_2.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep2_0 ls i n:
  P ls i (2+n*3) ->
  S' (ls,rh2) -->+
  S' (Dd::ls++[Dw]^^n,rh2).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs2_0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep2_1 ls i n:
  P ls i (3+n*3) ->
  S' (ls,rh2) -->+
  S' (Dd::ls++[Dw]^^(1+n),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs2_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep2_2 ls i n:
  P ls i (4+n*3) ->
  S' (ls,rh2) -->+
  S' (Dd::ls++[Dw]^^(1+n),rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs2_2.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  simpl_rotate.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1_0 ls i n:
  P ls i (2+n*3) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^(n*2)),rh0).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1_0.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1_1 ls i n:
  P ls i (3+n*3) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^(n*2)),rh2).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1_1.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma BigStep1_2 ls i n:
  P ls i (4+n*3) ->
  S' (ls,rh1) -->+
  S' (Dd::((ls++[Dd])++[Dw]^^(1+n*2)),rh1).
Proof.
  unfold P,S'.
  intros HP.
  eassert (I1:_). {
    eapply segRLs_sideRLs_concat.
    1: apply (HP O).
    apply RIncs1_2.
  }
  eapply sideRLs_1 in I1.
  follow10 I1. clear I1 HP.
  cbn.
  rewrite Rshift.
  rw_flat_map.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,r) => (r=rh0\/r=rh1\/r=rh2) /\ exists i n, P ls i n /\ 2<=n).
  2: {
    split.
    1: tauto.
    eexists _,_; split.
    repeat rewrite app_assoc.
    1: apply (P_Rws).
    1: apply (P_Rd).
    1: apply (P_Rw).
    1: do 5 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros [ls r] [[Hr|[Hr|Hr]] [i [n [I1 I2]]]]; subst r.
  - destruct (mod3 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep0_2 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_0 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep0_1 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
  - destruct (mod3 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep1_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply P_Rd.
          1: apply I1.
          all: lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep1_2 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply P_Rd.
          1: apply I1.
          all: lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep1_0 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply P_Rd.
          1: apply I1.
          all: lia.
        }
        lia.
  - destruct (mod3 n); subst n.
    + eexists (_,_); repeat split.
      * eapply BigStep2_1 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep2_2 with (n:=a-1).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
    + eexists (_,_); repeat split.
      * eapply BigStep2_0 with (n:=a).
        applys_eq I1; flia.
      * tauto.
      * eexists _,_; split.
        1:{
          apply P_Ld.
          apply P_Rws.
          1: apply I1.
          lia.
        }
        lia.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC0LE_1RD1RF_1LB0RA_0LA1LB_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (B,<[0;1]).
Notation hR := (D,[]).
Notation hL := (B,[]).
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [1;0;1;0;0;1;0;0;0].
Notation w := [1;0;0;0].

Lemma Incs_d n:
  segRLs tm (hRL^^n++hRL'++hRL) (hRL^^(n*2+2)++hRL'++hRL) d d.
Proof.
  rewrite lpow_add,<-app_assoc.
  eapply segRLs_trans.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  all: esx.
Qed.

Lemma LIncs n:
  segRLs tm hRL' (hRL^^(2^n*2-2)++hRL'++hRL) (d++[1;0]++d^^n) (d++[1;0]++d^^n).
Proof.
  induction n.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r n).
  rewrite lpow_add.
  repeat rewrite app_assoc in *.
  eapply segRLs_concat.
  1: apply IHn.
  repeat rewrite <-app_assoc.
  applys_eq (Incs_d (2^n*2-2)); flia.
Qed.

Definition RC a b := w^^a *> [0] *> w^^b *> 0inf.

Lemma RIncs0 a b:
  sideRLs tm (hRL^^(b*2)) (RC a b) (RC (b+a) 0).
Proof.
  unfold RC.
  gen a.
  rewrite lpow_mul.
  induction b; intros.
  1: esx.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHb (S a)); flia.
  esx.
Qed.

Lemma RIncs1 k a:
  sideRLs tm (hRL^^k) (RC a 0) (RC (k+a) 0).
Proof.
  unfold RC.
  sideRLs_ind k.
Qed.

Lemma RIncs b k:
  sideRLs tm (hRL^^((2+b)*2+k)++hRL'++hRL) (RC 1 (2+b)) (d *> RC 1 (k+b)).
Proof.
  eapply sideRLs_trans.
  1: eapply sideRLs_trans_add.
  1: apply RIncs0.
  1: apply RIncs1.
  unfold RC.
  esx.
Qed.

Definition RC' i b := (d++[1;0]++d^^i) *> RC 1 b.

Lemma RIncs' i b:
  2<=b<=2^i-1 ->
  sideRLs tm (hRL'++[]) (RC' i b) (RC' (i+1) (2^i*2-4-b)).
Proof.
  intros Hb.
  unfold RC'.
  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  1: applys_eq (RIncs (b-2) (2^i*2-2-b*2)); flia.
  st.
  applys_eq sideRLseq_O; flia.
Qed.

Definition S' '(i,b) := 0inf <* <[1;1;0;1] {{{ (hR',R) }}} RC' i b.

Lemma BigStep i b:
  2<=b<=2^i-1 ->
  S' (i,b) -->+
  S' (i+1,2^i*2-4-b).
Proof.
  intros.
  eapply RIncs',sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (4,10)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,b) => 2<=b<=2^i-3).
  2: lia.
  intros [i b] HP.
  eexists; split.
  1: apply BigStep; lia.
  cbn.
  rewrite Nat.pow_add_r.
  lia.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RE_0RA0LD_0LE1LC_1RC1LE_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR' := (C,<[0;1]).
Notation hR := (B,[]).
Notation hL := (C,[]).
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [1;0;1;0;0;1;0;0;0].
Notation d' := [1;0;1;0;0].
Notation w := [1;0;0;0].

Lemma Incs_d n m:
  segRLs tm (hRL^^n++hRL'++hRL^^(1+m)) (hRL^^(n*2+2)++hRL'++hRL^^(1+m*2)) d d.
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  1: applys_eq (segRLs_addmul_v2 1 2 m 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Notation dx := (d++[1;0]++d'^^2).

Lemma LIncs n:
  segRLs tm hRL' (hRL^^(2^n*2-2)++hRL'++hRL^^(1+2^n*5)) (dx++d^^n) (dx++d^^n).
Proof.
  induction n.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r n).
  rewrite (lpow_add _ n).
  repeat rewrite app_assoc in *.
  eapply segRLs_concat.
  1: apply IHn.
  repeat rewrite <-app_assoc.
  applys_eq (Incs_d (2^n*2-2)); flia.
Qed.

Definition RC a b := w^^a *> [0] *> w^^b *> 0inf.

Lemma RIncs0 a b:
  sideRLs tm (hRL^^(b*2)) (RC a b) (RC (b+a) 0).
Proof.
  unfold RC.
  gen a.
  rewrite lpow_mul.
  induction b; intros.
  1: esx.
  cbn[lpow].
  eapply sideRLs_trans.
  2: applys_eq (IHb (S a)); flia.
  esx.
Qed.

Lemma RIncs1 k a:
  sideRLs tm (hRL^^k) (RC a 0) (RC (k+a) 0).
Proof.
  unfold RC.
  sideRLs_ind k.
Qed.

Lemma ROv b:
  sideRLs tm (hRL'++hRL) (RC (3+b) 0) (d *> RC 1 b).
Proof.
  unfold RC.
  esx.
Qed.

Lemma RIncs a b k:
  sideRLs tm (hRL^^(3+a)++hRL'++hRL^^(1+(a+b+k))) (RC b 0) (d*>RC (k*2+(a+b+1)) 0).
Proof.
  eapply sideRLs_trans.
  1: apply RIncs1.
  rewrite lpow_add,app_assoc.
  eapply sideRLs_trans.
  1: apply (ROv (a+b)).
  eapply segRLs_sideRLs_concat.
  1: applys_eq (segRLs_addmul_v2 1 2 (a+b+k) 0 0); unfold DH0.
  1: flia.
  1,2: esx.
  replace ((a+b+k)*2+0) with ((a+b)*2+k*2) by lia.
  eapply sideRLs_trans_add.
  1: apply RIncs0.
  apply RIncs1.
Qed.

Definition RC' i b := (dx++d^^i) *> RC b 0.

Lemma RIncs' i b:
  5<=2^i*2 /\ b<=2^i*3+5 ->
  sideRLs tm (hRL'++[]) (RC' i b) (RC' (i+1) (2^i*8+6-b)).
Proof.
  intros Hb.
  unfold RC'.
  eapply sideRLs_trans.
  1: eapply segRLs_sideRLs_concat.
  1: apply LIncs.
  1: applys_eq (RIncs (2^i*2-5) b (2^i*3+5-b)); flia.
  st.
  applys_eq sideRLseq_O; flia.
Qed.

Definition S' '(i,b) := 0inf <* <[1;1;0;1] {{{ (hR',R) }}} RC' i b.

Lemma BigStep i b:
  5<=2^i*2 /\ b<=2^i*3+5 ->
  S' (i,b) -->+
  S' (i+1,2^i*8+6-b).
Proof.
  intros.
  eapply RIncs',sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2,14)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=fun '(i,b) => 5<=2^i*2 /\ 2^i*2+1<=b<=2^i*3+5).
  2: lia.
  intros [i b] HP.
  eexists; split.
  1: apply BigStep; lia.
  cbn.
  rewrite Nat.pow_add_r.
  lia.
Qed.

End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC---_1RD0LF_0RE1LD_0LA1RF_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hL := (F,[0]).
Notation hRL1 := [(hR,hL)].
Notation hRL := [(hR,hL);(hR,hL)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1].
Notation w := [0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := ([1;0;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} d *> (Rmp'^^^ls) *> r.

Notation dx := [1;0;0;1].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(3+n)) rh0 (0>>1>>dx*>w^^n*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(1+n)) (dx*>w^^n0*>0>>1>>rh0) (d*>w^^(n0+n*2)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep' ls r ls' r':
  sideRLs tm hRL (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  eassert (I1:_). {
    eapply @segRLs_sideRLs_concat with (ls1:=hRL1) (w1:=d).
    2: apply H.
    esx.
  }
  eapply sideRLs_1 in I1.
  follow10 I1.
  rewrite Rshift.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (3+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^n*>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (1+n) ->
  S' (ls,dx*>w^^n0*>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]^^(n0+n*2),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  3<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]^^(2^i*2+n*3-5)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-3)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i-1+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^5++[Dw]^^4++[Dd]++[Dw]++[Dd]++[Dw]^^49).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 3<=n<=2^i*4+2).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_assoc.
    1: apply P_Rws.
    1: apply P_Rd.
    1: apply P_Rw.
    1: apply P_Rd.
    1: apply P_Rws.
    1: do 5 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB1RF_0LB1LC_1LD0RA_0LE---_1RA0LF_0RC1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hL := (F,[0]).
Notation hRL1 := [(hR,hL)].
Notation hRL := [(hR,hL);(hR,hL)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1].
Notation w := [0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := ([1;0;1;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} d *> (Rmp'^^^ls) *> r.

Notation dx := [1;0;0;1].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(4+n)) rh0 (0>>1>>dx*>w^^n*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(1+n)) (dx*>w^^n0*>0>>1>>rh0) (d*>w^^(n0+n*2)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep' ls r ls' r':
  sideRLs tm hRL (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  eassert (I1:_). {
    eapply @segRLs_sideRLs_concat with (ls1:=hRL1) (w1:=d).
    2: apply H.
    esx.
  }
  eapply sideRLs_1 in I1.
  follow10 I1.
  rewrite Rshift.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (4+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^n*>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (1+n) ->
  S' (ls,dx*>w^^n0*>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]^^(n0+n*2),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  4<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]^^(2^i*2+n*3-6)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-4)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i-1+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^5++[Dw]^^14).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 4<=n<=2^i*4+1).
  2: {
    eexists _,_; split.
    1: apply P_Rws.
    1: do 5 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1RD_0RD1LE_0RE1RF_1LF0RB_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,[1]).
Notation hL := (D,[0]).
Notation hRL1 := [(hR,hL)].
Notation hRL := [(hR,hL);(hR,hL)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1].
Notation w := [0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := ([1;0;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} d *> (Rmp'^^^ls) *> r.

Notation dx := [1;0;0;1].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n)) rh0 (0>>1>>dx*>w^^(n*2)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(1+n)) (dx*>w^^n0*>0>>1>>rh0) (d*>w^^(n0+n*4)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep' ls r ls' r':
  sideRLs tm hRL (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  eassert (I1:_). {
    eapply @segRLs_sideRLs_concat with (ls1:=hRL1) (w1:=d).
    2: apply H.
    esx.
  }
  eapply sideRLs_1 in I1.
  follow10 I1.
  rewrite Rshift.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^(n*2)*>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (1+n) ->
  S' (ls,dx*>w^^n0*>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]^^(n0+n*4),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  2<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]^^(2^i*4+n*6-8)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-2)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i-1+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^3++[Dw]++[Dd]++[Dw]^^7).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 2<=n /\ n*2<=2^i+3).
  2: {
    eexists _,_; split.
    repeat rewrite app_assoc.
    1: apply P_Rws.
    1: apply P_Rd.
    1: apply P_Rw.
    1: do 3 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM19.


Module TM20.

Definition tm := Eval compute in (TM_from_str "1RB1RC_0RC1LD_0RD1RE_1LE0RA_0LF---_1RA0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[1]).
Notation hL := (C,[0]).
Notation hRL1 := [(hR,hL)].
Notation hRL := [(hR,hL);(hR,hL)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1].
Notation w := [0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := ([1;0;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} d *> (Rmp'^^^ls) *> r.

Notation dx := [1;0;0;1].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n)) rh0 (0>>1>>dx*>w^^(n*2)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(1+n)) (dx*>w^^n0*>0>>1>>rh0) (d*>w^^(n0+n*4)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep' ls r ls' r':
  sideRLs tm hRL (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  eassert (I1:_). {
    eapply @segRLs_sideRLs_concat with (ls1:=hRL1) (w1:=d).
    2: apply H.
    esx.
  }
  eapply sideRLs_1 in I1.
  follow10 I1.
  rewrite Rshift.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^(n*2)*>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (1+n) ->
  S' (ls,dx*>w^^n0*>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]^^(n0+n*4),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  2<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]^^(2^i*4+n*6-8)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-2)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i-1+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^2++[Dw]^^1).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 2<=n /\ n*2<=2^i+3).
  2: {
    eexists _,_; split.
    repeat rewrite app_assoc.
    1: apply P_Rws.
    1: do 2 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM20.


Module TM21.

Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC---_1RD0LF_1RE1RF_0RF1LA_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hL := (F,[0]).
Notation hRL1 := [(hR,hL)].
Notation hRL := [(hR,hL);(hR,hL)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1].
Notation w := [0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: apply Incs_d.
  cbn[Nat.pow].
  applys_eq (H (n*2+1)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := ([1;0;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} d *> (Rmp'^^^ls) *> r.

Notation dx := [1;0;0;1].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(2+n)) rh0 (0>>1>>dx*>w^^(n*2)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(1+n)) (dx*>w^^n0*>0>>1>>rh0) (d*>w^^(n0+n*4)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep' ls r ls' r':
  sideRLs tm hRL (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  eassert (I1:_). {
    eapply @segRLs_sideRLs_concat with (ls1:=hRL1) (w1:=d).
    2: apply H.
    esx.
  }
  eapply sideRLs_1 in I1.
  follow10 I1.
  rewrite Rshift.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i (2+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^(n*2)*>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (1+n) ->
  S' (ls,dx*>w^^n0*>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]^^(n0+n*4),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  2<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]^^(2^i*4+n*6-8)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-2)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i-1+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^2++[Dw]++[Dd]++[Dw]).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 2<=n /\ n*2<=2^i+3).
  2: {
    eexists _,_; split.
    repeat rewrite app_assoc.
    1: apply P_Rw.
    1: apply P_Rd.
    1: apply P_Rw.
    1: do 2 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM21.


Module TM22.

Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC---_1RD0LF_1RE1RF_0LE1LA_0RA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hL := (F,[0]).
Notation hRL1 := [(hR,hL)].
Notation hRL := [(hR,hL);(hR,hL)].
Notation d' := [0;1;0;1].
Notation d := [0;1;0;1].
Notation w' := [1;0;1].
Notation w := [0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> r =
  0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+8)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 8.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i*8+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: applys_eq (Incs_d (n+7)); flia.
  cbn[Nat.pow].
  applys_eq (H (n*2+8)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := ([1;0;1;1]*>0inf).

Notation ldh := (d^^2++[0;1;0]++d++[0;1;0]++d).
Notation ldh' := (d^^2++[0;0;1]++d++[0;0;1]++d).

Lemma Incs_ldh:
  segRLs tm hRL1 (hRL^^8) ldh ldh'.
Proof.
  esx.
Qed.

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} ldh *> (Rmp'^^^ls) *> r.

Notation dx := [1;0;0;1].

Lemma RIncs0 n:
  sideRLs tm (hRL^^(4+n)) rh0 (0>>1>>dx*>w^^n*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(1+n)) (dx*>w^^n0*>0>>1>>rh0) (d*>w^^(n0+n*2)*>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep' ls r ls' r':
  sideRLs tm (hRL^^8) (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  eassert (I1:_). {
    eapply @segRLs_sideRLs_concat.
    1: apply Incs_ldh.
    apply H.
  }
  eapply sideRLs_1 in I1.
  follow10 I1.
  rewrite Rshift.
  es.
Qed.

Lemma BigStep0 ls i n:
  P ls i n ->
  4<=n ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^(n-4)*>0>>1>>rh0).
Proof.
  intros HP Hn.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  applys_eq (RIncs0 (n-4)); flia.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i n ->
  1<=n ->
  S' (ls,dx*>w^^n0*>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]^^(n0+(n-1)*2),rh0).
Proof.
  intros HP Hn.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  applys_eq (RIncs1 (n-1)); flia.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  4<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]^^(2^i*16+n*3-6)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0.
  1: apply HP.
  1: lia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1.
  1: apply HP.
  1: lia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^2++[Dw]++[Dd]++[Dw]^^31).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 4<=n<=2^i*32+2).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_comm_cons.
    1: repeat rewrite app_assoc.
    1: apply P_Rws.
    1: apply P_Rd.
    1: apply P_Rw.
    1: do 2 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM22.


Module TM23.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RA_0LA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[1]).
Notation hR' := (A,<[1;1]).
Notation hR'' := (B,<[1;0;0]).
Notation hL := (B,[0]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [0;1;0;1].
Notation w := [0;0;1].

Goal segRLs tm (hRL'++hRL^^2) (hRL++hRL') w w.
Proof. esx. Qed.

Goal segRLs tm (hRL'++hRL^^2) (hRL'') d w.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL') w d.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL''++hRL) d d.
Proof. esx. Qed.

Lemma Incs_w_0 n:
  segRLs tm (hRL^^n) (hRL^^n) w w.
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma Incs_w a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a+1)++hRL'++hRL^^b) w w.
Proof.
  do 2 rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+b)) (hRL^^(a+n)++hRL'++hRL^^b) (w^^n) (w^^n).
Proof.
  gen a b.
  induction n; intros.
  - rewrite Nat.add_0_r.
    apply segRLs_nil.
  - cbn[lpow].
    eapply segRLs_concat.
    2: applys_eq (IHn (S a) b); flia.
    applys_eq (Incs_w a (n*2+b)); flia.
Qed.

Lemma Incs_d_0 n:
  segRLs tm (hRL^^n) (hRL^^(n*2)) d d.
Proof.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_d a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^(a*2)++hRL''++hRL^^(1+b*2)) d d.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  apply Incs_d_0.
Qed.

Lemma Incs_ds i:
  segRLs tm hRL'' (hRL''++hRL^^(2^i-1)) (d^^i) (d^^i).
Proof.
  induction i.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r i),lpow_add.
  eapply segRLs_concat.
  1: apply IHi.
  applys_eq (Incs_d 0 (2^i-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma Incs_wd a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^a++hRL'++hRL^^(b*2)) w d.
Proof.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  eapply segRLs_trans.
  2: apply Incs_d_0.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a*2)++hRL''++hRL^^b) d w.
Proof.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+(2+b))) (hRL^^((a+n)*2)++hRL'++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  eapply segRLs_concat.
  1: apply Incs_dw.
  apply Incs_wd.
Qed.

Lemma Incs_dsw i:
  segRLs tm hRL'' (hRL'++hRL^^((2^i-1)*2)) (d^^i++w) (d^^i++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ds.
  apply (Incs_wd 0).
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  unfold Rmp,Rmp' in *.
  cbn in *.
  st.
  rewrite IHls.
  st; simpl_rotate; reflexivity.
Qed.

Definition P ls i n n0 n1 :=
  forall c,
  segRLs tm (hRL'++hRL^^(c+n)) (hRL^^(n1*2)++hRL'++hRL^^(c*2^i+n0*2)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 0 0 0.
Proof.
  unfold P.
  intros.
  rewrite app_assoc.
  rewrite Nat.mul_1_r.
  apply segRLs_nil.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 m1 n c':
  P ls i m m0 m1 ->
  n*2+2<=c'*2^i+m0*2 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0*2-(n*2+2))) (m1*2+n).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (m1*2) ((c+c')*2^i+m0*2-(n*2+2)) n); flia.
Qed.

Definition RC0 a b := w^^a *> [0] *> w^^b *> 0inf.

Lemma RIncs0 a b n:
  sideRLs tm (hRL^^(n*2)) (RC0 a (1+b)) (RC0 (n+a) (1+b)).
Proof.
  unfold RC0.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_0 a n:
  sideRLs tm (hRL^^(n)) (RC0 a 0) (RC0 (n+a) 0).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 a b c := w^^a *> [0] *> w^^b *> [1] *> w^^c *> 0inf.

Lemma ROv0 a b:
  sideRLs tm (hRL') (RC0 a (1+b)) (RC1 0 (1+a) b).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma RIncs1 a b c:
  sideRLs tm (hRL^^(b*4)) (RC1 a (1+b) c) (RC1 (b*2+a) 1 c).
Proof.
  gen a.
  induction b; intros.
  1: esx.
  cbn[Nat.mul].
  eapply sideRLs_trans_add.
  2: applys_eq (IHb (2+a)); flia.
  unfold RC1.
  esx.
Qed.

Lemma ROv1 a c:
  sideRLs tm (hRL^^4) (RC1 a 1 (2+c)) (w^^(2+a)*>d*>RC0 0 (1+c)).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma ROv0_0 a:
  sideRLs tm (hRL') (RC0 a 0) (RC0 0 (1+a)).
Proof.
  unfold RC0.
  esx.
Qed.

Lemma ROv1_0 a:
  sideRLs tm (hRL^^2) (RC1 a 1 0) (RC0 (1+a) 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma ROv1_1 a:
  sideRLs tm (hRL^^4) (RC1 a 1 1) (w^^(2+a)*>d*>RC0 1 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma Incs_ws_0 n m:
  segRLs tm (hRL^^n) (hRL^^n) (w^^m) (w^^m).
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma RIncs a b n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(4+m))) (RC0 a (3+b)) (w^^(2+((n+a)*2+0))*>d*>RC0 m (1+b)).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ (2+b)).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ws_0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_d_0.
  applys_eq (RIncs0 0); flia.
Qed.

Lemma RIncs_1 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(2+m))) (RC0 a 1) (RC0 (1+(n+a)*2+m) 0).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ 0).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1_0.
  applys_eq RIncs0_0; flia.
Qed.

Lemma RIncs_0 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^(m*2)) (RC0 a 0) (RC0 m (1+(n*2+a))).
Proof.
  eapply sideRLs_trans.
  1: apply RIncs0_0.
  eapply sideRLs_trans.
  1: apply ROv0_0.
  applys_eq (RIncs0 0 (n*2+a) m); flia.
Qed.

Definition RC k ls a b :=
  d^^k *> w *> (Rmp'^^^ls) *> RC0 a b.

Definition S' '(k,ls,a,b) := 0inf <* <[1;0] {{{ (hR'',R) }}} RC k ls a b.

Lemma BigStep k ls a b k' ls' a' b':
  sideRLs tm hRL'' (RC (k) ls a b) (RC (k') ls' a' b') ->
  S' (k,ls,a,b) -->+ S' (k',ls',a',b').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL'++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL'' (d^^(k) *> w *> r) (d^^(k+1) *> w *> r').
Proof.
  intros.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ds.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  applys_eq (Incs_wd 0 (2^k-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma RC0_w a b:
  w *> RC0 a b = RC0 (1+a) b.
Proof.
  reflexivity.
Qed.

Close Scope sym.

Lemma BigStep_3 k ls a b i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,3+b) -->+ S' (k+1,ls++[(m1+a)*2+1],1+(v1-((m1+a)*2+3))*2,1+b) /\
  P (ls++[(m1+a)*2+1]) (S (S i)) (2^k*2-2) ((v1-((m1+a)*2+2))*2) (m1*4+a*2+1).
Proof.
  intros HP Hm v1 Hv1.
  split.
  2:{
    eapply P_S with (n:=(m1+a)*2+1) (c':=(2^k*2-2-m)) in HP.
    2: cbn[Nat.pow]; lia.
    applys_eq HP; cbn[Nat.pow]; lia.
  }
  apply BigStep.
  unfold RC.
  rw_flat_map.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  unfold Rmp'.
  repeat rewrite Str_app_assoc.
  rewrite (lpow_add' w 1).
  rewrite RC0_w.
  applys_eq (RIncs a b m1 ((v1-(m1+a+1)*2)*2)); flia.
Qed.

Lemma BigStep_1 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+1<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+1,ls,(v1-(m1+a+1))*2,0).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_1 a m1 ((v1-((m1+a)*2+1))*2)); flia.
Qed.

Lemma BigStep_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  1<=v1 ->
  S' (k,ls,a,0) -->+ S' (k+1,ls,v1-1,1+(m1*2+a)).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_0 a m1 v1); flia.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep_1_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+2,ls,2^k*2*2^i+v1-1,1+m1*2+(v1-(m1+a+1))*2).
Proof.
  intros HP Hm v1 Hv1.
  eapply progress_trans.
  1: apply BigStep_1; eauto 1.
  1: lia.
  eapply progress_evstep_trans.
  1: apply BigStep_0; eauto 1.
  all: rw_pa.
  all: replace (2^k*2^1*2-2-m) with (2^k*2+(2^k*2-2-m)) by lia.
  1,2: lia.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (5,[13],1,3) /\
  P [13] 1 28 0 13.
Proof.
  split.
  1: esx.
  epose proof P_O as HP.
  eapply P_S with (n:=13) (c':=28) in HP.
  2: lia.
  apply HP.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,a,b) => (b mod 2 = 1) /\ exists i m m0 m1, P ls (S i) m m0 m1 /\ m<=2^k*2-2 /\
  let v1:=(2^k*2-2-m)*2^i+m0 in
  (m1+a)*2+3<=v1 /\ m1*2+v1+1<=2^k*2*2^i).
  2:{
    split; [lia|].
    eexists _,_,_,_; split.
    1: apply init.
    lia.
  }
  intros [[[k ls] a] b] [I1 [i [m [m0 [m1 [I2 [I3 [I4 I5]]]]]]]].
  assert (b>=3\/b=1) as [E|E] by lia.
  {
    replace b with (3+(b-3)) by lia.
    eexists; split.
    1: apply BigStep_3.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply BigStep_3; eauto 1.
    1: lia.
    all: cbn[Nat.pow].
    all: remember ((2^k*2-2-m)*2^i+m0) as v1.
    1,2: replace (2^k*(2*1)*2-2-(2^k*2-2)) with (2^k*2) by lia; lia.
  }
  {
    subst b.
    eexists; split.
    1: apply BigStep_1_0.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply I2.
    1: lia.
    1,2: replace (2^k*2^2*2-2-m) with (2^k*6+(2^k*2-2-m)) by lia; lia.
  }
Qed.

End TM23.


Module TM24.

Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RA_0RD0LC_1LE1RF_0LB0RC_0RE1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hR' := (B,<[1;1]).
Notation hR'' := (C,<[1;0;0]).
Notation hL := (C,[0]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [0;1;0;1].
Notation w := [0;0;1].

Goal segRLs tm (hRL'++hRL^^2) (hRL++hRL') w w.
Proof. esx. Qed.

Goal segRLs tm (hRL'++hRL^^2) (hRL'') d w.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL') w d.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL''++hRL) d d.
Proof. esx. Qed.

Lemma Incs_w_0 n:
  segRLs tm (hRL^^n) (hRL^^n) w w.
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma Incs_w a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a+1)++hRL'++hRL^^b) w w.
Proof.
  do 2 rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+b)) (hRL^^(a+n)++hRL'++hRL^^b) (w^^n) (w^^n).
Proof.
  gen a b.
  induction n; intros.
  - rewrite Nat.add_0_r.
    apply segRLs_nil.
  - cbn[lpow].
    eapply segRLs_concat.
    2: applys_eq (IHn (S a) b); flia.
    applys_eq (Incs_w a (n*2+b)); flia.
Qed.

Lemma Incs_d_0 n:
  segRLs tm (hRL^^n) (hRL^^(n*2)) d d.
Proof.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_d a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^(a*2)++hRL''++hRL^^(1+b*2)) d d.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  apply Incs_d_0.
Qed.

Lemma Incs_ds i:
  segRLs tm hRL'' (hRL''++hRL^^(2^i-1)) (d^^i) (d^^i).
Proof.
  induction i.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r i),lpow_add.
  eapply segRLs_concat.
  1: apply IHi.
  applys_eq (Incs_d 0 (2^i-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma Incs_wd a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^a++hRL'++hRL^^(b*2)) w d.
Proof.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  eapply segRLs_trans.
  2: apply Incs_d_0.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a*2)++hRL''++hRL^^b) d w.
Proof.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+(2+b))) (hRL^^((a+n)*2)++hRL'++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  eapply segRLs_concat.
  1: apply Incs_dw.
  apply Incs_wd.
Qed.

Lemma Incs_dsw i:
  segRLs tm hRL'' (hRL'++hRL^^((2^i-1)*2)) (d^^i++w) (d^^i++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ds.
  apply (Incs_wd 0).
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  unfold Rmp,Rmp' in *.
  cbn in *.
  st.
  rewrite IHls.
  st; simpl_rotate; reflexivity.
Qed.

Definition P ls i n n0 n1 :=
  forall c,
  segRLs tm (hRL'++hRL^^(c+n)) (hRL^^(n1*2)++hRL'++hRL^^(c*2^i+n0*2)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 0 0 0.
Proof.
  unfold P.
  intros.
  rewrite app_assoc.
  rewrite Nat.mul_1_r.
  apply segRLs_nil.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 m1 n c':
  P ls i m m0 m1 ->
  n*2+2<=c'*2^i+m0*2 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0*2-(n*2+2))) (m1*2+n).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (m1*2) ((c+c')*2^i+m0*2-(n*2+2)) n); flia.
Qed.

Definition RC0 a b := w^^a *> [0] *> w^^b *> 0inf.

Lemma RIncs0 a b n:
  sideRLs tm (hRL^^(n*2)) (RC0 a (1+b)) (RC0 (n+a) (1+b)).
Proof.
  unfold RC0.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_0 a n:
  sideRLs tm (hRL^^(n)) (RC0 a 0) (RC0 (n+a) 0).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 a b c := w^^a *> [0] *> w^^b *> [1] *> w^^c *> 0inf.

Lemma ROv0 a b:
  sideRLs tm (hRL') (RC0 a (1+b)) (RC1 0 (1+a) b).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma RIncs1 a b c:
  sideRLs tm (hRL^^(b*4)) (RC1 a (1+b) c) (RC1 (b*2+a) 1 c).
Proof.
  gen a.
  induction b; intros.
  1: esx.
  cbn[Nat.mul].
  eapply sideRLs_trans_add.
  2: applys_eq (IHb (2+a)); flia.
  unfold RC1.
  esx.
Qed.

Lemma ROv1 a c:
  sideRLs tm (hRL^^4) (RC1 a 1 (2+c)) (w^^(2+a)*>d*>RC0 0 (1+c)).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma ROv0_0 a:
  sideRLs tm (hRL') (RC0 a 0) (RC0 0 (1+a)).
Proof.
  unfold RC0.
  esx.
Qed.

Lemma ROv1_0 a:
  sideRLs tm (hRL^^2) (RC1 a 1 0) (RC0 (1+a) 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma ROv1_1 a:
  sideRLs tm (hRL^^4) (RC1 a 1 1) (w^^(2+a)*>d*>RC0 1 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma Incs_ws_0 n m:
  segRLs tm (hRL^^n) (hRL^^n) (w^^m) (w^^m).
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma RIncs a b n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(4+m))) (RC0 a (3+b)) (w^^(2+((n+a)*2+0))*>d*>RC0 m (1+b)).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ (2+b)).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ws_0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_d_0.
  applys_eq (RIncs0 0); flia.
Qed.

Lemma RIncs_1 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(2+m))) (RC0 a 1) (RC0 (1+(n+a)*2+m) 0).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ 0).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1_0.
  applys_eq RIncs0_0; flia.
Qed.

Lemma RIncs_0 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^(m*2)) (RC0 a 0) (RC0 m (1+(n*2+a))).
Proof.
  eapply sideRLs_trans.
  1: apply RIncs0_0.
  eapply sideRLs_trans.
  1: apply ROv0_0.
  applys_eq (RIncs0 0 (n*2+a) m); flia.
Qed.

Definition RC k ls a b :=
  d^^k *> w *> (Rmp'^^^ls) *> RC0 a b.

Definition S' '(k,ls,a,b) := 0inf <* <[1;0] {{{ (hR'',R) }}} RC k ls a b.

Lemma BigStep k ls a b k' ls' a' b':
  sideRLs tm hRL'' (RC (k) ls a b) (RC (k') ls' a' b') ->
  S' (k,ls,a,b) -->+ S' (k',ls',a',b').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL'++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL'' (d^^(k) *> w *> r) (d^^(k+1) *> w *> r').
Proof.
  intros.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ds.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  applys_eq (Incs_wd 0 (2^k-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma RC0_w a b:
  w *> RC0 a b = RC0 (1+a) b.
Proof.
  reflexivity.
Qed.

Close Scope sym.

Lemma BigStep_3 k ls a b i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,3+b) -->+ S' (k+1,ls++[(m1+a)*2+1],1+(v1-((m1+a)*2+3))*2,1+b) /\
  P (ls++[(m1+a)*2+1]) (S (S i)) (2^k*2-2) ((v1-((m1+a)*2+2))*2) (m1*4+a*2+1).
Proof.
  intros HP Hm v1 Hv1.
  split.
  2:{
    eapply P_S with (n:=(m1+a)*2+1) (c':=(2^k*2-2-m)) in HP.
    2: cbn[Nat.pow]; lia.
    applys_eq HP; cbn[Nat.pow]; lia.
  }
  apply BigStep.
  unfold RC.
  rw_flat_map.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  unfold Rmp'.
  repeat rewrite Str_app_assoc.
  rewrite (lpow_add' w 1).
  rewrite RC0_w.
  applys_eq (RIncs a b m1 ((v1-(m1+a+1)*2)*2)); flia.
Qed.

Lemma BigStep_1 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+1<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+1,ls,(v1-(m1+a+1))*2,0).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_1 a m1 ((v1-((m1+a)*2+1))*2)); flia.
Qed.

Lemma BigStep_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  1<=v1 ->
  S' (k,ls,a,0) -->+ S' (k+1,ls,v1-1,1+(m1*2+a)).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_0 a m1 v1); flia.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep_1_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+2,ls,2^k*2*2^i+v1-1,1+m1*2+(v1-(m1+a+1))*2).
Proof.
  intros HP Hm v1 Hv1.
  eapply progress_trans.
  1: apply BigStep_1; eauto 1.
  1: lia.
  eapply progress_evstep_trans.
  1: apply BigStep_0; eauto 1.
  all: rw_pa.
  all: replace (2^k*2^1*2-2-m) with (2^k*2+(2^k*2-2-m)) by lia.
  1,2: lia.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (5,[13],1,3) /\
  P [13] 1 28 0 13.
Proof.
  split.
  1: esx.
  epose proof P_O as HP.
  eapply P_S with (n:=13) (c':=28) in HP.
  2: lia.
  apply HP.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,a,b) => (b mod 2 = 1) /\ exists i m m0 m1, P ls (S i) m m0 m1 /\ m<=2^k*2-2 /\
  let v1:=(2^k*2-2-m)*2^i+m0 in
  (m1+a)*2+3<=v1 /\ m1*2+v1+1<=2^k*2*2^i).
  2:{
    split; [lia|].
    eexists _,_,_,_; split.
    1: apply init.
    lia.
  }
  intros [[[k ls] a] b] [I1 [i [m [m0 [m1 [I2 [I3 [I4 I5]]]]]]]].
  assert (b>=3\/b=1) as [E|E] by lia.
  {
    replace b with (3+(b-3)) by lia.
    eexists; split.
    1: apply BigStep_3.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply BigStep_3; eauto 1.
    1: lia.
    all: cbn[Nat.pow].
    all: remember ((2^k*2-2-m)*2^i+m0) as v1.
    1,2: replace (2^k*(2*1)*2-2-(2^k*2-2)) with (2^k*2) by lia; lia.
  }
  {
    subst b.
    eexists; split.
    1: apply BigStep_1_0.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply I2.
    1: lia.
    1,2: replace (2^k*2^2*2-2-m) with (2^k*6+(2^k*2-2-m)) by lia; lia.
  }
Qed.

End TM24.


Module TM25.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD1RA_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[1]).
Notation hR' := (A,<[1;1]).
Notation hR'' := (F,<[1;0;0]).
Notation hL := (B,[0]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [0;1;0;1].
Notation w := [0;0;1].

Goal segRLs tm (hRL'++hRL^^2) (hRL++hRL') w w.
Proof. esx. Qed.

Goal segRLs tm (hRL'++hRL^^2) (hRL'') d w.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL') w d.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL''++hRL) d d.
Proof. esx. Qed.

Lemma Incs_w_0 n:
  segRLs tm (hRL^^n) (hRL^^n) w w.
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma Incs_w a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a+1)++hRL'++hRL^^b) w w.
Proof.
  do 2 rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+b)) (hRL^^(a+n)++hRL'++hRL^^b) (w^^n) (w^^n).
Proof.
  gen a b.
  induction n; intros.
  - rewrite Nat.add_0_r.
    apply segRLs_nil.
  - cbn[lpow].
    eapply segRLs_concat.
    2: applys_eq (IHn (S a) b); flia.
    applys_eq (Incs_w a (n*2+b)); flia.
Qed.

Lemma Incs_d_0 n:
  segRLs tm (hRL^^n) (hRL^^(n*2)) d d.
Proof.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_d a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^(a*2)++hRL''++hRL^^(1+b*2)) d d.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  apply Incs_d_0.
Qed.

Lemma Incs_ds i:
  segRLs tm hRL'' (hRL''++hRL^^(2^i-1)) (d^^i) (d^^i).
Proof.
  induction i.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r i),lpow_add.
  eapply segRLs_concat.
  1: apply IHi.
  applys_eq (Incs_d 0 (2^i-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma Incs_wd a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^a++hRL'++hRL^^(b*2)) w d.
Proof.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  eapply segRLs_trans.
  2: apply Incs_d_0.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a*2)++hRL''++hRL^^b) d w.
Proof.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+(2+b))) (hRL^^((a+n)*2)++hRL'++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  eapply segRLs_concat.
  1: apply Incs_dw.
  apply Incs_wd.
Qed.

Lemma Incs_dsw i:
  segRLs tm hRL'' (hRL'++hRL^^((2^i-1)*2)) (d^^i++w) (d^^i++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ds.
  apply (Incs_wd 0).
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  unfold Rmp,Rmp' in *.
  cbn in *.
  st.
  rewrite IHls.
  st; simpl_rotate; reflexivity.
Qed.

Definition P ls i n n0 n1 :=
  forall c,
  segRLs tm (hRL'++hRL^^(c+n)) (hRL^^(n1*2)++hRL'++hRL^^(c*2^i+n0*2)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 0 0 0.
Proof.
  unfold P.
  intros.
  rewrite app_assoc.
  rewrite Nat.mul_1_r.
  apply segRLs_nil.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 m1 n c':
  P ls i m m0 m1 ->
  n*2+2<=c'*2^i+m0*2 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0*2-(n*2+2))) (m1*2+n).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (m1*2) ((c+c')*2^i+m0*2-(n*2+2)) n); flia.
Qed.

Definition RC0 a b := w^^a *> [0] *> w^^b *> 0inf.

Lemma RIncs0 a b n:
  sideRLs tm (hRL^^(n*2)) (RC0 a (1+b)) (RC0 (n+a) (1+b)).
Proof.
  unfold RC0.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_0 a n:
  sideRLs tm (hRL^^(n)) (RC0 a 0) (RC0 (n+a) 0).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 a b c := w^^a *> [0] *> w^^b *> [1] *> w^^c *> 0inf.

Lemma ROv0 a b:
  sideRLs tm (hRL') (RC0 a (1+b)) (RC1 0 (1+a) b).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma RIncs1 a b c:
  sideRLs tm (hRL^^(b*4)) (RC1 a (1+b) c) (RC1 (b*2+a) 1 c).
Proof.
  gen a.
  induction b; intros.
  1: esx.
  cbn[Nat.mul].
  eapply sideRLs_trans_add.
  2: applys_eq (IHb (2+a)); flia.
  unfold RC1.
  esx.
Qed.

Lemma ROv1 a c:
  sideRLs tm (hRL^^4) (RC1 a 1 (2+c)) (w^^(2+a)*>d*>RC0 0 (1+c)).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma ROv0_0 a:
  sideRLs tm (hRL') (RC0 a 0) (RC0 0 (1+a)).
Proof.
  unfold RC0.
  esx.
Qed.

Lemma ROv1_0 a:
  sideRLs tm (hRL^^2) (RC1 a 1 0) (RC0 (1+a) 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma ROv1_1 a:
  sideRLs tm (hRL^^4) (RC1 a 1 1) (w^^(2+a)*>d*>RC0 1 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma Incs_ws_0 n m:
  segRLs tm (hRL^^n) (hRL^^n) (w^^m) (w^^m).
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma RIncs a b n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(4+m))) (RC0 a (3+b)) (w^^(2+((n+a)*2+0))*>d*>RC0 m (1+b)).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ (2+b)).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ws_0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_d_0.
  applys_eq (RIncs0 0); flia.
Qed.

Lemma RIncs_1 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(2+m))) (RC0 a 1) (RC0 (1+(n+a)*2+m) 0).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ 0).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1_0.
  applys_eq RIncs0_0; flia.
Qed.

Lemma RIncs_0 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^(m*2)) (RC0 a 0) (RC0 m (1+(n*2+a))).
Proof.
  eapply sideRLs_trans.
  1: apply RIncs0_0.
  eapply sideRLs_trans.
  1: apply ROv0_0.
  applys_eq (RIncs0 0 (n*2+a) m); flia.
Qed.

Definition RC k ls a b :=
  d^^k *> w *> (Rmp'^^^ls) *> RC0 a b.

Definition S' '(k,ls,a,b) := 0inf <* <[1;0] {{{ (hR'',R) }}} RC k ls a b.

Lemma BigStep k ls a b k' ls' a' b':
  sideRLs tm hRL'' (RC (k) ls a b) (RC (k') ls' a' b') ->
  S' (k,ls,a,b) -->+ S' (k',ls',a',b').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL'++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL'' (d^^(k) *> w *> r) (d^^(k+1) *> w *> r').
Proof.
  intros.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ds.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  applys_eq (Incs_wd 0 (2^k-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma RC0_w a b:
  w *> RC0 a b = RC0 (1+a) b.
Proof.
  reflexivity.
Qed.

Close Scope sym.

Lemma BigStep_3 k ls a b i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,3+b) -->+ S' (k+1,ls++[(m1+a)*2+1],1+(v1-((m1+a)*2+3))*2,1+b) /\
  P (ls++[(m1+a)*2+1]) (S (S i)) (2^k*2-2) ((v1-((m1+a)*2+2))*2) (m1*4+a*2+1).
Proof.
  intros HP Hm v1 Hv1.
  split.
  2:{
    eapply P_S with (n:=(m1+a)*2+1) (c':=(2^k*2-2-m)) in HP.
    2: cbn[Nat.pow]; lia.
    applys_eq HP; cbn[Nat.pow]; lia.
  }
  apply BigStep.
  unfold RC.
  rw_flat_map.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  unfold Rmp'.
  repeat rewrite Str_app_assoc.
  rewrite (lpow_add' w 1).
  rewrite RC0_w.
  applys_eq (RIncs a b m1 ((v1-(m1+a+1)*2)*2)); flia.
Qed.

Lemma BigStep_1 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+1<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+1,ls,(v1-(m1+a+1))*2,0).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_1 a m1 ((v1-((m1+a)*2+1))*2)); flia.
Qed.

Lemma BigStep_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  1<=v1 ->
  S' (k,ls,a,0) -->+ S' (k+1,ls,v1-1,1+(m1*2+a)).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_0 a m1 v1); flia.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep_1_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+2,ls,2^k*2*2^i+v1-1,1+m1*2+(v1-(m1+a+1))*2).
Proof.
  intros HP Hm v1 Hv1.
  eapply progress_trans.
  1: apply BigStep_1; eauto 1.
  1: lia.
  eapply progress_evstep_trans.
  1: apply BigStep_0; eauto 1.
  all: rw_pa.
  all: replace (2^k*2^1*2-2-m) with (2^k*2+(2^k*2-2-m)) by lia.
  1,2: lia.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (5,[13],1,3) /\
  P [13] 1 28 0 13.
Proof.
  split.
  1: esx.
  epose proof P_O as HP.
  eapply P_S with (n:=13) (c':=28) in HP.
  2: lia.
  apply HP.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,a,b) => (b mod 2 = 1) /\ exists i m m0 m1, P ls (S i) m m0 m1 /\ m<=2^k*2-2 /\
  let v1:=(2^k*2-2-m)*2^i+m0 in
  (m1+a)*2+3<=v1 /\ m1*2+v1+1<=2^k*2*2^i).
  2:{
    split; [lia|].
    eexists _,_,_,_; split.
    1: apply init.
    lia.
  }
  intros [[[k ls] a] b] [I1 [i [m [m0 [m1 [I2 [I3 [I4 I5]]]]]]]].
  assert (b>=3\/b=1) as [E|E] by lia.
  {
    replace b with (3+(b-3)) by lia.
    eexists; split.
    1: apply BigStep_3.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply BigStep_3; eauto 1.
    1: lia.
    all: cbn[Nat.pow].
    all: remember ((2^k*2-2-m)*2^i+m0) as v1.
    1,2: replace (2^k*(2*1)*2-2-(2^k*2-2)) with (2^k*2) by lia; lia.
  }
  {
    subst b.
    eexists; split.
    1: apply BigStep_1_0.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply I2.
    1: lia.
    1,2: replace (2^k*2^2*2-2-m) with (2^k*6+(2^k*2-2-m)) by lia; lia.
  }
Qed.

End TM25.


Module TM26.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB1RC_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,[1]).
Notation hR' := (C,<[1;1]).
Notation hR'' := (F,<[1;0;0]).
Notation hL := (D,[0]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [0;1;0;1].
Notation w := [0;0;1].

Goal segRLs tm (hRL'++hRL^^2) (hRL++hRL') w w.
Proof. esx. Qed.

Goal segRLs tm (hRL'++hRL^^2) (hRL'') d w.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL') w d.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL''++hRL) d d.
Proof. esx. Qed.

Lemma Incs_w_0 n:
  segRLs tm (hRL^^n) (hRL^^n) w w.
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma Incs_w a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a+1)++hRL'++hRL^^b) w w.
Proof.
  do 2 rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+b)) (hRL^^(a+n)++hRL'++hRL^^b) (w^^n) (w^^n).
Proof.
  gen a b.
  induction n; intros.
  - rewrite Nat.add_0_r.
    apply segRLs_nil.
  - cbn[lpow].
    eapply segRLs_concat.
    2: applys_eq (IHn (S a) b); flia.
    applys_eq (Incs_w a (n*2+b)); flia.
Qed.

Lemma Incs_d_0 n:
  segRLs tm (hRL^^n) (hRL^^(n*2)) d d.
Proof.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_d a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^(a*2)++hRL''++hRL^^(1+b*2)) d d.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  apply Incs_d_0.
Qed.

Lemma Incs_ds i:
  segRLs tm hRL'' (hRL''++hRL^^(2^i-1)) (d^^i) (d^^i).
Proof.
  induction i.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r i),lpow_add.
  eapply segRLs_concat.
  1: apply IHi.
  applys_eq (Incs_d 0 (2^i-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma Incs_wd a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^a++hRL'++hRL^^(b*2)) w d.
Proof.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  eapply segRLs_trans.
  2: apply Incs_d_0.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a*2)++hRL''++hRL^^b) d w.
Proof.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite lpow_add,app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+(2+b))) (hRL^^((a+n)*2)++hRL'++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  eapply segRLs_concat.
  1: apply Incs_dw.
  apply Incs_wd.
Qed.

Lemma Incs_dsw i:
  segRLs tm hRL'' (hRL'++hRL^^((2^i-1)*2)) (d^^i++w) (d^^i++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ds.
  apply (Incs_wd 0).
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  unfold Rmp,Rmp' in *.
  cbn in *.
  st.
  rewrite IHls.
  st; simpl_rotate; reflexivity.
Qed.

Definition P ls i n n0 n1 :=
  forall c,
  segRLs tm (hRL'++hRL^^(c+n)) (hRL^^(n1*2)++hRL'++hRL^^(c*2^i+n0*2)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 0 0 0.
Proof.
  unfold P.
  intros.
  rewrite app_assoc.
  rewrite Nat.mul_1_r.
  apply segRLs_nil.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 m1 n c':
  P ls i m m0 m1 ->
  n*2+2<=c'*2^i+m0*2 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0*2-(n*2+2))) (m1*2+n).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (m1*2) ((c+c')*2^i+m0*2-(n*2+2)) n); flia.
Qed.

Definition RC0 a b := w^^a *> [0] *> w^^b *> 0inf.

Lemma RIncs0 a b n:
  sideRLs tm (hRL^^(n*2)) (RC0 a (1+b)) (RC0 (n+a) (1+b)).
Proof.
  unfold RC0.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_0 a n:
  sideRLs tm (hRL^^(n)) (RC0 a 0) (RC0 (n+a) 0).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 a b c := w^^a *> [0] *> w^^b *> [1] *> w^^c *> 0inf.

Lemma ROv0 a b:
  sideRLs tm (hRL') (RC0 a (1+b)) (RC1 0 (1+a) b).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma RIncs1 a b c:
  sideRLs tm (hRL^^(b*4)) (RC1 a (1+b) c) (RC1 (b*2+a) 1 c).
Proof.
  gen a.
  induction b; intros.
  1: esx.
  cbn[Nat.mul].
  eapply sideRLs_trans_add.
  2: applys_eq (IHb (2+a)); flia.
  unfold RC1.
  esx.
Qed.

Lemma ROv1 a c:
  sideRLs tm (hRL^^4) (RC1 a 1 (2+c)) (w^^(2+a)*>d*>RC0 0 (1+c)).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma ROv0_0 a:
  sideRLs tm (hRL') (RC0 a 0) (RC0 0 (1+a)).
Proof.
  unfold RC0.
  esx.
Qed.

Lemma ROv1_0 a:
  sideRLs tm (hRL^^2) (RC1 a 1 0) (RC0 (1+a) 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma ROv1_1 a:
  sideRLs tm (hRL^^4) (RC1 a 1 1) (w^^(2+a)*>d*>RC0 1 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.

Lemma Incs_ws_0 n m:
  segRLs tm (hRL^^n) (hRL^^n) (w^^m) (w^^m).
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma RIncs a b n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(4+m))) (RC0 a (3+b)) (w^^(2+((n+a)*2+0))*>d*>RC0 m (1+b)).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ (2+b)).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ws_0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_d_0.
  applys_eq (RIncs0 0); flia.
Qed.

Lemma RIncs_1 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^((n+a)*4+(2+m))) (RC0 a 1) (RC0 (1+(n+a)*2+m) 0).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0 _ 0).
  eapply sideRLs_trans.
  1: apply ROv0.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1_0.
  applys_eq RIncs0_0; flia.
Qed.

Lemma RIncs_0 a n m:
  sideRLs tm (hRL^^(n*2)++hRL'++hRL^^(m*2)) (RC0 a 0) (RC0 m (1+(n*2+a))).
Proof.
  eapply sideRLs_trans.
  1: apply RIncs0_0.
  eapply sideRLs_trans.
  1: apply ROv0_0.
  applys_eq (RIncs0 0 (n*2+a) m); flia.
Qed.

Definition RC k ls a b :=
  d^^k *> w *> (Rmp'^^^ls) *> RC0 a b.

Definition S' '(k,ls,a,b) := 0inf <* <[1;0] {{{ (hR'',R) }}} RC k ls a b.

Lemma BigStep k ls a b k' ls' a' b':
  sideRLs tm hRL'' (RC (k) ls a b) (RC (k') ls' a' b') ->
  S' (k,ls,a,b) -->+ S' (k',ls',a',b').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL'++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL'' (d^^(k) *> w *> r) (d^^(k+1) *> w *> r').
Proof.
  intros.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ds.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  applys_eq (Incs_wd 0 (2^k-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma RC0_w a b:
  w *> RC0 a b = RC0 (1+a) b.
Proof.
  reflexivity.
Qed.

Close Scope sym.

Lemma BigStep_3 k ls a b i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,3+b) -->+ S' (k+1,ls++[(m1+a)*2+1],1+(v1-((m1+a)*2+3))*2,1+b) /\
  P (ls++[(m1+a)*2+1]) (S (S i)) (2^k*2-2) ((v1-((m1+a)*2+2))*2) (m1*4+a*2+1).
Proof.
  intros HP Hm v1 Hv1.
  split.
  2:{
    eapply P_S with (n:=(m1+a)*2+1) (c':=(2^k*2-2-m)) in HP.
    2: cbn[Nat.pow]; lia.
    applys_eq HP; cbn[Nat.pow]; lia.
  }
  apply BigStep.
  unfold RC.
  rw_flat_map.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  unfold Rmp'.
  repeat rewrite Str_app_assoc.
  rewrite (lpow_add' w 1).
  rewrite RC0_w.
  applys_eq (RIncs a b m1 ((v1-(m1+a+1)*2)*2)); flia.
Qed.

Lemma BigStep_1 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+1<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+1,ls,(v1-(m1+a+1))*2,0).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_1 a m1 ((v1-((m1+a)*2+1))*2)); flia.
Qed.

Lemma BigStep_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  1<=v1 ->
  S' (k,ls,a,0) -->+ S' (k+1,ls,v1-1,1+(m1*2+a)).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_0 a m1 v1); flia.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep_1_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+3<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+2,ls,2^k*2*2^i+v1-1,1+m1*2+(v1-(m1+a+1))*2).
Proof.
  intros HP Hm v1 Hv1.
  eapply progress_trans.
  1: apply BigStep_1; eauto 1.
  1: lia.
  eapply progress_evstep_trans.
  1: apply BigStep_0; eauto 1.
  all: rw_pa.
  all: replace (2^k*2^1*2-2-m) with (2^k*2+(2^k*2-2-m)) by lia.
  1,2: lia.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (5,[13],1,3) /\
  P [13] 1 28 0 13.
Proof.
  split.
  1: esx.
  epose proof P_O as HP.
  eapply P_S with (n:=13) (c':=28) in HP.
  2: lia.
  apply HP.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,a,b) => (b mod 2 = 1) /\ exists i m m0 m1, P ls (S i) m m0 m1 /\ m<=2^k*2-2 /\
  let v1:=(2^k*2-2-m)*2^i+m0 in
  (m1+a)*2+3<=v1 /\ m1*2+v1+1<=2^k*2*2^i).
  2:{
    split; [lia|].
    eexists _,_,_,_; split.
    1: apply init.
    lia.
  }
  intros [[[k ls] a] b] [I1 [i [m [m0 [m1 [I2 [I3 [I4 I5]]]]]]]].
  assert (b>=3\/b=1) as [E|E] by lia.
  {
    replace b with (3+(b-3)) by lia.
    eexists; split.
    1: apply BigStep_3.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply BigStep_3; eauto 1.
    1: lia.
    all: cbn[Nat.pow].
    all: remember ((2^k*2-2-m)*2^i+m0) as v1.
    1,2: replace (2^k*(2*1)*2-2-(2^k*2-2)) with (2^k*2) by lia; lia.
  }
  {
    subst b.
    eexists; split.
    1: apply BigStep_1_0.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply I2.
    1: lia.
    1,2: replace (2^k*2^2*2-2-m) with (2^k*6+(2^k*2-2-m)) by lia; lia.
  }
Qed.

End TM26.


Module TM27.

Definition tm := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1RA_0RE0LE_1LB1RF_0RB1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (F,[1]).
Notation hR' := (C,<[1;1]).
Notation hR'' := (D,<[1;0;0]).
Notation hL := (B,[1]).
Notation hRL'' := [(hR'',hL)].
Notation hRL' := [(hR',hL)].
Notation hRL := [(hR,hL)].
Notation d := [0;1;0;1].
Notation w := [0;0;1].

Goal segRLs tm (hRL'++hRL^^2) (hRL++hRL') w w.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL''++hRL) d d.
Proof. esx. Qed.

Goal segRLs tm (hRL'') (hRL') w d.
Proof. esx. Qed.

Goal segRLs tm (hRL'++hRL^^2) (hRL++hRL'') d w.
Proof. esx. Qed.

Lemma Incs_w_0 n:
  segRLs tm (hRL^^n) (hRL^^n) w w.
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma Incs_w a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a+1)++hRL'++hRL^^b) w w.
Proof.
  do 2 rewrite lpow_add.
  rewrite <-app_assoc.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  repeat rewrite app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_ws a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+b)) (hRL^^(a+n)++hRL'++hRL^^b) (w^^n) (w^^n).
Proof.
  gen a b.
  induction n; intros.
  - rewrite Nat.add_0_r.
    apply segRLs_nil.
  - cbn[lpow].
    eapply segRLs_concat.
    2: applys_eq (IHn (S a) b); flia.
    applys_eq (Incs_w a (n*2+b)); flia.
Qed.

Lemma Incs_d_0 n:
  segRLs tm (hRL^^n) (hRL^^(n*2)) d d.
Proof.
  1: applys_eq (segRLs_addmul_v2 1 2 n 0 0); unfold DH0.
  1,2: flia.
  1,2: esx.
Qed.

Lemma Incs_d a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^(a*2)++hRL''++hRL^^(1+b*2)) d d.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: esx.
  apply Incs_d_0.
Qed.

Lemma Incs_ds i:
  segRLs tm hRL'' (hRL''++hRL^^(2^i-1)) (d^^i) (d^^i).
Proof.
  induction i.
  1: esx.
  cbn[Nat.pow].
  rewrite <-(Nat.add_1_r i),lpow_add.
  eapply segRLs_concat.
  1: apply IHi.
  applys_eq (Incs_d 0 (2^i-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma Incs_wd a b:
  segRLs tm (hRL^^a++hRL''++hRL^^b) (hRL^^a++hRL'++hRL^^(b*2)) w d.
Proof.
  eapply segRLs_trans.
  1: apply Incs_w_0.
  eapply segRLs_trans.
  2: apply Incs_d_0.
  esx.
Qed.

Lemma Incs_dw a b:
  segRLs tm (hRL^^a++hRL'++hRL^^(2+b)) (hRL^^(a*2+1)++hRL''++hRL^^b) d w.
Proof.
  rewrite (lpow_add _ (a*2) 1),<-app_assoc.
  eapply segRLs_trans.
  1: apply Incs_d_0.
  rewrite lpow_add.
  do 2 rewrite app_assoc.
  eapply segRLs_trans.
  2: apply Incs_w_0.
  esx.
Qed.

Lemma Incs_wsdw a b n:
  segRLs tm (hRL^^a++hRL'++hRL^^(n*2+(2+b))) (hRL^^((a+n)*2+1)++hRL'++hRL^^(b*2)) (w^^n++d++w) (w^^n++w++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ws.
  eapply segRLs_concat.
  1: apply Incs_dw.
  apply Incs_wd.
Qed.

Lemma Incs_dsw i:
  segRLs tm hRL'' (hRL'++hRL^^((2^i-1)*2)) (d^^i++w) (d^^i++d).
Proof.
  eapply segRLs_concat.
  1: apply Incs_ds.
  apply (Incs_wd 0).
Qed.

Definition Rmp' n := w^^n++d++w.
Definition Rmp n := w^^n++w++d.

Lemma Rshift ls r:
  (Rmp^^^ls) *> w *> r =
  w *> (Rmp'^^^ls) *> r.
Proof.
  induction ls.
  1: reflexivity.
  unfold Rmp,Rmp' in *.
  cbn in *.
  st.
  rewrite IHls.
  st; simpl_rotate; reflexivity.
Qed.

Definition P ls i n n0 n1 :=
  forall c,
  segRLs tm (hRL'++hRL^^(c+n)) (hRL^^(n1*2+1)++hRL'++hRL^^(c*2^i+n0*2)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O n:
  P [n] 1 (n*2+2) 0 (n).
Proof.
  unfold P.
  intros.
  cbn[flat_map].
  do 2 rewrite app_nil_r.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw 0 c n).
  1: rewrite app_nil_l; flia.
  flia.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma P_S ls i m m0 m1 n c':
  P ls i m m0 m1 ->
  n*2+2<=c'*2^i+m0*2 ->
  P (ls++[n]) (S i) (c'+m) ((c'*2^i+m0*2-(n*2+2))) ((m1*2+1+n)).
Proof.
  unfold P; intros HP Hc' c.
  cbn[Nat.pow].
  rw_flat_map.
  rewrite Nat.add_assoc.
  eapply segRLs_concat.
  1: apply HP.
  unfold Rmp,Rmp'.
  applys_eq (Incs_wsdw (m1*2+1) ((c+c')*2^i+m0*2-(n*2+2)) n); flia.
Qed.

Definition RC0 a b := w^^a *> [0] *> w^^b *> 0inf.
Definition RC0' a b := w^^a *> [1] *> w^^b *> 0inf.

Lemma RIncs0 a b n:
  sideRLs tm (hRL^^(n*2)) (RC0 a (1+b)) (RC0 (n+a) (1+b)).
Proof.
  unfold RC0.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0' a b n:
  sideRLs tm (hRL^^(1+n*2)) (RC0 a (1+b)) (RC0' (1+(n+a)) b).
Proof.
  unfold RC0,RC0'.
  eapply sideRLs_trans_add.
  1: esx.
  rewrite lpow_mul.
  sideRLs_ind n.
Qed.

Lemma RIncs0_0 a n:
  sideRLs tm (hRL^^(n)) (RC0 a 0) (RC0 (n+a) 0).
Proof.
  unfold RC0.
  sideRLs_ind n.
Qed.

Definition RC1 a b c := w^^a *> [0] *> w^^b *> [0] *> w^^c *> 0inf.

Lemma ROv0' a b:
  sideRLs tm (hRL') (RC0' (1+a) b) (RC1 0 (1+a) (1+b)).
Proof.
  unfold RC0',RC1.
  esx.
Qed.

Lemma RIncs1 a b c:
  sideRLs tm (hRL^^(b*4)) (RC1 a (1+b) (1+c)) (RC1 (b*2+a) 1 (1+c)).
Proof.
  gen a.
  induction b; intros.
  1: esx.
  cbn[Nat.mul].
  eapply sideRLs_trans_add.
  2: applys_eq (IHb (2+a)); flia.
  unfold RC1.
  esx.
Qed.

Lemma ROv1 a c:
  sideRLs tm (hRL^^6) (RC1 a 1 (3+c)) (w^^(3+a)*>d*>RC0 0 (1+c)).
Proof.
  unfold RC0,RC1.
  esx.
Qed.

Lemma ROv0_0 a:
  sideRLs tm (hRL') (RC0 a 0) (RC0 0 (1+a)).
Proof.
  unfold RC0.
  esx.
Qed.

Lemma ROv1_0 a:
  sideRLs tm (hRL^^4) (RC1 a 1 1) (RC0 (2+a) 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.
(*
Lemma ROv1_1 a:
  sideRLs tm (hRL^^4) (RC1 a 1 1) (w^^(2+a)*>d*>RC0 1 0).
Proof.
  unfold RC1,RC0.
  esx.
Qed.
 *)
Lemma Incs_ws_0 n m:
  segRLs tm (hRL^^n) (hRL^^n) (w^^m) (w^^m).
Proof.
  eapply segRLs_wall''; esx.
Qed.

Lemma RIncs a b n m:
  sideRLs tm (hRL^^(1+n*2)++hRL'++hRL^^((n+a)*4+(6+m))) (RC0 a (3+b)) (w^^(3+((n+a)*2+0))*>d*>RC0 m (1+b)).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0' _ (2+b)).
  eapply sideRLs_trans.
  1: apply ROv0'.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ws_0.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_d_0.
  applys_eq (RIncs0 0); flia.
Qed.

Lemma RIncs_1 a n m:
  sideRLs tm (hRL^^(1+n*2)++hRL'++hRL^^((n+a)*4+(4+m))) (RC0 a 1) (RC0 (2+(n+a)*2+m) 0).
Proof.
  eapply sideRLs_trans.
  1: apply (RIncs0' _ 0).
  eapply sideRLs_trans.
  1: apply ROv0'.
  eapply sideRLs_trans_add.
  1: apply RIncs1.
  eapply sideRLs_trans_add.
  1: apply ROv1_0.
  applys_eq RIncs0_0; flia.
Qed.

Lemma RIncs_0 a n m:
  sideRLs tm (hRL^^(1+n*2)++hRL'++hRL^^(m*2)) (RC0 a 0) (RC0 m (2+(n*2+a))).
Proof.
  eapply sideRLs_trans.
  1: apply RIncs0_0.
  eapply sideRLs_trans.
  1: apply ROv0_0.
  applys_eq (RIncs0 0 (1+n*2+a) m); flia.
Qed.

Definition RC k ls a b :=
  d^^k *> w *> (Rmp'^^^ls) *> RC0 a b.

Definition S' '(k,ls,a,b) := 0inf <* <[1;0] {{{ (hR'',R) }}} RC k ls a b.

Lemma BigStep k ls a b k' ls' a' b':
  sideRLs tm hRL'' (RC (k) ls a b) (RC (k') ls' a' b') ->
  S' (k,ls,a,b) -->+ S' (k',ls',a',b').
Proof.
  intros.
  eapply sideRLs_1 in H.
  unfold S'.
  follow10 H.
  es.
Qed.

Lemma BigStep' k r r':
  sideRLs tm (hRL'++hRL^^(2^k*2-2)) r (w *> r') ->
  sideRLs tm hRL'' (d^^(k) *> w *> r) (d^^(k+1) *> w *> r').
Proof.
  intros.
  rewrite lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply Incs_ds.
  eapply segRLs_sideRLs_concat.
  2: apply H.
  applys_eq (Incs_wd 0 (2^k-1)).
  rewrite app_nil_l.
  flia.
Qed.

Lemma RC0_w a b:
  w *> RC0 a b = RC0 (1+a) b.
Proof.
  reflexivity.
Qed.

Close Scope sym.

Lemma BigStep_3 k ls a b i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+4<=v1 ->
  S' (k,ls,a,3+b) -->+ S' (k+1,ls++[(m1+a)*2+2],1+(v1-((m1+a)*2+4))*2,1+b) /\
  P (ls++[(m1+a)*2+2]) (S (S i)) (2^k*2-2) ((v1-((m1+a)*2+3))*2) (m1*4+a*2+3).
Proof.
  intros HP Hm v1 Hv1.
  split.
  2:{
    eapply P_S with (n:=(m1+a)*2+2) (c':=(2^k*2-2-m)) in HP.
    2: cbn[Nat.pow]; lia.
    applys_eq HP; cbn[Nat.pow]; lia.
  }
  apply BigStep.
  unfold RC.
  rw_flat_map.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  unfold Rmp'.
  repeat rewrite Str_app_assoc.
  rewrite (lpow_add' w 1).
  rewrite RC0_w.
  applys_eq (RIncs a b m1 ((v1-((m1+a)*2+3))*2)); flia.
Qed.

Lemma BigStep_1 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+2<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+1,ls,1+(v1-(m1+a+2))*2,0).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_1 a m1 ((v1-((m1+a)*2+2))*2)); flia.
Qed.

Lemma BigStep_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  1<=v1 ->
  S' (k,ls,a,0) -->+ S' (k+1,ls,v1-1,2+(m1*2+a)).
Proof.
  intros HP Hm v1 Hv1.
  apply BigStep.
  unfold RC.
  apply BigStep'.
  rewrite <-Rshift.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (HP (2^k*2-2-m)); flia.
  cbn[Nat.pow].
  rewrite RC0_w.
  applys_eq (RIncs_0 a m1 v1); flia.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep_1_0 k ls a i m m0 m1:
  P ls (S i) m m0 m1 ->
  m<=2^k*2-2 ->
  let v1:=(2^k*2-2-m)*(2^i)+m0 in
  (m1+a)*2+4<=v1 ->
  S' (k,ls,a,1) -->+ S' (k+2,ls,2^k*2*2^i+v1-1,1+m1*2+(v1-(m1+a+1))*2).
Proof.
  intros HP Hm v1 Hv1.
  eapply progress_trans.
  1: apply BigStep_1; eauto 1.
  1: lia.
  eapply progress_evstep_trans.
  1: apply BigStep_0; eauto 1.
  all: rw_pa.
  all: replace (2^k*2^1*2-2-m) with (2^k*2+(2^k*2-2-m)) by lia.
  1,2: lia.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (5,[13],1,3) /\
  P [13] 1 28 0 13.
Proof.
  split.
  1: esx.
  apply P_O.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,ls,a,b) => (b mod 2 = 1) /\ exists i m m0 m1, P ls (S i) m m0 m1 /\ m<=2^k*2-2 /\
  let v1:=(2^k*2-2-m)*2^i+m0 in
  (m1+a)*2+4<=v1 /\ m1*2+v1+2<=2^k*2*2^i).
  2:{
    split; [lia|].
    eexists _,_,_,_; split.
    1: apply init.
    lia.
  }
  intros [[[k ls] a] b] [I1 [i [m [m0 [m1 [I2 [I3 [I4 I5]]]]]]]].
  assert (b>=3\/b=1) as [E|E] by lia.
  {
    replace b with (3+(b-3)) by lia.
    eexists; split.
    1: apply BigStep_3.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply BigStep_3; eauto 1.
    1: lia.
    all: cbn[Nat.pow].
    all: remember ((2^k*2-2-m)*2^i+m0) as v1.
    1,2: replace (2^k*(2*1)*2-2-(2^k*2-2)) with (2^k*2) by lia; lia.
  }
  {
    subst b.
    eexists; split.
    1: apply BigStep_1_0.
    1: apply I2.
    1,2: lia.
    cbn match.
    split.
    1: lia.
    rw_pa.
    repeat eexists.
    1: apply I2.
    1: lia.
    1,2: replace (2^k*2^2*2-2-m) with (2^k*6+(2^k*2-2-m)) by lia.
    1,2: lia.
  }
Qed.

End TM27.


Module TM28.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC1RA_1LD1LA_1LB0LC_1RF1RC_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[1]).
Notation hL := (C,[0]).
Notation hRL := [(hR,hL)].
Notation d' := [1;0;1;1;0;1].
Notation d := [1;0;1;1;0;1].
Notation w' := [1;1;0;1].
Notation w := [1;0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> 1 >> r =
  1 >> 0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 3.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i*3+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: applys_eq (Incs_d (n+2)); flia.
  cbn[Nat.pow].
  applys_eq (H (n*2+3)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (w'^^2*>[1;0;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1;1;1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Notation dx := ([1;1;0;1;0;1]++w++d).

Lemma RIncs0 n:
  sideRLs tm (hRL^^(5+n)) rh0 (1>>0>>1>>dx*>w^^(n*2)*>1>>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(2+n)) (dx*>w^^n0*>1>>0>>1>>rh0) (d*>w*>d*>w^^(4+n*4+n0)*>1>>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Notation hLR := [(hL,hR)].

Lemma BigStep' ls r ls' r':
  sideRLs tm (hRL^^3) (Rmp'^^^ls *> r) (Rmp^^^ls' *> 1>>0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  cbn[lpow] in H.
  eapply sideRLs_split in H.
  destruct H as [r'0 [I1 I2]].
  eapply sideRLs_split in I2.
  destruct I2 as [r'1 [I2 I3]].
  eapply sideRLs_1 in I1,I2,I3.
  follow10 I1.
  er.
  follow100 I2.
  er.
  follow100 I3.
  rewrite Rshift.
  er.
Qed.

Lemma BigStep0 ls i n:
  P ls i (5+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^(n*2)*>1>>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (2+n) ->
  S' (ls,dx*>w^^n0*>1>>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]++[Dd]++[Dw]^^(4+n*4+n0),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  5<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]++[Dd]++[Dw]^^(2^i*12+n*6-14)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-5)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i*3-2+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^4++[Dw]^^2++[Dd]++[Dw]++[Dd]++[Dw]^^94).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 5<=n<=2^i*12).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_assoc.
    1: apply P_Rws.
    1: apply P_Rd.
    1: apply P_Rw.
    1: apply P_Rd.
    1: apply P_Rws.
    1: do 4 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      repeat rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: apply P_Rw.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM28.


Module TM29.

Definition tm := Eval compute in (TM_from_str "1LB0LC_0RC1RD_1LA1LD_1RB0RE_1RF1RC_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (D,[1]).
Notation hL := (C,[0]).
Notation hRL := [(hR,hL)].
Notation d' := [1;0;1;1;0;1].
Notation d := [1;0;1;1;0;1].
Notation w' := [1;1;0;1].
Notation w := [1;0;1;1].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 1 >> 0 >> 1 >> r =
  1 >> 0 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*(2^i)+c)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 3.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i*3+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: applys_eq (Incs_d (n+2)); flia.
  cbn[Nat.pow].
  applys_eq (H (n*2+3)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c-1)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Notation rh0 := (w'^^2*>[1;0;1]*>0inf).

Definition S' '(ls,r) :=
  0inf <* <[1;1;0;1;1;1;1;1;0;1;1;1] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Notation dx := ([1;1;0;1;0;1]++w++d).

Lemma RIncs0 n:
  sideRLs tm (hRL^^(5+n)) rh0 (1>>0>>1>>dx*>w^^(n*2)*>1>>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n n0:
  sideRLs tm (hRL^^(2+n)) (dx*>w^^n0*>1>>0>>1>>rh0) (d*>w*>d*>w^^(4+n*4+n0)*>1>>0>>1>>rh0).
Proof.
  sideRLs_ind n.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Notation hLR := [(hL,hR)].

Lemma BigStep' ls r ls' r':
  sideRLs tm (hRL^^3) (Rmp'^^^ls *> r) (Rmp^^^ls' *> 1>>0>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  cbn[lpow] in H.
  eapply sideRLs_split in H.
  destruct H as [r'0 [I1 I2]].
  eapply sideRLs_split in I2.
  destruct I2 as [r'1 [I2 I3]].
  eapply sideRLs_1 in I1,I2,I3.
  follow10 I1.
  er.
  follow100 I2.
  er.
  follow100 I3.
  rewrite Rshift.
  er.
Qed.

Lemma BigStep0 ls i n:
  P ls i (5+n) ->
  S' (ls,rh0) -->+
  S' (Dd::ls,dx*>w^^(n*2)*>1>>0>>1>>rh0).
Proof.
  intros HP.
  apply BigStep'.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs0.
Qed.

Lemma BigStep1 ls i n n0:
  P ls i (2+n) ->
  S' (ls,dx*>w^^n0*>1>>0>>1>>rh0) -->+
  S' (Dd::ls++[Dd]++[Dw]++[Dd]++[Dw]^^(4+n*4+n0),rh0).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply RIncs1.
Qed.

Definition S0 ls := S' (ls,rh0).

Lemma BigStep ls i n:
  P ls i n ->
  5<=n ->
  S0 (ls) -->+
  S0 (Dd::Dd::ls++[Dd]++[Dw]++[Dd]++[Dw]^^(2^i*12+n*6-14)).
Proof.
  unfold S0.
  intros HP Hn.
  eapply progress_trans.
  1: eapply BigStep0 with (n:=(n-5)).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  eapply progress_evstep_trans.
  1: eapply BigStep1 with (n:=2^i*3-2+n).
  1: applys_eq HP; flia.
  cbn[app].
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^3++[Dw]++[Dd]++[Dd]++[Dw]++[Dd]++[Dw]^^94).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun ls => exists i n, P ls i n /\ 5<=n<=2^i*12).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_assoc.
    1: apply P_Rws.
    1: apply P_Rd.
    1: apply P_Rw.
    1: apply P_Rd.
    1: apply P_Rd.
    1: apply P_Rw.
    1: do 3 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros ls [i [n [I1 I2]]].
  eexists; split.
  - eapply BigStep.
    1: apply I1.
    lia.
  - eexists _,_; split.
    + do 2 rewrite app_comm_cons.
      repeat rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: apply P_Rw.
      1: apply P_Rd.
      1: do 2 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM29.


Module TM30.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LE_1RD0RC_1RA1RF_1RC0LA_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,[]).
Notation hL := (A,[]).
Notation hRL := [(hR,hL)].
Notation d' := [0;1;1;0;1;1].
Notation d := [0;1;1;0;1;1].
Notation w' := [0;0;1;1].
Notation w := [0;1;1;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> 1 >> r =
  0 >> 1 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*(2^i)+c*3)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: applys_eq (Incs_d (n+2)); flia.
  cbn[Nat.pow].
  applys_eq (H (n*2+3)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c*3-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c*3-3)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma BigStep' ls r ls' r':
  sideRLs tm (hRL^^3) (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  cbn[lpow] in H.
  eapply sideRLs_split in H.
  destruct H as [r'0 [I1 I2]].
  eapply sideRLs_split in I2.
  destruct I2 as [r'1 [I2 I3]].
  eapply sideRLs_1 in I1,I2,I3.
  follow10 I1.
  er.
  follow100 I2.
  er.
  follow100 I3.
  rewrite Rshift.
  er.
Qed.

Lemma Incs_ws n m:
  segRLs tm (hRL^^(n*3+m)) (hRL^^m) (w'^^n) (w^^n).
Proof.
  induction n; intros.
  1: apply segRLs_nil.
  cbn[lpow].
  eapply segRLs_concat.
  2: apply IHn.
  applys_eq (Incs_w (n*3+m)); flia.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^n) 0inf (w^^n*>0inf).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*3)) (w'^^(n+m)*>0inf) (w^^n*>w'^^m*>0inf).
Proof.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws n 0); flia.
  esx.
Qed.

Lemma RIncs2 n m:
  sideRLs tm (hRL^^((n+m)*3)) ((0::w')*>w'^^n*>0inf) ((0::w')*>w^^(n+m*3)*>0inf).
Proof.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (segRLs_addmul_v2 3 3 (n+m) 0 0); unfold DH0.
  1: flia.
  1,2: esx.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws n (m*3)); flia.
  apply RIncs0.
Qed.

Lemma RIncs3 n m:
  sideRLs tm (hRL^^(2+m)) ((0::0::w')*>w^^n*>0inf) (0>>1>>1>>d'*>w'^^(1+n+m*2)*>0inf).
Proof.
  sideRLs_ind m.
Qed.

Lemma RIncs2' n m:
  sideRLs tm (hRL^^(3+(n+m)*3)) (w'*>(0::w')*>w'^^n*>0inf) (0>>1>>1>>(0::0::w')*>w^^(n+m*3)*>0inf).
Proof.
  eapply @segRLs_sideRLs_concat with (w2:=w).
  1: applys_eq (Incs_w ((n+m)*3)); flia.
  applys_eq (RIncs2 n m); flia.
Qed.

Lemma RIncs1' n m:
  sideRLs tm (hRL^^(6+n*3)) (w'^^(3+n+m)*>0inf) (0>>1>>1>>w'^^n*>w'*>(0::w')*>w'^^m*>0inf).
Proof.
  applys_eq (RIncs1 (2+n) (1+m)).
  1: flia.
  st; simpl_rotate; trivial.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n m:
  P ls i (2+n) ->
  S' (ls,w'^^(3+n+m)*>0inf) -->+
  S' (Dd::ls++[Dw]^^n,w'*>(0::w')*>w'^^m*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  unfold Rmp.
  applys_eq (RIncs1' n m).
  st; simpl_rotate; trivial.
Qed.

Lemma BigStep2 ls i n m:
  P ls i (1+n+m) ->
  S' (ls,w'*>(0::w')*>w'^^n*>0inf) -->+
  S' (Dd::ls,(0::0::w')*>w^^(n+m*3)*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply (RIncs2' n m).
Qed.

Lemma BigStep3 ls i n m:
  P ls i (1+m) ->
  S' (ls,(0::0::w')*>w^^n*>0inf) -->+
  S' (Dd::ls++[Dd],w'^^(3+n+m*6)*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  unfold Rmp.
  applys_eq (RIncs3 n (1+m*3)).
  st; simpl_rotate; trivial.
Qed.

Definition S0 '(ls,n) := S' (ls,(0::0::w')*>w^^n*>0inf).

Lemma BigStep312 ls i n m:
  P ls i m ->
  1<=m ->
  2^i*2+4<=n+m*4<=2^i*6+5 ->
  S0 (ls,n) -->+
  S0 (Dd::Dd::Dd::ls++[Dd]++[Dw]^^((2^i-1+m)*2),(2^i*16+11-(n*2+m*8))).
Proof.
  unfold S0.
  intros HP Hm Hm0.
  eapply progress_trans.
  1: eapply BigStep3 with (m:=m-1).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  apply P_Rd in HP.
  2: lia.
  epose proof (BigStep1 _ _ ((2^i-1+m)*2) (n+m*4-(2^i*2+4))) as I1.
  eapply progress_trans.
  1: applys_eq I1; flia.
  1: applys_eq HP; flia.
  clear I1.
  apply P_Ld in HP.
  apply P_Rws with (n:=(2^i-1+m)*2) in HP.
  2: cbn[Nat.pow]; lia.
  cbn[Nat.pow] in HP.
  epose proof (BigStep2 _ _ (n+m*4-(2^i*2+4)) (2^i*6+5-(n+m*4))) as I2.
  eapply progress_evstep_trans.
  1: applys_eq I2; flia.
  1: applys_eq HP; flia.
  clear I2.
  cbn[app].
  rewrite <-app_assoc.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^5++[Dw]^^6,27).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => exists i m, P ls i m /\ 1<=m /\ 2^i*2+4<=n+m*4<=2^i*6+5).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_assoc.
    1: apply P_Rws.
    1: do 5 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros [ls n] [i [m [I1 [I2 I3]]]].
  eexists; split.
  - eapply BigStep312.
    1: apply I1.
    all: lia.
  - eexists _,_; split.
    + repeat rewrite app_comm_cons.
      repeat rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 3 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM30.


Module TM31.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (A,[]).
Notation hL := (C,[]).
Notation hRL := [(hR,hL)].
Notation d' := [0;1;1;0;1;1].
Notation d := [0;1;1;0;1;1].
Notation w' := [0;0;1;1].
Notation w := [0;1;1;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> 1 >> r =
  0 >> 1 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*(2^i)+c*3)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: applys_eq (Incs_d (n+2)); flia.
  cbn[Nat.pow].
  applys_eq (H (n*2+3)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c*3-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c*3-3)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma BigStep' ls r ls' r':
  sideRLs tm (hRL^^3) (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  cbn[lpow] in H.
  eapply sideRLs_split in H.
  destruct H as [r'0 [I1 I2]].
  eapply sideRLs_split in I2.
  destruct I2 as [r'1 [I2 I3]].
  eapply sideRLs_1 in I1,I2,I3.
  follow10 I1.
  er.
  follow100 I2.
  er.
  follow100 I3.
  rewrite Rshift.
  er.
Qed.

Lemma Incs_ws n m:
  segRLs tm (hRL^^(n*3+m)) (hRL^^m) (w'^^n) (w^^n).
Proof.
  induction n; intros.
  1: apply segRLs_nil.
  cbn[lpow].
  eapply segRLs_concat.
  2: apply IHn.
  applys_eq (Incs_w (n*3+m)); flia.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^n) 0inf (w^^n*>0inf).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*3)) (w'^^(n+m)*>0inf) (w^^n*>w'^^m*>0inf).
Proof.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws n 0); flia.
  esx.
Qed.

Lemma RIncs2 n m:
  sideRLs tm (hRL^^((n+m)*3)) ((0::w')*>w'^^n*>0inf) ((0::w')*>w^^(n+m*3)*>0inf).
Proof.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (segRLs_addmul_v2 3 3 (n+m) 0 0); unfold DH0.
  1: flia.
  1,2: esx.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws n (m*3)); flia.
  apply RIncs0.
Qed.

Lemma RIncs3 n m:
  sideRLs tm (hRL^^(2+m)) ((0::0::w')*>w^^n*>0inf) (0>>1>>1>>d'*>w'^^(1+n+m*2)*>0inf).
Proof.
  sideRLs_ind m.
Qed.

Lemma RIncs2' n m:
  sideRLs tm (hRL^^(3+(n+m)*3)) (w'*>(0::w')*>w'^^n*>0inf) (0>>1>>1>>(0::0::w')*>w^^(n+m*3)*>0inf).
Proof.
  eapply @segRLs_sideRLs_concat with (w2:=w).
  1: applys_eq (Incs_w ((n+m)*3)); flia.
  applys_eq (RIncs2 n m); flia.
Qed.

Lemma RIncs1' n m:
  sideRLs tm (hRL^^(6+n*3)) (w'^^(3+n+m)*>0inf) (0>>1>>1>>w'^^n*>w'*>(0::w')*>w'^^m*>0inf).
Proof.
  applys_eq (RIncs1 (2+n) (1+m)).
  1: flia.
  st; simpl_rotate; trivial.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n m:
  P ls i (2+n) ->
  S' (ls,w'^^(3+n+m)*>0inf) -->+
  S' (Dd::ls++[Dw]^^n,w'*>(0::w')*>w'^^m*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  unfold Rmp.
  applys_eq (RIncs1' n m).
  st; simpl_rotate; trivial.
Qed.

Lemma BigStep2 ls i n m:
  P ls i (1+n+m) ->
  S' (ls,w'*>(0::w')*>w'^^n*>0inf) -->+
  S' (Dd::ls,(0::0::w')*>w^^(n+m*3)*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply (RIncs2' n m).
Qed.

Lemma BigStep3 ls i n m:
  P ls i (1+m) ->
  S' (ls,(0::0::w')*>w^^n*>0inf) -->+
  S' (Dd::ls++[Dd],w'^^(3+n+m*6)*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  unfold Rmp.
  applys_eq (RIncs3 n (1+m*3)).
  st; simpl_rotate; trivial.
Qed.

Definition S0 '(ls,n) := S' (ls,(0::0::w')*>w^^n*>0inf).

Lemma BigStep312 ls i n m:
  P ls i m ->
  1<=m ->
  2^i*2+4<=n+m*4<=2^i*6+5 ->
  S0 (ls,n) -->+
  S0 (Dd::Dd::Dd::ls++[Dd]++[Dw]^^((2^i-1+m)*2),(2^i*16+11-(n*2+m*8))).
Proof.
  unfold S0.
  intros HP Hm Hm0.
  eapply progress_trans.
  1: eapply BigStep3 with (m:=m-1).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  apply P_Rd in HP.
  2: lia.
  epose proof (BigStep1 _ _ ((2^i-1+m)*2) (n+m*4-(2^i*2+4))) as I1.
  eapply progress_trans.
  1: applys_eq I1; flia.
  1: applys_eq HP; flia.
  clear I1.
  apply P_Ld in HP.
  apply P_Rws with (n:=(2^i-1+m)*2) in HP.
  2: cbn[Nat.pow]; lia.
  cbn[Nat.pow] in HP.
  epose proof (BigStep2 _ _ (n+m*4-(2^i*2+4)) (2^i*6+5-(n+m*4))) as I2.
  eapply progress_evstep_trans.
  1: applys_eq I2; flia.
  1: applys_eq HP; flia.
  clear I2.
  cbn[app].
  rewrite <-app_assoc.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^3,9).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => exists i m, P ls i m /\ 1<=m /\ 2^i*2+4<=n+m*4<=2^i*6+5).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_assoc.
    1: do 3 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros [ls n] [i [m [I1 [I2 I3]]]].
  eexists; split.
  - eapply BigStep312.
    1: apply I1.
    all: lia.
  - eexists _,_; split.
    + repeat rewrite app_comm_cons.
      repeat rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 3 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM31.


Module TM32.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LD_0RE1LA_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,[]).
Notation hL := (D,[]).
Notation hRL := [(hR,hL)].
Notation d' := [0;1;1;0;1;1].
Notation d := [0;1;1;0;1;1].
Notation w' := [0;0;1;1].
Notation w := [0;1;1;0].

Inductive RD := Dd | Dw.

Definition Rmp x :=
match x with
| Dd => d
| Dw => w
end.

Definition Rmp' x :=
match x with
| Dd => d'
| Dw => w'
end.

Lemma Rshift ls r:
  (Rmp^^^ls) *> 0 >> 1 >> 1 >> r =
  0 >> 1 >> 1 >> (Rmp'^^^ls) *> r.
Proof.
  induction ls; st.
  1: trivial.
  rewrite IHls.
  destruct a; trivial.
Qed.

Lemma Incs_d n:
  segRLs tm (hRL^^(n*1+1)) (hRL^^(n*2+2)) d' d.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Lemma Incs_w n:
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*1+0)) w' w.
Proof.
  eapply segRLs_addmul_v2; esx.
Qed.

Definition P ls i c :=
  forall n,
  segRLs tm (hRL^^(n*1+3)) (hRL^^(n*(2^i)+c*3)) (Rmp'^^^ls) (Rmp^^^ls).

Lemma P_O:
  P [] 0 1.
Proof.
  unfold P.
  intros.
  apply segRLs_nil.
Qed.

Lemma P_Ld ls i c:
  P ls i c ->
  P (Dd::ls) (S i) (2^i+c).
Proof.
  unfold P; cbn[flat_map]; intros.
  eapply segRLs_concat.
  1: applys_eq (Incs_d (n+2)); flia.
  cbn[Nat.pow].
  applys_eq (H (n*2+3)); flia.
Qed.

Lemma P_Rd ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dd]) (S i) (c*2).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_d (n*2^i+c*3-1)); flia.
Qed.

Lemma P_Rw ls i c:
  P ls i c ->
  c>=1 ->
  P (ls++[Dw]) i (c-1).
Proof.
  unfold P; do 2 rewrite flat_map_app; intros.
  cbn[Nat.pow].
  eapply segRLs_concat.
  1: apply H.
  applys_eq (Incs_w (n*2^i+c*3-3)); flia.
Qed.

Lemma P_Rws ls i c n:
  P ls i c ->
  c>=n ->
  P (ls++[Dw]^^n) i (c-n).
Proof.
  intros.
  induction n.
  - cbn.
    rewrite app_nil_r.
    applys_eq H; flia.
  - apply P_Rw in IHn.
    2,3: lia.
    rewrite <-app_assoc in IHn.
    replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    applys_eq IHn; flia.
Qed.

Definition S' '(ls,r) :=
  0inf <* <[1;0] {{{ (hR,R) }}} (Rmp'^^^ls) *> r.

Lemma BigStep' ls r ls' r':
  sideRLs tm (hRL^^3) (Rmp'^^^ls *> r) (Rmp^^^ls' *> 0>>1>>1>>r') ->
  S' (ls,r) -->+
  S' (Dd::ls',r').
Proof.
  unfold S'.
  intros.
  cbn[lpow] in H.
  eapply sideRLs_split in H.
  destruct H as [r'0 [I1 I2]].
  eapply sideRLs_split in I2.
  destruct I2 as [r'1 [I2 I3]].
  eapply sideRLs_1 in I1,I2,I3.
  follow10 I1.
  er.
  follow100 I2.
  er.
  follow100 I3.
  rewrite Rshift.
  er.
Qed.

Lemma Incs_ws n m:
  segRLs tm (hRL^^(n*3+m)) (hRL^^m) (w'^^n) (w^^n).
Proof.
  induction n; intros.
  1: apply segRLs_nil.
  cbn[lpow].
  eapply segRLs_concat.
  2: apply IHn.
  applys_eq (Incs_w (n*3+m)); flia.
Qed.

Lemma RIncs0 n:
  sideRLs tm (hRL^^n) 0inf (w^^n*>0inf).
Proof.
  sideRLs_ind n.
Qed.

Lemma RIncs1 n m:
  sideRLs tm (hRL^^(n*3)) (w'^^(n+m)*>0inf) (w^^n*>w'^^m*>0inf).
Proof.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws n 0); flia.
  esx.
Qed.

Lemma RIncs2 n m:
  sideRLs tm (hRL^^((n+m)*3)) ((0::w')*>w'^^n*>0inf) ((0::w')*>w^^(n+m*3)*>0inf).
Proof.
  rewrite <-lpow_add'.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (segRLs_addmul_v2 3 3 (n+m) 0 0); unfold DH0.
  1: flia.
  1,2: esx.
  eapply segRLs_sideRLs_concat.
  1: applys_eq (Incs_ws n (m*3)); flia.
  apply RIncs0.
Qed.

Lemma RIncs3 n m:
  sideRLs tm (hRL^^(2+m)) ((0::0::w')*>w^^n*>0inf) (0>>1>>1>>d'*>w'^^(1+n+m*2)*>0inf).
Proof.
  sideRLs_ind m.
Qed.

Lemma RIncs2' n m:
  sideRLs tm (hRL^^(3+(n+m)*3)) (w'*>(0::w')*>w'^^n*>0inf) (0>>1>>1>>(0::0::w')*>w^^(n+m*3)*>0inf).
Proof.
  eapply @segRLs_sideRLs_concat with (w2:=w).
  1: applys_eq (Incs_w ((n+m)*3)); flia.
  applys_eq (RIncs2 n m); flia.
Qed.

Lemma RIncs1' n m:
  sideRLs tm (hRL^^(6+n*3)) (w'^^(3+n+m)*>0inf) (0>>1>>1>>w'^^n*>w'*>(0::w')*>w'^^m*>0inf).
Proof.
  applys_eq (RIncs1 (2+n) (1+m)).
  1: flia.
  st; simpl_rotate; trivial.
Qed.

Ltac rw_flat_map :=
  repeat (cbn[flat_map] ||
  rewrite flat_map_app ||
  rewrite flat_map_lpow ||
  rewrite app_nil_r ||
  rewrite Str_app_assoc).

Lemma BigStep1 ls i n m:
  P ls i (2+n) ->
  S' (ls,w'^^(3+n+m)*>0inf) -->+
  S' (Dd::ls++[Dw]^^n,w'*>(0::w')*>w'^^m*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  unfold Rmp.
  applys_eq (RIncs1' n m).
  st; simpl_rotate; trivial.
Qed.

Lemma BigStep2 ls i n m:
  P ls i (1+n+m) ->
  S' (ls,w'*>(0::w')*>w'^^n*>0inf) -->+
  S' (Dd::ls,(0::0::w')*>w^^(n+m*3)*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  apply (RIncs2' n m).
Qed.

Lemma BigStep3 ls i n m:
  P ls i (1+m) ->
  S' (ls,(0::0::w')*>w^^n*>0inf) -->+
  S' (Dd::ls++[Dd],w'^^(3+n+m*6)*>0inf).
Proof.
  intros HP.
  apply BigStep'.
  rw_flat_map.
  eapply segRLs_sideRLs_concat.
  1: apply (HP O).
  unfold Rmp.
  applys_eq (RIncs3 n (1+m*3)).
  st; simpl_rotate; trivial.
Qed.

Definition S0 '(ls,n) := S' (ls,(0::0::w')*>w^^n*>0inf).

Lemma BigStep312 ls i n m:
  P ls i m ->
  1<=m ->
  2^i*2+4<=n+m*4<=2^i*6+5 ->
  S0 (ls,n) -->+
  S0 (Dd::Dd::Dd::ls++[Dd]++[Dw]^^((2^i-1+m)*2),(2^i*16+11-(n*2+m*8))).
Proof.
  unfold S0.
  intros HP Hm Hm0.
  eapply progress_trans.
  1: eapply BigStep3 with (m:=m-1).
  1: applys_eq HP; flia.
  apply P_Ld in HP.
  apply P_Rd in HP.
  2: lia.
  epose proof (BigStep1 _ _ ((2^i-1+m)*2) (n+m*4-(2^i*2+4))) as I1.
  eapply progress_trans.
  1: applys_eq I1; flia.
  1: applys_eq HP; flia.
  clear I1.
  apply P_Ld in HP.
  apply P_Rws with (n:=(2^i-1+m)*2) in HP.
  2: cbn[Nat.pow]; lia.
  cbn[Nat.pow] in HP.
  epose proof (BigStep2 _ _ (n+m*4-(2^i*2+4)) (2^i*6+5-(n+m*4))) as I2.
  eapply progress_evstep_trans.
  1: applys_eq I2; flia.
  1: applys_eq HP; flia.
  clear I2.
  cbn[app].
  rewrite <-app_assoc.
  finish.
Qed.

Lemma init:
  c0 -->*
  S0 ([Dd]^^4++[Dw]^^2,15).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(ls,n) => exists i m, P ls i m /\ 1<=m /\ 2^i*2+4<=n+m*4<=2^i*6+5).
  2: {
    eexists _,_; split.
    1: repeat rewrite app_assoc.
    1: apply P_Rws.
    1: do 4 apply P_Ld.
    1: apply P_O.
    all: lia.
  }
  intros [ls n] [i [m [I1 [I2 I3]]]].
  eexists; split.
  - eapply BigStep312.
    1: apply I1.
    all: lia.
  - eexists _,_; split.
    + repeat rewrite app_comm_cons.
      repeat rewrite app_assoc.
      apply P_Rws.
      1: apply P_Rd.
      1: do 3 apply P_Ld.
      1: apply I1.
      all: cbn[Nat.pow]; lia.
    + cbn[Nat.pow].
      lia.
Qed.

End TM32.


