From BusyCoq Require Import Individual25.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Lemma Str_app_assoc_1{A} a (b:A) c:
  a *> [b] *> c =
  (a ++ [b]) *> c.
Proof.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Ltac solve_seg :=
  unfold segRL,segRR,segLL,segLR; intros; cbn; er; finish;
  repeat f_equal;
  repeat rewrite Str_cons_def;
  repeat rewrite Str_app_assoc_1;
  cbn[app];
  reflexivity.

Ltac solve_segLRs :=
  eapply segLRs_O ||
  (eapply segLRs_S; [solve_seg |];
  solve_segLRs).

Ltac solve_segRLs_lrcons :=
  eapply segRLs_lrcons;
  [solve_seg | | | ];
  [| solve_segLRs |];
  [solve_seg |].

Ltac solve_segRLs :=
  repeat (
  (eapply segRLs_S; [solve_seg |]) ||
  (eapply segRLs_RR_LLs; [solve_seg |]) ||
  (eapply segLLs_LR_LLs; [solve_seg |]) ||
  (eapply segLLs_LL_RLs; [solve_seg |]) ||
  eapply segRLs_O).

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RA2RA2LB---_2RA3LB4RA0LA3RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (B,[]).
Definition hL':DH0 := (B,[2;0]).
Definition hRL2: list (DH0*DH0) := [(hR,hL);(hR,hL')].

Lemma H20321:
  segRLs tm hRL2 hRL2 [2;0;3;2;1] [2;0;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H201203:
  segRLs tm hRL2 [] [2;0;1;2;0;3] [2;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H20221:
  segRLs tm hRL2 (hRL2^^2) [2;0;2;2;1] [2;0;2;0;2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H202021:
  segRLs tm hRL2 hRL2 [2;0;2;0;2;1] [2;0;3;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H2031:
  segRLs tm hRL2 hRL2 [2;0;3;1] [1;2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H203:
  segRLs tm hRL2 hRL2 [2;0;3] [2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H202:
  segRLs tm hRL2 hRL2 [2;0;2] [2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H2020:
  segRLs tm hRL2 hRL2 [2;0;2;0] [2;0;2;0].
Proof.
  solve_segRLs.
Qed.

Lemma H20:
  segRLs tm hRL2 hRL2 [2;0] [2;0].
Proof.
  solve_segRLs.
Qed.

Lemma H2:
  segRLs tm hRL2 hRL2 [2] [2].
Proof.
  solve_segRLs.
Qed.

Inductive Ltype :=
| L21 | L1203.

Definition Rstep r1 r2 :=
  sideRLs tm hRL2 r1 r2.

Definition R_P (R:Ltype->side->Prop) :=
  forall r,
  (R L21 r -> (
    (exists r', Rstep r r' /\ R L21 r') \/
    (exists r', r = [2;1]*>r' /\
    exists r'0 r'1,
    Rstep r' r'0 /\
    Rstep r'0 r'1 /\
    R L21 ([2;0;3]*>r'1) /\
    R L1203 ([2;0;2]*>r'0)))) /\
  (R L1203 r -> (
    (exists r', Rstep r r' /\ R L1203 r') \/
    (exists r', r = [1;2;0;3]*>r' /\
    R L21 ([2;0;3]*>r') /\
    R L1203 ([2;0;2]*>r') /\
    exists r'0,
    Rstep ([2;0;3]*>r') ([2;0;3]*>r'0) /\
    R L21 ([2;0;3]*>r'0) /\
    exists r'1,
    Rstep ([2;0;3]*>r'0) r'1 /\
    R L21 (r'1))
  )).

Inductive R0: Ltype->side->Prop :=
| L1203_0: R0 L1203 ([2;0;2;2;0;2;0;3;1]*>0inf)
| L1203_1: R0 L1203 ([2;0;2;2;0;1;2;0;1]*>0inf)
| L1203_2: R0 L1203 ([2;0;2;2;2;0;3;1]*>0inf)
| L1203_3: R0 L1203 ([2;0;2;2;1;2;0;1]*>0inf)
| L1203_4: R0 L1203 ([2;0;2;0;2;0;2;0;3;1]*>0inf)
| L1203_5: R0 L1203 ([2;0;2;0;2;0;1;2;0;1]*>0inf)
| L1203_6: R0 L1203 ([2;0;2;0;2;2;0;3;1]*>0inf)
| L1203_7: R0 L1203 ([2;0;2;0;2;1;2;0;1]*>0inf)
| L1203_8: R0 L1203 ([2;0;3;2;0;2;2;1]*>0inf)
| L1203_9: R0 L1203 ([2;0;3;2;0;2;0;2;1]*>0inf)
| L1203_10: R0 L1203 ([2;0;3;2;0;3;2;0;3;1]*>0inf)
| L1203_11: R0 L1203 ([2;0;3;2;0;3;1;2;0;1]*>0inf)
| L1203_12: R0 L1203 ([2;0;3;1;2;0;3;2;1]*>0inf)
| L1203_13: R0 L1203 ([1;2;0;3;2;0;2;0;3;1]*>0inf)
| L21_0: R0 L21 ([2;0;3;2;0;2;0;3;1]*>0inf)
| L21_1: R0 L21 ([2;0;3;2;0;1;2;0;1]*>0inf)
| L21_2: R0 L21 ([2;0;3;2;2;0;3;1]*>0inf)
| L21_3: R0 L21 ([2;0;3;2;1;2;0;1]*>0inf)
| L21_4: R0 L21 ([2;0;2;0;2;2;1]*>0inf)
| L21_5: R0 L21 ([2;0;2;0;2;0;2;1]*>0inf)
| L21_6: R0 L21 ([2;0;2;0;3;2;0;3;1]*>0inf)
| L21_7: R0 L21 ([2;0;2;0;3;1;2;0;1]*>0inf)
| L21_8: R0 L21 ([2;0;1;2;0;3;2;1]*>0inf)
| L21_9: R0 L21 ([2;2;0;2;2;1]*>0inf)
| L21_10: R0 L21 ([2;2;0;2;0;2;1]*>0inf)
| L21_11: R0 L21 ([2;2;0;3;2;0;3;1]*>0inf)
| L21_12: R0 L21 ([2;2;0;3;1;2;0;1]*>0inf)
| L21_13: R0 L21 ([2;1;2;0;3;2;1]*>0inf)
.

Inductive RS(R:Ltype->side->Prop): Ltype->side->Prop :=
| A203 r:
    R L21 r ->
    RS R L21 ([2;0;3]*>r)
| A20 r:
    R L1203 r ->
    RS R L21 ([2;0]*>r)
| A2 r:
    R L1203 r ->
    RS R L21 ([2]*>r)
| B202 r:
    R L21 r ->
    RS R L1203 ([2;0;2]*>r)
| B2020 r:
    R L21 r ->
    RS R L1203 ([2;0;2;0]*>r)
| B203 r:
    R L1203 r ->
    RS R L1203 ([2;0;3]*>r)
| BOv r:
    R L21 ([2;0;3]*>r) ->
    RS R L1203 ([1;2;0;3]*>[2;0;3]*>r)
.

Ltac des1 HP :=
  destruct HP as [[r' [HP1 HP2]]|[r' [HP1 [r'0 [r'1 [HP2 [HP3 [HP4 HP5]]]]]]]].

Ltac des2 HP :=
  destruct HP as [[r' [HP1 HP2]]|[r' [HP1 [HP2 [HP3 [r'0 [HP4 [HP5 [r'1 [HP6 HP7]]]]]]]]]].

Ltac ssc H :=
  repeat rewrite <-Str_app_assoc;
  eapply segRLs_sideRLs_concat;
  [ apply H | ];
  (assumption || constructor).

Ltac ca :=
  constructor; assumption.

Ltac solve_sideRLs :=
  (eapply sideRLseq_O; fail) ||
  (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    er | solve_sideRLs ]).

Ltac solve_R0 :=
  left;
  eexists; split;
  [ solve_sideRLs | ]; constructor.

Lemma R0_spec:
  R_P R0.
Proof.
  unfold R_P.
  intros r.
  split.
  - intros HO.
    inverts HO.
    1-13: solve_R0.
    right.
    eexists.
    split.
    1: cbn; reflexivity.
    eexists _,_.
    repeat split.
    1: solve_sideRLs.
    1: solve_sideRLs.
    1,2: constructor.
  - intros HO.
    inverts HO.
    1-13: solve_R0.
    right.
    eexists.
    split.
    1: cbn; reflexivity.
    repeat split.
    1,2: constructor.
    eexists.
    repeat split.
    1: solve_sideRLs.
    1: constructor.
    eexists.
    split.
    1: solve_sideRLs.
    1: constructor.
Qed.

Lemma RS_spec R:
  R_P R ->
  R_P (RS R).
Proof.
  unfold R_P.
  intros HP r.
  split.
  - intros HS.
    inverts HS.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;3]*>r').
        split.
        1: ssc H203.
        ca.
      * left.
        subst r0.
        exists ([2;0;2;0;2]*>r'0).
        split.
        1: ssc H20321.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0]*>r').
        split.
        1: ssc H20.
        ca.
      * left.
        subst r0.
        exists ([2;2;0;2]*>r').
        split.
        1: ssc H201203.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des2 HP.
      * left.
        exists ([2]*>r').
        split.
        1: ssc H2.
        ca.
      * subst r0.
        right.
        exists ([2;0;3]*>r').
        split.
        1: reflexivity.
        exists ([2;0;3]*>r'0) (r'1).
        repeat split.
        1,2: assumption.
        1,2: ca.
  - intros HS.
    inverts HS.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;2]*>r').
        split.
        1: ssc H202.
        ca.
      * left.
        subst r0.
        exists ([2;0;2;0;2;0;3]*>r'1).
        split.
        -- unfold Rstep.
           rewrite <-Str_app_assoc.
           eapply segRLs_sideRLs_concat.
           1: apply H20221.
           change (hRL2^^2) with (hRL2++hRL2).
           eapply sideRLs_trans; eassumption.
        -- ca.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;2;0]*>r').
        split.
        1: ssc H2020.
        ca.
      * left.
        subst r0.
        exists ([2;0;3;2;0;2]*>r'0).
        split.
        1: ssc H202021.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des2 HP.
      * left.
        exists ([2;0;3]*>r').
        split.
        1: ssc H203.
        ca.
      * subst r0.
        left.
        exists ([1;2;0;3]*>[2;0;3]*>r'0).
        split.
        -- change ([2;0;3]*>[1;2;0;3]*>r') with ([2;0;3;1]*>[2;0;3]*>r').
           remember ([2;0;3]*>r') as r'2.
           remember ([2;0;3]*>r'0) as r'3.
           ssc H2031.
        -- ca.
    + pose proof HP as HP'.
      specialize (HP ([2;0;3]*>r0)).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * right.
        exists ([2;0;3]*>r0).
        repeat split.
        1: ca.
        1: ca.
        exists (r').
        repeat split.
        1: remember ([2;0;3]*>r0) as r1.
        1: ssc H203.
        1: ca.
        specialize (HP' r').
        destruct HP' as [HP' _].
        specialize (HP' HP2).
        destruct HP' as [[r'' [HP1' HP2']]|[r'' [HP1' [r''0 [r''1 [HP2' [HP3' [HP4' HP5']]]]]]]].
        -- exists ([2;0;3]*>r'').
           split.
           1: ssc H203.
           ca.
        -- subst r'.
           exists ([2;0;2;0;2]*>r''0).
           split.
           1: ssc H20321.
           ca.
      * inverts HP1.
Qed.

Definition S0 (nr:nat*side) :=
  let '(n,r):=nr in
  0inf <* [3] <* <[4;1]^^n {{A}}> r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (26,[1;2;0;3;2;0;2;0;3;1]*>0inf)).
  1: do 2676 step1.
  1: finish.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) =>
  (forall r0, r=[1;2;0;3]*>r0 -> n<>O) /\
  (exists R, R_P R /\ R L1203 r)).
  2:{
    split.
    1: intros; congruence.
    exists R0.
    split.
    1: apply R0_spec.
    constructor.
  }
  intros [n r] [HP0 [R [HR Hr]]].
  pose proof HR as HR'.
  specialize (HR r).
  destruct HR as [_ HR].
  specialize (HR Hr).
  des2 HR.
  - exists (3+n,r').
    repeat split.
    + unfold S0.
      unfold Rstep in HP1.
      change hRL2 with (lrcons hR [(hL,hR)] hL') in HP1.
      assert (sideRLs (flip tm) [(hL,hR)] ([1;4]^^n*>[3]*>0inf) ([1;4]^^S n*>[3]*>0inf)) as HL. {
        solve_sideRLs.
        es.
      }
      follow10 (sideRLs_concat HL HP1).
      es.
    + intros.
      lia.
    + exists R.
      split; assumption.
  - subst r.
    exists (n,[2;0;3;2;0;2]*>r').
    repeat split.
    + specialize (HP0 _ (eq_refl)).
      destruct n as [|n].
      1: lia.
      unfold S0.
      remember (S n) as n0.
      er; sr; er.
      replace n0 with (n+1) by lia.
      rewrite <-lpow_add'.
      sr.
      es.
    + intros r0 HE; cbn in HE; congruence.
    + exists (RS R).
      split.
      1: apply RS_spec,HR'.
      constructor.
      assumption.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB3RB4LA4RA0LB_2LA1RB2RB---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.
Notation "'A'" := BB25.B.
Notation "'B'" := BB25.A.
Notation "'0'" := BB25.S0.
Notation "'1'" := BB25.S2.
Notation "'2'" := BB25.S1.
Notation "'3'" := BB25.S4.
Notation "'4'" := BB25.S3.
Notation "'0inf'" := (const 0).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (B,[]).
Definition hL':DH0 := (B,[2;0]).
Definition hRL2: list (DH0*DH0) := [(hR,hL);(hR,hL')].

Lemma H20321:
  segRLs tm hRL2 hRL2 [2;0;3;2;1] [2;0;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H201203:
  segRLs tm hRL2 [] [2;0;1;2;0;3] [2;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H20221:
  segRLs tm hRL2 (hRL2^^2) [2;0;2;2;1] [2;0;2;0;2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H202021:
  segRLs tm hRL2 hRL2 [2;0;2;0;2;1] [2;0;3;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H2031:
  segRLs tm hRL2 hRL2 [2;0;3;1] [1;2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H203:
  segRLs tm hRL2 hRL2 [2;0;3] [2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H202:
  segRLs tm hRL2 hRL2 [2;0;2] [2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H2020:
  segRLs tm hRL2 hRL2 [2;0;2;0] [2;0;2;0].
Proof.
  solve_segRLs.
Qed.

Lemma H20:
  segRLs tm hRL2 hRL2 [2;0] [2;0].
Proof.
  solve_segRLs.
Qed.

Lemma H2:
  segRLs tm hRL2 hRL2 [2] [2].
Proof.
  solve_segRLs.
Qed.

Inductive Ltype :=
| L21 | L1203.

Definition Rstep r1 r2 :=
  sideRLs tm hRL2 r1 r2.

Definition R_P (R:Ltype->side->Prop) :=
  forall r,
  (R L21 r -> (
    (exists r', Rstep r r' /\ R L21 r') \/
    (exists r', r = [2;1]*>r' /\
    exists r'0 r'1,
    Rstep r' r'0 /\
    Rstep r'0 r'1 /\
    R L21 ([2;0;3]*>r'1) /\
    R L1203 ([2;0;2]*>r'0)))) /\
  (R L1203 r -> (
    (exists r', Rstep r r' /\ R L1203 r') \/
    (exists r', r = [1;2;0;3]*>r' /\
    R L21 ([2;0;3]*>r') /\
    R L1203 ([2;0;2]*>r') /\
    exists r'0,
    Rstep ([2;0;3]*>r') ([2;0;3]*>r'0) /\
    R L21 ([2;0;3]*>r'0) /\
    exists r'1,
    Rstep ([2;0;3]*>r'0) r'1 /\
    R L21 (r'1))
  )).

Inductive R0: Ltype->side->Prop :=
| L1203_0: R0 L1203 ([2;0;2;2;0;2;0;3;1]*>0inf)
| L1203_1: R0 L1203 ([2;0;2;2;0;1;2;0;1]*>0inf)
| L1203_2: R0 L1203 ([2;0;2;2;2;0;3;1]*>0inf)
| L1203_3: R0 L1203 ([2;0;2;2;1;2;0;1]*>0inf)
| L1203_4: R0 L1203 ([2;0;2;0;2;0;2;0;3;1]*>0inf)
| L1203_5: R0 L1203 ([2;0;2;0;2;0;1;2;0;1]*>0inf)
| L1203_6: R0 L1203 ([2;0;2;0;2;2;0;3;1]*>0inf)
| L1203_7: R0 L1203 ([2;0;2;0;2;1;2;0;1]*>0inf)
| L1203_8: R0 L1203 ([2;0;3;2;0;2;2;1]*>0inf)
| L1203_9: R0 L1203 ([2;0;3;2;0;2;0;2;1]*>0inf)
| L1203_10: R0 L1203 ([2;0;3;2;0;3;2;0;3;1]*>0inf)
| L1203_11: R0 L1203 ([2;0;3;2;0;3;1;2;0;1]*>0inf)
| L1203_12: R0 L1203 ([2;0;3;1;2;0;3;2;1]*>0inf)
| L1203_13: R0 L1203 ([1;2;0;3;2;0;2;0;3;1]*>0inf)
| L21_0: R0 L21 ([2;0;3;2;0;2;0;3;1]*>0inf)
| L21_1: R0 L21 ([2;0;3;2;0;1;2;0;1]*>0inf)
| L21_2: R0 L21 ([2;0;3;2;2;0;3;1]*>0inf)
| L21_3: R0 L21 ([2;0;3;2;1;2;0;1]*>0inf)
| L21_4: R0 L21 ([2;0;2;0;2;2;1]*>0inf)
| L21_5: R0 L21 ([2;0;2;0;2;0;2;1]*>0inf)
| L21_6: R0 L21 ([2;0;2;0;3;2;0;3;1]*>0inf)
| L21_7: R0 L21 ([2;0;2;0;3;1;2;0;1]*>0inf)
| L21_8: R0 L21 ([2;0;1;2;0;3;2;1]*>0inf)
| L21_9: R0 L21 ([2;2;0;2;2;1]*>0inf)
| L21_10: R0 L21 ([2;2;0;2;0;2;1]*>0inf)
| L21_11: R0 L21 ([2;2;0;3;2;0;3;1]*>0inf)
| L21_12: R0 L21 ([2;2;0;3;1;2;0;1]*>0inf)
| L21_13: R0 L21 ([2;1;2;0;3;2;1]*>0inf)
.

Inductive RS(R:Ltype->side->Prop): Ltype->side->Prop :=
| A203 r:
    R L21 r ->
    RS R L21 ([2;0;3]*>r)
| A20 r:
    R L1203 r ->
    RS R L21 ([2;0]*>r)
| A2 r:
    R L1203 r ->
    RS R L21 ([2]*>r)
| B202 r:
    R L21 r ->
    RS R L1203 ([2;0;2]*>r)
| B2020 r:
    R L21 r ->
    RS R L1203 ([2;0;2;0]*>r)
| B203 r:
    R L1203 r ->
    RS R L1203 ([2;0;3]*>r)
| BOv r:
    R L21 ([2;0;3]*>r) ->
    RS R L1203 ([1;2;0;3]*>[2;0;3]*>r)
.

Ltac des1 HP :=
  destruct HP as [[r' [HP1 HP2]]|[r' [HP1 [r'0 [r'1 [HP2 [HP3 [HP4 HP5]]]]]]]].

Ltac des2 HP :=
  destruct HP as [[r' [HP1 HP2]]|[r' [HP1 [HP2 [HP3 [r'0 [HP4 [HP5 [r'1 [HP6 HP7]]]]]]]]]].

Ltac ssc H :=
  repeat rewrite <-Str_app_assoc;
  eapply segRLs_sideRLs_concat;
  [ apply H | ];
  (assumption || constructor).

Ltac ca :=
  constructor; assumption.

Ltac solve_sideRLs :=
  (eapply sideRLseq_O; fail) ||
  (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    er | solve_sideRLs ]).

Ltac solve_R0 :=
  left;
  eexists; split;
  [ solve_sideRLs | ]; constructor.

Lemma R0_spec:
  R_P R0.
Proof.
  unfold R_P.
  intros r.
  split.
  - intros HO.
    inverts HO.
    1-13: solve_R0.
    right.
    eexists.
    split.
    1: cbn; reflexivity.
    eexists _,_.
    repeat split.
    1: solve_sideRLs.
    1: solve_sideRLs.
    1,2: constructor.
  - intros HO.
    inverts HO.
    1-13: solve_R0.
    right.
    eexists.
    split.
    1: cbn; reflexivity.
    repeat split.
    1,2: constructor.
    eexists.
    repeat split.
    1: solve_sideRLs.
    1: constructor.
    eexists.
    split.
    1: solve_sideRLs.
    1: constructor.
Qed.

Lemma RS_spec R:
  R_P R ->
  R_P (RS R).
Proof.
  unfold R_P.
  intros HP r.
  split.
  - intros HS.
    inverts HS.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;3]*>r').
        split.
        1: ssc H203.
        ca.
      * left.
        subst r0.
        exists ([2;0;2;0;2]*>r'0).
        split.
        1: ssc H20321.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0]*>r').
        split.
        1: ssc H20.
        ca.
      * left.
        subst r0.
        exists ([2;2;0;2]*>r').
        split.
        1: ssc H201203.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des2 HP.
      * left.
        exists ([2]*>r').
        split.
        1: ssc H2.
        ca.
      * subst r0.
        right.
        exists ([2;0;3]*>r').
        split.
        1: reflexivity.
        exists ([2;0;3]*>r'0) (r'1).
        repeat split.
        1,2: assumption.
        1,2: ca.
  - intros HS.
    inverts HS.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;2]*>r').
        split.
        1: ssc H202.
        ca.
      * left.
        subst r0.
        exists ([2;0;2;0;2;0;3]*>r'1).
        split.
        -- unfold Rstep.
           rewrite <-Str_app_assoc.
           eapply segRLs_sideRLs_concat.
           1: apply H20221.
           change (hRL2^^2) with (hRL2++hRL2).
           eapply sideRLs_trans; eassumption.
        -- ca.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;2;0]*>r').
        split.
        1: ssc H2020.
        ca.
      * left.
        subst r0.
        exists ([2;0;3;2;0;2]*>r'0).
        split.
        1: ssc H202021.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des2 HP.
      * left.
        exists ([2;0;3]*>r').
        split.
        1: ssc H203.
        ca.
      * subst r0.
        left.
        exists ([1;2;0;3]*>[2;0;3]*>r'0).
        split.
        -- change ([2;0;3]*>[1;2;0;3]*>r') with ([2;0;3;1]*>[2;0;3]*>r').
           remember ([2;0;3]*>r') as r'2.
           remember ([2;0;3]*>r'0) as r'3.
           ssc H2031.
        -- ca.
    + pose proof HP as HP'.
      specialize (HP ([2;0;3]*>r0)).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * right.
        exists ([2;0;3]*>r0).
        repeat split.
        1: ca.
        1: ca.
        exists (r').
        repeat split.
        1: remember ([2;0;3]*>r0) as r1.
        1: ssc H203.
        1: ca.
        specialize (HP' r').
        destruct HP' as [HP' _].
        specialize (HP' HP2).
        destruct HP' as [[r'' [HP1' HP2']]|[r'' [HP1' [r''0 [r''1 [HP2' [HP3' [HP4' HP5']]]]]]]].
        -- exists ([2;0;3]*>r'').
           split.
           1: ssc H203.
           ca.
        -- subst r'.
           exists ([2;0;2;0;2]*>r''0).
           split.
           1: ssc H20321.
           ca.
      * inverts HP1.
Qed.

Definition S0 (nr:nat*side) :=
  let '(n,r):=nr in
  0inf <* <[4;4;1]^^n <* [2] {{BB25.B}}> [2;0;3] *> r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (12,[2;1;2;0;3;2;1]*>0inf)).
  1: do 3357 step1.
  1: finish.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) =>
  (forall r0, r=[2;1]*>r0 -> n<>O) /\
  (exists R, R_P R /\ R L21 r)).
  2:{
    split.
    1: intros; congruence.
    exists R0.
    split.
    1: apply R0_spec.
    constructor.
  }
  intros [n r] [HP0 [R [HR Hr]]].
  pose proof HR as HR'.
  specialize (HR r).
  destruct HR as [HR _].
  specialize (HR Hr).
  des1 HR.
  - exists (1+n,r').
    repeat split.
    + unfold S0.
      unfold Rstep in HP1.
      change hRL2 with (lrcons hR [(hL,hR)] hL') in HP1.
      assert (sideRLs (flip tm) [(hL,hR)] ([2]*>[1;4;4]^^n*>0inf) ([4]*>[1;4;4]^^n*>0inf)) as HL. {
        solve_sideRLs.
      }
      epose proof (segRLs_sideRLs_concat H203 HP1) as HP1'.
      follow10 (sideRLs_concat HL HP1').
      cbn.
      er; sr.
      change (2>>0>>3>>[2;0;3]^^n*>r') with ([2;0;3]^^(1+n)*>r').
      remember (1+n) as n0.
      er.
      replace n0 with (n+1) by lia.
      rewrite <-lpow_add'.
      sr.
      es.
    + intros.
      lia.
    + exists R.
      split; assumption.
  - subst r.
    exists (n,[2;0;2;0;2]*>r'0).
    repeat split.
    + unfold S0.
      assert (sideRLs tm hRL2 ([2;0;3;2;1]*>r') ([2;0;2;0;2]*>r'0)) as HR_. {
        ssc H20321.
      }
      change hRL2 with (lrcons hR [(hL,hR)] hL') in HR_.
      assert (sideRLs (flip tm) [(hL,hR)] ([2]*>[1;4;4]^^n*>0inf) ([4]*>[1;4;4]^^n*>0inf)) as HL. {
        solve_sideRLs.
      }
      follow10 (sideRLs_concat HL HR_).
      cbn.
      er; sr.
      mid (B,(0inf,0,[2;0;3]^^(n+1)*>[2;0;2;0;2]*>r'0)).
      1: es.
      rewrite <-lpow_add'.
      step1.
      sr.
      es.
    + intros r0 HE; cbn in HE; congruence.
    + exists (RS R).
      split.
      1: apply RS_spec,HR'.
      constructor.
      assumption.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB1RA3LB3RA---_0RA2LB0LA4RA2RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.
Notation "'0'" := BB25.S0.
Notation "'1'" := BB25.S1.
Notation "'2'" := BB25.S3.
Notation "'3'" := BB25.S2.
Notation "'4'" := BB25.S4.
Notation "'0inf'" := (const 0).

Definition hR:DH0 := (A,[]).
Definition hL:DH0 := (B,[]).
Definition hL':DH0 := (B,[2;0]).
Definition hRL2: list (DH0*DH0) := [(hR,hL);(hR,hL')].

Lemma H20321:
  segRLs tm hRL2 hRL2 [2;0;3;2;1] [2;0;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H201203:
  segRLs tm hRL2 [] [2;0;1;2;0;3] [2;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H20221:
  segRLs tm hRL2 (hRL2^^2) [2;0;2;2;1] [2;0;2;0;2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H202021:
  segRLs tm hRL2 hRL2 [2;0;2;0;2;1] [2;0;3;2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H2031:
  segRLs tm hRL2 hRL2 [2;0;3;1] [1;2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H203:
  segRLs tm hRL2 hRL2 [2;0;3] [2;0;3].
Proof.
  solve_segRLs.
Qed.

Lemma H202:
  segRLs tm hRL2 hRL2 [2;0;2] [2;0;2].
Proof.
  solve_segRLs.
Qed.

Lemma H2020:
  segRLs tm hRL2 hRL2 [2;0;2;0] [2;0;2;0].
Proof.
  solve_segRLs.
Qed.

Lemma H20:
  segRLs tm hRL2 hRL2 [2;0] [2;0].
Proof.
  solve_segRLs.
Qed.

Lemma H2:
  segRLs tm hRL2 hRL2 [2] [2].
Proof.
  solve_segRLs.
Qed.

Inductive Ltype :=
| L21 | L1203.

Definition Rstep r1 r2 :=
  sideRLs tm hRL2 r1 r2.

Definition R_P (R:Ltype->side->Prop) :=
  forall r,
  (R L21 r -> (
    (exists r', Rstep r r' /\ R L21 r') \/
    (exists r', r = [2;1]*>r' /\
    exists r'0 r'1,
    Rstep r' r'0 /\
    Rstep r'0 r'1 /\
    R L21 ([2;0;3]*>r'1) /\
    R L1203 ([2;0;2]*>r'0)))) /\
  (R L1203 r -> (
    (exists r', Rstep r r' /\ R L1203 r') \/
    (exists r', r = [1;2;0;3]*>r' /\
    R L21 ([2;0;3]*>r') /\
    R L1203 ([2;0;2]*>r') /\
    exists r'0,
    Rstep ([2;0;3]*>r') ([2;0;3]*>r'0) /\
    R L21 ([2;0;3]*>r'0) /\
    exists r'1,
    Rstep ([2;0;3]*>r'0) r'1 /\
    R L21 (r'1))
  )).

Inductive R0: Ltype->side->Prop :=
| L1203_0: R0 L1203 ([2;0;2;2;0;2;0;3;1]*>0inf)
| L1203_1: R0 L1203 ([2;0;2;2;0;1;2;0;1]*>0inf)
| L1203_2: R0 L1203 ([2;0;2;2;2;0;3;1]*>0inf)
| L1203_3: R0 L1203 ([2;0;2;2;1;2;0;1]*>0inf)
| L1203_4: R0 L1203 ([2;0;2;0;2;0;2;0;3;1]*>0inf)
| L1203_5: R0 L1203 ([2;0;2;0;2;0;1;2;0;1]*>0inf)
| L1203_6: R0 L1203 ([2;0;2;0;2;2;0;3;1]*>0inf)
| L1203_7: R0 L1203 ([2;0;2;0;2;1;2;0;1]*>0inf)
| L1203_8: R0 L1203 ([2;0;3;2;0;2;2;1]*>0inf)
| L1203_9: R0 L1203 ([2;0;3;2;0;2;0;2;1]*>0inf)
| L1203_10: R0 L1203 ([2;0;3;2;0;3;2;0;3;1]*>0inf)
| L1203_11: R0 L1203 ([2;0;3;2;0;3;1;2;0;1]*>0inf)
| L1203_12: R0 L1203 ([2;0;3;1;2;0;3;2;1]*>0inf)
| L1203_13: R0 L1203 ([1;2;0;3;2;0;2;0;3;1]*>0inf)
| L21_0: R0 L21 ([2;0;3;2;0;2;0;3;1]*>0inf)
| L21_1: R0 L21 ([2;0;3;2;0;1;2;0;1]*>0inf)
| L21_2: R0 L21 ([2;0;3;2;2;0;3;1]*>0inf)
| L21_3: R0 L21 ([2;0;3;2;1;2;0;1]*>0inf)
| L21_4: R0 L21 ([2;0;2;0;2;2;1]*>0inf)
| L21_5: R0 L21 ([2;0;2;0;2;0;2;1]*>0inf)
| L21_6: R0 L21 ([2;0;2;0;3;2;0;3;1]*>0inf)
| L21_7: R0 L21 ([2;0;2;0;3;1;2;0;1]*>0inf)
| L21_8: R0 L21 ([2;0;1;2;0;3;2;1]*>0inf)
| L21_9: R0 L21 ([2;2;0;2;2;1]*>0inf)
| L21_10: R0 L21 ([2;2;0;2;0;2;1]*>0inf)
| L21_11: R0 L21 ([2;2;0;3;2;0;3;1]*>0inf)
| L21_12: R0 L21 ([2;2;0;3;1;2;0;1]*>0inf)
| L21_13: R0 L21 ([2;1;2;0;3;2;1]*>0inf)
.

Inductive RS(R:Ltype->side->Prop): Ltype->side->Prop :=
| A203 r:
    R L21 r ->
    RS R L21 ([2;0;3]*>r)
| A20 r:
    R L1203 r ->
    RS R L21 ([2;0]*>r)
| A2 r:
    R L1203 r ->
    RS R L21 ([2]*>r)
| B202 r:
    R L21 r ->
    RS R L1203 ([2;0;2]*>r)
| B2020 r:
    R L21 r ->
    RS R L1203 ([2;0;2;0]*>r)
| B203 r:
    R L1203 r ->
    RS R L1203 ([2;0;3]*>r)
| BOv r:
    R L21 ([2;0;3]*>r) ->
    RS R L1203 ([1;2;0;3]*>[2;0;3]*>r)
.

Ltac des1 HP :=
  destruct HP as [[r' [HP1 HP2]]|[r' [HP1 [r'0 [r'1 [HP2 [HP3 [HP4 HP5]]]]]]]].

Ltac des2 HP :=
  destruct HP as [[r' [HP1 HP2]]|[r' [HP1 [HP2 [HP3 [r'0 [HP4 [HP5 [r'1 [HP6 HP7]]]]]]]]]].

Ltac ssc H :=
  repeat rewrite <-Str_app_assoc;
  eapply segRLs_sideRLs_concat;
  [ apply H | ];
  (assumption || constructor).

Ltac ca :=
  constructor; assumption.

Ltac solve_sideRLs :=
  (eapply sideRLseq_O; fail) ||
  (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    er | solve_sideRLs ]).

Ltac solve_R0 :=
  left;
  eexists; split;
  [ solve_sideRLs | ]; constructor.

Lemma R0_spec:
  R_P R0.
Proof.
  unfold R_P.
  intros r.
  split.
  - intros HO.
    inverts HO.
    1-13: solve_R0.
    right.
    eexists.
    split.
    1: cbn; reflexivity.
    eexists _,_.
    repeat split.
    1: solve_sideRLs.
    1: solve_sideRLs.
    1,2: constructor.
  - intros HO.
    inverts HO.
    1-13: solve_R0.
    right.
    eexists.
    split.
    1: cbn; reflexivity.
    repeat split.
    1,2: constructor.
    eexists.
    repeat split.
    1: solve_sideRLs.
    1: constructor.
    eexists.
    split.
    1: solve_sideRLs.
    1: constructor.
Qed.

Lemma RS_spec R:
  R_P R ->
  R_P (RS R).
Proof.
  unfold R_P.
  intros HP r.
  split.
  - intros HS.
    inverts HS.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;3]*>r').
        split.
        1: ssc H203.
        ca.
      * left.
        subst r0.
        exists ([2;0;2;0;2]*>r'0).
        split.
        1: ssc H20321.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0]*>r').
        split.
        1: ssc H20.
        ca.
      * left.
        subst r0.
        exists ([2;2;0;2]*>r').
        split.
        1: ssc H201203.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des2 HP.
      * left.
        exists ([2]*>r').
        split.
        1: ssc H2.
        ca.
      * subst r0.
        right.
        exists ([2;0;3]*>r').
        split.
        1: reflexivity.
        exists ([2;0;3]*>r'0) (r'1).
        repeat split.
        1,2: assumption.
        1,2: ca.
  - intros HS.
    inverts HS.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;2]*>r').
        split.
        1: ssc H202.
        ca.
      * left.
        subst r0.
        exists ([2;0;2;0;2;0;3]*>r'1).
        split.
        -- unfold Rstep.
           rewrite <-Str_app_assoc.
           eapply segRLs_sideRLs_concat.
           1: apply H20221.
           change (hRL2^^2) with (hRL2++hRL2).
           eapply sideRLs_trans; eassumption.
        -- ca.
    + specialize (HP r0).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * left.
        exists ([2;0;2;0]*>r').
        split.
        1: ssc H2020.
        ca.
      * left.
        subst r0.
        exists ([2;0;3;2;0;2]*>r'0).
        split.
        1: ssc H202021.
        ca.
    + specialize (HP r0).
      destruct HP as [_ HP].
      specialize (HP H).
      des2 HP.
      * left.
        exists ([2;0;3]*>r').
        split.
        1: ssc H203.
        ca.
      * subst r0.
        left.
        exists ([1;2;0;3]*>[2;0;3]*>r'0).
        split.
        -- change ([2;0;3]*>[1;2;0;3]*>r') with ([2;0;3;1]*>[2;0;3]*>r').
           remember ([2;0;3]*>r') as r'2.
           remember ([2;0;3]*>r'0) as r'3.
           ssc H2031.
        -- ca.
    + pose proof HP as HP'.
      specialize (HP ([2;0;3]*>r0)).
      destruct HP as [HP _].
      specialize (HP H).
      des1 HP.
      * right.
        exists ([2;0;3]*>r0).
        repeat split.
        1: ca.
        1: ca.
        exists (r').
        repeat split.
        1: remember ([2;0;3]*>r0) as r1.
        1: ssc H203.
        1: ca.
        specialize (HP' r').
        destruct HP' as [HP' _].
        specialize (HP' HP2).
        destruct HP' as [[r'' [HP1' HP2']]|[r'' [HP1' [r''0 [r''1 [HP2' [HP3' [HP4' HP5']]]]]]]].
        -- exists ([2;0;3]*>r'').
           split.
           1: ssc H203.
           ca.
        -- subst r'.
           exists ([2;0;2;0;2]*>r''0).
           split.
           1: ssc H20321.
           ca.
      * inverts HP1.
Qed.

Definition S0 (nr:nat*side) :=
  let '(n,r):=nr in
  0inf <* [3] <* <[4;4;1]^^n <* [2] {{A}}> [2;0;3] *> r.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (12,[2;1;2;0;3;2;1]*>0inf)).
  1: do 3594 step1.
  1: finish.
  eapply progress_nonhalt_cond with (P:=fun '(n,r) =>
  (forall r0, r=[2;1]*>r0 -> n<>O) /\
  (exists R, R_P R /\ R L21 r)).
  2:{
    split.
    1: intros; congruence.
    exists R0.
    split.
    1: apply R0_spec.
    constructor.
  }
  intros [n r] [HP0 [R [HR Hr]]].
  pose proof HR as HR'.
  specialize (HR r).
  destruct HR as [HR _].
  specialize (HR Hr).
  des1 HR.
  - exists (1+n,r').
    repeat split.
    + unfold S0.
      unfold Rstep in HP1.
      change hRL2 with (lrcons hR [(hL,hR)] hL') in HP1.
      assert (sideRLs (flip tm) [(hL,hR)] ([2]*>[1;4;4]^^n*>[3]*>0inf) ([4]*>[1;4;4]^^n*>[3]*>0inf)) as HL. {
        solve_sideRLs.
      }
      epose proof (segRLs_sideRLs_concat H203 HP1) as HP1'.
      follow10 (sideRLs_concat HL HP1').
      cbn.
      er; sr.
      change (2>>0>>3>>[2;0;3]^^n*>r') with ([2;0;3]^^(1+n)*>r').
      remember (1+n) as n0.
      er.
      replace n0 with (n+1) by lia.
      rewrite <-lpow_add'.
      sr.
      es.
    + intros.
      lia.
    + exists R.
      split; assumption.
  - subst r.
    exists (n,[2;0;2;0;2]*>r'0).
    repeat split.
    + unfold S0.
      assert (sideRLs tm hRL2 ([2;0;3;2;1]*>r') ([2;0;2;0;2]*>r'0)) as HR_. {
        ssc H20321.
      }
      change hRL2 with (lrcons hR [(hL,hR)] hL') in HR_.
      assert (sideRLs (flip tm) [(hL,hR)] ([2]*>[1;4;4]^^n*>[3]*>0inf) ([4]*>[1;4;4]^^n*>[3]*>0inf)) as HL. {
        solve_sideRLs.
      }
      follow10 (sideRLs_concat HL HR_).
      cbn.
      specialize (HP0 _ (eq_refl)).
      destruct n as [|n]. 1: lia.
      er; sr.
      mid (B,(0inf,3,[2;0;3]^^(1+n+1)*>[2;0;2;0;2]*>r'0)).
      1: es.
      do 2 rewrite <-lpow_add'.
      repeat step1.
      sr.
      es.
    + intros r0 HE; cbn in HE; congruence.
    + exists (RS R).
      split.
      1: apply RS_spec,HR'.
      constructor.
      assumption.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB2LA3LB1RA3LA_1LA4RA3RB0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[1]).
Definition hL:DH0 := (A,[]).
Definition hRL2: list (DH0*DH0) := [(hR,hL);(hR,hL)].

Inductive RDigits :=
| d00 | d22 | d3.

Fixpoint R ls :=
match ls with
| d00::ls0 => [0;0]*>R ls0
| d22::ls0 => [2;2]*>R ls0
| d3::ls0 => [3]*>R ls0
| [] => 0inf
end.

Fixpoint RInc ls :=
match ls with
| d00::ls0 => d3::d3::d22::ls0
| d22::ls0 => d22::RInc ls0
| d3::ls0 => d3::RInc ls0
| [] => [d3;d3;d22]
end.

Ltac solve_sideRLs :=
  (eapply sideRLseq_O; fail) ||
  (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    er | solve_sideRLs ]).

Lemma RInc_spec ls:
  sideRLs tm hRL2 (R ls) (R (RInc ls)).
Proof.
  induction ls.
  - cbn.
    solve_sideRLs.
  - destruct a.
    1: cbn; solve_sideRLs.
    1,2: cbn[RInc]; cbn[R];
      eapply @segRLs_sideRLs_concat with (ls2:=hRL2);
      [ solve_segRLs |];
      assumption.
Qed.

Lemma RInc_spec' ls:
  exists n ls0, RInc ls = [d22]^^n ++ d3::ls0.
Proof.
  induction ls.
  - cbn.
    eexists O,_.
    reflexivity.
  - cbn.
    destruct IHls as [n [ls0 I]].
    rewrite I.
    destruct a.
    + eexists O,_; reflexivity.
    + eexists (S n),_; reflexivity.
    + eexists O,_; reflexivity.
Qed.
    
Lemma ROv n ls:
  sideRL tm (B,[]) (B,[0]) (R ([d22]^^n ++ d3::ls)) (R ([d00]^^n ++ ls)).
Proof.
  unfold sideRL,to_DH_config.
  induction n; intros.
  - cbn. er.
  - er.
    follow100 IHn.
    er.
Qed.

Definition hR':DH0 := (B,[]).
Definition hL':DH0 := (B,[0]).
Definition hRL3 := hRL2^^2++[(hR',hL')].

Lemma Rstep ls:
  exists ls',
  sideRLs tm hRL3 (R ls) (R ls').
Proof.
  epose proof (RInc_spec' (RInc ls)) as [n [ls0 I]].
  eexists _.
  unfold hRL3.
  eapply sideRLs_trans.
  1:{
    change (hRL2^^2) with (hRL2++hRL2).
    eapply sideRLs_trans;
    apply RInc_spec.
  }
  eapply sideRLseq_S.
  2: constructor.
  rewrite I.
  apply ROv.
Qed.

Definition config '(n,ls) := 0inf <* [4]^^n <* <[1;3;4;1;3;3;4;4] {{{ (hR,TM.R) }}} R ls.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (10,[d00;d3;d22]++[d3;d3;d22]^^3)).
  1: do 1086 step1.
  1: finish.
  eapply progress_nonhalt_simple.
  intros [n ls].
  pose proof (Rstep ls) as [ls' Hls'].
  eexists (3+n,ls').
  change hRL3 with (lrcons hR [(hL,hR);(hL,hR);(hL,hR);(hL,hR')] hL') in Hls'.
  epose proof (sideRLs_concat _ Hls') as H.
  follow10 H.
  Unshelve.
  3: solve_sideRLs; es.
  es.
Qed.

End TM4.


