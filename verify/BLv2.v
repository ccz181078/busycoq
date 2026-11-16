From BusyCoq Require Import Individual62.

Require Import ZArith Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal.
Import Eqb.

Definition if_None {A} (a:option A) b :=
match a with
| None => b tt
| _ => a
end.

Notation "a ||| b" := (if_None a b) (at level 30, right associativity).

Import Eqb.

Ltac des_if H :=
  cbn[if_None] in H;
  cbn[if_Some] in H;
  let E:=fresh "E" in
  match type of H with
  | ?a ||| _ = _ =>
    destruct a eqn:E
  | ?a &&& _ = _ =>
    destruct a eqn:E
  end.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_0RB0RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,<[0;1]).
Notation hL := (C,@nil Sym).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation w := [1;0;0;0].
Notation w' := <[0;1;1;1].
Notation d2 := [1;0;0;1;0;1;0;0;1;0].
Notation d2' := <[1;0;1;1;1;1].

Inductive LC: nat->side->Prop :=
| LC_O:
  LC O (0inf<*<[1])
| LC_S i l n:
  LC i l ->
  LC (S i) (l<*w'^^n<*d2').

Definition tm' := flip tm.

Lemma d2'_Incs k n:
  segRLs tm' (hLR^^k) (hLR^^(k*3)) (w'^^n<+d2') (w'^^(k+n)<+d2').
Proof.
  gen n.
  induction k; intros.
  - esx.
  - replace (S k*3) with (3+k*3) by lia.
    cbn[lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: applys_eq (IHk (1+n)); flia.
    esx.
Qed.

Lemma LIncs i l n:
  LC i l ->
  exists l',
  sideRLs tm' (hLR^^n) l l' /\
  LC i l'.
Proof.
  gen l n.
  induction i; intros.
  - inverts H.
    eexists; split.
    + apply sideRLs_wall; esx.
    + apply LC_O.
  - inverts H.
    epose proof (IHi _ n H1) as [l2 [I1 I2]].
    epose proof (IHi _ n I2) as [l3 [I3 I4]].
    epose proof (IHi _ n I4) as [l4 [I5 I6]].
    rewrite <-Str_app_assoc.
    eexists; split.
    + eapply segRLs_sideRLs_concat.
      1: apply d2'_Incs.
      replace (n*3) with (n+(n+n)) by lia.
      eapply sideRLs_trans_add; [eauto 1|].
      eapply sideRLs_trans_add; eauto 1.
    + rewrite Str_app_assoc.
      eapply LC_S,I6.
Qed.

Definition S0 l m r := l <* w'^^m {{{ (hR,R) }}} r.
Definition maxT := 1000.

Definition RInc r :=
  skip_prefix w r ||| (fun _ =>
  skip_prefix d2 r ||| (fun _ =>
  sideRL_c tm hR hL r maxT)).

Opaque maxT.

Lemma RInc_spec r r' i l m:
  RInc r = Some r' ->
  LC i l ->
  exists i' l' m',
  S0 l m r -->* S0 l' m' r' /\ LC i' l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    exists i l (1+m); split.
    - er.
    - apply HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    exists (S i) (l<*w'^^(1+m)<*d2') O; split.
    - er.
    - apply LC_S,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    epose proof (LIncs _ _ 1 HLC) as [l' [I1 I2]].
    eapply sideRLs_1 in I1.
    eapply unflip_progress in I1.
    cbn in I1.
    eexists _,l',m; split.
    - unfold S0.
      follow100 H.
      es; er.
      follow100 I1.
      es.
    - apply I2.
  }
Qed.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec i n l m r r':
  LC i l ->
  RIncs n r = Some r' ->
  exists i' l' m', S0 l m r -->* S0 l' m' r' /\ LC i' l'.
Proof.
  gen i l m r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists _,_,_; split.
    + finish.
    + apply HLC.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [i' [l'0 [m' [I3 I4]]]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [i'0 [l'1 [m'0 [I1 I2]]]].
      eexists _,_,_; split.
      * follow I3; apply I1.
      * eauto 1.
    + inverts H.
Qed.

Transparent maxT.

Notation rh := ([1;0;1]*>0inf).

Lemma init:
  exists i l m,
  c0 -->* S0 l m rh /\ LC i l.
Proof.
  eexists _,_,1%nat; split.
  2: apply LC_O.
  esx.
Qed.

Lemma halt:
  halts tm c0.
Proof.
  epose proof init as [i [l [m [I1 I2]]]].
  epose proof (RIncs_spec _ 10430 _ _ rh _ I2 ltac:(vm_compute; reflexivity)) as [i' [l' [m' [I3 I4]]]].
  eapply halts_evstep.
  2:{
    follow I1.
    follow I3.
    finish.
  }
  esx.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LD_1LD1RF_1RE0LD_0LB0RB_0RC0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[0;1]).
Notation hL := (D,@nil Sym).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation w := [1;0;0;0].
Notation w' := <[0;1;1;1].
Notation d2 := [1;0;0;1;0;1;0;0;1;0].
Notation d2' := <[1;0;1;1;1;1].

Inductive LC: nat->side->Prop :=
| LC_O:
  LC O (0inf<*<[1])
| LC_S i l n:
  LC i l ->
  LC (S i) (l<*w'^^n<*d2').

Definition tm' := flip tm.

Lemma d2'_Incs k n:
  segRLs tm' (hLR^^k) (hLR^^(k*3)) (w'^^n<+d2') (w'^^(k+n)<+d2').
Proof.
  gen n.
  induction k; intros.
  - esx.
  - replace (S k*3) with (3+k*3) by lia.
    cbn[lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: applys_eq (IHk (1+n)); flia.
    esx.
Qed.

Lemma LIncs i l n:
  LC i l ->
  exists l',
  sideRLs tm' (hLR^^n) l l' /\
  LC i l'.
Proof.
  gen l n.
  induction i; intros.
  - inverts H.
    eexists; split.
    + apply sideRLs_wall; esx.
    + apply LC_O.
  - inverts H.
    epose proof (IHi _ n H1) as [l2 [I1 I2]].
    epose proof (IHi _ n I2) as [l3 [I3 I4]].
    epose proof (IHi _ n I4) as [l4 [I5 I6]].
    rewrite <-Str_app_assoc.
    eexists; split.
    + eapply segRLs_sideRLs_concat.
      1: apply d2'_Incs.
      replace (n*3) with (n+(n+n)) by lia.
      eapply sideRLs_trans_add; [eauto 1|].
      eapply sideRLs_trans_add; eauto 1.
    + rewrite Str_app_assoc.
      eapply LC_S,I6.
Qed.

Definition S0 l m r := l <* w'^^m {{{ (hR,R) }}} r.
Definition maxT := 1000.

Definition RInc r :=
  skip_prefix w r ||| (fun _ =>
  skip_prefix d2 r ||| (fun _ =>
  sideRL_c tm hR hL r maxT)).

Opaque maxT.

Lemma RInc_spec r r' i l m:
  RInc r = Some r' ->
  LC i l ->
  exists i' l' m',
  S0 l m r -->* S0 l' m' r' /\ LC i' l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    exists i l (1+m); split.
    - er.
    - apply HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    exists (S i) (l<*w'^^(1+m)<*d2') O; split.
    - er.
    - apply LC_S,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    epose proof (LIncs _ _ 1 HLC) as [l' [I1 I2]].
    eapply sideRLs_1 in I1.
    eapply unflip_progress in I1.
    cbn in I1.
    eexists _,l',m; split.
    - unfold S0.
      follow100 H.
      es; er.
      follow100 I1.
      es.
    - apply I2.
  }
Qed.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec i n l m r r':
  LC i l ->
  RIncs n r = Some r' ->
  exists i' l' m', S0 l m r -->* S0 l' m' r' /\ LC i' l'.
Proof.
  gen i l m r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists _,_,_; split.
    + finish.
    + apply HLC.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [i' [l'0 [m' [I3 I4]]]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [i'0 [l'1 [m'0 [I1 I2]]]].
      eexists _,_,_; split.
      * follow I3; apply I1.
      * eauto 1.
    + inverts H.
Qed.

Transparent maxT.

Notation rh := ([1;0;1]*>0inf).

Lemma init:
  exists i l m,
  c0 -->* S0 l m rh /\ LC i l.
Proof.
  eexists _,_,0%nat; split.
  2:{
    apply LC_S with (n:=2).
    apply LC_O.
  }
  esx.
Qed.

Lemma halt:
  halts tm c0.
Proof.
  epose proof init as [i [l [m [I1 I2]]]].
  epose proof (RIncs_spec _ 10430 _ _ rh _ I2 ltac:(vm_compute; reflexivity)) as [i' [l' [m' [I3 I4]]]].
  eapply halts_evstep.
  2:{
    follow I1.
    follow I3.
    finish.
  }
  esx.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC1RF_1LD1LE_0LC1RE_1RA0LE_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (E,<[0;1;0;1;1;1;0;1;1;1;1;0]).
Notation hL := (E,[0;0;0;0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].
Notation w := [1;0;1;0;0;1;0;1;0;0;0;0;1;0;1].
Notation w' := <[1;1;1;0;1;0;1;0;1;1;1;1;1;1;1].
Notation d2 := [1;0;1;0;0;0;0;0;1;0;0;0;0;0;1;0;0;0;0;0;0;1;0;1;0;0;0;1;0;1;0;0;1;0;1;0;0;0;0;1;0;1].
Notation d2' := <[0;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1].

Inductive LC: nat->side->Prop :=
| LC_O:
  LC O (0inf<*<[1]^^11)
| LC_S i l n:
  LC i l ->
  LC (S i) (l<*w'^^n<*d2').

Definition tm' := flip tm.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^5); reflexivity).

Lemma d2'_Incs k n:
  segRLs tm' (hLR^^k) (hLR^^(k*16)) (w'^^n<+d2') (w'^^(k*8+n)<+d2').
Proof.
  gen n.
  induction k; intros.
  - esx.
  - replace (S k*16) with (16+k*16) by lia.
    cbn[lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: applys_eq (IHk (8+n)); flia.
    rewrite lpow_add,app_assoc.
    eapply @segRLs_concat with (ls2:=hLR^^16).
    1: esc.
    eapply segRLs_wall''.
    clear.
    induction n.
    1: esx.
    cbn[lpow].
    eapply segRLs_concat.
    2: apply IHn.
    esc.
Qed.

Lemma LIncs i l n:
  LC i l ->
  exists l',
  sideRLs tm' (hLR^^n) l l' /\
  LC i l'.
Proof.
  gen l n.
  induction i; intros.
  - inverts H.
    eexists; split.
    + apply sideRLs_wall; esx.
    + apply LC_O.
  - inverts H.
    assert (I0:forall k, exists l1', sideRLs tm' (hLR^^(k*n)) l1 l1' /\ LC i l1'). {
      induction k.
      - eexists; split.
        2: apply H1.
        esx.
      - destruct IHk as [l1' [I1 I2]].
        epose proof (IHi _ n I2) as [l1'0 [I3 I4]].
        eexists; split.
        + replace (S k*n) with (k*n+n) by lia.
          eapply sideRLs_trans_add; eauto 1.
        + eauto 1.
    }
    destruct (I0 16) as [l1' [I1 I2]].
    rewrite <-Str_app_assoc.
    eexists; split.
    + eapply segRLs_sideRLs_concat.
      1: apply d2'_Incs.
      applys_eq I1; flia.
    + rewrite Str_app_assoc.
      eapply LC_S,I2.
Qed.

Definition S0 l m r := l <* w'^^m {{{ (hR,R) }}} r.
Definition maxT := (10^5).

Definition RInc r :=
  skip_prefix w r ||| (fun _ =>
  skip_prefix d2 r ||| (fun _ =>
  sideRL_c tm hR hL r maxT)).

Opaque maxT.

Ltac use_shift_rule ::= use_shift_rule'.

Lemma RInc_spec r r' i l m:
  RInc r = Some r' ->
  LC i l ->
  exists i' l' m',
  S0 l m r -->* S0 l' m' r' /\ LC i' l'.
Proof.
  unfold RInc.
  intros H HLC.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    exists i l (1+m); split.
    - er.
    - apply HLC.
  }
  clear E.
  des_if H.
  {
    inverts H.
    apply skip_prefix_spec in E; subst.
    exists (S i) (l<*w'^^(m)<*d2') O; split.
    - er.
    - apply LC_S,HLC.
  }
  clear E.
  cbn[if_None] in H.
  {
    apply sideRL_c_spec in H.
    unfold sideRL in H.
    epose proof (LIncs _ _ 1 HLC) as [l' [I1 I2]].
    eapply sideRLs_1 in I1.
    eapply unflip_progress in I1.
    cbn in I1.
    eexists _,l',m; split.
    - unfold S0.
      follow100 H.
      es; er.
      follow100 I1.
      es.
    - apply I2.
  }
Qed.

Definition RIncs n (r:side) :=
  N.iter n (fun x => x &&& RInc) (Some r).

Lemma RIncs_spec i n l m r r':
  LC i l ->
  RIncs n r = Some r' ->
  exists i' l' m', S0 l m r -->* S0 l' m' r' /\ LC i' l'.
Proof.
  gen i l m r r'.
  induction n using N.peano_ind.
  - introv HLC H.
    inverts H.
    eexists _,_,_; split.
    + finish.
    + apply HLC.
  - introv HLC H.
    unfold RIncs in H.
    rewrite N.iter_succ in H.
    des_if H.
    + inverts H.
      eapply IHn in E.
      2: apply HLC.
      destruct E as [i' [l'0 [m' [I3 I4]]]].
      eapply RInc_spec in H1.
      2: apply I4.
      destruct H1 as [i'0 [l'1 [m'0 [I1 I2]]]].
      eexists _,_,_; split.
      * follow I3; apply I1.
      * eauto 1.
    + inverts H.
Qed.

Transparent maxT.

Notation rh := ([1;0;1;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;1;0;0;1;0;1;0;0;0;0;0;1;0;1;0;1]*>0inf).

Lemma init:
  exists i l m,
  c0 -->* S0 l m rh /\ LC i l.
Proof.
  eexists _,_,0%nat; split.
  2: apply LC_O.
  esx.
Qed.

Lemma halt:
  halts tm c0.
Proof.
  epose proof init as [i [l [m [I1 I2]]]].
  epose proof (RIncs_spec _ 478 _ _ rh _ I2 ltac:(vm_compute; reflexivity)) as [i' [l' [m' [I3 I4]]]].
  eapply halts_evstep.
  2:{
    follow I1.
    follow I3.
    eapply without_counter.
    eapply multistep_c_spec with (n:=6827).
    1: vm_compute; reflexivity.
  }
  esx.
Qed.

End TM3.



