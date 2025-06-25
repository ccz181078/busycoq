From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import NatMod.
From BusyCoq Require Import SimplTape.

Open Scope list.

From BusyCoq Require Import Longitudinal.

Lemma lpow_rotate_list {A} (a0:list A) a1 b n:
  (a1::a0)^^n ++ a1::b = a1::(a0++[a1])^^n++b.
Proof.
  induction n; cbn.
  - trivial.
  - repeat rewrite <-app_assoc.
    rewrite IHn.
    trivial.
Qed.

Ltac solve_seg :=
  unfold segRL,segRR,segLL,segLR; intros; cbn;
  (eapply evstep_progress_trans || eapply evstep_trans);
  [ repeat (rewrite Str_app_assoc || cbn[Str_app]);
    simpl_tape;
    finish
  | ];
  (repeat (er; try sr)); finish;
  repeat rewrite Str_cons_def;
  repeat rewrite <-Str_app_assoc;
  cbn[app];
  reflexivity.

Ltac solve_segRLs :=
  repeat (
  (eapply segRLs_S; [solve_seg |]) ||
  (eapply segRLs_RR_LLs; [solve_seg |]) ||
  (eapply segLLs_LR_LLs; [solve_seg |]) ||
  (eapply segLLs_LL_RLs; [solve_seg |]) ||
  eapply segRLs_O ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite lpow_rotate_list ||
  cbn[app]).

Ltac solve_sideRLs :=
  repeat (eapply sideRLseq_S;
  [ intros ?l;
    unfold to_DH_config; cbn;
    (repeat (er; try sr)) | ] ||
  eapply sideRLseq_O).

Lemma segRLs_addmul tm a x b c h w1 w2:
  segRLs tm (h^^b) (h^^c) w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^(x+c)) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ c).
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Lemma segRLs_addmul' tm a x b c h w1 w2:
  x>=c ->
  segRLs tm (h^^b) (h^^c) w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^((x-c)*a+b)) (h^^x) w1 w2.
Proof.
  intros H.
  replace (h^^x) with (h^^(x-c+c)) by (f_equal; lia).
  apply segRLs_addmul.
Qed.

Lemma segRLs_addmul'' tm a x b h w1 w2:
  segRLs tm (h^^b) [] w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^x) w1 w2.
Proof.
  epose proof (segRLs_addmul tm a x b O _ _ _) as H.
  rewrite Nat.add_0_r in H.
  apply H.
Qed.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RC_0LC1RE_0RE0RD_0LE---_1LF1RA_1LA0LC").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{C}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{A}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (A,<[0;0;1]).
Notation hL := (C,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RE_1LA1RD_1LA1RB_0RD0RF_0LC---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RE_1LA1RD_1LA1RB_0RD0RF_0LD---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RE_0LC1RD_1LA1RB_0RD0RF_0LD---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RE_0RF1RD_1LA1RB_0RD0RF_0LD---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM5.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0LE_1RD0RF_0LE1RA_0RA1LB_0RA---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{C}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (C,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LF_1RD---_0LF1RA_1RD0RF_0RA1LB").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{F}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{E}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (E,<[0;0;1]).
Notation hL := (F,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC---_1LA1RD_1LA1RF_0RD1LA_1RC0RE").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{F}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (F,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC---_0LC1RD_1LA1RF_0RD1LA_1RC0RE").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{F}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (F,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RF_1LA1RD_1LA1RB_0RC1LA_0RD---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RF_1LA1RD_1LA1RB_0RD1LA_0RD---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0RF_0LC1RD_1LA1RB_0RD1LA_0RD---").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation w0 := <[0;0;1].
Notation w1 := <[1;1;1].
Notation "l <| r" := (l <{{E}} [0;1;0] *> r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).

Inductive LD := W0 | W1.

Fixpoint Lmp(ls:list LD):side :=
match ls with
| [] => 0inf
| W0::t => Lmp t <* w0
| W1::t => Lmp t <* w1
end.

Inductive LInc: (list LD)->(list LD)->Prop :=
| LInc_w0 x x':
  LInc x x' ->
  LInc (W0::x) (W0::x')
| LInc_d0 x:
  LInc (W1::W0::x) (W1::W1::x)
| LInc_d1 x x':
  LInc x x' ->
  LInc (W1::W1::x) (W1::W0::x')
.

Lemma LInc_spec [x x']:
  LInc x x' ->
  forall r,
  Lmp x <| r -->*
  Lmp x' <* w0 |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
Qed.

Inductive LOv: (list LD)->(list LD)->Prop :=
| LOv_O: LOv [] [W0;W1] 
| LOv_d1_0 x x':
  LOv x (W0::x') ->
  LOv (W1::W1::x) (W0::W0::W1::x')
| LOv_d1_1 x x' x'':
  LOv x (W1::x') ->
  LInc x' x'' ->
  LOv (W1::W1::x) (W0::W0::W0::x'')
| LOv_w0 x x':
  LOv x x' ->
  LOv (W0::x) (W1::x')
.

Lemma LOv_spec [x x']:
  LOv x x' ->
  forall r,
  Lmp x <| [1] *> r -->*
  Lmp x' |> r.
Proof.
  intros H.
  induction H; intros; cbn.
  all: repeat (er || follow).
  follow (LInc_spec H0); er.
Qed.


Inductive LIncs: (list LD)->(list LD)->nat->Prop :=
| LIncs_O:
  LIncs [] [] O
| LIncs_w0 x x' n:
  LIncs x x' n ->
  LIncs (W0::x) (W0::x') n
| LIncs_d0 x x' n:
  LIncs x x' n ->
  LIncs (W1::W0::x) (W1::W1::x') (n*2+1)
| LIncs_d1 x x' n:
  LIncs x x' n ->
  LIncs (W1::W1::x) (W1::W1::x') (n*2+0)
.

Notation hR := (B,<[0;0;1]).
Notation hL := (E,[0;1;0]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Lemma LIncs_spec [x x' n]:
  LIncs x x' n ->
  sideRLs tm' (hLR^^n) (Lmp x) (Lmp x').
Proof.
  intros H.
  induction H; cbn[Lmp].
  - solve_sideRLs.
  - eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_wall.
    1: solve_seg.
    1: solve_seg.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
  - do 2 rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat.
    2: eassumption.
    eapply segRLs_addmul''.
    1: solve_segRLs.
    1: solve_segRLs.
Qed.

Definition RC n := [1] *> [0;1;1]^^n *> [0;1] *> 0inf.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  - solve_sideRLs.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    simpl_tape; simpl_rotate.
    solve_sideRLs.
Qed.

Definition init_x :=
(<[W1;W1;W1;W1;W0;W0;W0;W1;W1;W0;W0;W1;W1;W0;W0;W0;W0;W1;W1;W0;W0;W0;W1] <+ <[W0;W1]^^18).

Lemma Incs x x' n0:
  LIncs x x' (n0*2+1) ->
  Lmp x <| RC 1 -->*
  Lmp x' <| RC ((n0+1)*2).
Proof.
  intros HL.
  epose proof (LIncs_spec HL) as HL'.
  epose proof (RIncs (n0*2+1) 1) as HR.
  replace (n0*2+1+1) with ((n0+1)*2) in HR by lia.
  apply (sideRLs_concat_1L HR HL').
Qed.

Lemma Lmp_d0 x n:
  Lmp (x <+ <[W0;W1]^^n) = Lmp x <* (w0<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Lmp_d1 x n:
  Lmp (x <+ <[W1;W1]^^n) = Lmp x <* (w1<+w1)^^n.
Proof.
  induction n; cbn.
  - trivial.
  - rewrite IHn; reflexivity.
Qed.

Lemma Ov x x' m:
  LOv x (W0::x') ->
  Lmp x <| RC ((m+1)*2) -->*
  Lmp (x' <+ <[W1;W1] <+ <[W0;W1]^^m) <| RC 1.
Proof.
  rewrite Lmp_d0.
  intros HL.
  follow (LOv_spec HL).
  es.
Qed.

Lemma LIncs_lpow [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W0;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0+1)*2^n-1).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0+1)*2^(S n)-1) with (((n0+1)*2^n-1)*2+1) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LIncs_lpow' [x x' n0] n:
  LIncs x x' n0 ->
  LIncs (x <+ <[W1;W1]^^n) (x' <+ <[W1;W1]^^n) ((n0)*2^n).
Proof.
  intros H.
  induction n.
  - cbn.
    applys_eq H; lia.
  - epose proof (Nat.pow_nonzero 2 n).
    replace ((n0)*2^(S n)) with (((n0)*2^n)*2+0) by (cbn; lia).
    econstructor; eassumption.
Qed.

Lemma LOv_lpow x x' n:
  LOv x (W0::W0::x') ->
  LOv (x <+ <[W1;W1]^^n) (x' <+ <[W0;W1]^^n <+ <[W0;W0]).
Proof.
  intros H.
  induction n.
  - eassumption.
  - econstructor; eassumption.
Qed.


Inductive LD' :=
| W0' | W1' | W10 | W11.

Inductive Lmp': list LD' -> list LD -> Prop :=
| Lmp'_W0' x x':
  Lmp' x x' ->
  Lmp' (W0'::x) (W0::x')
| Lmp'_W1' x x':
  Lmp' x x' ->
  Lmp' (W1'::x) (W1::x')
| Lmp'_W10 x x' n:
  Lmp' x x' ->
  Lmp' (W10::x) ([W1;W0]^^(1+n)++x')
| Lmp'_W11 x x' n:
  Lmp' x x' ->
  Lmp' (W11::x) ([W1;W1]^^(1+n)++x')
| Lmp'_O:
  Lmp' [] []
.


From BusyCoq Require Import Eqb.

Fixpoint LInc_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LInc_rec t T0 &&& (fun v => Some (W0'::v))
| W1'::W1'::t =>
  LInc_rec t T0 &&& (fun v => Some (W1'::W0'::v))
| W1'::W0'::t =>
  Some (W1'::W1'::t)
| _ => None
end
end.

Definition maxv:nat := 4.

Fixpoint LIncs_rec(x:list LD')(T:nat){struct T}:option ((list LD')*nat*nat) :=
match T with
| O => None
| S T0 =>
match x with
| W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W0'::v,n,m))
| W1'::W1'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),0)%nat)
| W1'::W0'::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W1'::W1'::v,Nat.min maxv (n*2+m),1)%nat)
| W11::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),0)%nat)
| W10::t =>
  LIncs_rec t T0 &&& (fun '(v,n,m) => Some (W11::v,Nat.min maxv (n*2+m),1)%nat)
| [] => Some ([],0,0)%nat
| _ => None
end
end.

Fixpoint LOv_rec(x:list LD')(T:nat){struct T}:option (list LD') :=
match T with
| O => None
| S T0 =>
match x with
| [] => Some [W0';W1']
| W0'::t =>
  LOv_rec t T0 &&& (fun v => Some (W1'::v))
| W1'::W1'::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::v0 => Some (W0'::W0'::W1'::v0)
  | W1'::v0 =>
    LInc_rec v0 T &&& (fun v1 => Some (W0'::W0'::W0'::v1))
  | _ => None
  end)
| W11::t =>
  LOv_rec t T0 &&& (fun v =>
  match v with
  | W0'::W0'::v0 => Some (W0'::W0'::W10::v0)
  | _ => None
  end)
| _ => None
end
end.

Hint Constructors LInc LIncs LOv Lmp' : core.

Ltac invs :=
repeat
match goal with
| [ H: Some _ = Some _ |- _ ] => inverts H
| [ H: Lmp' (_::_) _ |- _ ] => inverts H
| [ H: Lmp' [] _ |- _ ] => inverts H
end.

Ltac eic :=
repeat
match goal with
| |- exists _, _ => eexists
| |- _ /\ _ => econstructor
| |- _ -> _ => intros
end.

Lemma LInc_rec_spec x T x0 x':
  LInc_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LInc x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  destruct w...
  - destruct (LInc_rec x T) eqn:E...
    invs.
    specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
    eic; eauto.
  - destruct x as [|w x]...
    destruct w...
    + invs.
      eic; eauto.
    + destruct (LInc_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H0) as [x0' [I1 I2]].
      eic; eauto.
Qed.

Opaque LInc_rec.

Lemma LOv_rec_spec x T x0 x':
  LOv_rec x T = Some x0 ->
  Lmp' x x' ->
  exists x0',
  LOv x' x0' /\
  Lmp' x0 x0'.
Proof with try congruence.
  gen x x0 x'.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto.
  - destruct w...
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H1) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      * invs.
        eic; eauto.
      * invs.
        destruct (LInc_rec l (S T)) eqn:E1...
        epose proof (LInc_rec_spec _ _ _ _ E1 H2) as [x1' [I3 I4]].
        invs.
        eic; eauto.
    + destruct (LOv_rec x T) eqn:E...
      invs.
      specialize (IHT _ _ _ E H2) as [x0' [I1 I2]].
      destruct l as [|w l]...
      destruct w...
      destruct l as [|w l]...
      destruct w...
      invs.
      eic.
      * eapply LOv_lpow; eauto.
      * repeat econstructor; eauto.
Qed.

Transparent LInc_rec.

Opaque maxv.

Lemma LIncs_rec_spec x T x0 x' n m:
  LIncs_rec x T = Some (x0,n,m) ->
  Lmp' x x' ->
  exists x0' n',
  LIncs x' x0' (n'*2+m) /\
  Lmp' x0 x0' /\
  n'>=n.
Proof with try congruence.
  gen x x0 x' n m.
  induction T; cbn in *; intros...
  unfold if_Some in *.
  destruct x as [|w x]...
  - invs.
    eic; eauto; eauto.
  - destruct w...
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic; eauto.
    + destruct x as [|w x]...
      destruct w...
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
      * destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
        invs.
        specialize (IHT _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
        eic; eauto; lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        rewrite Nat.mul_add_distr_r.
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
    + destruct (LIncs_rec x T) as [[[v1 n1] m1]|] eqn:E...
      invs.
      specialize (IHT _ _ _ _ _ E H1) as [x0' [n' [I1 [I2 I3]]]].
      eic.
      * rewrite lpow_add; cbn.
        econstructor.
        eapply LIncs_lpow'; eauto.
      * econstructor; eauto.
      * pose proof (Nat.pow_nonzero 2 n).
        pose proof (Nat.mul_le_mono_l 1 (2^n) (n'*2+m1)).
        lia.
Qed.

Transparent maxv.

Definition step_rec(x:list LD'):option (list LD') :=
LIncs_rec x (S(length x)) &&& (fun '(x0,n,m) =>
if m =? 1 then
  match n with
  | O => None
  | S n0 =>
    LOv_rec x0 (S(length x0)) &&& (fun x1 =>
    match x1 with
    | W0'::x2 =>
      Some ([W1';W0']^^(n0-n0/2)++W10::[W1';W0']^^(n0/2)++W1'::W1'::x2)
    | _ => None
    end)
  end
else None).

Lemma Lmp'_lpow x x' n:
  Lmp' x x' ->
  Lmp' ([W1';W0']^^n++x) ([W1;W0]^^n++x').
Proof.
  intros H.
  induction n; cbn; eauto.
Qed.

Inductive P: (list LD')->Prop :=
| P_intro x x':
  Lmp' x x' ->
  c0 -->* Lmp x' <| RC 1 ->
  P x.

Lemma step_rec_spec x x':
  step_rec x = Some x' ->
  P x ->
  P x'.
Proof with try congruence.
  intros H.
  unfold step_rec in H.
  unfold if_Some in H.
  intros HP.
  inverts HP.
  destruct (LIncs_rec x (S(length x))) as [[[v n] m]|] eqn:E...
  destruct (Nat.eqb_spec m 1)...
  subst.
  destruct n as [|n]...
  destruct (LOv_rec v (S(length v))) eqn:E0...
  destruct l as [|w l]...
  destruct w...
  remember (n/2) as n1.
  invs.
  epose proof (LIncs_rec_spec _ _ _ _ _ _ E H0) as [x0' [n' [I1 [I2 I3]]]].
  epose proof (LOv_rec_spec _ _ _ _ E0 I2) as [x1' [I4 I5]].
  invs.
  epose proof (Nat.Div0.div_mod n 2).
  eapply P_intro with (x':=[W1;W0]^^(n')++[W1;W1]++x').
  - replace (n') with (n-n1+(1+(n'-S n))+n1) by lia.
    do 2 rewrite lpow_add.
    do 2 rewrite <-app_assoc.
    eapply Lmp'_lpow.
    econstructor.
    eapply Lmp'_lpow.
    cbn.
    eauto.
  - follow H1.
    follow Incs.
    follow Ov.
    finish.
Qed.

Lemma init:
  P (map (fun x => match x with W0 => W0' | W1 => W1' end) (init_x)).
Proof.
  econstructor.
  1: cbn; repeat econstructor.
  cbn; solve_init.
Qed.

Lemma init1:
  P [W1'; W0'; W1'; W0'; W10; W1'; W0'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W10;
   W1'; W0'; W0'; W0'; W0'; W1'; W1'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0';
   W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1';
   W0'; W1'; W0'; W1'; W0'; W1'; W0'; W1'; W0'; W0'; W0'; W0'; W0'; W1'; W0';
   W0'; W1'; W1'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0'; W0'; W1'; W1'; W0';
   W1'; W0'; W1'; W1'].
Proof.
  eapply step_rec_spec.
  2: eapply step_rec_spec.
  3: apply init.
  2: vm_compute; reflexivity.
  1: vm_compute; reflexivity.
Qed.

Ltac solve_L :=
  solve [(econstructor ||
  eapply LIncs_lpow ||
  eapply LOv_lpow); solve_L].

Lemma halt: halts tm c0.
Proof.
  epose proof init1 as H.
  inverts H.
  invs.
  eapply halts_evstep.
  2:{
    follow H1.
    follow Incs.
    1: solve_L.
    finish.
  }
  clear H1.
  match goal with
  | |- halts tm (_ <| RC ((?a+1)*2)) =>
    remember a as m
  end.
  clear Heqm.
  eapply halts_evstep.
  2:{
    repeat (cbn || rewrite Lmp_d1).
    time repeat (step1 || sr).
    finish.
  }
  eapply halted_halts.
  constructor.
Qed.

End TM16.


