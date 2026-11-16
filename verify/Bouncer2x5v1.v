From BusyCoq Require Import Individual25.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


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

Ltac crefl := vm_compute; try reflexivity.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB2LA0LB1LA2RA_0LA3RA1RA4LB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation lh0 := (0inf<*<[1;3;1;3;3;2;3;3;1;3;1;3;1;3;3]).
Notation lh1 := (0inf<*<[1;3;1;3;3;2;3;2;3;3;1;3;3;1;1;3;1;3;3;1;1;3;1;3;1;3;3]).
Notation lh2 := (0inf<*<[1;3;1;3;3;2;3;3;1;3;1;3;3;1;1;2;1;3;3;1;1;3;3;1;1;3;1;3;3;1;1;3;1;3;1;3;3]).
Notation w := [2;2;2;1;2;2;1;1;2;2;1;2;1;1;2;2;1;2;1;2;1;1;1;2;1;1;2;2;1;2;1;1;2;1].
Notation hL := (A,[1;2;1;1;2;2;1;2;1;1;2;1]).
Notation hR := (B,<[2;3;2;1;3;1]).
Notation h := [(hR,hL)].

Inductive Tp := tp0|tp1|tp2.

Lemma w_Incs n:
  segRLs tm h h (w^^n) (w^^n).
Proof.
  induction n.
  1: esc.
  cbn[lpow].
  eapply segRLs_concat; eauto 1.
  esc.
Qed.

Section maxT_sec.
Hypothesis maxT:nat.
Definition RInc0 r := sideRL_c tm hR hL r maxT.
Definition RInc1 r := sideRL_c tm hR hL (w*>r) maxT.
Definition MInc '(n,r) :=
(RInc0 r &&& (fun r => Some (n,r))) ||| (fun _ =>
match n with
| O => None
| S n => RInc1 r &&& (fun r => Some (n,r))
end).

Definition Inc '(n,r,tp) :=
let '(n,tp) :=
match tp with
| tp0 => (n,tp1)
| tp1 => (n,tp2)
| tp2 => (S n,tp0)
end in
MInc (n,r) &&& (fun '(n,r) => Some (n,r,tp)).

Lemma MInc_spec n r n' r':
  MInc (n,r) = Some (n',r') ->
  sideRLs tm h (w^^n *> r) (w^^n' *> r').
Proof.
  unfold MInc,RInc0,RInc1.
  intros H.
  des_if H.
  - inverts H.
    des_if E; inverts E.
    eapply sideRL_c_spec in E0.
    eapply segRLs_sideRLs_concat.
    1: apply w_Incs.
    econstructor; [apply E0| constructor].
  - cbn[if_None] in H.
    destruct n; [inverts H|].
    des_if H; [|inverts H].
    inverts H.
    eapply sideRL_c_spec in E0.
    replace (S n') with (n'+1) by lia.
    rewrite <-lpow_add'.
    eapply segRLs_sideRLs_concat.
    1: apply w_Incs.
    econstructor; [apply E0| constructor].
Qed.

Definition LC tp :=
match tp with
| tp0 => lh0
| tp1 => lh1
| tp2 => lh2
end.

Definition S' '(n,r,tp) := LC tp {{{ (hL,L) }}} w^^n *> r.

Lemma Inc_spec x x':
  Inc x = Some x' ->
  S' x -->+ S' x'.
Proof.
  unfold S',LC,Inc.
  destruct x as [[n r] tp].
  destruct x' as [[n' r'] tp'].
  intros.
  destruct tp.
  - des_if H. 2: inverts H.
    destruct p as [n0 r0].
    apply MInc_spec in E.
    mid01 (lh1 {{{ (hR,R) }}} w^^n *> r).
    1: es.
    inverts H.
    inverts E.
    inverts H5.
    apply H4.
  - des_if H. 2: inverts H.
    destruct p as [n0 r0].
    apply MInc_spec in E.
    mid01 (lh2 {{{ (hR,R) }}} w^^n *> r).
    1: es.
    inverts H.
    inverts E.
    inverts H5.
    apply H4.
  - des_if H. 2: inverts H.
    destruct p as [n0 r0].
    apply MInc_spec in E.
    mid01 (lh0 {{{ (hR,R) }}} w^^(S n) *> r).
    1: es.
    inverts H.
    inverts E.
    inverts H5.
    apply H4.
Time Qed.

Fixpoint Incs T x :=
match T with
| O => Some x
| S T => Inc x &&& (fun x => Incs T x)
end.

Lemma Incs_spec T x x':
  Incs T x = Some x' ->
  S' x -->* S' x'.
Proof.
  gen x x'.
  induction T; cbn; intros.
  - inverts H.
    finish.
  - des_if H; inverts H.
    apply Inc_spec in E.
    apply IHT in H1.
    eapply progress_evstep in E.
    follow E.
    apply H1.
Qed.

Lemma Incs_spec' T x x':
  Incs (S T) x = Some x' ->
  S' x -->+ S' x'.
Proof.
  cbn.
  intros.
  des_if H; inverts H.
  apply Inc_spec in E.
  follow10 E.
  eapply Incs_spec,H1.
Qed.

Definition tp_eqb(a b:Tp):bool :=
match a,b with
| tp0,tp0 => true
| tp1,tp1 => true
| tp2,tp2 => true
| _,_ => false
end.

Lemma tp_eqb_spec a b:
  Bool.reflect (a=b) (tp_eqb a b).
Proof.
  destruct a,b; solve_Bool_reflect.
Qed.

Definition check_loop n0 r0 PP P PP' x :=
  Incs PP x &&& (fun '(n,r,tp) =>
  let r1:=Str_firstn PP' r in
  Incs (S P) (n+n0,r1 *> r0,tp) &&& (fun '(n',r',tp') =>
  if eqb r1 (Str_firstn PP' r') then
  if Nat.leb n n' then
  if tp_eqb tp tp' then Some tt
  else None
  else None
  else None
  )).

Local Opaque Eqb.eqb Incs.

Lemma check_loop_spec PP P PP' x:
  (forall n0 r0,
  check_loop n0 r0 PP P PP' x = Some tt) ->
  ~halts tm (S' x).
Proof.
  unfold check_loop.
  intros.
  destruct (Incs PP x) as [[[n r] tp]|] eqn:E; cbn in H.
  2: specialize (H O (const s0)); congruence.
  eapply Incs_spec in E.
  pose (fun '(n0,r0) => S' (n+n0,Str_firstn PP' r *> r0, tp)) as S''.
  eapply multistep_nonhalt with (c':=S'' (O,Str_nth_tl PP' r)).
  - unfold S''.
    rewrite Nat.add_0_r.
    rewrite <-Str_firstn_spec.
    apply E.
  - eapply progress_nonhalt_simple.
    intros [n0 r0].
    specialize (H n0 r0).
    des_if H.
    2: inverts H.
    cbn in H.
    destruct p as [[n' r'] tp'].
    destruct (eqb_spec (Str_firstn PP' r) (Str_firstn PP' r')).
    2: congruence.
    destruct (Nat.leb_spec n n').
    2: congruence.
    destruct (tp_eqb_spec tp tp').
    2: congruence.
    subst.
    eapply Incs_spec' in E0.
    unfold S''.
    exists (n'-n,Str_nth_tl PP' r').
    follow10 E0.
    rewrite e.
    rewrite <-Str_firstn_spec.
    finish.
Qed.

End maxT_sec.

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; try reflexivity.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (2%nat,_,tp0)).
  1: stepn 115664%N.
  eapply check_loop_spec with (maxT:=10^6) (PP:=110000) (P:=78506*3-1) (PP':=21866).
  intros.
  native_check_eq.
Time Qed.

End TM1.


