From BusyCoq Require Import Individual.
From BusyCoq Require Export BigUint.
From BusyCoq Require Import Eqb.
Require Import PeanoNat ZArith Streams List.
Require Import Lia.

Definition b2o(b:bool) := if b then Some tt else None.

Definition if_None {A} (a:option A) b :=
match a with
| None => b tt
| _ => a
end.

Notation "a ||| b" := (if_None a b) (at level 30, right associativity).

Ltac ec := econstructor.
Ltac eex := repeat eexists.

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

Ltac des_if' H := des_if H; [|inverts H].

Module LongAcc(Ctx:Ctx).
Module TM := Flip Ctx.
Export TM.
Import Eqb.

Section tm_sec.
Hypothesis tm:TM.
Hypothesis D:nat.

Definition Q2: Type := Q*Q.

Inductive RLs: (list Q2)->(list Sym)->(list Sym)->Prop :=
| RLs_O w: RLs [] w w
| RLs_S QR QL t w w0 w1:
  (forall l r, l {{QR}}> w *> r -[ tm ]->* l <{{QL}} w0 *> r) ->
  RLs t w0 w1 ->
  RLs ((QR,QL)::t) w w1.

Inductive RRs: (list Q2)->Q->Q->(list Sym)->(list Sym)->Prop :=
| RRs_intro h QR QR' w w0 w1:
  RLs h w w0 ->
  (forall l r, l {{QR}}> w0 *> r -[ tm ]->* l <* rev w1 {{QR'}}> r) ->
  RRs h QR QR' w w1. 

Local Hint Constructors RLs RRs : core.

Definition RLs' h h' w w' :=
  forall w0 w0', RLs h' w0 w0' -> RLs h (w++w0) (w'++w0').

Definition RRs' h h' QR QR' w w' :=
  forall w0 w0' QR'', RRs h' QR' QR'' w0 w0' -> RRs h QR QR'' (w++w0) (w'++w0').

Lemma RRs'_O q1 q2 w1 w2:
  RRs' [] [] q1 q2 w1 w2 ->
  (forall l r, l {{q1}}> w1 *> r -[ tm ]->* l <* rev w2 {{q2}}> r).
Proof.
  unfold RRs'.
  intros.
  unshelve epose proof (H [] [] q2 _) as H.
  1: eauto.
  do 2 rewrite app_nil_r in H.
  inverts H.
  inverts H0.
  eauto.
Qed.

Lemma RLs'_concat h1 h2 h3 w1 w2 w3 w4:
  RLs' h1 h2 w1 w2 ->
  RLs' h2 h3 w3 w4 ->
  RLs' h1 h3 (w1++w3) (w2++w4).
Proof.
  unfold RLs'.
  intros.
  repeat rewrite <-app_assoc.
  eauto.
Qed.

Lemma RLs_concat h1 h2 w1 w2 w3 w4:
  RLs' h1 h2 w1 w2 ->
  RLs h2 w3 w4 ->
  RLs h1 (w1++w3) (w2++w4).
Proof.
  unfold RLs'.
  intros.
  eauto.
Qed.

Lemma RRs'_concat h1 h2 h3 q1 q2 q3 w1 w2 w3 w4:
  RRs' h1 h2 q1 q2 w1 w2 ->
  RRs' h2 h3 q2 q3 w3 w4 ->
  RRs' h1 h3 q1 q3 (w1++w3) (w2++w4).
Proof.
  unfold RRs'.
  intros.
  repeat rewrite <-app_assoc.
  eauto.
Qed.

Lemma RLs_trans h1 h2 w1 w2 w3:
  RLs h1 w1 w2 ->
  RLs h2 w2 w3 ->
  RLs (h1++h2) w1 w3.
Proof.
  intro H.
  induction H; cbn; eauto.
Qed.

Lemma RLs_split h1 h2 w1 w2:
  RLs (h1++h2) w1 w2 ->
  exists w3, RLs h1 w1 w3 /\ RLs h2 w3 w2.
Proof.
  gen h2 w1 w2.
  induction h1; cbn; intros.
  - eauto.
  - inverts H.
    eapply IHh1 in H5.
    destruct H5 as [w3 [I1 I2]].
    eauto.
Qed.

Lemma RLs'_trans h1 h2 h3 h4 w1 w2 w3:
  RLs' h1 h2 w1 w2 ->
  RLs' h3 h4 w2 w3 ->
  RLs' (h1++h3) (h2++h4) w1 w3.
Proof.
  unfold RLs'.
  intros.
  apply RLs_split in H1.
  destruct H1 as [w [I1 I2]].
  eapply RLs_trans; eauto.
Qed.

Lemma RLs'_trans_lpow h1 h2 w n:
  RLs' h1 h2 w w ->
  RLs' (h1^^n) (h2^^n) w w.
Proof.
  intros.
  induction n.
  - unfold RLs'; intros.
    inverts H0.
    eauto.
  - cbn[lpow].
    eauto using RLs'_trans.
Qed.

Lemma RRs_split h1 h2 q1 q2 w1 w2:
  RRs (h1++h2) q1 q2 w1 w2 ->
  exists w3, RLs h1 w1 w3 /\ RRs h2 q1 q2 w3 w2.
Proof.
  intros H.
  inverts H.
  apply RLs_split in H0.
  destruct H0 as [w3 [I1 I2]].
  eauto.
Qed.

Lemma RRs_trans h1 h2 q1 q2 w1 w2 w3:
  RLs h1 w1 w2 ->
  RRs h2 q1 q2 w2 w3 ->
  RRs (h1++h2) q1 q2 w1 w3.
Proof.
  intros.
  inverts H0.
  eauto using RLs_trans.
Qed.

Lemma RRs'_trans h1 h2 h3 h4 q1 q2 w1 w2 w3:
  RLs' h1 h2 w1 w2 ->
  RRs' h3 h4 q1 q2 w2 w3 ->
  RRs' (h1++h3) (h2++h4) q1 q2 w1 w3.
Proof.
  unfold RLs',RRs'.
  intros.
  apply RRs_split in H1.
  destruct H1 as [w [I1 I2]].
  eapply RRs_trans; eauto.
Qed.

Fixpoint LRs_c h QR w :=
match h with
| (QR',QL)::h =>
  if eqb QR QR' then
    match tm (QL,w) with
    | Some (w,L,Q') => Some (inl (h,Q',w))
    | Some (w,R,Q') => LRs_c h Q' w
    | None => None
    end
  else None
| [] => Some (inr (QR,w))
end.

Fixpoint RLs_c h1 h2 w :=
match h1 with
| (QR,QL)::h1 =>
  match tm (QR,w) with
  | Some (w,L,Q') =>
    if eqb QL Q' then
      RLs_c h1 h2 w
    else None
  | Some (w,R,Q') =>
    LRs_c h2 Q' w &&& (fun x =>
    match x with
    | inl (h2,Q',w) =>
      if eqb QL Q' then
        RLs_c h1 h2 w
      else None
    | inr x =>
      match h1 with
      | [] => Some (inr x)
      | _ => None
      end
    end)
  | None => None
  end
| [] =>
  match h2 with
  | [] => Some (inl w)
  | _ => None
  end
end.

Definition RLs_c' h1 h2 w w' :=
RLs_c h1 h2 w &&& (fun w => b2o (eqb w (inl w'))).

Definition RRs_c' h1 h2 q1 q2 w :=
  RLs_c (h1++[(q1,q1)]) h2 w &&& (fun x =>
  match x with
  | inr (q2',w') =>
    b2o (eqb q2 q2') &&& (fun _ => Some w')
  | _ => None
  end).


Local Opaque eqb.

Lemma LRs_c_spec h QR w h' Q' w':
  LRs_c h QR w = Some (inl (h',Q',w')) ->
  forall w0 w0', RLs h w0 w0' -> 
  (exists w0'',
  RLs h' w0'' w0' /\
  (forall l r, l<<w {{QR}}> w0*>r -[ tm ]->* l <{{Q'}} w'>>w0''*>r)).
Proof.
  gen QR w.
  induction h as [|[QR QL] h]; intros.
  - inverts H.
  - cbn[LRs_c] in H.
    destruct (eqb_spec QR0 QR); [subst QR0|inverts H].
    inverts H0.
    destruct (tm (QL,w)) as [[[w1 []] Q0]|] eqn:E; inverts H.
    + eexists; split.
      1: apply H7.
      intros.
      eapply evstep_trans; eauto.
    + epose proof (IHh _ _ H1 _ _ H7) as [w0'' [I1 I2]].
      eexists; split.
      1: apply I1.
      intros.
      eapply evstep_trans; eauto.
Qed.

Lemma RLs_c_spec h1 h2 w w':
  RLs_c h1 h2 w = Some (inl w') ->
  RLs' h1 h2 [w] [w'].
Proof.
  gen h2 w w'.
  induction h1 as [|[QR QL] h1]; intros.
  - destruct h2; inverts H.
    unfold RLs'.
    intros.
    inverts H.
    eauto.
  - cbn[RLs_c] in H.
    destruct (tm (QR,w)) as [[[w0 []] Q0]|] eqn:E; inverts H.
    + destruct (eqb_spec QL Q0); [subst Q0|inverts H1].
      apply IHh1 in H1.
      eapply RLs'_trans with (h1:=[(QR,QL)]) (h2:=[]).
      2: apply H1.
      unfold RLs'.
      intros.
      inverts H.
      econstructor.
      2: eauto.
      eauto.
    + des_if' H1.
      destruct s as [[[h3 Q'] w1]|];
      cbn in H1.
      2: destruct h1; inverts H1.
      destruct (eqb_spec QL Q'); [subst Q'|inverts H1].
      apply IHh1 in H1.
      unfold RLs'.
      intros.
      epose proof (LRs_c_spec _ _ _ _ _ _ E0 _ _ H) as [w0'' [I1 I2]].
      econstructor.
      2: eapply RLs_concat; eauto.
      intros.
      eapply evstep_step.
      1: eauto.
      cbn.
      eauto.
Qed.

Lemma RLs_c'_spec h1 h2 w w' u:
  RLs_c' h1 h2 w w' = Some u ->
  RLs' h1 h2 [w] [w'].
Proof.
  unfold RLs_c'.
  intros.
  des_if' H.
  cbn in H.
  destruct (eqb_spec s (inl w')); [subst|inverts H].
  apply RLs_c_spec in E.
  eauto.
Qed.

Lemma LRs_c_spec' h q1 q2 Q0 w w' w0:
  LRs_c h Q0 w0 = Some (inr (q2, w')) ->
  tm (q1, w) = Some (w0, R, Q0) ->
  RRs' [] h q1 q2 [w] [w'].
Proof.
  gen q1 q2 Q0 w w' w0.
  induction h as [|[QR QL] h]; intros.
  - inverts H.
    unfold RRs'.
    intros.
    inverts H.
    inverts H1.
    ec.
    1: ec.
    intros.
    cbn.
    rewrite Str_app_assoc.
    eapply evstep_step; eauto.
  - cbn[LRs_c] in H.
    destruct (eqb_spec Q0 QR); [subst Q0|inverts H].
    destruct (tm (QL,w0)) as [[[w1 []] Q']|] eqn:E; inverts H.
    eassert (I1:_) by (eapply IHh; eauto).
    clear E.
    unfold RRs'.
    intros.
    inverts H.
    inverts H1.
    ec.
    1: ec.
    intros.
    cbn.
    eapply evstep_step; [eauto|cbn].
    eapply evstep_trans; [eauto|].
    cbn.
    eassert (I2:RRs h _ _ w5 _) by (ec; eauto).
    apply I1 in I2.
    inverts I2.
    inverts H.
    apply H1.
Qed.

Lemma RRs_c_spec h1 h2 q1 q1x q2 w w':
  RLs_c (h1++[(q1,q1x)]) h2 w = Some (inr (q2,w')) ->
  RRs' h1 h2 q1 q2 [w] [w'].
Proof.
  gen h2 w w'.
  induction h1 as [|[QR QL] h1]; intros.
  - cbn[app RLs_c] in H.
    destruct (tm (q1,w)) as [[[w0 []] Q0]|] eqn:E; inverts H.
    + destruct (eqb q1x Q0); destruct h2; inverts H1.
    + des_if' H1.
      cbn in H1.
      destruct s as [[[h2' Q'] w'0]|].
      * destruct (eqb q1x Q'); destruct h2'; inverts H1.
      * inverts H1.
        unfold RRs'.
        intros.
        eapply LRs_c_spec' in E0; eauto.
  - cbn[app RLs_c] in H.
    destruct (tm (QR,w)) as [[[w0 []] Q0]|] eqn:E; inverts H.
    + destruct (eqb_spec QL Q0); [subst Q0|inverts H1].
      apply IHh1 in H1.
      eapply RRs'_trans with (h1:=[(QR,QL)]) (h2:=[]).
      2: apply H1.
      unfold RLs'.
      intros.
      inverts H.
      econstructor.
      2: eauto.
      eauto.
    + des_if' H1.
      destruct s as [[[h3 Q'] w1]|];
      cbn in H1.
      2: destruct h1; inverts H1.
      destruct (eqb_spec QL Q'); [subst Q'|inverts H1].
      apply IHh1 in H1.
      unfold RRs'.
      intros.
      inverts H.
      epose proof (LRs_c_spec _ _ _ _ _ _ E0 _ _ H0) as [w0'' [I1 I2]].
      eapply RRs_trans with (h1:=[(QR,QL)]).
      2: eauto.
      econstructor.
      2: econstructor.
      intros.
      cbn.
      eapply evstep_step.
      1: eauto.
      cbn.
      eauto.
Qed.

Lemma RRs_c'_spec h1 h2 q1 q2 w w':
  RRs_c' h1 h2 q1 q2 w = Some w' ->
  RRs' h1 h2 q1 q2 [w] [w'].
Proof.
  unfold RRs_c'.
  intros.
  des_if' H.
  destruct s as [|[q2' w'0]].
  1: inverts H.
  des_if' H.
  destruct (eqb_spec q2 q2'); [subst|inverts E0].
  inverts H.
  apply RRs_c_spec in E.
  eauto.
Qed.


Definition Q1: Type := Q*dir*bool.
Definition Q1s_rev (ls:list Q1) := map (fun '(q,d,i) => (q,dir_rev d,i)) ls.

Fixpoint Q1s_periodic_1(h1 h2:list Q1): bool :=
match h2,h1 with
| [],_ => true
| a2::h2,a1::h1 => eqb a1 a2 && Q1s_periodic_1 h1 h2
| a2::h2,[] => false
end.

Fixpoint Q1s_to_Q2s(h:list Q1)(T:nat):=
match T with
| O => None
| S T =>
match h with
| (q,d,true)::(q0,d0,false)::h =>
  Q1s_to_Q2s h T &&& (fun x => Some ((q,q0)::x))
| [] => Some []
| _ => None
end
end.

Definition Q1s_split(h:list Q1):=
  Q1s_to_Q2s
    (filter (fun '(q,d,i) => eqb d L) h) D &&& (fun ls1 =>
  Q1s_to_Q2s
    (map (fun '(qd,i) => (qd,negb i))
    (filter (fun '(q,d,i) => eqb d R) h)) D &&& (fun ls2 =>
  Some (ls1,ls2))).

Fixpoint Q1s_periodic_2(w:Sym)(h1 h2 h3:list Q1) :=
if Q1s_periodic_1 h1 h2 then
  Q1s_split h3 &&& (fun '(ls1,ls2) =>
  RLs_c' ls1 ls2 w w &&& (fun _ =>
  Some (ls1,ls2,h3)))
else
match h2 with
| [] => None
| a2::h2 => Q1s_periodic_2 w h1 h2 (a2::h3)
end.

Definition Q1s_get_period(w:Sym)(h1:list Q1) :=
match h1 with
| [] => None
| a2::h2 => Q1s_periodic_2 w h1 h2 [a2]
end.

Definition Q1s_ins(h1 h2:list Q1) := firstn D (h1++h2).

Fixpoint lcpf(h1 h2:list Q2):option nat :=
match h1,h2 with
| (QR1,QL1)::h1,(QR2,QL2)::h2 =>
  if eqb QR1 QR2 then
    if eqb QL1 QL2 then
      match lcpf h1 h2 with
      | Some n => Some (S n)
      | None => Some O
      end
    else
      Some O
  else
    None
| _,_ => None
end.

Fixpoint ps1(h:list Q1)(n m:nat):=
match h with
| (q,L,false)::h =>
  match n with
  | O => m
  | S n => ps1 h n m
  end
| (q,R,false)::h => ps1 h n (S m)
| _::h => ps1 h n m
| [] => O
end.

Fixpoint ps2(h:list Q1)(n m:nat):=
match h with
| (q,R,false)::h =>
  match n with
  | O => Nat.pred m
  | S n => ps2 h n m
  end
| (q,L,true)::h => ps2 h n (S m)
| _::h => ps2 h n m
| [] => O
end.

Fixpoint ps(h:list Q1)(n m:nat):=
match h with
| (q,R,false)::h =>
  match n with
  | O => S m
  | S n => ps h n (S m)
  end
| _::h => ps h n (S m)
| [] => O
end.

Fixpoint lpowf (h:list Q2) n :=
match h with
| (QR,QL)::h =>
  match n with
  | O => Some ([],QR)
  | S n => lpowf (h++[(QR,QL)]) n &&& (fun '(h',Q') => Some ((QR,QL)::h',Q'))
  end
| [] => None
end.

Fixpoint upd(T:nat)(hx:list Q2)(n:N')(r:side)(rh:Stream (list Q1)){struct T}:
  option (Q*(list Sym)*side*(list (list Q1))*(Stream (list Q1))*N') :=
match T with
| O => None
| S T =>
  match r,rh with
  | w>>r,h>>rh =>
    (Q1s_get_period w h &&& (fun '(ls1,ls2,h') =>
    b2o (negb (eqb hx [])) &&& (fun _ =>
    b2o (negb (eqb ls1 [])) &&& (fun _ =>
    b2o (negb (eqb ls2 [])) &&& (fun _ =>
    let len0 := length hx in
    let len1 := length ls1 in
    let len2 := length ls2 in
    let g := Nat.gcd len0 len1 in
    let len1g:=len1/g in
    let len0g:=len0/g in
    b2o (negb (eqb len0g O)) &&& (fun _ =>
    b2o (negb (eqb len1g O)) &&& (fun _ =>
    let hp := hx^^(len1g) in
    let ls1p := ls1^^(len0g) in
    lcpf hp ls1p &&& (fun lcp =>
    let lcp := of_nat lcp in
    let e := eqb hp ls1p in
    let sz1 := of_nat len1 in
    let sz2 := of_nat len2 in
    let n1a := (if e then n else min n lcp) in
    divmod_small n1a sz1 &&& (fun '(c,d) =>
    let d := to_nat d in
    let n2a := (c*sz2+(of_nat (ps1 h' d O)))%N' in
    subge n2a (of_nat 1) &&& (fun n2a =>
    upd T ls2 n2a r rh &&& (fun '(Q',m,r',mh,rh',n2b) =>
    divmod_small n2b sz2 &&& (fun '(c',d') =>
    let d' := to_nat d' in
    let d'' := (ps2 h' d' O) in
    let n1b := (c'*sz1+(of_nat d''))%N' in
    b2o (e || (let k := to_nat n1b in (eqb (lpowf hx k) (lpowf ls1 k)))) &&& (fun _ =>
    let h'' := firstn (ps h' d' O) h' in
    let ls3 := firstn d'' ls1 in
    b2o (d'' <? len1) &&& (fun _ =>
    nth_error ls1 d'' &&& (fun '(q3,_) =>
    let ls4 := firstn d' ls2 in
    b2o (d' <? len2) &&& (fun _ =>
    nth_error ls2 d' &&& (fun '(q4,_) =>
    RLs_c' ls1 ls2 w w &&& (fun _ =>
    RRs_c' ls3 ls4 q3 q4 w &&& (fun w_ =>
    let h_ := Q1s_rev (Q1s_ins (rev h'') h) in
    Some (Q',w_::m,r',h_::mh,rh',n1b)
    ))))))))))))))))))) ||| (fun _ =>
    match hx with
    | (QR,_)::_ =>
      Some (QR,[],w>>r,[],h>>rh,BigUintNil)
    | _ => None
    end
    )
  end
end.



Lemma lpowf_eq h1 h2 n1 n2 n:
  h1<>[] ->
  h2<>[] ->
  h1^^n1 = h2^^n2 ->
  n1<>O ->
  n2<>O ->
  lpowf h1 n = lpowf h2 n.
Proof.
  intros.
  destruct n1; try congruence.
  destruct n2; try congruence.
  gen h1 h2.
  induction n; intros.
  - destruct h1 as [|[] h1]; try congruence.
    destruct h2 as [|[] h2]; try congruence.
    cbn in *.
    inverts H1.
    trivial.
  - destruct h1 as [|[] h1]; try congruence.
    destruct h2 as [|[] h2]; try congruence.
    cbn.
    unshelve epose proof (IHn (h1++[(q,q2)]) _ (h2++[(q3,q4)]) _) as I1.
    1,2: symmetry; apply app_cons_not_nil.
    assert (I2:(q,q2)=(q3,q4)) by (inverts H1; trivial).
    rewrite I2 in *.
    rewrite I1; trivial.
    remember (S n1) as n1'.
    remember (S n2) as n2'.
    epose proof (lpow_rotate_list h1 (q3,q4) [] n1') as I3.
    rewrite app_nil_r in I3.
    rewrite H1 in I3.
    rewrite lpow_rotate_list in I3.
    rewrite app_nil_r in I3.
    inverts I3.
    symmetry.
    apply H5.
Qed.

Lemma lpowf_spec h c d:
  d<length h ->
  exists QR QL,
  nth_error h d = Some (QR,QL) /\
  lpowf h (c*(length h)+d) = Some (h^^c++firstn d h,QR).
Proof.
  remember (c*(length h)+d) as n.
  gen h c d.
  induction n; intros.
  - replace d with O in * by lia.
    replace c with O in * by lia.
    destruct h as [|[]].
    1: cbn in H; lia.
    eexists _,_; split.
    1: apply nth_error_cons_0.
    reflexivity.
  - destruct d.
    + destruct c; [lia|].
      destruct h as [|[QR QL] h]; cbn in H.
      1: lia.
      specialize (IHn (h++[(QR,QL)]) c (length h)).
      rewrite length_app in IHn.
      unshelve epose proof (IHn _ _) as [QR0 [QL0 [I1 I2]]].
      1,2: cbn in *; lia.
      apply nth_error_nth with (d:=(QR,QL)) in I1.
      rewrite nth_middle in I1.
      inverts I1.
      eexists _,_; split.
      1: apply nth_error_cons_0.
      cbn[lpowf].
      unfold Q2.
      rewrite I2.
      cbn.
      do 3 f_equal.
      rewrite firstn_app,firstn_all.
      rewrite Nat.sub_diag.
      rewrite app_assoc.
      rewrite lpow_rotate_list'.
      cbn.
      repeat rewrite <-app_assoc.
      reflexivity.
    + destruct h as [|[QR QL] h]; cbn in H.
      1: lia.
      specialize (IHn (h++[(QR,QL)]) c d).
      rewrite length_app in IHn.
      unshelve epose proof (IHn _ _) as [QR0 [QL0 [I1 I2]]].
      1,2: cbn in *; lia.
      rewrite nth_error_app1 in I1 by lia.
      eexists _,_; split.
      1: cbn; apply I1.
      cbn.
      unfold Q2.
      rewrite I2.
      cbn.
      do 2 f_equal.
      rewrite lpow_rotate_list.
      rewrite firstn_app.
      replace (d-length h) with 0 by lia.
      rewrite app_nil_r; reflexivity.
Qed.

Ltac des_v1 H :=
  match type of H with
  | b2o (negb (eqb ?a ?b)) = Some _ =>
    destruct (eqb_spec a b); [inverts H|clear H]
  end.

Lemma upd_spec T:
  forall hx n r rh Q' m' r' mh rh' n1',
  upd T hx n r rh = Some (Q',m',r',mh,rh',n1') ->
  exists m hx' QR,
  r = m*>r' /\
  lpowf hx (to_nat n1') = Some (hx',QR) /\
  RRs' hx' [] QR Q' m m'.
Proof.
  induction T; cbn[upd]; intros.
  1: inverts H.
  destruct r as [w r].
  destruct rh as [h rh].
  des_if H.
  {
    inverts H.
    des_if' E.
    destruct p as [[ls1 ls2] h'].
    do 5 (des_if' E; des_v1 E1).
    remember (length hx) as len0.
    remember (length ls1) as len1.
    remember (length ls2) as len2.
    remember (Nat.gcd len0 len1) as g.
    des_if' E.
    cbn[if_Some] in E.
    remember (hx^^(len1/g)) as hp.
    remember (ls1^^(len0/g)) as ls1p.
    des_if' E.
    destruct p as [c d].
    des_if' E.
    des_if' E.
    destruct p as [[[[[Q'0 m'0] r'0] mh0] rh'0] n2b].
    apply IHT in E4.
    destruct E4 as [m0 [hx' [QR [I1 [I2 I3]]]]].
    subst r.
    cbn[if_Some] in E.
    des_if' E.
    destruct p as [c' d'].
    eapply inj_divmod_small in E4.
    des_if' E.
    des_if' E.
    des_if' E.
    destruct p as [q3 q3x].
    des_if' E.
    des_if' E.
    destruct p as [q4 q4x].
    des_if' E.
    des_if' E.
    inverts E.
    apply RLs_c'_spec in E10.
    apply RRs_c'_spec in E11.
    remember (ps2 h' (to_nat d') 0) as d''.
    destruct (Nat.ltb_spec (d'') len1); [|solve[inverts E6]].
    destruct (Nat.ltb_spec (to_nat d') len2); [|solve[inverts E8]].
    repeat rewrite inj_add in *.
    repeat rewrite inj_mul in *.
    repeat rewrite to_of_nat in *.
    remember ((to_nat c' * len1 + (d''))) as v1.
    assert (I5:lpowf hx v1 = lpowf ls1 v1). {
      destruct (eqb_spec hp ls1p).
      2:{
        destruct (eqb_spec (lpowf hx v1) (lpowf ls1 v1)).
        2: inverts E5.
        trivial.
      }
      subst hp ls1p.
      eapply lpowf_eq.
      3: apply e.
      1,2: eauto 1.
      1,2: lia.
    }
    rewrite I5.
    unshelve epose proof (lpowf_spec ls1 (to_nat c') (d'') _) as [q3' [q3x' [I6a I6b]]].
    1: lia.
    rewrite E7 in I6a.
    inverts I6a.
    unshelve epose proof (lpowf_spec ls2 (to_nat c') (to_nat d') _) as [q4' [q4x' [I8a I8b]]].
    1: lia.
    rewrite E9 in I8a.
    inverts I8a.
    replace (to_nat c' * length ls1 + d'') with v1 in I6b by lia.
    replace (to_nat c' * length ls2 + to_nat d') with ((to_nat n2b)) in I8b by lia.
    rewrite I6b.
    rewrite I8b in I2.
    inverts I2.
    eexists (w::m0),_,_; split.
    1: trivial.
    split.
    1: trivial.
    eapply RRs'_concat with (w1:=[w]) (w2:=[s]).
    2: apply I3.
    eapply RRs'_trans.
    2: apply E11.
    apply RLs'_trans_lpow,E10.
  }
  {
    clear E.
    cbn in H.
    destruct hx as [|[]]; inverts H.
    eexists [],[],Q'; split.
    1: trivial.
    split.
    1: trivial.
    unfold RRs'.
    eauto.
  }
Qed.

End tm_sec.

Definition cflip tm d :=
match d with
| R => tm
| L => flip tm
end.

Definition Config: Type := (side*side*Q*dir)*((Stream (list Q1))*(Stream (list Q1))).

Definition Config_eval (x:Config) :=
match x with
| ((l,r,q,R),_) => l {{q}}> r
| ((l,r,q,L),_) => r <{{q}} l
end.

Section tm_sec.
Hypothesis tm:TM.
Hypothesis D:nat.

Definition upd1(x:Config): Config+(Q*Sym) :=
match x with
| ((l,m>>r,q,d),(lh,mh>>rh)) =>
  match cflip tm d (q,m) with
  | Some (m',d',q') =>
    let mh' := Q1s_ins D [(q',d',false);(q,L,true)] mh in
    match d' with
    | R => inl ((l<<m',r,q',d),(lh<<(Q1s_rev mh'),rh))
    | L => inl ((r<<m',l,q',dir_rev d),(rh<<mh',lh))
    end
  | None => inr (q,m)
  end
end.

Definition upd2(T:nat)(x:Config): option Config :=
match x with
| ((l,r,q,d),(lh,rh)) =>
  upd (cflip tm d) D T [(q,q)] BigUintNil r rh &&& (fun '(q',m',r',mh',rh',n) =>
  b2o (is0 n) &&& (fun _ =>
  Some ((l<*rev m',r',q',d),(lh<*rev mh',rh'))
  ))
end.

Definition isLedge(x:Config): option unit :=
match x with
| ((l,r,q,d),(lh,mh>>rh)) =>
  b2o (eqb d L) &&& (fun _ =>
  b2o (eqb mh []))
end.

Definition mstep T x :=
match upd1 x with
| inl x =>
  match upd2 T x with
  | Some x => inl x
  | None => inr None
  end
| inr x => inr (Some x)
end.

Definition msteps T T0 x :=
  N_iter_until (mstep T0) (inl x) T.

Definition mstep_to_Ledge T x :=
if isLedge x then inr (Some x) else
match mstep T x with
| inl x => inl x
| _ => inr None
end.

Definition msteps_to_Ledge T T0 x :=
  N_iter_until (mstep_to_Ledge T0) (inl x) T.

Definition msteps_to_Ledge' T T0 x :=
match mstep T0 x with
| inl x =>
  match msteps_to_Ledge T T0 x with
  | inr (Some x) => inl x
  | _ => inr tt
  end
| _ => inr tt
end.

Definition mstepsLe T T0 T1 x :=
  N_iter_until (msteps_to_Ledge' T0 T1) (inl x) T.

Definition mstepsLe' T T0 T1 x :=
  match msteps_to_Ledge' T0 T1 x with
  | inl x => mstepsLe (T-1) T0 T1 x
  | _ => inr tt
  end.

Lemma upd1_spec x:
match upd1 x with
| inl x' => Config_eval x -[ tm ]-> Config_eval x'
| inr tr => halts_at_trans tm (Config_eval x) tr
end.
Proof.
  refine (
  match x with
  | ((l,m>>r,q,d),(lh,mh>>rh)) => _
  end);
  unfold upd1,Config_eval.
  destruct (cflip tm d (q,m)) as [[[m' []] q']|] eqn:E.
  - destruct d; cbn; cbn in E.
    + unfold flip in E.
      destruct (tm (q,m)) as [[[m'0 []] q'0]|] eqn:E0; inverts E.
      eapply step_right,E0.
    + eapply step_left,E.
  - destruct d; cbn; cbn in E.
    + unfold flip in E.
      destruct (tm (q,m)) as [[[m'0 []] q'0]|] eqn:E0; inverts E.
      eapply step_left,E0.
    + eapply step_right,E.
  - destruct d; cbn; cbn in E.
    + unfold flip in E.
      destruct (tm (q,m)) as [[[m'0 []] q'0]|] eqn:E0; inverts E.
      exists O.
      econstructor; eauto.
    + exists O.
      econstructor; eauto.
Qed.

Lemma upd2_spec T x x':
  upd2 T x = Some x' ->
  Config_eval x -[ tm ]->* Config_eval x'.
Proof.
  refine (
  match x with
  | ((l,r,q,d),(lh,rh)) => _
  end);
  unfold upd2.
  intros H.
  des_if' H.
  destruct p3 as [[[[[q' m'] r'] mh'] rh'] n'].
  apply upd_spec in E.
  destruct E as [m [hx' [QR [I1 [I2 I3]]]]].
  subst r.
  des_if' H.
  inverts H.
  destruct (is0_spec n'); [|inverts E].
  unfold to_nat in I2; rewrite e in I2.
  inverts I2.
  unfold cflip in I3.
  unfold Config_eval; destruct d.
  - eapply RRs'_O in I3.
    apply unflip_evstep in I3.
    apply I3.
  - eapply RRs'_O in I3; eauto.
Qed.

Lemma mstep_spec T x:
match mstep T x with
| inl x' => Config_eval x -[ tm ]->+ Config_eval x'
| inr (Some tr) => halts_at_trans tm (Config_eval x) tr
| inr None => True
end.
Proof.
  unfold mstep.
  pose proof (upd1_spec x) as I1.
  destruct (upd1 x).
  2: trivial.
  destruct (upd2 T c) eqn:E; trivial.
  apply upd2_spec in E.
  eapply progress_intro; eauto.
Qed.

Lemma msteps_spec T T0 x:
match msteps T T0 x with
| inl x' => Config_eval x -[ tm ]->* Config_eval x'
| inr (Some tr) => halts_at_trans tm (Config_eval x) tr
| inr None => True
end.
Proof.
  unfold msteps.
  eapply N_iter_until_spec.
  2: eauto.
  intros.
  pose proof (mstep_spec T0 x0).
  destruct (mstep T0 x0) as [x1|[tr|]]; trivial.
  - eapply progress_evstep in H0.
    eapply evstep_trans; eauto.
  - eapply halts_at_trans_evstep; eauto.
Qed.

Lemma mstep_to_Ledge_spec T x:
match mstep_to_Ledge T x with
| inl x' => Config_eval x -[ tm ]->+ Config_eval x'
| inr (Some x') => x=x'
| inr None => True
end.
Proof.
  unfold mstep_to_Ledge.
  destruct (isLedge x); trivial.
  pose proof (mstep_spec T x).
  destruct (mstep T x) as [x'|[|]]; trivial.
Qed.

Lemma msteps_to_Ledge_spec T T0 x:
match msteps_to_Ledge T T0 x with
| inl x' => Config_eval x -[ tm ]->* Config_eval x'
| inr (Some x') => Config_eval x -[ tm ]->* Config_eval x'
| inr None => True
end.
Proof.
  unfold msteps_to_Ledge.
  eapply N_iter_until_spec.
  2: eauto.
  intros.
  pose proof (mstep_to_Ledge_spec T0 x0).
  destruct (mstep_to_Ledge T0 x0) as [x1|[tr|]]; trivial.
  - eapply progress_evstep in H0.
    eapply evstep_trans; eauto.
  - congruence.
Qed.

Lemma msteps_to_Ledge'_spec T T0 x:
match msteps_to_Ledge' T T0 x with
| inl x' => Config_eval x -[ tm ]->+ Config_eval x'
| inr _ => True
end.
Proof.
  unfold msteps_to_Ledge'.
  intros.
  pose proof (mstep_spec T0 x).
  destruct (mstep T0 x); trivial.
  pose proof (msteps_to_Ledge_spec T T0 c).
  destruct (msteps_to_Ledge T T0 c) as [|[|]]; trivial.
  eapply progress_evstep_trans; eauto.
Qed.

Lemma mstepsLe_spec T T0 T1 x:
match mstepsLe T T0 T1 x with
| inl x' => Config_eval x -[ tm ]->* Config_eval x'
| _ => True
end.
Proof.
  unfold mstepsLe.
  eapply N_iter_until_spec.
  2: eauto.
  intros.
  pose proof (msteps_to_Ledge'_spec T0 T1 x0).
  destruct (msteps_to_Ledge' T0 T1 x0) as [x1|]; trivial.
  eapply progress_evstep in H0.
  eapply evstep_trans; eauto.
Qed.

Lemma mstepsLe'_spec T T0 T1 x:
match mstepsLe' T T0 T1 x with
| inl x' => Config_eval x -[ tm ]->+ Config_eval x'
| _ => True
end.
Proof.
  unfold mstepsLe'.
  pose proof (msteps_to_Ledge'_spec T0 T1 x).
  destruct (msteps_to_Ledge' T0 T1 x) as [x1|]; trivial.
  pose proof (mstepsLe_spec (T-1) T0 T1 x1).
  destruct (mstepsLe (T-1) T0 T1 x1); trivial.
  eapply progress_evstep_trans; eauto.
Qed.

Definition C0: Config :=
  ((const s0,const s0,q0,R),(const [],const [])).

End tm_sec.

Lemma decide_halt tm D T T0 tr:
  msteps tm D T T0 C0 = inr (Some tr) ->
  halts_at_trans tm c0 tr.
Proof.
  intros H.
  epose proof (msteps_spec tm D T T0 C0) as I1.
  rewrite H in I1.
  apply I1.
Qed.

Lemma decide_loop tm D PP P T0 T1 m m0 l r q lh rh lh' rh':
  mstepsLe tm D PP T0 T1 C0 = inl ((m*>l,r,q,L),(lh,rh)) ->
  (forall l,
  mstepsLe' tm D P T0 T1 ((m*>l,r,q,L),(lh,rh)) = inl ((m*>m0*>l,r,q,L),(lh',rh'))) ->
  ~halts tm c0.
Proof.
  intros.
  epose proof (mstepsLe_spec _ _ _ _ _ _) as I1.
  rewrite H in I1.
  eapply multistep_nonhalt.
  1: apply I1.
  eapply progress_nonhalt_simple with (C:=fun l => r <{{q}} m *> l).
  intro l'.
  specialize (H0 l').
  epose proof (mstepsLe'_spec _ _ _ _ _ _) as I2.
  rewrite H0 in I2.
  eexists.
  apply I2.
Qed.

Lemma decide_evstep tm D T T0 T1 x':
  match mstepsLe tm D T T0 T1 C0 with
  | inl x' => Some (Config_eval x')
  | _ => None
  end = Some x' ->
  c0 -[ tm ]->* x'.
Proof.
  destruct (mstepsLe tm D T T0 T1 C0) as [x|] eqn:E.
  2: congruence.
  epose proof (mstepsLe_spec _ _ _ _ _ _) as I1.
  rewrite E in I1.
  intro H.
  inverts H.
  apply I1.
Qed.


Fixpoint Str_firstn{A}(n:nat)(r:Stream A) :=
match n with
| O => []
| S n => Streams.hd r :: Str_firstn n (Streams.tl r)
end.

Lemma Str_firstn_spec{A} n (r:Stream A):
  r = (Str_firstn n r) *> (Str_nth_tl n r).
Proof.
  gen r.
  induction n; intros; cbn.
  - trivial.
  - rewrite <-(IHn (Streams.tl r)).
    destruct r; trivial.
Qed.

Section dec_sec.

Local Opaque eqb.

Lemma decide_loop' tm D PP P' P T0 T1:
  (forall l,
  match mstepsLe tm D PP T0 T1 C0 with
  | inl ((l0,r,q,L),(lh,rh)) =>
    let m:=Str_firstn P' l0 in
    match mstepsLe' tm D P T0 T1 ((m*>l,r,q,L),(lh,rh)) with
    | inl ((l0',r',q',L),_) =>
      b2o (eqb (Str_firstn P' l0') m) &&& (fun _ =>
      b2o (eqb q q') &&& (fun _ =>
      Some (r,r')))
    | _ => None
    end
  | _ => None
  end = Some (s0>>const s0,s0>>const s0)) ->
  ~halts tm c0.
Proof.
  rewrite <-const_unfold.
  intros.
  destruct (mstepsLe tm D PP T0 T1 C0) as [[[[[l0 r] q] []] [lh rh]]|] eqn:E.
  2,3: specialize (H (const s0)); congruence.
  remember (Str_firstn P' l0) as m.
  cbn in H.
  epose proof (mstepsLe_spec _ _ _ _ _ _) as I1.
  rewrite E in I1.
  eapply multistep_nonhalt.
  1: apply I1.
  cbn[Config_eval].
  rewrite (Str_firstn_spec P' l0),<-Heqm.
  eapply progress_nonhalt_simple with (C:=fun l => r <{{q}} m *> l).
  intro l.
  specialize (H l).
  destruct (mstepsLe' tm D P T0 T1 (m *> l, r, q, L, (lh, rh))) as 
  [[[[[l0' r'] q'] []] [lh' rh']]|] eqn:E'; try congruence.
  des_if' H.
  des_if' H.
  cbn in H.
  inverts H.
  destruct (eqb_spec q q'); [subst q'|inverts E1].
  destruct (eqb_spec (Str_firstn P' l0') m); [|inverts E0].
  epose proof (mstepsLe'_spec _ _ _ _ _ _) as I2.
  rewrite E' in I2.
  cbn[Config_eval] in I2.
  eexists (Str_nth_tl P' l0').
  applys_eq I2.
  rewrite <-e,<-Str_firstn_spec; trivial.
Qed.

End dec_sec.

End LongAcc.

