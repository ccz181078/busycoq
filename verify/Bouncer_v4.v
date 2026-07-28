From BusyCoq Require Import Individual62.

Require Import ZArith Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal ES_v3.
Import HashTable Eqb.


Module URRBA.
Module K_Hash.
Import HashConcat.
Definition K:Type := Q*(list Sym)*(list (Q*Q)).
Definition K_eq:K->K->bool := eqb.
Definition K_eq_spec:forall a b:K, Bool.reflect (a=b) (K_eq a b) := eqb_spec.
Definition K_hash: K->hash_t := hash.
Definition V := K.
End K_Hash.

Module K_Map := HashMap K_Hash K_Hash.

Definition to_DH02(x:Q*Q):DH0*DH0 :=
let '(a,b):=x in ((a,[]),(b,[])).

Section tm_sec.
Hypothesis tm:TM.
Hypothesis ls:list (Q*Q).
Hypothesis P_LC0: side->Prop.
Hypothesis ls_spec: forall l, P_LC0 l -> exists l', sideRLs (flip tm) (map to_DH02 ls) l l' /\ P_LC0 l'.

Inductive P_LC: (list Sym)->(list (Q*Q))->side->Prop :=
| P_LC_O l0 l ls0:
  P_LC0 l0 ->
  sideRLs (flip tm) (map to_DH02 ls0) l l0 ->
  P_LC [] ls0 l
| P_LC_S h t ls0 l:
  P_LC t ls0 l ->
  P_LC (h::t) ls0 (h>>l)
.

Definition LR x x' :=
  let '(q,l0,v):=x in
  let '(q',l0',v'):=x' in
  forall l,
  P_LC l0 v l ->
  exists l',
  P_LC l0' v' l' /\
  (forall r, l <{{q}} r -[ tm ]->+ l' {{q'}}> r).

Definition LRH x :=
  let '(q,l0,v):=x in
  forall l,
  P_LC l0 v l ->
  forall r, halts tm (l <{{q}} r).

Definition mp_WF(mp:K_Map.hmap_t):Prop :=
  K_Map.hmap_WF mp /\
  forall x x',
  K_Map.hmap_get x mp = Some x' ->
  LR x x'.

Definition ret(mp:K_Map.hmap_t)(l l':K_Hash.K) :=
let mp':=K_Map.hmap_set l l' mp in
Some (Some (mp',l')).

Fixpoint exec(T:nat)(mp:K_Map.hmap_t)(l:K_Hash.K):option (option (K_Map.hmap_t*K_Hash.K)) :=
match T with
| O => None
| S T =>
match K_Map.hmap_get l mp with
| Some l' => Some (Some (mp,l'))
| None =>
  let '(q,l0,v):=l in
  match l0 with
  | s::l1 =>
    match tm (q,s) with
    | None => Some None
    | Some (s',L,q') =>
      match exec T mp (q',l1,v) with
      | Some (Some (mp,(q2,l2,v))) =>
        match exec T mp (q2,s'::l2,v) with
        | Some (Some (mp,l')) => ret mp l l'
        | Some None => Some None
        | None => None
        end
      | Some None => Some None
      | None => None
      end
    | Some (s',R,q') =>
      ret mp l (q',s'::l1,v)
    end
  | [] =>
    match v with
    | (q1,q2)::v =>
      if eqb q q1 then
        ret mp l (q2,[],v)
      else None
    | [] =>
      match ls with
      | (q1,q2)::v =>
        if eqb q q1 then
          ret mp l (q2,[],v)
        else None
      | [] => None
      end
    end
  end
end
end.

Fixpoint exec0(T:nat)(mp:K_Map.hmap_t)(l:K_Hash.K)(r:side):bool :=
match T with
| O => false
| S T =>
  match r with
  | m>>r =>
  let '(q,l1,v):=l in
  match tm (q,m) with
  | None => true
  | Some (m',L,q') =>
    match exec T mp (q',l1,v) with
    | Some (Some (mp,l')) =>
      exec0 T mp l' (m'>>r)
    | Some None => true
    | None => false
    end
  | Some (m',R,q') =>
    exec0 T mp (q',m'::l1,v) r
  end
  end
end.

Lemma ret_spec mp x x':
mp_WF mp ->
LR x x' ->
match ret mp x x' with
| Some (Some (mp',x')) => mp_WF mp' /\ LR x x'
| Some None => LRH x
| None => True
end.
Proof with trivial.
  intros [I1 I2] I3.
  unfold ret.
  split...
  unfold mp_WF in *; split.
  1: apply K_Map.hmap_set_WF...
  intros.
  destruct (eqb_spec x0 x); subst.
  - rewrite K_Map.hmap_get_set_same in H...
    inverts H...
  - rewrite K_Map.hmap_get_set_other in H...
    eauto 2.
Qed.

Lemma exec_spec T mp x:
mp_WF mp ->
match exec T mp x with
| Some (Some (mp',x')) => mp_WF mp' /\ LR x x'
| Some None => LRH x
| None => True
end.
Proof with trivial.
  gen mp x.
  induction T; cbn[exec]; intros...
  destruct (K_Map.hmap_get x mp) as [l'|] eqn:E.
  - split...
    apply H in E...
  - destruct x as [[q l0] v].
    destruct l0 as [|s l1].
    + destruct v as [|[q2 q3] v].
      * destruct ls as [|[q2 q3] v]...
        destruct (eqb_spec q q2)...
        subst.
        apply ret_spec.
        1: auto 1.
        unfold LR.
        intros.
        inverts H0.
        inverts H2.
        destruct (ls_spec _ H1) as [l' [I1 I2]].
        inverts I1.
        eexists; split.
        -- eapply P_LC_O; eauto 1.
        -- intros r.
           specialize (H6 r).
           apply unflip_progress in H6.
           apply H6.
      * destruct (eqb_spec q q2)...
        subst.
        apply ret_spec.
        1: auto 1.
        unfold LR.
        intros.
        inverts H0.
        inverts H2.
        eexists; split.
        -- eapply P_LC_O; eauto 1.
        -- intros r.
           specialize (H7 r).
           apply unflip_progress in H7.
           apply H7.
    + destruct (tm (q,s)) as [[[s' []] q']|] eqn:E2.
      * epose proof (IHT _ (q',l1,v) H) as I1.
        destruct (exec T mp (q', l1, v)) as [[[mp0 [[q2 l2] v0]]|]|] eqn:E0...
        -- destruct I1 as [I1a I1b].
           epose proof (IHT _ (q2,s'::l2,v0) I1a) as I2.
           destruct (exec T mp0 (q2, s' :: l2, v0)) as [[[mp1 [[q3 l3] v1]]|]|] eqn:E1...
           ++ destruct I2 as [I2a I2b].
              apply ret_spec.
              1: auto 1.
              unfold LR in *.
              intros.
              inverts H0.
              destruct (I1b _ H5) as [l' [I3a I3b]].
              eapply P_LC_S with (h:=s') in I3a.
              destruct (I2b _ I3a) as [l'0 [I4a I4b]].
              eexists; split.
              1: apply I4a.
              intros.
              eapply step_left in E2.
              eapply progress_step.
              1: apply E2.
              cbn.
              follow11 I3b.
              apply I4b.
           ++ unfold LR,LRH in *.
              intros.
              inverts H0.
              destruct (I1b _ H5) as [l' [I3a I3b]].
              eapply halts_evstep.
              2:{
                eapply evstep_step.
                eapply step_left in E2.
                1: apply E2.
                cbn.
                follow100 I3b.
                finish.
              }
              cbn.
              eapply P_LC_S with (h:=s') in I3a.
              apply (I2 _ I3a).
        -- unfold LRH in *.
           intros.
           inverts H0.
           eapply halts_evstep.
           2:{
             eapply evstep_step.
             eapply step_left in E2.
             1: apply E2.
             cbn.
             finish.
           }
           apply I1,H5.
      * apply ret_spec.
        1: auto 1.
        unfold LR.
        intros.
        inverts H0.
        eexists; split.
        1: eapply P_LC_S,H5.
        intros.
        eapply progress_base.
        eapply step_right in E2.
        apply E2.
      * unfold LRH.
        intros.
        inverts H0.
        eapply halted_halts,E2.
Qed.

Lemma exec0_spec T mp q l0 v r:
mp_WF mp ->
exec0 T mp (q,l0,v) r = true ->
forall l,
P_LC l0 v l ->
halts tm (l {{q}}> r).
Proof.
  gen mp q l0 v r.
  induction T; cbn[exec0]; intros.
  1: congruence.
  destruct r as [m r].
  destruct (tm (q,m)) as [[[m' []] q']|] eqn:E2.
  - epose proof (exec_spec T mp (q',l0,v) H) as I1.
    destruct (exec T mp (q',l0,v)) as [[[mp' [[q'0 l1] v0]]|]|].
    + destruct I1 as [I1a I1b].
      unfold LR in *.
      destruct (I1b _ H1) as [l' [I2a I2b]].
      eapply halts_evstep.
      2:{
        eapply evstep_step.
        eapply step_left in E2.
        1: apply E2.
        cbn.
        follow100 I2b.
        cbn.
        finish.
      }
      eapply IHT in H0; eauto 1.
    + unfold LRH in *.
      specialize (I1 _ H1).
      eapply halts_evstep.
      2:{
        eapply evstep_step.
        eapply step_left in E2.
        1: apply E2.
        cbn.
        finish.
      }
      apply I1.
    + congruence.
  - eapply halts_evstep.
    2:{
      eapply evstep_step.
      eapply step_right in E2.
      1: apply E2.
      cbn.
      finish.
    }
    eapply P_LC_S with (h:=m') in H1.
    eapply IHT; eauto 1.
  - eapply halted_halts,E2.
Qed.

Lemma halt T S q r:
exec0 T (K_Map.hmap_make S) (q,[],[]) r = true ->
forall l,
P_LC0 l ->
halts tm (l {{q}}> r).
Proof.
  intros H.
  intros.
  eapply exec0_spec in H.
  1: apply H.
  1:{
    split.
    1: apply K_Map.hmap_make_WF.
    intros.
    rewrite K_Map.hmap_get_make in H1.
    congruence.
  }
  eapply P_LC_O; eauto 1.
  apply sideRLseq_O.
Qed.

End tm_sec.

End URRBA.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1RD_1LB1RA_1RE0RE_1LF0RC_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition LC m n :=
  0inf
  <*<[1;1;0;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  <*<[0;1;1;0;1;1;1;1;1;1;1;1;0;1;1;1;1;1;1]^^(1+m)
  <*<[0;1;1;0;1;1;1;1;1;1;0;1;1;1;1;0;0;1;1;1;1;1;0;1;1;1;1;1;1;0;1;1;0;1;1;0;1]
  <*<[1;1;1;1;1;0;1;1;1;1;0;0]^^(2+n)
  <*<[1].

Definition LH :=
  [(A,C);(B,D);(A,E);(A,B);(A,E);(F,E);(A,B);(A,A);(A,C);(B,D);(A,E);(A,B);(A,E);(F,E);(A,B);(A,E);(F,A);(A,C);(B,D);(A,E);(A,B);(A,B);(A,E);(F,C);(A,B);(A,C);(B,D);(A,E);(A,B);(A,B);(A,E);(F,C);(A,B);(A,C);(B,D);(A,B);(A,E);(F,E);(A,B);(A,E);(F,C);(A,B);(A,C);(B,D);(A,B);(A,E);(F,C);(A,B);(A,C);(B,D);(A,C);(B,C);(A,C);(B,D);(A,B);(A,E);(F,C);(A,B);(A,C);(B,D);(A,C);(A,B);(A,C);(B,D);(A,E);(F,C);(A,B);(A,C);(B,D);(A,C);(B,D);(A,A);(A,C);(B,D);(A,E);(F,C);(A,B);(A,C);(B,D);(A,C);(B,D);(A,A);(A,C);(B,D);(A,E);(F,D);(A,C);(A,B);(A,C);(B,D);(A,A);(A,C);(B,D);(A,E);(A,B);(A,C);(B,D);(A,A);(A,C);(B,D);(A,E);(A,B);(A,A);(A,E);(F,D);(A,A);(A,C);(B,D);(A,E);(F,A);(A,C);(B,D);(A,E);(A,B);(A,A)].

Definition rh0 := [0;0;0;1;1;0;1;1;0;1;1;0;0;0;0;1;1;0;1;1;0;1;1;0;0;1;1;0;1;1;0;0;0;0;0;0;0;1;1;0;0;0;0;0;1;1;0;1;1;0;1;1;1;1;0;1;1;0;0;0;1;1;0;1;1;0;1;1;1;1;0;1;1;1;1;0;1;1;0;1;1;0;0;0;1;1;0;1;1;1] *> 0inf.

Lemma LInc m n:
  sideRLs (flip tm) (map URRBA.to_DH02 LH) (LC m n) (LC (12+m) (5+n)).
Proof.
  unfold LC.
  es' m n.
Qed.

Lemma init:
  c0 -->*
  LC 18 3 {{A}}> rh0.
Proof.
  eapply without_counter.
  eapply multistep_c_spec with (n:=629411).
  vm_check_eq.
Qed.

Lemma halt: halts tm c0.
Proof.
  eapply halts_evstep.
  2: apply init.
  eapply URRBA.halt with (P_LC0:=fun l => exists m n, l=LC m n)
  (S:=Uint63.of_Z (10^5)) (T:=10^4).
  3: do 2 eexists; trivial.
  - intros l [m [n I1]].
    subst.
    eexists; split.
    1: apply LInc.
    do 2 eexists. trivial.
  - native_check_eq.
Time Qed.

End TM1.


