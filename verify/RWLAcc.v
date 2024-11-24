Require Import NArith.
Require Import List.
Require Import Lia.
From BusyCoq Require Import DHTM.
From BusyCoq Require Import Eqb.

Ltac destruct_spec_expr e f :=
match e with
| match ?a with _ => _ end => destruct_spec_expr a f
| if ?a then _ else _ => destruct_spec_expr a f
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 ?arg6 ?arg7 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5 arg6 arg7);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 ?arg6 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5 arg6);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 =>
  pose proof (f arg1 arg2 arg3 arg4);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 =>
  pose proof (f arg1 arg2 arg3);
  destruct e
| ?a ?arg1 ?arg2 =>
  pose proof (f arg1 arg2);
  destruct e
| ?a ?arg1 =>
  pose proof (f arg1);
  destruct e
end.

Ltac destruct_spec f :=
match goal with
|- ?a => destruct_spec_expr a f
end.

Module RWLAcc(Ctx:Ctx).
Module DHTM := DHTM Ctx.
Export DHTM.
Section bsz.
Hypothesis tm:TM.
Hypothesis bsz:nat.
Hypothesis bmaxT:N.
Definition RW:Type := (list Sym)*N*N.
Definition RWL:Type := list RW.
Definition RWL_config:Type := RWL*RWL*Q*dir.

Definition pop(ls:RWL):option ((list Sym)*RWL) :=
match ls with
| [] => Some (repeat s0 bsz,[])
| (w,a,Npos b)::t =>
  let b':=Pos.pred_N b in
  match b' with
  | N0 =>
    match a with
    | N0 => Some (w,t)
    | _ => None
    end
  | _ => Some (w,(w,a,b')::t)
  end
| _ => None
end.

Definition push(w:list Sym)(ls:RWL):RWL :=
match ls with
| [] => (w,0,1)%N::nil
| (w',a,b)::t =>
  if eqb w w' then
    (w,a,N.succ b)::t
  else
    (w,0,1)%N::ls
end.

Definition push'(x:RW)(ls:RWL):RWL :=
let '(w,a,b):=x in
match ls with
| (w',a',b')::t =>
  if eqb w w' then
    (w',a+a',b+b')%N::t
  else x::ls
| _ => x::ls
end.

Fixpoint match_side(ls1 ls2:RWL):option RWL :=
match ls1,ls2 with
| (w1,N0,b1)::t1,(w2,N0,b2)::t2 =>
  if (eqb w1 w2) && (b1 <=? b2)%N then
    match_side t1 t2 &&& (fun t0 => Some ((w1,b2-b1,b1)%N::t0))
  else None
| nil,nil => Some nil
| _,_ => None
end.

Definition match_config(c1 c2:RWL_config):option RWL_config :=
let '(l1,r1,s1,sgn1):=c1 in
let '(l2,r2,s2,sgn2):=c2 in
if (eqb s1 s2) && (eqb sgn1 sgn2) then
  match_side l1 l2 &&& (fun l0 =>
  match_side r1 r2 &&& (fun r0 =>
  Some (l0,r0,s1,sgn1)
  ))
else None.

Definition RWL_step(c:RWL_config):option RWL_config :=
let '(l,r,s,sgn):=c in
pop l &&& (fun '(l0,l1) =>
pop r &&& (fun '(r0,r1) =>
DH_cconfig_bounded_progress tm (l0,r0,s,sgn) bmaxT &&& (fun '(l0',r0',s',sgn') =>
match r0' with
| nil =>
let l0a := firstn bsz l0' in
let l0b := skipn bsz l0' in
if eqb sgn sgn' then
if eqb s s' && eqb l0 l0a then
match r with
| nil => None
| (w,a,b)::t =>
  if eqb r0 w then
  match b with
  | Npos _ => Some (push l0a (push' (l0b,a,b) l1),t,s',sgn')
  | _ => None
  end
  else None
end
else Some (push l0a (push l0b l1),r1,s',sgn')
else Some (push l0a (push l0b r1),l1,s',sgn')
| _ => None
end
))).

Definition RWL_step''(c:RWL_config*bool):RWL_config*bool+unit :=
let (c,_):=c in
match RWL_step c with
| None => inr tt
| Some c' => inl (c',true)
end.

Definition side_subst_S(ls:RWL):RWL :=
map (fun '(w,a,b) => (w,a,a+b)%N) ls.

Definition side_subst_O(ls:RWL):RWL :=
map (fun '(w,a,b) => (w,0,b)%N) ls.

Definition config_subst_S(c:RWL_config):RWL_config :=
let '(l,r,s,sgn):=c in
(side_subst_S l,side_subst_S r,s,sgn).

Definition config_subst_O(c:RWL_config):RWL_config :=
let '(l,r,s,sgn):=c in
(side_subst_O l,side_subst_O r,s,sgn).

Definition check_nonhalt c1 c2 n :=
match match_config c1 c2 with
| None => false
| Some c3 =>
  match N_iter_until RWL_step'' (inl (c3,false)) n with
  | inl (c4,true) => eqb (config_subst_S c3) c4 && eqb (config_subst_O c3) c1
  | _ => false
  end
end.

Definition RWL_state:Type := RWL_config*RWL_config*N*N.
Definition RWL_step'(x:RWL_state):RWL_state+bool :=
let '(c1,c,n,n0):=x in
match RWL_step c with
| None => inr false
| Some c' =>
  if (n <? n0)%N then
    if check_nonhalt c1 c' (N.succ n) then inr true
    else inl (c1,c',N.succ n,n0)
  else
    inl (c',c',N0,n0*2)%N
end.

Definition RWL_state_0:RWL_state := ((([],[],q0,R),([],[],q0,R),0,1)%N).

Definition RWL_steps T :=
N_iter_until RWL_step' (inl RWL_state_0) T.

Section subst_i.
Hypothesis i:nat.

Definition to_seg(x:RW) :=
let '(w,a,b):=x in
w ^^ ((N.to_nat a)*i+(N.to_nat b)).

Definition to_side(ls:RWL) := (flat_map to_seg ls) *> Streams.const s0.

Definition to_config(c:RWL_config):DH_config :=
let '(l,r,s,sgn):=c in
(to_side l,to_side r,s,sgn).

Lemma push_spec w ls:
  to_side (push w ls) =
  w *> to_side ls.
Proof.
  destruct ls as [|[[w' a'] b'] t].
  - cbn.
    rewrite Str_app_assoc.
    cbn.
    change (Pos.to_nat 1) with 1.
    cbn.
    rewrite Str_app_assoc.
    reflexivity.
  - cbn - [eqb].
    destruct (eqb_spec w w').
    + cbn.
      repeat rewrite Str_app_assoc.
      replace (N.to_nat a' * i + N.to_nat (N.succ b')) with (S(N.to_nat a' * i + N.to_nat b')) by lia.
      cbn.
      rewrite Str_app_assoc.
      subst.
      reflexivity.
    + cbn.
      repeat rewrite Str_app_assoc.
      change (Pos.to_nat 1) with 1.
      cbn.
      rewrite Str_app_assoc.
      reflexivity.
Qed.

Lemma push'_spec x ls:
  to_side (push' x ls) =
  to_seg x *> to_side ls.
Proof.
  destruct x as [[w a] b].
  destruct ls as [|[[w' a'] b'] t].
  - cbn.
    rewrite Str_app_assoc.
    reflexivity.
  - cbn - [eqb].
    destruct (eqb_spec w w').
    + cbn.
      repeat rewrite Str_app_assoc.
      replace (N.to_nat (a + a') * i + N.to_nat (b + b')) with ((N.to_nat a * i + N.to_nat b)+(N.to_nat a' * i + N.to_nat b')) by lia.
      rewrite lpow_add.
      rewrite Str_app_assoc.
      subst.
      reflexivity.
    + cbn.
      repeat rewrite Str_app_assoc.
      reflexivity.
Qed.

Lemma pop_spec ls:
match pop ls with
| None => True
| Some (x,t) =>
  to_side ls =
  x *> to_side t
end.
Proof.
  destruct ls as [|[[w a] b] t].
  - cbn.
    induction bsz.
    1: reflexivity.
    cbn. rewrite <-IHn,<-const_unfold.
    reflexivity.
  - cbn.
    destruct b as [|b]; trivial.
    destruct (Pos.pred_N b) eqn:E.
    + cbn.
      repeat rewrite Str_app_assoc.
      assert (b=1)%positive by lia.
      subst b.
      change (Pos.to_nat 1) with 1.
      destruct a as [|a]; trivial.
      cbn.
      rewrite Str_app_assoc.
      reflexivity.
    + cbn.
      replace (N.to_nat a * i + Pos.to_nat b) with (S(N.to_nat a * i + Pos.to_nat p)) by lia.
      cbn.
      repeat rewrite Str_app_assoc.
      reflexivity.
Qed.

Lemma to_side_def a b:
  to_side (a::b) = to_seg a *> to_side b.
Proof.
  cbn.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma RWL_step_spec c:
match RWL_step c with
| None => True
| Some c' => (to_config c) -[ tm ]->+ (to_config c')
end.
Proof.
  destruct c as [[[l r] s] sgn].
  unfold RWL_step.
  unfold if_Some.
  destruct_spec pop_spec; trivial.
  destruct p as [l0 l1].
  destruct_spec pop_spec; trivial.
  destruct p as [r0 r1].
  destruct_spec DH_cconfig_bounded_progress_spec; trivial.
  destruct p as [[[l0' r0'] s'] sgn'].
  destruct H1 as [H1 H2].
  cbn in H2.
  unfold to_config.
  rewrite H,H0.
  destruct r0'; trivial.
  destruct (eqb_spec sgn sgn').
  - destruct sgn,sgn'; try congruence; (
      destruct (eqb_spec s s');
      [| shelve];
      destruct (eqb_spec l0 (firstn bsz l0'));
      [| shelve];
      destruct r as [|[[w a] b] r]; trivial;
      destruct (eqb_spec r0 w); trivial;
      rewrite <-H0;
      destruct b as [|b]; trivial;
      rewrite to_side_def;
      rewrite push_spec;
      rewrite push'_spec;
      unfold to_seg;
      remember (N.to_nat a * i + N.to_nat (N.pos b)) as v1;
      rewrite <-(firstn_skipn bsz l0') in H2;
      subst l0;
      remember (firstn bsz l0') as l0a;
      remember (skipn bsz l0') as l0b;
      destruct v1 as [|v1]; try lia;
      clear Heqv1;
      generalize (to_side r) as r';
      generalize (to_side l1) as l';
      subst r0 s;
      induction v1; intros;
      [ epose proof (H2 _ _) as H2;
        rewrite Str_app_assoc in H2;
        cbn in H2;
        cbn[lpow];
        repeat rewrite app_nil_r;
        apply H2
      | remember (S v1) as v2;
        epose proof (H2 _ _) as H2;
        rewrite Str_app_assoc in H2;
        cbn in H2;
        cbn[lpow];
        repeat rewrite Str_app_assoc;
        eapply progress_trans;
        [ apply H2
        | applys_eq IHv1;
           do 4 f_equal;
           repeat rewrite <-Str_app_assoc;
           f_equal;
           rewrite lpow_shift;
           reflexivity ] ]).
  - destruct sgn,sgn'; try congruence;
    shelve.
Unshelve.
all:
      unfold to_config;
      do 2 rewrite push_spec;
      rewrite <-(firstn_skipn bsz l0') in H2;
      applys_eq H2;
      rewrite Str_app_assoc;
      reflexivity.
Qed.
End subst_i.

Lemma RWL_step_spec' c:
match RWL_step c with
| None => True
| Some c' => forall i, (to_config i c) -[ tm ]->+ (to_config i c')
end.
Proof.
  destruct (RWL_step c) eqn:E; trivial.
  intros i.
  pose proof (RWL_step_spec i c) as H.
  rewrite E in H.
  apply H.
Qed.

Lemma side_subst_S_spec i ls:
  to_side i (side_subst_S ls) = to_side (S i) ls.
Proof.
  unfold to_side,side_subst_S.
  induction ls.
  1: reflexivity.
  cbn.
  repeat rewrite Str_app_assoc.
  rewrite IHls.
  f_equal.
  destruct a as [[w a] b].
  cbn.
  f_equal. lia.
Qed.

Lemma side_subst_O_spec i ls:
  to_side i (side_subst_O ls) = to_side 0 ls.
Proof.
  unfold to_side,side_subst_O.
  induction ls.
  1: reflexivity.
  cbn.
  repeat rewrite Str_app_assoc.
  rewrite IHls.
  f_equal.
  destruct a as [[w a] b].
  cbn.
  f_equal. lia.
Qed.

Lemma config_subst_S_spec i c:
  to_config i (config_subst_S c) = to_config (S i) c.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  repeat rewrite side_subst_S_spec.
  reflexivity.
Qed.

Lemma config_subst_O_spec i c:
  to_config i (config_subst_O c) = to_config O c.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  repeat rewrite side_subst_O_spec.
  reflexivity.
Qed.

Lemma nonhalt_cond c:
  c0 -[ tm ]->* (to_config 0 c) ->
  (forall i, to_config i c -[ tm ]->+ to_config (S i) c) ->
  ~halts tm c0.
Proof.
  intros.
  eapply evstep_nonhalt.
  2: apply H.
  eapply progress_nonhalt with (P:=fun c' => exists i, c' = to_config i c).
  2: eexists; reflexivity.
  intros c1 [i Hc1].
  subst c1.
  eexists _.
  split.
  2: apply (H0 i).
  eexists; reflexivity.
Qed.

Lemma RWL_step''_spec c n:
match N_iter_until RWL_step'' (inl (c,false)) n with
| inl (c',flag) =>
  if flag then
    (forall i, to_config i c -[ tm ]->+ to_config i c')
  else c=c'
| inr _ => True
end.
Proof.
  eapply N_iter_until_spec.
  2: reflexivity.
  intros [c1 flag1] H.
  unfold RWL_step''.
  destruct flag1.
  - destruct_spec (RWL_step_spec'); trivial.
    intros i.
    eapply progress_trans; eauto.
  - destruct_spec (RWL_step_spec'); trivial.
    subst c1.
    apply H0. 
Qed.

Lemma check_nonhalt_spec c1 c2 n:
  c0 -[ tm ]->* (to_config 0 c1) ->
  if check_nonhalt c1 c2 n then ~halts tm c0 else True.
Proof.
  intros Hc1.
  unfold check_nonhalt.
  destruct (match_config c1 c2) as [c3|]; trivial.
  pose proof (RWL_step''_spec c3 n) as Hc4.
  destruct (N_iter_until RWL_step'' (inl (c3, false)) n) as [[c4 [|]]|]; trivial.
  destruct (eqb_spec (config_subst_S c3) c4); trivial.
  destruct (eqb_spec (config_subst_O c3) c1); trivial.
  rewrite <-e in Hc4.
  apply (nonhalt_cond c3).
  2: intros i; applys_eq Hc4.
  2: rewrite config_subst_S_spec; reflexivity.
  erewrite <-config_subst_O_spec.
  rewrite e0.
  apply Hc1.
Qed.

Definition RWL_state_WF(x:RWL_state) :=
let '(c1,c2,_,_) := x in
  c0 -[ tm ]->* to_config 0 c1 /\
  c0 -[ tm ]->* to_config 0 c2.

Lemma RWL_step'_spec x0 T:
RWL_state_WF x0 ->
match N_iter_until RWL_step' (inl x0) T with
| inr flag =>
  if flag then ~halts tm c0 else True
| inl x1 => RWL_state_WF x1
end.
Proof.
  intros Hx0.
  eapply N_iter_until_spec.
  2: apply Hx0.
  intros [[[c1 c2] n1] n2].
  unfold RWL_step'.
  intros [Hc1 Hc2].
  destruct_spec (RWL_step_spec O); trivial.
  destruct (n1 <? n2)%N.
  2: cbn; split;
    apply progress_evstep; eapply evstep_progress_trans; eauto.
  destruct_spec check_nonhalt_spec.
  1: tauto.
  cbn.
  split. 1: tauto.
  apply progress_evstep.
  eapply evstep_progress_trans; eauto.
Qed.

Lemma RWL_state_0_WF:
RWL_state_WF RWL_state_0.
Proof.
  cbn; split; constructor.
Qed.

Definition decide_nonhalt T :=
match RWL_steps T with
| inr true => true
| _ => false
end.

Lemma decide_nonhalt_spec T:
  decide_nonhalt T = true ->
  ~halts tm c0.
Proof.
  unfold decide_nonhalt,RWL_steps.
  pose proof (RWL_step'_spec RWL_state_0 T) as H0.
  intros H.
  destruct (N_iter_until RWL_step' (inl RWL_state_0) T).
  1: congruence.
  destruct b.
  2: congruence.
  apply H0,RWL_state_0_WF.
Qed.

End bsz.

End RWLAcc.

