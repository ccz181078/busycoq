Require Import ZArith.
Require Import List.
Require Import Lia.
Require Uint63.
From BusyCoq Require Import HashTable.
From BusyCoq Require TM.
From BusyCoq Require Import Eqb.
From Coq Require Import Lists.Streams.
From Coq Require Import Lists.List.

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
Module Uint.
Import Uint63.
Open Scope uint63.
Definition uint_0 := 0x0.
Definition uint_1 := 0x1.

#[export]
Instance uint_Eqb: Eqb int.
Proof.
  apply Build_Eqb with (eqb:=eqb).
  intros.
  pose proof (eqb_spec x y) as H.
  destruct (x=?y); constructor.
  1: tauto.
  intro.
  rewrite <-H in H0.
  congruence.
Defined.

Fixpoint to_Pos_rec(x:int)(n:nat) :=
if x =? 0x1 then xH else
match n with
| O => xH
| S n0 =>
  let y := (to_Pos_rec (x>>0x1) n0) in
  (if is_even x then y~0 else y~1)%positive
end.

Definition to_N(x:int) :=
if x=?0x0 then N0 else Npos (to_Pos_rec x size).

End Uint.

Import TM.
Module TC(Ctx:Ctx).
Module TM := TM Ctx.
Export TM.

Import Uint.

Module BoundedConfig.
Record T := {
  l: list Sym;
  r: list Sym;
  s: Q;
  sgn: dir;
}.

Definition T_eqb(a b:T) :=
let (l1,r1,s1,sgn1):=a in
let (l2,r2,s2,sgn2):=b in
((eqb s1 s2) && (eqb sgn1 sgn2) && (eqb l1 l2) && (eqb r1 r2))%bool.

#[export]
Instance T_Eqb: Eqb T.
Proof.
  apply Build_Eqb with (eqb:=T_eqb).
  intros.
  destruct x,y.
  unfold T_eqb.
  destruct (eqb_spec s2 s3); solve_Bool_reflect.
  destruct (eqb_spec sgn0 sgn1); solve_Bool_reflect.
  destruct (eqb_spec l0 l1); solve_Bool_reflect.
  destruct (eqb_spec r0 r1); solve_Bool_reflect.
Defined.


Definition T0:T := Build_T [] [] q0 R.

Definition to_config (x:T) (l0 r0:side) :=
let (l,r,s,sgn):=x in
match sgn with
| L => l0 <* r <{{s}} l *> r0
| R => l0 <* l {{s}}> r *> r0
end.

Definition to_config' (x:T) :=
let (l,r,s,sgn):=x in
match sgn with
| L => const s0 <* r <{{s}} l *> const s0
| R => const s0 <* l {{s}}> r *> const s0
end.

Definition step(tm:TM)(x:T):option (T*(Q*Sym)) :=
let (l,r,s,sgn):=x in
match r with
| nil => None
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (Build_T (m'::l) r0 s' sgn',(s,m))
    else
      Some (Build_T (m'::r0) l s' sgn',(s,m))
  end
end.

Definition step1(tm:TM)(x:T):T+T :=
match step tm x with
| Some (x',_) => inl x'
| None => inr x
end.

Definition multistep(tm:TM)(x:T)(n:N):T+T :=
N_iter_until (step1 tm) (inl x) n.

Definition progress(tm:TM)(x:T)(n:N):T+T :=
match n with
| N0 => inr x
| _ => multistep tm x n
end.

Definition ht_r(ls:list Sym):Sym*(list Sym) :=
match ls with
| nil => (s0,nil)
| h::t => (h,t)
end.

Definition T':Type := T*(nat*nat*nat*nat).

Definition step'(tm:TM)(x:T'):T' :=
let '(x0,(ld1,rd1,ld2,rd2)):=x in
let (l,r,s,sgn):=x0 in
let (m,r0):=ht_r r in
match tm (s,m) with
| None => x
| Some (m',sgn',s') =>
  if dir_eqb sgn sgn' then
    (Build_T (m'::l) r0 s' sgn',
    match rd2 with
    | O => (ld1,S rd1,S ld2,O)
    | S rd2' => (ld1,rd1,S ld2,rd2')
    end)
  else
    (Build_T (m'::r0) l s' sgn',
    match rd2 with
    | O => (S rd1,ld1,S O,ld2)
    | S rd2' => (rd1,ld1,rd2,ld2)
    end)
end.

Definition steps'(tm:TM)(x:T)(n:N):T':=
N.iter n (step' tm) (x,(O,O,O,O)).

Definition step_d(tm:TM)(x:T*Uint63.int):option (T*Uint63.int) :=
let (x1,x2):=x in
let (l,r,s,sgn):=x1 in
match r with
| nil => None
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    let x2':=
      match sgn' with
      | R => Uint63.add x2 uint_1
      | L => Uint63.sub x2 uint_1
      end in
    if dir_eqb sgn sgn' then
      Some (Build_T (m'::l) r0 s' sgn',x2')
    else
      Some (Build_T (m'::r0) l s' sgn',x2')
  end
end.

Fixpoint find_cycle_0(tm:TM)(x0:T)(x1:T*Uint63.int)(n:nat) :=
match n with
| O => false
| S n0 =>
  match step_d tm x1 with
  | None => false
  | Some (x2a,x2b) =>
    if ((eqb x2b uint_0) && (eqb x0 x2a))%bool then
      true
    else
      find_cycle_0 tm x0 (x2a,x2b) n0
  end
end.

Definition find_cycle(tm:TM)(x:T)(n:nat) :=
  find_cycle_0 tm x (x,uint_0) n.

End BoundedConfig.


Module TC_state.
Import HashConcat.
Record T := {
  bc: BoundedConfig.T;
  t0: Uint63.int;
  h0: hash_t;
  hs: list (Uint63.int*dir*(hash_t))
}.
Definition upd(tm:TM)(x:T):T+(T*(Q*Sym)) :=
let (bc,t0,h0,hs):=x in
match BoundedConfig.step tm bc with
| Some (bc',h) => inl (Build_T bc' (Uint63.succ t0) ((hash h) ## h0) hs)
| None =>
  let (l,r,s,sgn):=bc in
  match r with
  | nil => inl (Build_T (BoundedConfig.Build_T l [s0] s sgn) uint_0 hv1 ((t0,sgn,h0)::hs))
  | m0::r0 => inr (x,(s,m0))
  end
end.

Definition upds(tm:TM)(x:T)(n:N) :=
  N_iter_until (upd tm) (inl x) n.

Definition T0:T := Build_T BoundedConfig.T0 uint_0 hv1 [].

Fixpoint check_TC_0(ls1 ls2:list (Uint63.int*dir*(hash_t)))(n:nat):bool :=
match n with
| O => true
| S n0 =>
  match ls1,ls2 with
  | h1::t1,h2::t2 => (eqb h1 h2) && check_TC_0 t1 t2 n0
  | _,_ => false
  end
end.

Fixpoint get_TC_period(ls:list (Uint63.int*dir*(hash_t)))(n:nat):Uint63.int :=
match n with
| O => uint_0
| S n0 =>
  match ls with
  | nil => uint_0
  | (h0,h1,h2)::t => Uint63.add h0 (get_TC_period t n0)
  end
end.

Fixpoint check_TC_1(ls1 ls2:list (Uint63.int*dir*(hash_t)))(n:nat):option (Uint63.int*nat) :=
match ls2 with
| nil => None
| h2::t2 =>
  if (check_TC_0 ls1 ls2 n) then Some (get_TC_period ls1 n,n) else (check_TC_1 ls1 t2 (S n))
end.

Definition check_TC_2(ls:list (Uint63.int*dir*(hash_t))):option (Uint63.int*nat) :=
  check_TC_1 ls (List.tl ls) (S O).

Definition check_TC(tm:TM)(x:T):bool :=
match check_TC_2 x.(hs) with
| Some (p,d) =>
  let p' := (to_N p) in
  let '(ld1,rd1,_,_) := snd (BoundedConfig.steps' tm x.(bc) p') in
  let (l,r,s,sgn):=x.(bc) in
  match x.(hs) with
  | nil => false
  | (_,sgn0,_)::_ =>
    if eqb sgn sgn0 then
      let l1:=firstn ld1 l in
      let r1:=r++(repeat s0 d) in
      let c1:=BoundedConfig.Build_T l1 r1 s sgn in
      match BoundedConfig.progress tm c1 p' with
      | inl (BoundedConfig.Build_T l2 r2 s2 sgn2) =>
        ((eqb s2 s) && (eqb sgn2 sgn) && (eqb r2 r) && (eqb l2 (l1++(skipn (length l1) l2))))%bool
      | _ => false
      end
    else
      let r1:=firstn rd1 r in
      let l1:=l++(repeat s0 d) in
      let c1:=BoundedConfig.Build_T l1 r1 s sgn in
      match BoundedConfig.progress tm c1 p' with
      | inl (BoundedConfig.Build_T l2 r2 s2 sgn2) =>
        ((eqb s2 s) && (eqb sgn2 sgn) && (eqb l2 l) && (eqb r2 (r1++(skipn (length r1) r2))))%bool
      | _ => false
      end
  end
| None => false
end.

Fixpoint decide_0(tm:TM)(ls:list N)(x:T):DecideResult*T :=
match ls with
| nil => (Unknown,x)
| n::t =>
  match upds tm x n with
  | inr (x',h) => (Halt h,x')
  | inl x' =>
    if check_TC tm x' then (NonHalt,x') else decide_0 tm t x'
  end
end.

Fixpoint decide_1(tm:TM)(ls:list ((list N)*nat))(x:T):DecideResult*T :=
match ls with
| nil => (Unknown,x)
| (n,n0)::t =>
  let res := decide_0 tm n x in
  match res with
  | (Unknown,x') =>
    if BoundedConfig.find_cycle tm x'.(bc) n0 then (NonHalt,x')
    else decide_1 tm t x'
  | _ => res
  end
end.

Definition decide(tm:TM)(ls:list ((list N)*nat)):DecideResult*T :=
  decide_1 tm ls T0.

End TC_state.


Section tm_ctx.
Hypothesis tm:TM.

Lemma BoundedConfig_step_spec x:
match BoundedConfig.step tm x with
| None =>
    x.(BoundedConfig.r) = nil \/
    forall l r,
    halted tm (BoundedConfig.to_config x l r)
| Some (x',h) =>
    forall l r,
    (BoundedConfig.to_config x l r) -[ tm ]-> (BoundedConfig.to_config x' l r)
end.
Proof.
  destruct x as [l [|m r] s sgn]; cbn; trivial.
  - left; reflexivity.
  - destruct (tm (s,m)) as [[[m' sgn'] s']|] eqn:E; trivial.
    + destruct sgn,sgn'; cbn; intros; constructor; apply E.
    + right. intros.
      destruct sgn; apply E.
Qed.

Definition f_if_inl{S S'}(f:S->S+S') a :=
match a with
| inl a0 => f a0
| inr a0 => a
end.

Lemma N_iter_until_spec' {S S'} (f:S->S+S') x n:
  N_iter_until f x n =
  N.iter n (f_if_inl f) x.
Proof.
  rewrite Nnat.N2Nat.inj_iter.
  destruct n.
  1: reflexivity.
  cbn[N.to_nat].
  cbn[N_iter_until].
  gen x.
  induction p; intros; cbn.
  - destruct x.
    + rewrite IHp.
      rewrite IHp.
      replace (Pos.to_nat (p~1)) with ((Pos.to_nat p)+(Pos.to_nat p)+1) by lia.
      repeat rewrite Nat.iter_add.
      reflexivity.
    + generalize (Pos.to_nat p~1) as n.
      induction n.
      1: reflexivity.
      rewrite Nat.iter_succ,<-IHn.
      reflexivity.
  - destruct x.
    rewrite IHp.
    rewrite IHp.
    + replace (Pos.to_nat (p~0)) with ((Pos.to_nat p)+(Pos.to_nat p)) by lia.
      repeat rewrite Nat.iter_add.
      reflexivity.
    + generalize (Pos.to_nat p~0) as n.
      induction n.
      1: reflexivity.
      rewrite Nat.iter_succ,<-IHn.
      reflexivity.
  - replace (Pos.to_nat 1) with 1 by lia.
    destruct x; reflexivity.
Qed.


Lemma BoundedConfig_multistep_spec x n:
match BoundedConfig.multistep tm x n with
| inl x' =>
    forall l r,
    (BoundedConfig.to_config x l r) -[ tm ]->> (N.to_nat n) / (BoundedConfig.to_config x' l r)
| inr _ => True
end.
Proof.
  unfold BoundedConfig.multistep.
  rewrite N_iter_until_spec'.
  induction n using N.peano_ind; cbn; intros.
  - constructor.
  - rewrite N.iter_succ.
    destruct (N.iter n (f_if_inl (BoundedConfig.step1 tm)) (inl x)); trivial.
    unfold f_if_inl.
    unfold BoundedConfig.step1.
    destruct_spec (BoundedConfig_step_spec); trivial.
    destruct p as [x' _].
    intros.
    replace (N.to_nat (N.succ n)) with ((N.to_nat n)+1) by lia.
    eapply multistep_trans; eauto.
Qed.

Lemma BoundedConfig_progress_spec x n:
match BoundedConfig.progress tm x n with
| inl x' =>
    forall l r,
    (BoundedConfig.to_config x l r) -[ tm ]->+ (BoundedConfig.to_config x' l r)
| inr _ => True
end.
Proof.
  destruct n as [|n].
  1: cbn; trivial.
  unfold BoundedConfig.progress.
  destruct_spec (BoundedConfig_multistep_spec); trivial.
  intros.
  eapply multistep_progress.
  applys_eq H.
  replace (N.to_nat (N.pos n)) with (S ((N.to_nat (N.pos n))-1)) by lia.
  reflexivity.
Qed.


Inductive TC_state_WF:TC_state.T->nat->Prop :=
| TC_state_WF_intro bc t0 h0 hs n:
    c0 -[ tm ]->> n / (BoundedConfig.to_config bc (const s0) (const s0)) ->
    TC_state_WF (TC_state.Build_T bc t0 h0 hs) n.

Lemma TC_state_upd_spec x n:
  TC_state_WF x n ->
  match TC_state.upd tm x with
  | inl x' =>
    exists n', TC_state_WF x' n' /\ n'<=S n
  | inr (x',h) => halts_at tm c0 n h
  end.
Proof.
  destruct x as [bc t0 h0 hs]; cbn; intros.
  inverts H.
  destruct_spec (BoundedConfig_step_spec); trivial.
  - destruct p as [x' h].
    exists (S n).
    split. 2: lia.
    econstructor.
    replace (S n) with (n+1) by lia.
    eapply multistep_trans; eauto.
  - destruct bc as [l r s sgn].
    destruct r as [|m r].
    + exists n.
      split. 2: lia.
      econstructor.
      apply H5.
    + cbn in H.
      destruct H as [H|H]; try congruence.
      destruct sgn; econstructor; eauto; apply H.
Qed.

Lemma TC_state_upds_spec x n m:
  TC_state_WF x n ->
  match TC_state.upds tm x m with
  | inl x' =>
    exists n', TC_state_WF x' n' /\ n'<=n+(N.to_nat m)
  | inr (x',h) =>
    exists n', halts_at tm c0 n' h /\ n'<=n+(N.to_nat m)
  end.
Proof.
  intros H.
  unfold TC_state.upds.
  rewrite N_iter_until_spec'.
  induction m using N.peano_ind.
  - cbn.
    exists n.
    split; auto; lia.
  - rewrite N.iter_succ.
    destruct (N.iter m (f_if_inl (TC_state.upd tm)) (inl x)) eqn:E.
    + destruct IHm as [n' [Hm1 Hm2]].
      cbn.
      destruct_spec TC_state_upd_spec.
      * specialize (H0 _ Hm1).
        destruct H0 as [n'0 [Hm3 Hm4]].
        exists n'0.
        split; auto; lia.
      * destruct p as [x0 h].
        eexists; split; eauto; lia.
    + cbn.
      destruct p as [x0 h].
      destruct IHm as [n' [Hm1 Hm2]].
      eexists; split; eauto; lia.
Qed.

Fixpoint N_list_sum (ls:list N):N :=
match ls with
| nil => N0
| h::t => (h+(N_list_sum t))%N
end.

Lemma repeat_s0_const_s0 n:
  repeat s0 n *> const s0 = const s0.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  rewrite <-const_unfold.
  reflexivity.
Qed.


Lemma TC_state_check_TC_spec t n:
  TC_state_WF t n ->
  if TC_state.check_TC tm t then ~halts tm c0 else True.
Proof.
  intros H.
  inverts H.
  unfold TC_state.check_TC.
  cbn[TC_state.hs].
  cbn[TC_state.bc].
  destruct (TC_state.check_TC_2 hs) as [[p d]|]; trivial.
  destruct (snd (BoundedConfig.steps' tm bc (to_N (p)))) as [[[ld1 rd1] _] _].
  destruct bc as [l r s sgn].
  destruct hs as [|[[_ sgn0] _]]; trivial.
  destruct (eqb sgn sgn0).
  - destruct_spec (BoundedConfig_progress_spec); trivial.
    destruct t as [l2 r2 s2 sgn2].
    destruct (eqb_spec s2 s); trivial.
    destruct (eqb_spec sgn2 sgn); trivial.
    destruct (eqb_spec r2 r); trivial.
    remember (firstn ld1 l) as l1.
    remember (skipn (length l1) l2) as l3.
    destruct (eqb_spec l2 (l1++l3)); trivial.
    subst s2 sgn2 r2.
    cbn in H0,H.
    rewrite e2 in H.
    destruct sgn.
    + eapply multistep_nonhalt.
      1: eapply without_counter,H0.
      rewrite <-(firstn_skipn ld1 l).
      rewrite <-Heql1.
      repeat rewrite Str_app_assoc.
      eapply progress_nonhalt_simple with (C:=fun t => const s0 <* r <{{s}} l1 *> t).
      intros t.
      eexists.
      specialize (H (const s0) t).
      repeat rewrite Str_app_assoc in H.
      rewrite repeat_s0_const_s0 in H.
      apply H.
    + eapply multistep_nonhalt.
      1: eapply without_counter,H0.
      rewrite <-(firstn_skipn ld1 l).
      rewrite <-Heql1.
      repeat rewrite Str_app_assoc.
      eapply progress_nonhalt_simple with (C:=fun t => t <* l1 {{s}}> r *> const s0).
      intros t.
      eexists.
      specialize (H t (const s0)).
      repeat rewrite Str_app_assoc in H.
      rewrite repeat_s0_const_s0 in H.
      apply H.
  - destruct_spec (BoundedConfig_progress_spec); trivial.
    destruct t as [l2 r2 s2 sgn2].
    destruct (eqb_spec s2 s); trivial.
    destruct (eqb_spec sgn2 sgn); trivial.
    destruct (eqb_spec l2 l); trivial.
    remember (firstn rd1 r) as r1.
    remember (skipn (length r1) r2) as r3.
    destruct (eqb_spec r2 (r1++r3)); trivial.
    subst s2 sgn2 l2.
    cbn in H0,H.
    rewrite e2 in H.
    destruct sgn.
    + eapply multistep_nonhalt.
      1: eapply without_counter,H0.
      rewrite <-(firstn_skipn rd1 r).
      rewrite <-Heqr1.
      repeat rewrite Str_app_assoc.
      eapply progress_nonhalt_simple with (C:=fun t => t <* r1 <{{s}} l *> const s0).
      intros t.
      eexists.
      specialize (H t (const s0)).
      repeat rewrite Str_app_assoc in H.
      rewrite repeat_s0_const_s0 in H.
      apply H.
    + eapply multistep_nonhalt.
      1: eapply without_counter,H0.
      rewrite <-(firstn_skipn rd1 r).
      rewrite <-Heqr1.
      repeat rewrite Str_app_assoc.
      eapply progress_nonhalt_simple with (C:=fun t => const s0 <* l {{s}}> r1 *> t).
      intros t.
      eexists.
      specialize (H (const s0) t).
      repeat rewrite Str_app_assoc in H.
      rewrite repeat_s0_const_s0 in H.
      apply H.
Qed.

Lemma TC_state_decide_0_spec x n ls:
  TC_state_WF x n ->
  match (TC_state.decide_0 tm ls x) with
  | (Halt h,_) => exists n', halts_at tm c0 n' h /\ n'<=n+(N.to_nat (N_list_sum ls))
  | (NonHalt,_) => ~halts tm c0
  | (Unknown,x') => exists n', TC_state_WF x' n' /\ n'<=n+(N.to_nat (N_list_sum ls))
  end.
Proof.
  gen x n.
  induction ls; intros.
  1: cbn; exists n; split; auto; lia.
  cbn.
  pose proof (TC_state_upds_spec x _ a H).
  destruct (TC_state.upds tm x a).
  - destruct_spec (TC_state_check_TC_spec).
    + destruct H0 as [n' [Hm1 Hm2]]. 
      eauto.
    + destruct H0 as [n' [Hm1 Hm2]].
      specialize (IHls _ _ Hm1).
      destruct_spec TC_state.decide_0.
      destruct d.
      * destruct IHls as [n'0 [Hm3 Hm4]].
        exists n'0.
        split; auto; lia.
      * apply IHls.
      * destruct IHls as [n'0 [Hm3 Hm4]].
        exists n'0.
        split; auto; lia.
  - destruct p as [x' h].
    destruct H0 as [n' [Hm1 Hm2]].
    exists n'.
    split; auto; lia.
Qed.


Lemma BoundedConfig_step_d_spec x d:
match BoundedConfig.step_d tm (x,d) with
| Some (x',d') =>
    forall l r,
    (BoundedConfig.to_config x l r) -[ tm ]-> (BoundedConfig.to_config x' l r)
| None => True
end.
Proof.
  destruct x as [l [|m r] s sgn]; cbn; trivial.
  destruct (tm (s,m)) as [[[m' sgn'] s']|] eqn:E; trivial.
  destruct sgn,sgn'; cbn; intros; constructor; apply E.
Qed.

Lemma find_cycle_0_spec x0 x1 d n:
if BoundedConfig.find_cycle_0 tm x0 (x1,d) n then
  (forall l r,
  (BoundedConfig.to_config x0 l r) -[ tm ]->* (BoundedConfig.to_config x1 l r)) ->
  forall l r,
  ~halts tm (BoundedConfig.to_config x0 l r)
else True.
Proof.
  Import BoundedConfig.
  gen x1 d.
  induction n; intros.
  1: cbn; trivial.
  cbn[BoundedConfig.find_cycle_0].
  pose proof (BoundedConfig_step_d_spec x1 d).
  destruct (BoundedConfig.step_d tm (x1, d)); trivial.
  destruct p as [x2a x2b].
  destruct (eqb x2b uint_0 && eqb x0 x2a)%bool eqn:E.
  - destruct (eqb_spec x2b uint_0).
    2: cbn in E; congruence.
    destruct (eqb_spec x0 x2a).
    2: congruence.
    intros H0 l r.
    eapply progress_nonhalt_simple with (C:=fun _:unit=>(to_config x0 l r)).
    1: apply tt.
    intros _.
    exists tt.
    subst x2a.
    eapply evstep_progress_trans; eauto.
  - specialize (IHn x2a x2b).
    destruct_spec find_cycle_0; trivial.
    intros H1.
    apply IHn.
    intros l r.
    eapply progress_evstep.
    eapply evstep_progress_trans; eauto.
Qed.

Lemma find_cycle_spec x0 n:
if BoundedConfig.find_cycle tm x0 n then
  forall l r,
  ~halts tm (BoundedConfig.to_config x0 l r)
else True.
Proof.
  unfold find_cycle.
  pose proof (find_cycle_0_spec x0 x0 uint_0 n) as H.
  destruct (find_cycle_0 tm x0 (x0, uint_0) n); trivial.
  intros.
  apply H.
  intros.
  auto.
Qed.

Lemma TC_state_decide_1_spec x n ls:
  TC_state_WF x n ->
  match (TC_state.decide_1 tm ls x) with
  | (Halt h,_) => exists n', halts_at tm c0 n' h /\ n'<=n+(N.to_nat (N_list_sum (map N_list_sum (map fst ls))))
  | (NonHalt,_) => ~halts tm c0
  | (Unknown,x') => exists n', TC_state_WF x' n' /\ n'<=n+(N.to_nat (N_list_sum (map N_list_sum (map fst ls))))
  end.
Proof.
  gen x n.
  induction ls; intros.
  1: cbn; exists n; split; auto; lia.
  cbn.
  destruct a as [n0 n1].
  pose proof (TC_state_decide_0_spec x _ n0 H).
  destruct (TC_state.decide_0 tm n0 x).
  - cbn[fst].
    destruct d.
    + destruct H0 as [n' [Hm1 Hm2]]. 
      exists n'.
      split; auto; lia.
    + apply H0.
    + destruct_spec (find_cycle_spec).
      * eapply multistep_nonhalt.
        2: apply (H1 (const s0) (const s0)).
        destruct H0 as [n' [Hm1 Hm2]]. 
        inverts Hm1.
        eapply without_counter; eauto.
      * destruct H0 as [n' [Hm1 Hm2]]. 
        specialize (IHls _ _ Hm1).
        destruct_spec TC_state.decide_1.
        destruct d.
        -- destruct IHls as [n'0 [Hm3 Hm4]].
           exists n'0. split; auto; lia.
        -- apply IHls.
        -- destruct IHls as [n'0 [Hm3 Hm4]].
           exists n'0. split; auto; lia.
Qed.

Lemma TC_state_decide_spec ls:
  match (TC_state.decide tm ls) with
  | (Halt h,_) => exists n', halts_at tm c0 n' h /\ n'<=(N.to_nat (N_list_sum (map N_list_sum (map fst ls))))
  | (NonHalt,_) => ~halts tm c0
  | (Unknown,x') => exists n', TC_state_WF x' n' /\ n'<=(N.to_nat (N_list_sum (map N_list_sum (map fst ls))))
  end.
Proof.
  unfold TC_state.decide.
  apply (TC_state_decide_1_spec TC_state.T0 O ls).
  constructor; auto.
Qed.

Definition decide_TC ls :=
  match (TC_state.decide tm ls) with
  | (NonHalt,_) => true
  | _ => false
  end.

Lemma decide_TC_spec ls:
  decide_TC ls = true ->
  ~halts tm c0.
Proof.
  unfold decide_TC.
  pose proof (TC_state_decide_spec ls).
  destruct (TC_state.decide tm ls).
  destruct d; try congruence.
Qed.

End tm_ctx.

End TC.


