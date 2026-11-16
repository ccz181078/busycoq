Require Import PeanoNat ZArith List.
Require Import Lia.
From BusyCoq Require Import TM.
From BusyCoq Require Export BigUint.
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
Module TM := TM Ctx.
Export TM.


Lemma evstep_halts_at_trans tm c1 c2 tr:
  c1 -[ tm ]->* c2 ->
  halts_at_trans tm c2 tr ->
  halts_at_trans tm c1 tr.
Proof.
  intros Hev Hh.
  destruct Hh as [n Hh].
  destruct Hh.
  epose proof (with_counter Hev) as [n1 Hev'].
  eexists.
  econstructor; eauto.
  eapply multistep_trans; eauto.
Qed.

Module BoundedConfig.
Record T := {
  l: list Sym;
  r: list Sym;
  s: Q;
  sgn: dir;
}.

Definition to_config (x:T) (l0 r0:side) :=
let (l,r,s,sgn):=x in
match sgn with
| L => l0 <* r <{{s}} l *> r0
| R => l0 <* l {{s}}> r *> r0
end.

Section tm_ctx.
Hypothesis tm:TM.

Definition step(x:T):option T :=
let (l,r,s,sgn):=x in
match r with
| nil => None
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (Build_T (m'::l) r0 s' sgn')
    else
      Some (Build_T (m'::r0) l s' sgn')
  end
end.

Fixpoint steps(n:nat)(x:T) :=
match step x with
| None => Some x
| Some x =>
  match n with
  | O => None
  | S n => steps n x
  end
end.

Definition check_halt(x:T):option (Q*Sym) :=
let (l,r,s,sgn):=x in
match r with
| nil => None
| m::_ =>
  match tm (s,m) with
  | None => Some (s,m)
  | _ => None
  end
end.

Definition progress_or_halt n x :=
match step x with
| None =>
  check_halt x &&& (fun v => Some (inr v))
| Some x' =>
  steps n x' &&& (fun y =>
  match check_halt y with
  | None => Some (inl y)
  | Some v => Some (inr v)
  end)
end.

Lemma step_spec x:
match step x with
| Some x' =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->
  to_config x' l0 r0
| None =>
  True
end.
Proof.
  destruct x as [l1 r1 s1 sgn1].
  unfold step.
  destruct r1 as [|m r1]; cbn; trivial.
  destruct (tm (s1,m)) as [[[m2 sgn2] s2]|] eqn:E; trivial.
    destruct sgn1,sgn2; cbn;
    econstructor; eauto.
Qed.

Lemma steps_spec n x:
match steps n x with
| None => True
| Some (x') =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->*
  to_config x' l0 r0
end.
Proof.
  gen x.
  induction n; intros.
  - unfold steps.
    destruct_spec (step_spec); trivial.
  - cbn[steps].
    destruct_spec (step_spec); trivial.
    specialize (IHn t).
    destruct_spec steps; trivial.
    eauto.
Qed.

Lemma check_halt_spec x:
match check_halt x with
| None => True
| Some v => forall l0 r0, halts_at_trans tm (to_config x l0 r0) v
end.
Proof.
  destruct x as [l1 r1 s1 sgn1].
  destruct r1 as [|m r1]; cbn; trivial.
  destruct (tm (s1,m)) eqn:E; trivial.
  destruct sgn1; intros.
  all: exists O; econstructor; eauto.
Qed.

Lemma progress_or_halt_spec n x:
match progress_or_halt n x with
| None => True
| Some (inl x') =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->+
  to_config x' l0 r0
| Some (inr tr) =>
  forall l0 r0,
  halts_at_trans tm (to_config x l0 r0) tr
end.
Proof.
  unfold progress_or_halt,if_Some.
  destruct_spec step_spec.
  - destruct_spec steps_spec; trivial.
    destruct_spec check_halt_spec.
    + intros.
      eapply evstep_halts_at_trans.
      2: apply H1.
      eauto.
    + intros.
      eapply progress_evstep_trans; eauto.
  - destruct_spec check_halt_spec; trivial.
Qed.

End tm_ctx.

End BoundedConfig.


Section bsz.
Hypothesis tm:TM.
Hypothesis bsz:nat.
Hypothesis bmaxT:nat.
Hypothesis use_acc:bool.
Hypothesis mnc:N'.
Definition RW:Type := (list Sym)*(N'*N')*N'.
Definition RWL:Type := list RW.
Definition RWL_config:Type := RWL*RWL*Q*dir.

Definition pop(ls:RWL):option ((list Sym)*RWL) :=
match ls with
| [] => Some (repeat s0 bsz,[])
| (w,a,b)::t =>
  match pred b with
  | Some b' =>
  match b' with
  | N0 =>
    match a with
    | (N0,N0) => Some (w,t)
    | _ => None
    end
  | _ => Some (w,(w,a,b')::t)
  end
  | _ => None
  end
end.

Definition push(w:list Sym)(ls:RWL):RWL :=
match ls with
| [] => (w,(N0,N0),N1)%N::nil
| (w',a,b)::t =>
  if eqb w w' then
    (w,a,succ b)::t
  else
    (w,(N0,N0),N1)::ls
end.

Definition push'(x:RW)(ls:RWL):RWL :=
let '(w,(a0,a1),b):=x in
match ls with
| (w',(a0',a1'),b')::t =>
  if eqb w w' then
    (w',(a0+a0',a1+a1'),b+b')%N'::t
  else x::ls
| _ => x::ls
end.

Fixpoint match_side_0(ls1 ls2:RWL):option RWL :=
match ls1,ls2 with
| (w1,(N0,N0),b1)::t1,(w2,(N0,N0),b2)::t2 =>
  if (eqb w1 w2) then
    match_side_0 t1 t2 &&& (fun t0 =>
      match subge b2 b1 with
      | Some b21 =>
        Some ((w1,(b21,N0),b2)::t0)
      | None =>
        Some ((w1,(N0,b1-b2),b2)::t0)
      end
    )%N'
  else None
| nil,nil => Some nil
| _,_ => None
end.

Definition oNmin(a b:option N'):option N' :=
match a,b with
| Some a0,Some b0 => Some (min a0 b0)
| Some a0,None => a
| None,_ => b
end.

Fixpoint get_loop_cnt(ls:RWL):option (option N') :=
match ls with
| (w1,(a0,a1),b1)::t =>
  get_loop_cnt t &&& (fun n0 =>
    match a1 with
    | N0 => Some n0
    | _ =>
      (match subge b1 mnc with
       | Some v =>
         match div_small v a1 with
         | Some v0 => Some (oNmin (Some v0) n0)
         | _ => None
         end
       | _ => None
       end)%N'
    end
  )
| nil => Some None
end.

Definition RW_subst_Si:RW->RW :=
  (fun '(w,(a0,a1),b) => (w,(a0,a1),a0+b)%N').

Definition RW_subst_Sj:RW->RW :=
  (fun '(w,(a0,a1),b) => (w,(a0,a1),a1+b)%N').

Definition RW_subst_i0:RW->RW :=
  (fun '(w,(a0,a1),b) => (w,(N0,a1),b)%N').

Definition RW_subst_c(x0 x1:N'):RW->RW :=
  (fun '(w,(a0,a1),b) => (w,(N0,N0),a0*x0+a1*x1+b)%N').

Definition RW_set_loop_cnt(n:option N'):RW->RW :=
fun x =>
let '(w,(a0,a1),b):=x in 
match n with
| None => x
| Some n0 =>
  (w,(a0,a1),b-a1*n0)%N'
end.

Definition config_subst(f:RW->RW)(c:RWL_config) :=
let '(l,r,s,sgn):=c in
(map f l,map f r,s,sgn).

Definition match_config(c1 c2:RWL_config):option (RWL_config*(option N')) :=
let '(l1,r1,s1,sgn1):=c1 in
let '(l2,r2,s2,sgn2):=c2 in
if (eqb s1 s2) && (eqb sgn1 sgn2) then
  match_side_0 l1 l2 &&& (fun l0 =>
  match_side_0 r1 r2 &&& (fun r0 =>
  get_loop_cnt l0 &&& (fun cl =>
  get_loop_cnt r0 &&& (fun cr =>
  let n := (oNmin cl cr) in
  Some (config_subst (RW_set_loop_cnt n) (l0,r0,s1,sgn1),n)
  ))))
else None.

Definition RWL_step(c:RWL_config):option (RWL_config+Q*Sym) :=
let '(l,r,s,sgn):=c in
pop l &&& (fun '(l0,l1) =>
pop r &&& (fun '(r0,r1) =>
BoundedConfig.progress_or_halt tm bmaxT (BoundedConfig.Build_T l0 r0 s sgn) &&& (fun y =>
match y with
| inl (BoundedConfig.Build_T l0' r0' s' sgn') =>
  match r0' with
  | nil =>
  let l0a := firstn bsz l0' in
  let l0b := skipn bsz l0' in
  if eqb sgn sgn' then
  if eqb s s' && eqb l0 l0a then
  match r with
  | nil =>
    Some (inl (push l0a (push l0b l1),r1,s',sgn'))
  | (w,a,b)::t =>
    if eqb r0 w then
    if is0 b then None
    else Some (inl (push l0a (push' (l0b,a,b) l1),t,s',sgn'))
    else None
  end
  else Some (inl (push l0a (push l0b l1),r1,s',sgn'))
  else Some (inl (push l0a (push l0b r1),l1,s',sgn'))
  | _ => None
  end
| inr tr => Some (inr tr)
end
))).

Definition RWL_step''(c:RWL_config*bool):RWL_config*bool+(option (Q*Sym)) :=
let (c,_):=c in
match RWL_step c with
| None => inr None
| Some (inl c') => inl (c',true)
| Some (inr tr) => inr (Some tr)
end.

Definition config_subst_Si(c:RWL_config):RWL_config :=
config_subst RW_subst_Si c.

Definition config_subst_Sj(c:RWL_config):RWL_config :=
config_subst RW_subst_Sj c.

Definition config_subst_i0(c:RWL_config):RWL_config :=
config_subst RW_subst_i0 c.

Definition config_subst_c(x0 x1:N')(c:RWL_config):RWL_config :=
config_subst (RW_subst_c x0 x1) c.

Instance BigUint_eqb:
  Eqb BigUint.
Proof.
  esplit.
  apply BigUint.eqb_spec.
Defined.

Definition check_loop c1 c2 n :=
if use_acc then
match match_config c1 c2 with
| None => None
| Some (c3,k) =>
  match k with
  | None =>
    match N_iter_until RWL_step'' (inl (c3,false)) n with
    | inl (c4,true) =>
      if eqb (config_subst_Si c3) c4 then
        if eqb (config_subst_i0 c3) c2 then Some None else None
      else None
    | _ => None
    end
  | Some k0 =>
    let c3' := config_subst_Sj c3 in
    match N_iter_until RWL_step'' (inl (c3',false)) n with
    | inl (c4,true) =>
      if eqb (config_subst_Si c3) c4 then
        if eqb (config_subst_c N0 k0 c3) c2 then Some (Some (config_subst_c k0 N0 c3)) else None
      else None
    | _ => None
    end
  end
end
else None.

Definition RWL_state:Type := RWL_config*RWL_config*BinNums.N*BinNums.N.
Definition RWL_step'(x:RWL_state):RWL_state+_ :=
let '(c1,c,n,n0):=x in
match RWL_step c with
| None => inr Unknown
| Some (inl c') =>
  if (N.ltb n n0) then
    match check_loop c1 c' (N.succ n) with
    | Some (Some c'') => inl (c'',c'',0,1)%N
    | Some None => inr NonHalt
    | None => inl (c1,c',N.succ n,n0)
    end
  else
    inl (c',c',0,n0*2)%N
| Some (inr tr) => inr (Halt tr)
end.

Definition RWL_state_0:RWL_state := ((([],[],q0,R),([],[],q0,R),0,1)%N).

Definition RWL_steps T :=
N_iter_until RWL_step' (inl RWL_state_0) T.

Section subst_i.
Hypothesis i j:nat.

Definition to_seg(x:RW) :=
let '(w,(a0,a1),b):=x in
w ^^ ((to_nat a0)*i+(to_nat a1)*j+(to_nat b)).

Definition to_side(ls:RWL) := (flat_map to_seg ls) *> Streams.const s0.

Definition to_config(c:RWL_config):Q*tape :=
let '(l,r,s,sgn):=c in
match sgn with
| L => to_side r <{{s}} to_side l
| R => to_side l {{s}}> to_side r
end.

Lemma lpow_add_Str_app{T}(x:list T)(n1 n2:nat) r:
  x^^n1 *> x^^n2 *> r =
  x^^(n1+n2) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lpow_S_Str_app{T}(x:list T) n r:
  x *> x^^n *> r =
  x^^(S n) *> r.
Proof.
  cbn.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

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
      destruct a' as [a0 a1].
      subst.
      rewrite lpow_S_Str_app.
      rw_N'.
      repeat (lia || f_equal).
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
  destruct x as [[w [a0 a1]] b].
  destruct ls as [|[[w' [a0' a1']] b'] t].
  - cbn.
    rewrite Str_app_assoc.
    reflexivity.
  - cbn - [eqb].
    destruct (eqb_spec w w').
    + cbn.
      repeat rewrite Str_app_assoc.
      subst.
      rewrite lpow_add_Str_app.
      rw_N'.
      repeat (lia || f_equal).
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
  destruct ls as [|[[w [a0 a1]] b] t].
  - cbn.
    induction bsz.
    1: reflexivity.
    cbn. rewrite <-IHn,<-const_unfold.
    reflexivity.
  - cbn.
    epose proof (inj_pred b).
    destruct (pred b) as [b'|]; trivial.
    destruct b' as [|b'0 b'1].
    + cbn.
      repeat rewrite Str_app_assoc.
      rewrite H.
      change (to_nat N0) with O.
      destruct a0 as [|a0]; trivial.
      destruct a1 as [|a1]; trivial.
      cbn.
      rewrite Str_app_assoc.
      reflexivity.
    + cbn.
      repeat rewrite Str_app_assoc.
      rewrite lpow_S_Str_app.
      repeat (lia || f_equal).
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
| Some (inl c') => (to_config c) -[ tm ]->+ (to_config c')
| Some (inr tr) => halts_at_trans tm (to_config c) tr
end.
Proof.
  destruct c as [[[l r] s] sgn].
  unfold RWL_step.
  unfold if_Some.
  destruct_spec pop_spec; trivial.
  destruct p as [l0 l1].
  destruct_spec pop_spec; trivial.
  destruct p as [r0 r1].
  destruct_spec BoundedConfig.progress_or_halt_spec; trivial.
  destruct s2.
  2: {
    cbn in H1.
    destruct sgn; cbn;
    rewrite H,H0;
    apply H1.
  }
  destruct t as [l0' r0' s' sgn'].
  pose proof H1 as H2.
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
      destruct r as [|[[w [a0 a1]] b] r]; [shelve |];
      destruct (eqb_spec r0 w); trivial;
      rewrite <-H0;
      destruct (inj_is0 b); trivial;
      rewrite to_side_def;
      rewrite push_spec;
      rewrite push'_spec;
      unfold to_seg;
      remember (to_nat a0 * i + to_nat a1 * j + to_nat b) as v1;
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
          rewrite <-(Str_app_assoc l0b);
          rewrite <-lpow_shift;
          rewrite Str_app_assoc;
          reflexivity ] ] ).
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
| Some (inl c') => forall i j, (to_config i j c) -[ tm ]->+ (to_config i j c')
| Some (inr tr) => forall i j, halts_at_trans tm (to_config i j c) tr
end.
Proof.
  destruct (RWL_step c) eqn:E; trivial.
  destruct s; intros i j;
  pose proof (RWL_step_spec i j c) as H;
  rewrite E in H;
  apply H.
Qed.

Ltac solve_side_subst ls :=
  induction ls as [|a ls IHls];
  [ reflexivity |
  cbn;
  repeat rewrite Str_app_assoc;
  rewrite IHls;
  f_equal;
  destruct a as [[w [a0 a1]] b];
  cbn;
  rw_N';
  f_equal; lia ].

Lemma side_subst_Si_spec i j ls:
  to_side i j (map RW_subst_Si ls) = to_side (S i) j ls.
Proof.
  unfold to_side,RW_subst_Si.
  solve_side_subst ls.
Qed.

Lemma side_subst_Sj_spec i j ls:
  to_side i j (map RW_subst_Sj ls) = to_side i (S j) ls.
Proof.
  unfold to_side,RW_subst_Sj.
  solve_side_subst ls.
Qed.

Lemma side_subst_i0_spec i j ls:
  to_side i j (map RW_subst_i0 ls) = to_side O j ls.
Proof.
  unfold to_side,RW_subst_i0.
  solve_side_subst ls.
Qed.

Lemma side_subst_c_spec i j ls x0 x1:
  to_side i j (map (RW_subst_c x0 x1) ls) = to_side (to_nat x0) (to_nat x1) ls.
Proof.
  unfold to_side,RW_subst_c.
  solve_side_subst ls.
Qed.

Lemma config_subst_Si_spec i j c:
  to_config i j (config_subst_Si c) = to_config (S i) j c.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  repeat rewrite side_subst_Si_spec.
  reflexivity.
Qed.

Lemma config_subst_Sj_spec i j c:
  to_config i j (config_subst_Sj c) = to_config i (S j) c.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  repeat rewrite side_subst_Sj_spec.
  reflexivity.
Qed.

Lemma config_subst_i0_spec i j c:
  to_config i j (config_subst_i0 c) = to_config O j c.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  repeat rewrite side_subst_i0_spec.
  reflexivity.
Qed.

Lemma config_subst_c_spec i j c x0 x1:
  to_config i j ((config_subst_c x0 x1) c) = to_config (to_nat x0) (to_nat x1) c.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  repeat rewrite side_subst_c_spec.
  reflexivity.
Qed.

Lemma nonhalt_cond c j0:
  c0 -[ tm ]->* (to_config 0 j0 c) ->
  (forall i j, to_config i j c -[ tm ]->+ to_config (S i) j c) ->
  ~halts tm c0.
Proof.
  intros.
  eapply multistep_nonhalt.
  1: apply H.
  eapply progress_nonhalt with (P:=fun c' => exists i, c' = to_config i j0 c).
  2: eexists; reflexivity.
  intros c1 [i Hc1].
  subst c1.
  eexists _.
  split.
  2: apply (H0 i).
  eexists; reflexivity.
Qed.

Lemma acc_cond c:
  (forall i j, to_config i (S j) c -[ tm ]->+ to_config (S i) j c) ->
  (forall i j, to_config i j c -[ tm ]->* to_config (j+i) O c).
Proof.
  intros.
  gen i.
  induction j; intros.
  1: constructor.
  eapply evstep_trans.
  1: apply progress_evstep,H.
  applys_eq (IHj (S i)).
  f_equal; lia.
Qed.

Lemma RWL_step''_spec c n:
match N_iter_until RWL_step'' (inl (c,false)) n with
| inl (c',flag) =>
  if flag then
    (forall i j, to_config i j c -[ tm ]->+ to_config i j c')
  else c=c'
| inr (Some tr) =>
    (forall i j, halts_at_trans tm (to_config i j c) tr)
| inr _ => True
end.
Proof.
  eapply N_iter_until_spec.
  2: reflexivity.
  intros [c1 flag1] H.
  unfold RWL_step''.
  destruct flag1.
  - destruct_spec (RWL_step_spec'); trivial.
    destruct s;
    intros i j.
    + eapply progress_trans; eauto.
    + eapply evstep_halts_at_trans.
      2: apply H0.
      eapply progress_evstep; eauto.
  - destruct_spec (RWL_step_spec'); trivial.
    subst c1.
    destruct s; eauto.
Qed.

Lemma check_loop_spec c1 c2 n:
  match check_loop c1 c2 n with
  | None => True
  | Some None =>
    c0 -[ tm ]->* to_config 0 0 c2 ->
    ~halts tm c0
  | Some (Some c') =>
    c0 -[ tm ]->* to_config 0 0 c2 ->
    c0 -[ tm ]->* to_config 0 0 c'
  end.
Proof.
  unfold check_loop.
  destruct use_acc; trivial.
  destruct (match_config c1 c2) as [[c3 k]|]; trivial.
  destruct k as [k0|].
  - remember (config_subst_Sj c3) as c4.
    pose proof (RWL_step''_spec c4 n) as Hc4.
    destruct (N_iter_until RWL_step'' (inl (c4, false)) n) as [[c5 [|]]|]; trivial.
    destruct (eqb_spec (config_subst_Si c3) c5); trivial.
    destruct (eqb_spec (config_subst_c N0 k0 c3) c2); trivial.
    intros Hc2.
    eapply evstep_trans.
    1: apply Hc2.
    subst c2 c4 c5.
    eassert (H:_). {
      eapply acc_cond with (i:=O) (j:=(to_nat k0)).
      intros i j.
      specialize (Hc4 i j).
      rewrite config_subst_Si_spec in Hc4.
      rewrite config_subst_Sj_spec in Hc4.
      apply Hc4.
    }
    do 2 rewrite config_subst_c_spec.
    applys_eq H.
    repeat (lia || f_equal).
  - pose proof (RWL_step''_spec c3 n) as Hc4.
    destruct (N_iter_until RWL_step'' (inl (c3, false)) n) as [[c4 [|]]|]; trivial.
    destruct (eqb_spec (config_subst_Si c3) c4); trivial.
    destruct (eqb_spec (config_subst_i0 c3) c2); trivial.
    intros Hc2.
    rewrite <-e in Hc4.
    eapply (nonhalt_cond c3).
    2: intros i j; applys_eq Hc4.
    2: rewrite config_subst_Si_spec; reflexivity.
    epose proof (config_subst_i0_spec _ _ _) as H.
    rewrite e0 in H.
    rewrite <-H.
    apply Hc2.
Qed.

Definition RWL_state_WF(x:RWL_state) :=
let '(c1,c2,_,_) := x in
  c0 -[ tm ]->* to_config 0 0 c1 /\
  c0 -[ tm ]->* to_config 0 0 c2.

Lemma RWL_step'_spec x0 T:
RWL_state_WF x0 ->
match N_iter_until RWL_step' (inl x0) T with
| inr Unknown => True
| inr NonHalt => ~halts tm c0
| inr (Halt tr) => halts_at_trans tm c0 tr
| inl x1 => RWL_state_WF x1
end.
Proof.
  intros Hx0.
  eapply N_iter_until_spec.
  2: apply Hx0.
  intros [[[c1 c2] n1] n2].
  unfold RWL_step'.
  intros [Hc1 Hc2].
  destruct_spec (RWL_step_spec O O); trivial.
  destruct s.
  2: eapply evstep_halts_at_trans; eauto.
  destruct (n1 <? n2)%N.
  2: cbn; split;
    apply progress_evstep; eapply evstep_progress_trans; eauto.
  destruct_spec check_loop_spec.
  - destruct o.
    + unfold RWL_state_WF.
      refine (let x:=_ in conj x x).
      eapply H0.
      eapply evstep_trans; eauto.
      eapply progress_evstep; eauto.
    + apply H0.
      eapply evstep_trans; eauto.
      eapply progress_evstep; eauto.
  - unfold RWL_state_WF.
    split. 1: tauto.
    eapply evstep_trans; eauto.
    eapply progress_evstep; eauto.
Qed.

Lemma RWL_state_0_WF:
RWL_state_WF RWL_state_0.
Proof.
  cbn; split; constructor.
Qed.

Definition decide_nonhalt T :=
match RWL_steps T with
| inr NonHalt => true
| _ => false
end.

Definition decide_halt T :=
match RWL_steps T with
| inr (Halt tr) => Some tr
| _ => None
end.

Lemma decide_nonhalt_spec T:
  decide_nonhalt T = true ->
  ~halts tm c0.
Proof.
  unfold decide_nonhalt,RWL_steps.
  pose proof (RWL_step'_spec RWL_state_0 T RWL_state_0_WF) as H0.
  destruct (N_iter_until RWL_step' (inl RWL_state_0) T).
  1: congruence.
  destruct d; try congruence.
Qed.

Lemma decide_halt_spec T tr:
  decide_halt T = Some tr ->
  halts_at_trans tm c0 tr.
Proof.
  unfold decide_halt,RWL_steps.
  pose proof (RWL_step'_spec RWL_state_0 T RWL_state_0_WF) as H0.
  destruct (N_iter_until RWL_step' (inl RWL_state_0) T).
  1: congruence.
  destruct d; try congruence.
Qed.

End bsz.

End RWLAcc.



