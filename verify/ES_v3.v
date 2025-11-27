Require Import ZArith Lia String List.
From BusyCoq Require Import RWLAcc62 Individual62 Eqb.

Definition multistep' tm (p:bool) s0 s1 :=
if p then s0-[tm]->+s1 else s0-[tm]->*s1.

Lemma multistep'_trans tm b1 b2 b3 c1 c2 c3:
  orb (negb b3) (orb b1 b2) = true ->
  multistep' tm b1 c1 c2 ->
  multistep' tm b2 c2 c3 ->
  multistep' tm b3 c1 c3.
Proof.
  destruct b1,b2,b3; cbn; intros; try congruence.
  - eapply progress_trans; eauto.
  - eapply progress_evstep,progress_trans; eauto.
  - eapply progress_evstep_trans; eauto.
  - eapply progress_evstep,progress_evstep_trans; eauto.
  - eapply evstep_progress_trans; eauto.
  - eapply progress_evstep,evstep_progress_trans; eauto.
  - eapply evstep_trans; eauto.
Qed.


Inductive vside :=
| vside_cons(h:sym)(t:vside)
| vside_app(h:list sym)(n:string)(t:vside)
| vside_0inf
| vside_var(i:string)
.

Inductive vconfig :=
| vconfig_L(l r:vside)(q:Q)
| vconfig_R(l r:vside)(q:Q)
| vconfig_mid(l r:vside)(m:sym)(q:Q)
.

Definition rw_vconfig_LR(x:vconfig):vconfig :=
match x with
| vconfig_L (vside_cons m l) r q => vconfig_mid l r m q
| vconfig_L (vside_0inf) r q => vconfig_mid vside_0inf r s0 q
| vconfig_R l (vside_cons m r) q => vconfig_mid l r m q
| vconfig_R l (vside_0inf) q => vconfig_mid l vside_0inf s0 q
| _ => x
end.

Fixpoint vside_rw_lpow_rotate_all0(x x0:list sym)(n:string):vside :=
match x with
| h::t =>
  if eqb h s0 then
    vside_cons h (vside_rw_lpow_rotate_all0 t (h::x0) n)
  else
    vside_app (x++rev x0) n vside_0inf
| _ =>
    vside_app (x++rev x0) n vside_0inf
end.

Fixpoint is_all0(x:list sym):bool :=
match x with
| [] => true
| h::t =>
  if eqb h s0 then is_all0 t else false
end.

Fixpoint vside_rw_lpow_rotate'(h:list sym)(n:string)(x:vside):vside :=
match h with
| [] => vside_app h n x
| h0::h1 =>
  match x with
  | vside_cons h' t =>
    if eqb h0 h' then
      vside_cons h0 (vside_rw_lpow_rotate' (h1++[h0]) n t)
    else
      vside_app h n x
  | vside_0inf =>
      if is_all0 h
      then vside_0inf
      else vside_rw_lpow_rotate_all0 h [] n
  | _ => vside_app h n x
  end
end.

Definition vside_cons_rw_0inf h t :=
match t with
| vside_0inf => if eqb h s0 then vside_0inf else vside_cons h t
| _ => vside_cons h t
end.

Fixpoint vside_rw_lpow_rotate(x:vside):vside :=
match x with
| vside_cons h t => vside_cons_rw_0inf h (vside_rw_lpow_rotate t)
| vside_app h n t => vside_rw_lpow_rotate' h n (vside_rw_lpow_rotate t)
| _ => x
end.

Definition rw_lpow_rotate(x:vconfig):vconfig :=
match x with
| vconfig_L l r q => vconfig_L (vside_rw_lpow_rotate l) (vside_rw_lpow_rotate r) q
| vconfig_R l r q => vconfig_R (vside_rw_lpow_rotate l) (vside_rw_lpow_rotate r) q
| vconfig_mid l r m q => vconfig_mid (vside_rw_lpow_rotate l) (vside_rw_lpow_rotate r) m q
end.

Section tm_sec.
Hypothesis tm:TM.

Definition vconfig_step1 x :=
match x with
| vconfig_mid l r m q =>
  match tm (q,m) with
  | None => None
  | Some (m',L,q') => Some (vconfig_L l (vside_cons m' r) q')
  | Some (m',R,q') => Some (vconfig_R (vside_cons m' l) r q')
  end
| _ => None
end.

Fixpoint vside_eqb x y :=
match x,y with
| vside_cons h t,vside_cons h' t' => eqb h h' && vside_eqb t t'
| vside_app h n t,vside_app h' n' t' => eqb h h' && String.eqb n n' && vside_eqb t t'
| vside_0inf,vside_0inf => true
| vside_var i,vside_var i' => String.eqb i i'
| _,_ => false
end.

Lemma vside_eqb_spec x y:
  Bool.reflect (x=y) (vside_eqb x y).
Proof with solve_Bool_reflect.
  gen y.
  induction x; intros; destruct y; cbn[vside_eqb]...
  - destruct (eqb_spec h h0)...
    destruct (IHx y)...
  - destruct (eqb_spec h h0)...
    destruct (String.eqb_spec n n0)...
    destruct (IHx y)...
  - destruct (String.eqb_spec i i0)...
Qed.

Instance vside_Eqb: Eqb vside.
econstructor.
apply vside_eqb_spec.
Defined.

Definition vconfig_eqb x y :=
match x,y with
| vconfig_L l r q,vconfig_L l' r' q' => eqb q q' && eqb l l' && eqb r r'
| vconfig_R l r q,vconfig_R l' r' q' => eqb q q' && eqb l l' && eqb r r'
| vconfig_mid l r m q,vconfig_mid l' r' m' q' => eqb q q' && eqb m m' && eqb l l' && eqb r r'
| _,_ => false
end.

Lemma vconfig_eqb_spec x y:
  Bool.reflect (x=y) (vconfig_eqb x y).
Proof with solve_Bool_reflect.
  destruct x,y; cbn[vconfig_eqb]...
  - destruct (eqb_spec q q2)...
    destruct (eqb_spec l l0)...
    destruct (eqb_spec r r0)...
  - destruct (eqb_spec q q2)...
    destruct (eqb_spec l l0)...
    destruct (eqb_spec r r0)...
  - destruct (eqb_spec q q2)...
    destruct (eqb_spec m m0)...
    destruct (eqb_spec l l0)...
    destruct (eqb_spec r r0)...
Qed.

Instance vconfig_Eqb: Eqb vconfig.
econstructor.
apply vconfig_eqb_spec.
Defined.

Fixpoint vconfig_step1s x y b T :=
match T with
| O => Some (x,y,b)
| S T0 => 
  let x0:=rw_vconfig_LR x in
  if (eqb x0 y) && negb b then
    None
  else
    match vconfig_step1 x0 with
    | Some x1 => vconfig_step1s x1 y false T0
    | None => Some (x0,y,b)
    end
end.

Fixpoint vside_split x n {struct n} :=
match n with
| O => Some (x,[])
| S n0 =>
  match x with
  | vside_cons h t =>
    match vside_split t n0 with
    | Some (x0,x1) => Some (x0,h::x1)
    | None => None
    end
  | vside_0inf =>
    Some (x,[s0]^^n)
  | _ => None
  end
end.

Fixpoint vside_app_seg x x0 :=
match x with
| h::t => vside_cons h (vside_app_seg t x0)
| [] => x0
end.

Definition chk_sr(l0:list sym)(l1 r:vside)(q:Q)(d:dir)(T:nat) :=
match r with
| vside_app r0 i r1 =>
  let c1 := BoundedConfig.Build_T l0 r0 q d in
  match BoundedConfig.steps tm T c1 with
  | Some (BoundedConfig.Build_T l0' r0' q' d') =>
    if eqb d d' && eqb q q' && eqb r0' [] then
      let len := List.length l0 in
      if eqb (firstn len l0') l0 then
        let l' := (vside_app_seg l0 (vside_app (skipn len l0') i l1)) in
        match d with
        | L => Some (vconfig_L r1 l' q)
        | R => Some (vconfig_R l' r1 q)
        end
      else None
    else None
  | _ => None
  end
| _ => None
end.

Fixpoint try_sr(l r:vside)(q:Q)(d:dir)(n n' T:nat) :=
match n with
| O => None
| S n0 =>
  match vside_split l n' with
  | Some (l1,l0) =>
    match chk_sr l0 l1 r q d T with
    | Some res => Some res
    | None => try_sr l r q d n0 (S n') T
    end
  | None => None
  end
end.

Definition vconfig_er x y T :=
let x0 := rw_lpow_rotate x in
vconfig_step1s x0 y T.

Definition vconfig_sr x T :=
match x with
| vconfig_L l r q => try_sr r l q L T O T
| vconfig_R l r q => try_sr l r q R T O T
| _ => None
end.


Fixpoint vconfig_er_sr x y b T :=
match T with
| O => Some (x,y,b)
| S T0 =>
  match vconfig_er x y b T with
  | None => None
  | Some (x0,y0,b0) =>
    match vconfig_sr x0 T with
    | None => Some (x0,y0,b0)
    | Some x1 => vconfig_er_sr x1 y0 b0 T0
    end
  end
end.


Definition vconfig_es x y b T :=
let y0 := rw_lpow_rotate y in
let y1 := rw_vconfig_LR y0 in
vconfig_er_sr x y1 b T.

Section vside_to_side.
Hypothesis nat_mp: string->nat.
Hypothesis side_mp: string->side.

Fixpoint to_side(x:vside):side :=
match x with
| vside_cons h t => h >> to_side t
| vside_app h n t => h^^(nat_mp n) *> to_side t
| vside_0inf => 0inf
| vside_var i => side_mp i
end.

Definition to_config(x:vconfig):Q*tape :=
match x with
| vconfig_L l r q => to_side l <{{q}} to_side r
| vconfig_R l r q => to_side l {{q}}> to_side r
| vconfig_mid l r m q => (q,(to_side l,m,to_side r))
end.

Lemma rw_vconfig_LR_spec x:
  to_config (rw_vconfig_LR x) = to_config x.
Proof.
  destruct x; cbn.
  - destruct l; reflexivity.
  - destruct r; reflexivity.
  - reflexivity.
Qed.

Lemma vside_cons_rw_0inf_spec h x:
  to_side (vside_cons_rw_0inf h x) = h >> to_side x.
Proof.
  destruct x; cbn; trivial.
  destruct (sym_eqb_spec h s0); cbn; subst; solve_const0_eq.
Qed.

Lemma is_all0_spec x:
  is_all0 x = true -> x *> 0inf = 0inf.
Proof.
  induction x; cbn; trivial.
  destruct (sym_eqb_spec a s0).
  2: congruence.
  subst.
  intros H.
  rewrite IHx by apply H.
  solve_const0_eq.
Qed.

Lemma vside_rw_lpow_rotate_all0_spec x x0 n:
  to_side (vside_rw_lpow_rotate_all0 x x0 n) = to_side (vside_app (x++rev x0) n vside_0inf).
Proof.
  gen x0 n.
  induction x; cbn; intros; trivial.
  destruct (sym_eqb_spec a s0); trivial.
  subst; cbn.
  rewrite IHx.
  cbn.
  rewrite const_unfold.
  rewrite lpow_rotate.
  rewrite <-const_unfold.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma vside_rw_lpow_rotate'_spec h n x:
  to_side (vside_rw_lpow_rotate' h n x) = to_side (vside_app h n x).
Proof.
  gen h n.
  induction x; cbn[vside_rw_lpow_rotate']; intros.
  - destruct h0; trivial.
    destruct (eqb_spec s h).
    + subst.
      cbn.
      rewrite IHx.
      rewrite lpow_rotate.
      reflexivity.
    + reflexivity.
  - destruct h0; trivial.
  - destruct h; trivial.
    destruct (is_all0 (s::h)) eqn:E; cbn[vside_rw_lpow_rotate'].
    + apply is_all0_spec in E.
      cbn.
      rewrite lpow_all0; trivial.
    + rewrite vside_rw_lpow_rotate_all0_spec.
      rewrite app_nil_r.
      reflexivity.
  - destruct h; trivial.
Qed.

Lemma vside_rw_lpow_rotate_spec x:
  to_side (vside_rw_lpow_rotate x) = to_side x.
Proof.
  induction x; cbn; trivial.
  - rewrite vside_cons_rw_0inf_spec,IHx; trivial.
  - rewrite vside_rw_lpow_rotate'_spec.
    cbn.
    congruence.
Qed.

Lemma rw_lpow_rotate_spec x:
  to_config (rw_lpow_rotate x) = to_config x.
Proof.
  destruct x; cbn; repeat rewrite vside_rw_lpow_rotate_spec; trivial.
Qed.

Lemma vconfig_step1_spec x x0:
  vconfig_step1 x = Some x0 ->
  multistep' tm true (to_config x) (to_config x0).
Proof.
  intros.
  destruct x; cbn in H; try congruence.
  destruct (tm (q,m)) as [[[m' [|]] q']|] eqn:E.
  - inverts H.
    cbn.
    apply progress_base.
    apply step_left,E.
  - inverts H.
    cbn.
    apply progress_base.
    apply step_right,E.
  - congruence.
Qed.

Lemma vconfig_step1s_spec x y b T:
  match vconfig_step1s x y b T with
  | Some (x',y',b') =>
    multistep' tm b' (to_config x') (to_config y') ->
    multistep' tm b (to_config x) (to_config y)
  | None => multistep' tm b (to_config x) (to_config y)
  end.
Proof.
  gen x y b.
  induction T; cbn[vconfig_step1s]; intros.
  1: trivial.
  remember (rw_vconfig_LR x) as x0.
  destruct (eqb_spec x0 y).
  - destruct b eqn:Eb; cbn.
    + destruct (vconfig_step1 x0) eqn:E.
      * apply vconfig_step1_spec in E.
        destruct (vconfig_step1s v y false T) as [[[x' y'] b']|] eqn:E0.
        -- epose proof (IHT _ _ _) as IHT.
           rewrite E0 in IHT.
           intros.
           specialize (IHT H).
           subst.
           rewrite rw_vconfig_LR_spec in *.
           eapply progress_evstep_trans.
           1: apply E.
           apply IHT.
        -- epose proof (IHT _ _ _) as IHT.
           rewrite E0 in IHT.
           subst.
           rewrite rw_vconfig_LR_spec in *.
           eapply progress_evstep_trans.
           1: apply E.
           apply IHT.
      * subst.
        intros.
        rewrite rw_vconfig_LR_spec in *.
        apply H.
    + subst.
      rewrite rw_vconfig_LR_spec in *.
      constructor.
  - destruct (vconfig_step1 x0) eqn:E.
    + apply vconfig_step1_spec in E.
      destruct (vconfig_step1s v y false T) as [[[x' y'] b']|] eqn:E0.
      -- epose proof (IHT _ _ _) as IHT.
         rewrite E0 in IHT.
         intros.
         specialize (IHT H).
         subst.
         rewrite rw_vconfig_LR_spec in *.
         eapply multistep'_trans.
         2,3: eassumption.
         destruct b; cbn; trivial.
      -- epose proof (IHT _ _ _) as IHT.
         rewrite E0 in IHT.
         subst.
         rewrite rw_vconfig_LR_spec in *.
         eapply multistep'_trans.
         2,3: eassumption.
         destruct b; cbn; trivial.
    + subst.
      rewrite rw_vconfig_LR_spec in *.
      tauto.
Qed.

Lemma vside_split_spec x n x1 x0:
  vside_split x n = Some (x1,x0) ->
  to_side x = x0 *> to_side x1.
Proof.
  gen x x1 x0.
  induction n; intros.
  - cbn in H.
    inverts H.
    reflexivity.
  - cbn in H.
    destruct x; inverts H.
    + destruct (vside_split x n) as [[x1' x0']|] eqn:E; inverts H1.
      apply IHn in E.
      cbn.
      congruence.
    + cbn.
      unfold s0.
      rewrite lpow_all0 by solve_const0_eq.
      solve_const0_eq.
Qed.

Lemma vside_app_seg_spec x x0:
  to_side (vside_app_seg x x0) = x *> to_side x0.
Proof.
  induction x; cbn; congruence.
Qed.

Lemma vconfig_er_spec x y b T:
  match vconfig_er x y b T with
  | None => multistep' tm b (to_config x) (to_config y)
  | Some (x0,y0,b0) =>
    multistep' tm b0 (to_config x0) (to_config y0) ->
    multistep' tm b (to_config x) (to_config y)
  end.
Proof.
  unfold vconfig_er.
  epose proof (vconfig_step1s_spec (rw_lpow_rotate x) y b T) as E.
  destruct (vconfig_step1s (rw_lpow_rotate x) y b T) as [[[x' y'] b']|].
  - rewrite rw_lpow_rotate_spec in *.
    tauto.
  - rewrite rw_lpow_rotate_spec in *.
    tauto.
Qed.

Lemma chk_sr_spec l0 l1 r q d T x:
  chk_sr l0 l1 r q d T = Some x ->
  to_config (
  match d with
  | L => vconfig_L r (vside_app_seg l0 l1) q
  | R => vconfig_R (vside_app_seg l0 l1) r q
  end) -[ tm ]->* to_config x.
Proof.
  unfold chk_sr.
  intros.
  destruct r; try congruence.
  epose proof (BoundedConfig.steps_spec tm T (BoundedConfig.Build_T l0 h q d)) as E.
  destruct (BoundedConfig.steps tm T (BoundedConfig.Build_T l0 h q d)) as [[l0' r0' q' d']|].
  2: congruence.
  cbn in E.
  destruct (eqb_spec d d'); try congruence.
  destruct (eqb_spec q q'); try congruence.
  destruct (eqb_spec r0' []); try congruence.
  destruct (eqb_spec (firstn (Datatypes.length l0) l0') l0); try congruence.
  subst.
  destruct d'.
  - inverts H.
    subst.
    cbn.
    repeat rewrite vside_app_seg_spec.
    cbn.
    apply shift_rule_L.
    intros.
    epose proof (firstn_skipn (List.length l0) l0') as Hl0'.
    rewrite e2 in Hl0'.
    epose proof (E l r0) as E.
    eapply RWLAcc62.TM.with_counter in E.
    destruct E as [n0 E].
    eapply RWLAcc62.TM.multistep_c_spec in E.
    rewrite <-Hl0',Str_app_assoc in E.
    eapply without_counter.
    eapply multistep_c_spec.
    apply E.
  - inverts H.
    subst.
    cbn.
    repeat rewrite vside_app_seg_spec.
    cbn.
    apply shift_rule_R.
    intros.
    epose proof (firstn_skipn (List.length l0) l0') as Hl0'.
    rewrite e2 in Hl0'.
    epose proof (E l r0) as E.
    eapply RWLAcc62.TM.with_counter in E.
    destruct E as [n0 E].
    eapply RWLAcc62.TM.multistep_c_spec in E.
    rewrite <-Hl0',Str_app_assoc in E.
    eapply without_counter.
    eapply multistep_c_spec.
    apply E.
Qed.

Lemma try_sr_spec l r q d n n' T x:
  try_sr l r q d n n' T = Some x ->
  to_config (
  match d with
  | L => vconfig_L r l q
  | R => vconfig_R l r q
  end) -[ tm ]->* to_config x.
Proof.
  gen l r q d n' T x.
  induction n; cbn[try_sr]; intros.
  1: congruence.
  destruct (vside_split l n') as [[l1 l0]|] eqn:E.
  2: congruence.
  apply vside_split_spec in E.
  destruct (chk_sr l0 l1 r q d T) eqn:E0.
  - inverts H.
    apply chk_sr_spec in E0.
    destruct d.
    + unfold to_config in *.
      rewrite vside_app_seg_spec in *.
      rewrite <-E in E0.
      apply E0.
    + unfold to_config in *.
      rewrite vside_app_seg_spec in *.
      rewrite <-E in E0.
      apply E0.
  - eapply IHn,H.
Qed.

Lemma vconfig_sr_spec x T x0:
  vconfig_sr x T = Some x0 ->
  multistep' tm false (to_config x) (to_config x0).
Proof.
  unfold vconfig_sr.
  destruct x; intros.
  3: congruence.
  - apply try_sr_spec in H.
    apply H.
  - apply try_sr_spec in H.
    apply H.
Qed.

Lemma vconfig_er_sr_spec x y b T:
  vconfig_er_sr x y b T = None ->
  multistep' tm b (to_config x) (to_config y).
Proof.
  gen x y b.
  induction T; intros; cbn[vconfig_er_sr] in *.
  1: congruence.
  epose proof (vconfig_er_spec x y b (S T)) as E.
  destruct (vconfig_er x y b (S T)) as [[[x0 y0] b0]|].
  - apply E.
    destruct (vconfig_sr x0 (S T)) eqn:E0; try congruence.
    apply vconfig_sr_spec in E0.
    apply IHT in H.
    eapply multistep'_trans.
    2,3: eassumption.
    destruct b0; trivial.
  - apply E.
Qed.

Lemma vconfig_es_spec x y b T:
  vconfig_es x y b T = None ->
  multistep' tm b (to_config x) (to_config y).
Proof.
  unfold vconfig_es.
  intros.
  apply vconfig_er_sr_spec in H.
  rewrite rw_vconfig_LR_spec in *.
  rewrite rw_lpow_rotate_spec in *.
  apply H.
Qed.

End vside_to_side.

End tm_sec.


Lemma rw_progress tm c1 c2 c1' c2':
  c1 = c1' ->
  c2 = c2' ->
  c1 -[ tm ]->+ c2 = 
  multistep' tm true c1' c2'.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_evstep tm c1 c2 c1' c2':
  c1 = c1' ->
  c2 = c2' ->
  c1 -[ tm ]->* c2 = 
  multistep' tm false c1' c2'.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_config_L nmp smp l r q l' r':
  l = to_side nmp smp l' ->
  r = to_side nmp smp r' ->
  l <{{q}} r = to_config nmp smp (vconfig_L l' r' q).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_config_R nmp smp l r q l' r':
  l = to_side nmp smp l' ->
  r = to_side nmp smp r' ->
  l {{q}}> r = to_config nmp smp (vconfig_R l' r' q).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_config_mid nmp smp l r q m l' r':
  l = to_side nmp smp l' ->
  r = to_side nmp smp r' ->
  (q,(l,m,r)) = to_config nmp smp (vconfig_mid l' r' m q).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_side_cons nmp smp h t t':
  t = to_side nmp smp t' ->
  h>>t = to_side nmp smp (vside_cons h t').
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_side_app_seg nmp smp h t t':
  t = to_side nmp smp t' ->
  h *> t = to_side nmp smp (vside_app_seg h t').
Proof.
  intros; subst.
  rewrite vside_app_seg_spec; trivial.
Qed.

Lemma rw_0inf nmp smp:
  0inf = to_side nmp smp (vside_0inf).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_side_app nmp smp h n t t':
  t = to_side nmp smp t' ->
  h ^^ (nmp n) *> t = to_side nmp smp (vside_app h n t').
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_side_var nmp smp i:
  smp i = to_side nmp smp (vside_var i).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma rw_side_lpow_add (h:list sym) a b t y:
  h^^a *> h^^b *> t = y ->
  h^^(a+b) *> t = y.
Proof.
  rewrite lpow_add,Str_app_assoc.
  tauto.
Qed.

Ltac rw_side :=
match goal with
| |- (_ ^^ (_ + _)) *> _ = _ => eapply rw_side_lpow_add; rw_side
| |- (_ ^^ (_ _)) *> _ = _ => eapply rw_side_app; rw_side
| |- (_) *> _ = _ => eapply rw_side_app_seg; rw_side
| |- _ >> _ = _ => eapply rw_side_cons; rw_side
| |- 0inf = _ => eapply rw_0inf
| |- _ = _ => eapply rw_side_var
end.

Ltac rw_config :=
match goal with
| |- _ <{{ _ }} _ = _ => eapply rw_config_L; rw_side
| |- _ {{ _ }}> _ = _ => eapply rw_config_R; rw_side
| |- (_,(_,_,_)) = _ => eapply rw_config_mid; rw_side
end.

Ltac vm_check_eq :=
match goal with
| |- _ = ?a => vm_cast_no_check (eq_refl a)
end.

Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Open Scope string.

Ltac var a sa :=
  replace a with sa by reflexivity.

Ltac rw_multistep' :=
  (erewrite rw_evstep || erewrite rw_progress); [| rw_config | rw_config].

Ltac rw_mp_expr fn e :=
match e with
| if _ =? ?sa then ?a else ?e0 =>
  var a (fn sa);
  rw_mp_expr fn e0
| _ => idtac
end.

Ltac rw_mp' :=
  match goal with
  | [ fn1 := fun _ => _ |- _] =>
    progress (
    epose (fn1 "") as v1;
    unfold fn1 in v1;
    match goal with
    | [ v1 := ?v2 |- _] =>
      match v2 with
      | if _ then _ else _ =>
        clear v1;
        rw_mp_expr fn1 v2
      end
    end)
  end.

Ltac rw_mp :=
  repeat rw_mp'.

Ltac es_v3 :=
  rw_mp;
  rw_multistep';
  apply vconfig_es_spec with (T:=N.to_nat (10^6));
  time vm_compute; reflexivity.

Ltac es_v3_nmp nmp' :=
  pose nmp' as nmp;
  unshelve es_v3; apply (fun _ => 0inf).

Ltac es_v3_nmp_smp nmp' smp' :=
  pose nmp' as nmp;
  pose smp' as smp;
  es_v3.

Tactic Notation "es'" constr(a) :=
  (es_v3_nmp (fun s =>
  if s=?"a" then a else
  O)).

Tactic Notation "es'" constr(a) constr(b) :=
  (es_v3_nmp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  O)).

Tactic Notation "es'" constr(a) constr(b) constr(c) :=
  (es_v3_nmp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O)).

Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) :=
  (es_v3_nmp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  if s=?"d" then d else
  O)).

Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (es_v3_nmp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  if s=?"d" then d else
  if s=?"e" then e else
  O)).

Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
  (es_v3_nmp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  if s=?"d" then d else
  if s=?"e" then e else
  if s=?"f" then f else
  O)).

Tactic Notation "es'" constr(a) constr(b) "&" constr(c) :=
  (es_v3_nmp_smp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  O)
  (fun s =>
  if s=?"c" then c else
  0inf)).

Tactic Notation "es'" constr(a) constr(b) constr(c) "&" constr(d) :=
  (es_v3_nmp_smp (fun s =>
  if s=?"a" then a else
  if s=?"b" then b else
  if s=?"c" then c else
  O)
  (fun s =>
  if s=?"d" then d else
  0inf)).

Close Scope string.

