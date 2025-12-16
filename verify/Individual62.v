From BusyCoq Require Export Individual BB62.

Module Individual62 := Individual BB62.
Export Individual62.
Require Import Ascii.
Require Import String.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.
Notation "'0inf'" := (const 0) : sym_scope.

(* Make sure that [{{D}}>] still refers to the state, even if we shadowed
   [D] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).
Notation "l '{{C}}>'  r" := (l {{C}}> r) (at level 30).
Notation "l '{{D}}>'  r" := (l {{D}}> r) (at level 30).
Notation "l '{{E}}>'  r" := (l {{E}}> r) (at level 30).
Notation "l '{{F}}>'  r" := (l {{F}}> r) (at level 30).

Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).
Notation "l '<{{C}}' r" := (l <{{C}} r) (at level 30).
Notation "l '<{{D}}' r" := (l <{{D}} r) (at level 30).
Notation "l '<{{E}}' r" := (l <{{E}} r) (at level 30).
Notation "l '<{{F}}' r" := (l <{{F}} r) (at level 30).


Ltac mid m :=
  eapply evstep_trans with (c':=m).

Ltac mid10 m :=
  eapply progress_evstep_trans with (c':=m).

Ltac mid01 m :=
  eapply evstep_progress_trans with (c':=m).

Ltac follow10 H :=
  eapply progress_evstep_trans; [ apply H; fail | idtac ].

Ltac follow100 H :=
  apply progress_evstep;
  follow10 H.

Ltac follow11 H :=
  eapply progress_trans; [ apply H; fail | idtac ].


Ltac steps := cbn; intros;
  repeat ((try apply evstep_refl); step).

Ltac solve_const0_eq:=
  cbv; (repeat rewrite <-const_unfold); reflexivity.

Ltac solve_shift_rule H l r n :=
  gen l r;
  induction n as [|n IHn]; intros l r;
  [ finish |
    simpl_tape;
    follow H;
    follow IHn;
    rewrite lpow_shift';
    finish ].

Ltac shift_rule :=
  intros;
  match goal with
  | |-
    (?l <* ?w0^^?n <{{?QL}} ?w *> ?r -[ ?tm ]->*
    ?l <{{?QL}} ?w *> ?w0'^^?n *> ?r) =>
    cut (forall l r,
    l <* w0 <{{QL}} w *> r -[tm]->*
    l <{{QL}} w *> w0' *> r);
    [ intros H; solve_shift_rule H l r n
    | idtac ]
  | |-
    (?l <* ?w {{?QR}}> ?w0^^?n *> ?r -[ ?tm ]->*
    ?l <* ?w0'^^?n <* ?w {{?QR}}> ?r) =>
    cut (forall l r,
    l <* w {{QR}}> w0 *> r -[tm]->*
    l <* w0' <* w {{QR}}> r);
    [ intros H; solve_shift_rule H l r n
    | idtac ]
  | |-
    (?l <* ?w0^^?n <{{?QL}} ?r -[ ?tm ]->*
    ?l <{{?QL}} ?w0'^^?n *> ?r) =>
    cut (forall l r,
    l <* w0 <{{QL}} r -[tm]->*
    l <{{QL}} w0' *> r);
    [ intros H; solve_shift_rule H l r n
    | idtac ]
  | |-
    (?l {{?QR}}> ?w0^^?n *> ?r -[ ?tm ]->*
    ?l <* ?w0'^^?n {{?QR}}> ?r) =>
    cut (forall l r,
    l {{QR}}> w0 *> r -[tm]->*
    l <* w0' {{QR}}> r);
    [ intros H; solve_shift_rule H l r n
    | idtac ]
  end.


Lemma lpow_shift1(a:Sym)(b:Stream Sym) n:
  [a]^^n *> a >> b = a >> [a]^^n *> b.
Proof.
  change (a>>b) with ([a] *> b).
  apply lpow_shift'.
Qed.

Lemma lpow_shift2(a0 a1:Sym)(b:Stream Sym) n:
  [a0;a1]^^n *> a0 >> a1 >> b = a0 >> a1 >> [a0;a1]^^n *> b.
Proof.
  change (a0>>a1>>b) with ([a0;a1] *> b).
  apply lpow_shift'.
Qed.

Lemma lpow_shift21(a0 a1:Sym)(b:Stream Sym) n:
  a0 >> [a1;a0]^^n *> a1 >> b = a0 >> a1 >> [a0;a1]^^n *> b.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

Lemma lpow_rotate a0 a1 (b:Stream Sym) n:
  (a1::a0)^^n *> a1 >> b = a1 >> (a0++[a1])^^n *> b.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    simpl_tape.
    rewrite IHn.
    reflexivity.
Qed.


Lemma lpow_rotate_const0 a0 n:
  (0::a0)^^n *> const 0 = 0 >> (a0++[0])^^n *> const 0.
Proof.
  rewrite const_unfold.
  rewrite lpow_rotate.
  rewrite <-const_unfold.
  reflexivity.
Qed.

Lemma lpow_rotate' a0 a1 (b:Stream Sym) n:
  (a1++a0)^^n *> a1 *> b = a1 *> (a0++a1)^^n *> b.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    simpl_tape.
    rewrite IHn.
    reflexivity.
Qed.

Lemma lpow_mul{A} (a:list A) b n:
  a^^(b*n) = (a^^n)^^b.
Proof.
  induction b.
  - reflexivity.
  - cbn.
    rewrite lpow_add.
    congruence.
Qed.

Lemma lpow_shift21e(a:Sym)(b:Stream Sym) n:
  a >> [a;a]^^n *> b = [a;a]^^n *> a >> b.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

Lemma flat_map_lpow{A B} (f:A->list B) ls n:
  List.flat_map f (ls^^n) = (List.flat_map f ls)^^n.
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite <-IHn.
    apply List.flat_map_app.
Qed.

Lemma Forall_lpow{A} (P:A->Prop) a n:
  List.Forall P a ->
  List.Forall P (a^^n).
Proof.
  intro H.
  induction n.
  - auto.
  - cbn.
    rewrite List.Forall_app; split; auto.
Qed.

Lemma lpow_length{A} (s:list A) n:
  List.length (s^^n) = n*(List.length s).
Proof.
  induction n.
  - reflexivity.
  - cbn.
    rewrite List.app_length,IHn.
    reflexivity.
Qed.

Lemma lpow_all0 a n:
  a *> const 0 = const 0 ->
  a^^n *> const 0 = const 0.
Proof.
  intro H.
  induction n.
  - reflexivity.
  - simpl_tape.
    rewrite IHn.
    apply H.
Qed.

Lemma lpow_add' (a:list Sym) n1 n2 r:
  a^^n1 *> a^^n2 *> r =
  a^^(n1+n2) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  reflexivity.
Qed.


Lemma shift_rule_L d tm x x' X:
  (forall l r,
    l <* x <{{X}} d *> r -[ tm ]->*
    l <{{X}} d *> x' *> r) ->
  forall l r n,
    l <* x^^n <{{X}} d *> r -[ tm ]->*
    l <{{X}} d *> x'^^n *> r.
Proof.
  intros.
  gen l r.
  induction n; intros.
  - finish.
  - simpl_tape.
    follow H.
    follow IHn.
    rewrite lpow_shift'.
    finish.
Qed.

Lemma shift_rule_R d tm x x' X:
  (forall l r,
    l <* d {{X}}> x *> r -[ tm ]->*
    l <* x' <* d {{X}}> r) ->
  forall l r n,
    l <* d {{X}}> x^^n *> r -[ tm ]->*
    l <* x'^^n <* d {{X}}> r.
Proof.
  intros.
  gen l r.
  induction n; intros.
  - finish.
  - simpl_tape.
    follow H.
    follow IHn.
    rewrite lpow_shift'.
    finish.
Qed.

Lemma Str_cons_def{A} (a:A) b:
  a >> b = [a] *> b.
Proof.
  reflexivity.
Qed.

Ltac step1 :=
  match goal with
  | |- (_ -[ _ ]->+ _) => eapply progress_intro
  | |- (_ -[ _ ]->* _) => eapply evstep_step
  | _ => fail "fail1"
  end; [prove_step|simpl_tape].

Ltac simpl_rotate :=
  cbn;
  repeat ((rewrite lpow_rotate || rewrite lpow_rotate_const0); cbn).

Ltac step1s :=
  repeat ((try (apply evstep_refl'; reflexivity; fail)); step1).

Ltac execute_with_rotate :=
  simpl_rotate; step1s.

Ltac find_shift_rule :=
  steps;
  eapply evstep_refl';
  repeat f_equal;
  repeat rewrite Str_cons_def;
  repeat rewrite <-Str_app_assoc;
  cbn[List.app];
  f_equal;
  fail.

Open Scope list.

Ltac use_shift_rule :=
  match goal with
  | |- (_ -[ _ ]->+ _) => eapply evstep_progress_trans
  | |- (_ -[ _ ]->* _) => eapply evstep_trans
  | _ => idtac "fail1"; fail
  end; [
    let x :=
    match goal with
    | |- (_ <* _ ^^ _ <{{ _ }} _ -[ _ ]->* _) => shift_rule_L
    | |- (_ {{ _ }}> _ ^^ _ *> _ -[ _ ]->* _) => shift_rule_R
    | _ => (*idtac "fail2";*) fail
    end in
      (eapply (x []); find_shift_rule) ||
      (eapply (x [_]); find_shift_rule) ||
      (eapply (x [_;_]); find_shift_rule) ||
      (eapply (x [_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_]); find_shift_rule) ||
      (fail)
  |].

Ltac use_shift_rule' :=
  match goal with
  | |- (_ -[ _ ]->+ _) => eapply evstep_progress_trans
  | |- (_ -[ _ ]->* _) => eapply evstep_trans
  | _ => idtac "fail1"; fail
  end; [
    let x :=
    match goal with
    | |- (_ <* _ ^^ _ <{{ _ }} _ -[ _ ]->* _) => shift_rule_L
    | |- (_ {{ _ }}> _ ^^ _ *> _ -[ _ ]->* _) => shift_rule_R
    | _ => idtac "fail2"; fail
    end in
      (eapply (x []); find_shift_rule) ||
      (eapply (x [_]); find_shift_rule) ||
      (eapply (x [_;_]); find_shift_rule) ||
      (eapply (x [_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_;_;_;_;_;_]); find_shift_rule) ||
      (eapply (x [_;_;_;_;_;_;_;_;_;_;_;_]); find_shift_rule) ||
      (fail)
  |].

Ltac execute_with_shift_rule :=
  intros;
  repeat (execute_with_rotate; use_shift_rule).

Ltac execute_with_shift_rule' :=
  intros;
  repeat (execute_with_rotate; use_shift_rule').

Ltac simpl_flat_map :=
  repeat rewrite List.flat_map_app;
  repeat rewrite flat_map_lpow;
  cbn;
  simpl_tape.

Ltac casen_execute_with_shift_rule n :=
  (execute_with_shift_rule; fail) ||
  (destruct n; [ step1s | execute_with_shift_rule ]).




Definition cconfig:Set := (list Sym)*(list Sym)*Sym*Q.

Definition cconfig_to_config(x:cconfig):Q*tape:=
match x with
| (l,r,m,s) =>
  (s,(const 0 <* l,m,r *>const 0))
end.

Definition cconfig_step(tm:TM)(x:cconfig):option cconfig:=
match x with
| (l,r,m,s) =>
  match tm (s,m) with
  | Some (o,d,s') =>
    match d with
    | L => Some (List.tl l,o::r,List.hd 0 l,s')
    | R => Some (o::l,List.tl r,List.hd 0 r,s')
    end
  | None => None
  end
end.

Local Notation "x &&& y" := (if x then y else false) (at level 80, right associativity).
Local Notation "x ||| y" := (if x then true else y) (at level 85, right associativity).

Lemma andb_shortcut_spec(a b:bool):
  (a&&&b) = (a&&b)%bool.
Proof.
  reflexivity.
Qed.

Lemma orb_shortcut_spec(a b:bool):
  (a|||b) = (a||b)%bool.
Proof.
  reflexivity.
Qed.

Fixpoint cside_eqb_const0(x:list Sym):bool :=
match x with
| a::b => sym_eqb a 0 &&& cside_eqb_const0 b
| nil => true
end.

Fixpoint cside_eqb(x y:list Sym):bool :=
match x,y with
| a::b,c::d => sym_eqb a c &&& cside_eqb b d
| a::b,nil => cside_eqb_const0 x
| nil,_ => cside_eqb_const0 y
end.

Definition cconfig_eqb(x y:cconfig):bool :=
match x,y with
| (l,r,m,s),(l',r',m',s') =>
  q_eqb s s' &&&
  sym_eqb m m' &&&
  cside_eqb l l' &&&
  cside_eqb r r'
end.

Lemma cside_eqb_const0_spec x:
  cside_eqb_const0 x = true ->
  x *> const 0 = const 0.
Proof.
  induction x; cbn; try congruence.
  repeat rewrite andb_shortcut_spec.
  rewrite Bool.andb_true_iff.
  intros [H H0].
  destruct (sym_eqb_spec a 0); subst; try congruence.
  rewrite IHx; auto.
  solve_const0_eq.
Qed.

Lemma cside_eqb_spec x y:
  cside_eqb x y = true ->
  x *> const 0 = y *> const 0.
Proof.
  gen y.
  induction x; intros.
  - cbn. rewrite cside_eqb_const0_spec; auto.
  - cbn.
    cbn in H.
    destruct y; repeat rewrite andb_shortcut_spec,Bool.andb_true_iff in H.
    + destruct H as [H H0].
      destruct (sym_eqb_spec a 0); subst; try congruence.
      rewrite cside_eqb_const0_spec; auto.
      rewrite <-const_unfold; auto.
    + destruct H as [H H0].
      destruct (sym_eqb_spec a s); subst; try congruence.
      cbn.
      erewrite IHx; eauto.
Qed.

Lemma cconfig_eqb_spec x y:
  cconfig_eqb x y = true ->
  cconfig_to_config x = cconfig_to_config y.
Proof.
  destruct x as [[[l1 r1] m1] s1].
  destruct y as [[[l2 r2] m2] s2].
  cbn.
  repeat rewrite andb_shortcut_spec.
  repeat rewrite Bool.andb_true_iff.
  intros [H [H0 [H1 H2]]].
  destruct (q_eqb_spec s1 s2); subst; try congruence.
  destruct (sym_eqb_spec m1 m2); subst; try congruence.
  rewrite (cside_eqb_spec _ _ H1).
  rewrite (cside_eqb_spec _ _ H2).
  reflexivity.
Qed.

Lemma cconfig_step_spec tm x:
  match cconfig_step tm x with
  | Some y => (cconfig_to_config x) -[ tm ]-> (cconfig_to_config y)
  | None => True
  end.
Proof.
  destruct x as [[[l1 r1] m1] s1].
  cbn.
  destruct (tm (s1,m1)) as [[[o d] s']|] eqn:E.
  2: auto.
  destruct d; cbn.
  - epose proof (@step_left tm s1 _ m1 _ (l1 *> const 0) (r1 *> const 0) E) as H.
    cbn in H.
    destruct l1; apply H.
  - epose proof (@step_right tm s1 _ m1 _ (l1 *> const 0) (r1 *> const 0) E) as H.
    cbn in H.
    destruct r1; apply H.
Qed.

Fixpoint cconfig_evstep_dec(tm:TM)(x y:cconfig)(n:nat) :=
match n with
| O => false
| S n0 =>
  cconfig_eqb x y |||
  match cconfig_step tm x with
  | None => false
  | Some x0 => cconfig_evstep_dec tm x0 y n0
  end
end.

Lemma cconfig_evstep_dec_spec tm x y n:
  cconfig_evstep_dec tm x y n = true ->
  (cconfig_to_config x) -[ tm ]->* (cconfig_to_config y).
Proof.
  gen x.
  induction n; cbn; intros.
  1: congruence.
  pose proof (cconfig_eqb_spec x y) as HE.
  destruct (cconfig_eqb x y) eqn:E.
  - rewrite HE; auto.
  - pose proof (cconfig_step_spec tm x) as HE0.
    destruct (cconfig_step tm x) as [x0|].
    + eapply evstep_step; eauto.
    + congruence.
Qed.

Lemma simpl_directed_head_l (l:list Sym)(r:side) (q:Q):
  const 0 <* l <{{ q }} r =
  (q,(const 0 <* (List.tl l), (List.hd 0 l), r)).
Proof.
  destruct l; reflexivity.
Qed.

Lemma simpl_directed_head_r (l:side)(r:list Sym) (q:Q):
  l {{ q }}> r *> const 0 =
  (q,(l, (List.hd 0 r), (List.tl r) *> const 0)).
Proof.
  destruct r; reflexivity.
Qed.

Lemma config_to_cconfig l r q m:
  (q,(const 0 <* l,m,r *> const 0)) =
  cconfig_to_config (l,r,m,q).
Proof.
  reflexivity.
Qed.

Lemma l_const0_app_nil (r:side)(m:Sym)(q:Q):
  (q,(const 0,m,r)) =
  (q,([] *> const 0,m,r)).
Proof.
  reflexivity.
Qed.

Lemma r_const0_app_nil (l:side)(m:Sym)(q:Q):
  (q,(l,m,const 0)) =
  (q,(l,m,[] *> const 0)).
Proof.
  reflexivity.
Qed.

Lemma c0_to_cconfig:
  c0 = cconfig_to_config (nil,nil,0,q0).
Proof.
  reflexivity.
Qed.

Ltac solve_init :=
  rewrite c0_to_cconfig;
  repeat rewrite Str_cons_def;
  repeat rewrite <-Str_app_assoc;
  repeat rewrite simpl_directed_head_l;
  repeat rewrite simpl_directed_head_r;
  repeat rewrite l_const0_app_nil;
  repeat rewrite r_const0_app_nil;
  repeat rewrite config_to_cconfig;
  apply cconfig_evstep_dec_spec with (n:=1000000);
  vm_compute;
  reflexivity.



Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac unfold_config_expr x :=
match x with
| ?a ?b => unfold_config_expr a
| ?a => try (unfold a)
end.

Ltac unfold_config :=
match goal with
| |- ?a -[_]->* ?b =>
  unfold_config_expr a;
  unfold_config_expr b
| |- ?a -[_]->+ ?b =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac st :=
  repeat
  (rewrite lpow_add ||
  rewrite Str_app_assoc ||
  rewrite lpow_mul);
  simpl_tape.

Ltac es :=
  intros;
  unfold_config;
  st;
  execute_with_shift_rule.

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].

Ltac solve_halt :=
  eapply halts_evstep; [|
    repeat (rewrite lpow_add || rewrite lpow_mul || simpl_tape || simpl_rotate);
    repeat (step1 || sr || simpl_rotate);
    finish
  ];
  eapply halted_halts;
  constructor.

Ltac solve_halts_at_trans :=
  eapply halts_at_trans_evstep; [
    repeat (rewrite lpow_add || rewrite lpow_mul || simpl_tape || simpl_rotate);
    repeat (step1 || sr || simpl_rotate);
    finish
 |];
  do 4 econstructor.

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
  rewrite lpow_mul ||
  rewrite <-List.app_assoc ||
  rewrite lpow_rotate_list ||
  rewrite List.app_nil_r ||
  cbn[app] || cbn[lpow]).

Ltac solve_sideRLs :=
  st;
  simpl_rotate;
  repeat (eapply sideRLseq_S;
  [ intros ?l;
    unfold to_DH_config; cbn;
    (repeat (er; try sr)) | ] ||
  eapply sideRLseq_O).

Lemma feq{A B}(f g:A->B)(x y:A):
  f=g ->
  x=y ->
  f x = g y.
Proof.
  congruence.
Qed.

Lemma Peq(P Q:Prop):
  Q=P -> P -> Q.
Proof.
  congruence.
Qed.

Ltac ret_tape a :=
match a with
| _ -> ?b => ret_tape b
| Q*tape => idtac
| list Sym => idtac
| list sym => idtac
| side => idtac
| Stream sym => idtac
end.

Ltac unfold_tape :=
repeat (
eapply Peq; [
repeat
match goal with
| |- ?a = _ =>
  match type of a with
  | nat => reflexivity
  end
| |- _ _ = _ => eapply feq
| |- const = _ => reflexivity
| |- Str_app = _ => reflexivity
| |- app = _ => reflexivity
| |- lpow = _ => reflexivity
| |- ?a = _ =>
  let t:=type of a in
  ret_tape t; unfold a
| _ => reflexivity
end | cbn ]).

Ltac ut := unfold_tape.

Lemma lpow_unrotate_1 n (a:Sym) r:
  a >> [a]^^n *> r =
  [a]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma lpow_unrotate_2 n (a a0:Sym) r:
  a >> [a0;a]^^n *> r =
  [a;a0]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma lpow_unrotate_3 n (a a0 a1:Sym) r:
  a >> [a0;a1;a]^^n *> r =
  [a;a0;a1]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma lpow_unrotate_4 n (a a0 a1 a2:Sym) r:
  a >> [a0;a1;a2;a]^^n *> r =
  [a;a0;a1;a2]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma lpow_unrotate_5 n (a a0 a1 a2 a3:Sym) r:
  a >> [a0;a1;a2;a3;a]^^n *> r =
  [a;a0;a1;a2;a3]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Lemma lpow_unrotate_6 n (a a0 a1 a2 a3 a4:Sym) r:
  a >> [a0;a1;a2;a3;a4;a]^^n *> r =
  [a;a0;a1;a2;a3;a4]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Ltac esx :=
  lazymatch goal with
  | |- forall _, _ => intro; esx
  | |- segRLs _ _ _ _ _ => solve_segRLs
  | |- sideRLs _ _ _ _ => solve_sideRLs
  | |- c0 -[ _ ]->* _ => cbn; solve_init
  | |- _ -[ _ ]->* _ => es
  | |- _ -[ _ ]->+ _ => es
  | |- halts _ _ => solve_halt
  | |- halts_at_trans _ _ _ => solve_halts_at_trans
  end.

Ltac toX X :=
  repeat
  lazymatch goal with
  | |- (X,_) -[ _ ]->* _ => fail
  | _ => step1 || simpl_rotate || sr
  end.

Definition Sym_from_char(x:ascii):option Sym :=
match x with
| "0"%char => Some S0
| "1"%char => Some S1
| _ => None
end.

Definition dir_from_char(x:ascii):option dir :=
match x with
| "L"%char => Some L
| "R"%char => Some R
| _ => None
end.

Definition Q_from_char(x:ascii):option Q :=
match x with
| "A"%char => Some A
| "B"%char => Some B
| "C"%char => Some C
| "D"%char => Some D
| "E"%char => Some E
| "F"%char => Some F
| _ => None
end.

Definition trans_from_char(c0 c1 c2:ascii):option (Sym * dir * Q) :=
  match (Sym_from_char c0),(dir_from_char c1),(Q_from_char c2) with
  | Some o, Some d, Some s => Some (o,d,s)
  | _,_,_ => None
  end.

Definition trans_from_str(x:string): string*(option (Sym * dir * Q)) :=
match x with
| (String c0 (String c1 (String c2 x0))) =>
  (x0,trans_from_char c0 c1 c2)
| _ => (x,None)
end.

Definition skip_sep(x:string): string :=
match x with
| String ("_"%char) x0 => x0
| _ => x
end.

Definition Q_from_str(x:string): string*(option (Sym * dir * Q))*(option (Sym * dir * Q)) :=
  let (x0,A0):=trans_from_str x in
  let (x1,A1):=trans_from_str x0 in
  let x2:=skip_sep x1 in
  (x2,A0,A1).

Definition TM_from_str(x:string):TM :=
  let '(x0,A0,A1):=Q_from_str x in
  let '(x1,B0,B1):=Q_from_str x0 in
  let '(x2,C0,C1):=Q_from_str x1 in
  let '(x3,D0,D1):=Q_from_str x2 in
  let '(x4,E0,E1):=Q_from_str x3 in
  let '(x5,F0,F1):=Q_from_str x4 in
  fun '(q,s) =>
  match q,s with
  | A,0 => A0  | A,1 => A1
  | B,0 => B0  | B,1 => B1
  | C,0 => C0  | C,1 => C1
  | D,0 => D0  | D,1 => D1
  | E,0 => E0  | E,1 => E1
  | F,0 => F0  | F,1 => F1
  end.

Definition Sym_to_str(x:Sym):string :=
match x with
| S0 => "0"
| S1 => "1"
end.

Definition dir_to_str(x:dir):string :=
match x with
| L => "L"
| R => "R"
end.

Definition Q_to_str(x:Q):string :=
match x with
| A => "A"
| B => "B"
| C => "C"
| D => "D"
| E => "E"
| F => "F"
end.

Definition Trans_to_str(x:option (Sym*dir*Q)):string :=
match x with
| None => "---"
| Some (o,d,s) => (Sym_to_str o) ++ (dir_to_str d) ++ (Q_to_str s)
end.

Definition TM_Q_to_str(tm:TM)(q:Q):string :=
  (Trans_to_str (tm (q,S0))) ++
  (Trans_to_str (tm (q,S1))).

Definition TM_to_str(tm:TM):string :=
  (TM_Q_to_str tm A) ++ "_" ++
  (TM_Q_to_str tm B) ++ "_" ++
  (TM_Q_to_str tm C) ++ "_" ++
  (TM_Q_to_str tm D) ++ "_" ++
  (TM_Q_to_str tm E) ++ "_" ++
  (TM_Q_to_str tm F).

