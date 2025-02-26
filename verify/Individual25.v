From BusyCoq Require Export Individual BB25.
Require Import Ascii.
Require Import String.

Module Individual25 := Individual BB25.
Export Individual25.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.
Notation "2" := S2 : sym_scope.
Notation "3" := S3 : sym_scope.
Notation "4" := S4 : sym_scope.

(* Make sure that [{{A}}>] still refers to the state, even if we shadowed
   [A] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).

Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).

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
    rewrite List.length_app,IHn.
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
    | _ => idtac "fail2"; fail
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

Ltac es :=
  intros;
  unfold_config;
  repeat
  (rewrite lpow_add ||
  rewrite Str_app_assoc ||
  rewrite lpow_mul);
  simpl_tape;
  execute_with_shift_rule.

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].
Definition Sym_from_char(x:ascii):option Sym :=
match x with
| "0"%char => Some S0
| "1"%char => Some S1
| "2"%char => Some S2
| "3"%char => Some S3
| "4"%char => Some S4
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

Definition Q_from_str(x:string) :=
  let (x,A0):=trans_from_str x in
  let (x,A1):=trans_from_str x in
  let (x,A2):=trans_from_str x in
  let (x,A3):=trans_from_str x in
  let (x,A4):=trans_from_str x in
  let x:=skip_sep x in
  (x,A0,A1,A2,A3,A4).

Definition TM_from_str(x:string):TM :=
  let '(x,A0,A1,A2,A3,A4):=Q_from_str x in
  let '(x,B0,B1,B2,B3,B4):=Q_from_str x in
  fun '(q,s) =>
  match q,s with
  | A,0 => A0  | A,1 => A1 | A,2 => A2 | A,3 => A3 | A,4 => A4
  | B,0 => B0  | B,1 => B1 | B,2 => B2 | B,3 => B3 | B,4 => B4
  end.

Definition Sym_to_str(x:Sym):string :=
match x with
| S0 => "0"
| S1 => "1"
| S2 => "2"
| S3 => "3"
| S4 => "4"
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
end.

Definition Trans_to_str(x:option (Sym*dir*Q)):string :=
match x with
| None => "---"
| Some (o,d,s) => (Sym_to_str o) ++ (dir_to_str d) ++ (Q_to_str s)
end.

Definition TM_Q_to_str(tm:TM)(q:Q):string :=
  (Trans_to_str (tm (q,S0))) ++
  (Trans_to_str (tm (q,S1))) ++
  (Trans_to_str (tm (q,S2))) ++
  (Trans_to_str (tm (q,S3))) ++
  (Trans_to_str (tm (q,S4))).

Definition TM_to_str(tm:TM):string :=
  (TM_Q_to_str tm A) ++ "_" ++
  (TM_Q_to_str tm B).

