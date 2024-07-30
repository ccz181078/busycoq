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


Ltac follow10 H :=
  eapply progress_evstep_trans; [ apply H; fail | idtac ].

Ltac follow100 H :=
  apply progress_evstep;
  follow10 H.

Ltac follow11 H :=
  eapply progress_trans; [ apply H; fail | idtac ].


Ltac steps := cbn; intros;
  repeat ((try apply evstep_refl); step).


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

Lemma evstep_multistep tm c c':
  c -[ tm ]->* c' ->
  exists n, c -[ tm ]->> n / c'.
Proof.
  intro H.
  induction H.
  - exists O.
    constructor.
  - destruct IHevstep as [n IH].
    exists (S n).
    econstructor; eauto.
Qed.


Lemma halts_evstep tm c c':
  halts tm c' ->
  c -[ tm ]->* c' -> halts tm c.
Proof.
  intros H H0.
  destruct (evstep_multistep _ _ _ H0) as [n H1].
  eapply halts_multistep; eauto.
Qed.

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