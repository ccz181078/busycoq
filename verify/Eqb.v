Require Import List.
Require Import ZArith.
From BusyCoq Require Import LibTactics.

Notation "x || y" := (if x then true else y) : bool_scope.
Notation "x && y" := (if x then y else false) : bool_scope.
Open Scope bool.

Lemma or_false_iff (a b:bool):
  (a || b) = false <->
  a = false /\ b = false.
Proof.
  destruct a,b; tauto.
Qed.

Lemma and_true_iff (a b:bool):
  (a && b) = true <->
  a = true /\ b = true.
Proof.
  destruct a,b; tauto.
Qed.

Definition if_Some{A B}(a:option A)(b:A->option B) :=
match a with
| Some a0 => b a0
| None => None
end.

Notation "a &&& b" := (if_Some a b) (at level 40, left associativity).

Ltac solve_Bool_reflect :=
  try (constructor; congruence).

Fixpoint list_eqb{T}(T_eqb:T->T->bool)(a b:list T):bool :=
match a,b with
| a0::a1,b0::b1 => (T_eqb a0 b0) && (list_eqb T_eqb a1 b1)
| nil,nil => true
| _,_ => false
end.

Lemma list_eqb_spec {T} T_eqb (a b:list T):
  (forall a0 b0, Bool.reflect (a0=b0) (T_eqb a0 b0)) ->
  Bool.reflect (a=b) (list_eqb T_eqb a b).
Proof.
  intro H.
  gen b.
  induction a as [|a0 a1]; intros b; destruct b as [|b0 b1]; cbn.
  all: solve_Bool_reflect.
  destruct (H a0 b0),(IHa1 b1); solve_Bool_reflect.
Qed.

Definition prod_eqb{A B}(A_eqb:A->A->bool)(B_eqb:B->B->bool)(a b:A*B):bool :=
match a,b with
| (a0,a1),(b0,b1) =>
  A_eqb a0 b0 && B_eqb a1 b1
end.

Lemma prod_eqb_spec{A B} A_eqb B_eqb (a b:A*B):
  (forall a0 b0, Bool.reflect (a0=b0) (A_eqb a0 b0)) ->
  (forall a0 b0, Bool.reflect (a0=b0) (B_eqb a0 b0)) ->
  Bool.reflect (a=b) (prod_eqb A_eqb B_eqb a b).
Proof.
  intros Ha Hb.
  destruct a as [a0 a1].
  destruct b as [b0 b1]; cbn.
  destruct (Ha a0 b0),(Hb a1 b1); solve_Bool_reflect.
Qed.

Definition sum_eqb{A B}(A_eqb:A->A->bool)(B_eqb:B->B->bool)(a b:A+B):bool :=
match a,b with
| inl a0,inl b0 =>
  A_eqb a0 b0
| inr a1,inr b1 =>
  B_eqb a1 b1
| _,_ => false
end.

Lemma sum_eqb_spec{A B} A_eqb B_eqb (a b:A+B):
  (forall a0 b0, Bool.reflect (a0=b0) (A_eqb a0 b0)) ->
  (forall a0 b0, Bool.reflect (a0=b0) (B_eqb a0 b0)) ->
  Bool.reflect (a=b) (sum_eqb A_eqb B_eqb a b).
Proof.
  intros Ha Hb.
  destruct a,b; solve_Bool_reflect; unfold sum_eqb.
  - destruct (Ha a a0); solve_Bool_reflect.
  - destruct (Hb b0 b); solve_Bool_reflect.
Qed.

Definition option_eqb{A}(A_eqb:A->A->bool)(a b:option A):bool :=
match a,b with
| Some a0,Some b0 =>
  A_eqb a0 b0
| None,None => true
| _,_ => false
end.

Lemma option_eqb_spec{A} A_eqb (a b:option A):
  (forall a0 b0, Bool.reflect (a0=b0) (A_eqb a0 b0)) ->
  Bool.reflect (a=b) (option_eqb A_eqb a b).
Proof.
  intros Ha.
  destruct a,b; cbn; solve_Bool_reflect.
  destruct (Ha a a0); solve_Bool_reflect.
Qed.

Class Eqb A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y, Bool.reflect (x=y) (eqb x y)
}.

#[export] Instance List_eqb A:
  Eqb A ->
  Eqb (list A).
Proof.
  intro H.
  unshelve esplit.
  - apply list_eqb,eqb.
  - intros. apply list_eqb_spec,eqb_spec.
Defined.

#[export] Instance Prod_eqb A B:
  Eqb A ->
  Eqb B ->
  Eqb (A*B).
Proof.
  intros HA HB.
  unshelve esplit.
  - apply prod_eqb; apply eqb.
  - intros; apply prod_eqb_spec; apply eqb_spec.
Defined.

#[export] Instance Sum_eqb A B:
  Eqb A ->
  Eqb B ->
  Eqb (A+B).
Proof.
  intros HA HB.
  unshelve esplit.
  - apply sum_eqb; apply eqb.
  - intros; apply sum_eqb_spec; apply eqb_spec.
Defined.

#[export] Instance Option_eqb A:
  Eqb A ->
  Eqb (option A).
Proof.
  intros HA.
  unshelve esplit.
  - apply option_eqb; apply eqb.
  - intros; apply option_eqb_spec; apply eqb_spec.
Defined.

#[export] Instance Nat_eqb: Eqb nat := Build_Eqb _ Nat.eqb Nat.eqb_spec.

#[export] Instance Pos_eqb: Eqb positive := Build_Eqb _ Pos.eqb Pos.eqb_spec.

#[export] Instance N_eqb: Eqb N := Build_Eqb _ N.eqb N.eqb_spec.

#[export] Instance Z_eqb: Eqb Z := Build_Eqb _ Z.eqb Z.eqb_spec.

#[export] Instance bool_Eqb: Eqb bool := Build_Eqb _ Bool.eqb Bool.eqb_spec.

Fixpoint Pos_iter_until{S S'}(f:S->S+S')(x:S+S')(T:positive):S+S' :=
match x with
| inl s =>
  match T with
  | xH => f s
  | xO T0 => Pos_iter_until f (Pos_iter_until f x T0) T0
  | xI T0 => Pos_iter_until f (Pos_iter_until f (f s) T0) T0
  end
| _ => x
end.

Definition N_iter_until{S S'}(f:S->S+S')(x:S+S')(T:N):S+S' :=
match T with
| N0 => x
| Npos T0 => Pos_iter_until f x T0
end.

Lemma N_iter_until_spec{S S'}{f:S->S+S'}{x:S+S'}{T:N}(P:S->Prop)(P':S'->Prop):
(forall x0:S, P x0 ->
match f x0 with
| inl x1 => P x1
| inr x1 => P' x1
end) ->
(match x with
| inl x1 => P x1
| inr x1 => P' x1
end) ->
match N_iter_until f x T with
| inl x1 => P x1
| inr x1 => P' x1
end.
Proof.
  intros H.
  destruct T as [|T].
  1: cbn; tauto.
  cbn.
  gen x.
  induction T; intros x Hx; cbn.
  - destruct x.
    + apply IHT,IHT,H,Hx.
    + apply Hx.
  - destruct x.
    + apply IHT,IHT,Hx.
    + apply Hx.
  - destruct x.
    + apply H,Hx.
    + apply Hx.
Qed.
