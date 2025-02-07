From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From BusyCoq Require Export Flip.
From BusyCoq Require Import HashTable.
From BusyCoq Require Import QSymMap.
Set Default Goal Selector "!".

Module TMAddOneSymbolCtx(Ctx0:Ctx) <: Ctx.
  Module TM0 := TM Ctx0.
  Import TM0.
  Definition Q:Type := Ctx0.Q.
  Definition Sym:Type := option Ctx0.Sym.
  Definition q0 := Ctx0.q0.
  Definition q1 := Ctx0.q1.
  Definition s0:Sym := None.
  Definition s1 := Some Ctx0.s1.

  Definition from(tm:TM0.TM):Q*Sym->(option (Sym*dir*Q)) :=
  fun '(q,s) =>
  let s' :=
  match s with
  | None => Ctx0.s0
  | Some s' => s'
  end in
  match tm (q,s') with
  | None => None
  | Some (o,d,s'') => Some (Some o,d,s'')
  end.

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. cbv. intros. inverts H. apply Ctx0.q0_neq_q1,H1. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
  destruct (eqb_spec a b); tauto.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
  destruct (eqb_spec a b); tauto.
  Defined.

  Definition q_eqb(a b:Q):bool :=
  eqb a b.

  Definition q_eqb_spec a b:
    Bool.reflect (a=b) (q_eqb a b) := eqb_spec a b.

  Definition sym_eqb(a b:Sym):bool :=
    eqb a b.

  Definition sym_eqb_spec a b:
    Bool.reflect (a=b) (sym_eqb a b) :=
    eqb_spec a b.

  Import HashConcat.

  Definition q_hash(a:Q) := hash a.

  Definition sym_hash(a:Sym) := hash a.

  Definition all_qs:list Q := Ctx0.all_qs.

  Lemma all_qs_spec : forall a, In a all_qs.
  Admitted.

  Definition all_syms:list Sym := [None]++(List.map Some Ctx0.all_syms).

  Lemma all_syms_spec : forall a, In a all_syms.
  Admitted.
End TMAddOneSymbolCtx.

Module TMAddOneSymbol(Ctx0:Ctx).
Module Ctx1 := TMAddOneSymbolCtx Ctx0.
Module QSymMap := QSymMap Ctx0 Ctx1.
Export QSymMap.

Definition Fsym(x:Ctx1.Sym):Ctx0.Sym :=
  match x with
  | Some x0 => x0
  | None => Ctx0.s0
  end.

Lemma from_nonhalt tm:
  ~TM1.halts' (Ctx1.from tm) TM1.c0 ->
  ~TM0.halts' tm TM0.c0.
Proof.
  apply QSymMap.from_nonhalt with (Fq:=fun x=>x) (Fsym:=Fsym).
  1,2: reflexivity.
  intros.
  unfold Ctx1.from.
  destruct s as [s|]; cbn.
  - destruct (tm0 (q,s)) as [[[a b] c]|] eqn:E; trivial.
  - destruct (tm0 (q,Ctx0.s0)) as [[[a b] c]|] eqn:E; trivial.
Qed.

End TMAddOneSymbol.

