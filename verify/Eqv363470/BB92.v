(** * Instantiating the development to machines with 9 states and 2 symbols *)

From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export TM.
From BusyCoq Require Import BB62.
From BusyCoq Require Import HashTable.
Set Default Goal Selector "!".

Inductive state92 := A92 | B92 | C92 | D92 | E92 | F92 | G92 | H92 | I92.
Notation sym92 := BB62.sym.
Notation S092 := BB62.S0.
Notation S192 := BB62.S1.

Module BB92 <: Ctx.
  Definition Q := state92.
  Definition Sym := sym92.
  Definition q0 := A92.
  Definition q1 := B92.
  Definition s0 := S092.
  Definition s1 := S192.

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. discriminate. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition q_eqb(a b:Q):bool:=
  match a,b with
  | A92,A92 | B92,B92 | C92,C92 | D92,D92 | E92,E92 | F92,F92 | G92,G92 | H92,H92 | I92,I92 => true
  | _,_ => false
  end.

  Lemma q_eqb_spec a b:
    Bool.reflect (a=b) (q_eqb a b).
  Proof.
    destruct a,b; cbn; constructor; congruence.
  Qed.

  Definition sym_eqb(a b:Sym):bool:=
  match a,b with
  | S092,S092 | S192,S192 => true
  | _,_ => false
  end.

  Lemma sym_eqb_spec a b:
    Bool.reflect (a=b) (sym_eqb a b).
  Proof.
    destruct a,b; cbn; constructor; congruence.
  Qed.

  Import HashConcat.

  Definition q_hash(a:Q) :=
  match a with
  | A92 => hv1
  | B92 => hv2
  | C92 => hv3
  | D92 => hv4
  | E92 => hv5
  | F92 => hv6
  | G92 => hv7
  | H92 => hv8
  | I92 => hv9
  end.

  Definition sym_hash(a:sym92) :=
  match a with
  | S092 => hv1
  | S192 => hv2
  end.

  Definition all_qs := [A92; B92; C92; D92; E92; F92; G92; H92; I92].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S092; S192].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB92.
