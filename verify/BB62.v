(** * Instantiating the development to machines with 6 states and 2 symbols *)

From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Inductive state := A | B | C | D | E | F.
Inductive sym := S0 | S1.

Module BB62 <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := A.
  Definition q1 := B.
  Definition s0 := S0.
  Definition s1 := S1.

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
  | A,A | B,B | C,C | D,D | E,E | F,F => true
  | _,_ => false
  end.

  Lemma q_eqb_spec a b:
    Bool.reflect (a=b) (q_eqb a b).
  Proof.
    destruct a,b; cbn; constructor; congruence.
  Qed.

  Definition sym_eqb(a b:Sym):bool:=
  match a,b with
  | S0,S0 | S1,S1 => true
  | _,_ => false
  end.

  Lemma sym_eqb_spec a b:
    Bool.reflect (a=b) (sym_eqb a b).
  Proof.
    destruct a,b; cbn; constructor; congruence.
  Qed.

  Definition all_qs := [A; B; C; D; E; F].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB62.
