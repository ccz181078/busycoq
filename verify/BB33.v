(** * Instantiating the development to machines with 3 states and 3 symbols *)

From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
From BusyCoq Require Import HashTable.
Set Default Goal Selector "!".

Inductive state := A | B | C.
Inductive sym := S0 | S1 | S2.

Module BB33 <: Ctx.
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
  | A,A | B,B | C,C => true
  | _,_ => false
  end.

  Lemma q_eqb_spec a b:
    Bool.reflect (a=b) (q_eqb a b).
  Proof.
    destruct a,b; cbn; constructor; congruence.
  Qed.

  Definition sym_eqb(a b:Sym):bool:=
  match a,b with
  | S0,S0 | S1,S1 | S2,S2 => true
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
  | A => hv1
  | B => hv2
  | C => hv3
  end.

  Definition sym_hash(a:sym) :=
  match a with
  | S0 => hv1
  | S1 => hv2
  | S2 => hv3
  end.
  Definition all_qs := [A; B; C].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1; S2].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB33.
