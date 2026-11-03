(** * Instantiating the development to machines with unbounded states and symbols *)

From Coq Require Import Lists.List NArith. Import ListNotations.
From BusyCoq Require Export Flip.
From BusyCoq Require Import HashTable.
Set Default Goal Selector "!".

Module BBinf <: Ctx.
  Definition Q := N.
  Definition Sym := N.
  Definition q0 := 0%N.
  Definition q1 := 1%N.
  Definition s0 := 0%N.
  Definition s1 := 1%N.

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. discriminate. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
    decide equality.
    decide equality.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
    decide equality.
    decide equality.
  Defined.

  Definition q_eqb(a b:Q):bool:=N.eqb a b.

  Lemma q_eqb_spec a b:
    Bool.reflect (a=b) (q_eqb a b).
  Proof.
    apply N.eqb_spec.
  Qed.

  Definition sym_eqb(a b:Sym):bool:=N.eqb a b.

  Lemma sym_eqb_spec a b:
    Bool.reflect (a=b) (sym_eqb a b).
  Proof.
    apply N.eqb_spec.
  Qed.

  Import HashConcat.

  Definition q_hash(a:Q) := hash a.

  Definition sym_hash(a:Sym) := hash a.

  (* [Q] and [Sym] are [N]: infinite, so not enumerable. This context
     implements the base [Ctx] only. Upstream set [all_qs := []] and
     [Admitted] [all_qs_spec : forall a, In a []], which over an inhabited [Q]
     is a proof of [False] -- in the [core] hint database, and underneath the
     extracted decider via [Inductive_inf.v]. *)
End BBinf.


