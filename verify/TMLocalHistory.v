From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From BusyCoq Require Export Flip.
From BusyCoq Require Import HashTable.
From BusyCoq Require Import QSymMap.
Set Default Goal Selector "!".

Module TMLocalHistoryCtx(Ctx0:Ctx) <: Ctx.
  Module TM0 := TM Ctx0.
  Import TM0.
  Definition Q:Type := Ctx0.Q.
  Definition Sym:Type := Ctx0.Sym*(list (Ctx0.Q*Ctx0.Sym)).
  Definition q0 := Ctx0.q0.
  Definition q1 := Ctx0.q1.
  Definition s0:Sym := (Ctx0.s0,[]).
  Definition s1:Sym := (Ctx0.s1,[]).

  Definition from(n:nat)(tm:TM0.TM):Q*Sym->(option (Sym*dir*Q)) :=
  fun '(s,(i0,i1)) =>
  match tm (s,i0) with
  | None => None
  | Some (o,d,s'') => Some ((o,firstn n ((s,i0)::i1)),d,s'')
  end.

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. apply Ctx0.q0_neq_q1. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. intros H. injection H as H1. exact (Ctx0.s0_neq_s1 H1). Qed.

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

  (* [Sym] is [Ctx0.Sym * list (Ctx0.Q*Ctx0.Sym)], whose list component is
     unbounded, so this context is genuinely not enumerable. It therefore
     implements the base [Ctx] only. Upstream instead kept it a full [Ctx] and
     [Admitted] the enumeration specs -- which, for the empty/undefined lists
     supplied, asserted [False]. *)
End TMLocalHistoryCtx.

Module TMLocalHistory(Ctx0:Ctx).
Module Ctx1 := TMLocalHistoryCtx Ctx0.
Module QSymMap := QSymMap Ctx0 Ctx1.
Export QSymMap.

Lemma from_nonhalt n tm:
  ~TM1.halts' (Ctx1.from n tm) TM1.c0 ->
  ~TM0.halts' tm TM0.c0.
Proof.
  apply QSymMap.from_nonhalt with (Fq:=fun x=>x) (Fsym:=fst).
  1,2: reflexivity.
  intros.
  unfold Ctx1.from.
  destruct s as [s h]; cbn.
  destruct (tm0 (q,s)) as [[[a b] c]|] eqn:E; trivial.
Qed.

End TMLocalHistory.


