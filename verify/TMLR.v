From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From BusyCoq Require Export Flip.
From BusyCoq Require Import HashTable.
From BusyCoq Require Import QSymMap.
Set Default Goal Selector "!".

Module TMLRCtx(Ctx0:FiniteCtx) <: FiniteCtx.
  Module TM0 := TM Ctx0.
  Import TM0.
  Definition Q:Type := Ctx0.Q*dir*dir.
  Definition Sym:Type := Ctx0.Sym*dir.
  Definition q0 := (Ctx0.q0,R,R).
  Definition q1 := (Ctx0.q1,R,R).
  Definition s0 := (Ctx0.s0,L).
  Definition s1 := (Ctx0.s1,R).

  Definition from(tm:TM0.TM):Q*Sym->(option (Sym*dir*Q)) :=
  fun '((q,tp,d),(s,tp')) =>
  match tm (q,s) with
  | None => None
  | Some (o,d',s') =>
    let tp:=(if (negb (dir_eqb tp d) && dir_eqb d tp')%bool then d else tp) in
    Some ((o,tp),d',(s',tp,d'))
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

  Definition q_hash(a:Q) :=
  let '(a0,a1,a2):=a in Ctx0.q_hash a0 ## hash a1 ## hash a2.

  Definition sym_hash(a:Sym) :=
  let '(a0,a1):=a in Ctx0.sym_hash a0 ## hash a1.

  (* [Q] and [Sym] are finite whenever [Ctx0] is: both just pair [Ctx0]'s
     carriers with [dir], which has two elements. Upstream admitted all four
     of these; they are constructible and provable. *)
  Definition all_dirs : list dir := [L; R].

  Lemma all_dirs_spec : forall d, In d all_dirs.
  Proof. intros d. destruct d; simpl; tauto. Qed.

  Definition all_qs:list Q :=
    list_prod (list_prod Ctx0.all_qs all_dirs) all_dirs.

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    intros [[q d1] d2]. unfold all_qs.
    apply in_prod.
    - apply in_prod.
      + apply Ctx0.all_qs_spec.
      + apply all_dirs_spec.
    - apply all_dirs_spec.
  Qed.

  Definition all_syms:list Sym := list_prod Ctx0.all_syms all_dirs.

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    intros [s d]. unfold all_syms.
    apply in_prod.
    - apply Ctx0.all_syms_spec.
    - apply all_dirs_spec.
  Qed.
End TMLRCtx.

Module TMLR(Ctx0:FiniteCtx).
Module Ctx1 := TMLRCtx Ctx0.
Module QSymMap := QSymMap Ctx0 Ctx1.
Export QSymMap.

Definition Fq(x:Ctx1.Q):Ctx0.Q :=
let '(q,_,_):=x in q.

Definition Fsym(x:Ctx1.Sym):Ctx0.Sym :=
let '(s,_):=x in s.

Lemma from_nonhalt tm:
  ~TM1.halts' (Ctx1.from tm) TM1.c0 ->
  ~TM0.halts' tm TM0.c0.
Proof.
  apply QSymMap.from_nonhalt with (Fq:=Fq) (Fsym:=Fsym).
  1,2: reflexivity.
  intros.
  unfold Ctx1.from.
  destruct q as [[q0 tp] d].
  destruct s as [s0 tp'].
  cbn.
  destruct (tm0 (q0,s0)) as [[[a b] c]|]; trivial.
Qed.

End TMLR.

