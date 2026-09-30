From BusyCoq.Eqv363470 Require Import BB92.
From BusyCoq Require Import CTL.
From Coq Require Import List NArith ZArith. Import ListNotations. Require Uint63.
Module Guard := CTLDecider BB92.
Open Scope N_scope.
Definition monitor_guard_tm : Guard.DHTMFromTM.TM.TM :=
  fun '(q,s) => match q,s with
  | A92,S092 => Some (S192,R,B92)
  | A92,S192 => Some (S192,L,C92)
  | B92,S092 => Some (S192,L,C92)
  | B92,S192 => Some (S092,R,G92)
  | C92,S092 => Some (S092,L,E92)
  | C92,S192 => Some (S192,L,A92)
  | D92,S092 => Some (S092,R,F92)
  | D92,S192 => Some (S192,R,A92)
  | E92,S092 => Some (S192,R,D92)
  | E92,S192 => Some (S092,L,A92)
  | F92,S092 => Some (S092,R,I92)
  | F92,S192 => Some (S092,R,B92)
  | G92,S092 => Some (S092,R,H92)
  | G92,S192 => Some (S192,R,A92)
  | H92,S092 => Some (S092,R,I92)
  | H92,S192 => None
  | I92,S092 => Some (S092,R,I92)
  | I92,S192 => Some (S192,R,I92)
  end.
Definition binary_sym_id (s:sym92) : Uint63.int :=
  match s with S092 => Uint63.of_Z 0%Z | S192 => Uint63.of_Z 1%Z end.
Definition guard_parameters := Guard.MITMDFA 10000 10000
  [0;1;2;1;0;3;2;3]
  [0;1;2;1;0;3;4;5;6;6;6;1;6;6]
  binary_sym_id (Uint63.of_Z 2%Z).
Lemma monitor_guard_decides : Guard.decide_nonhalt monitor_guard_tm guard_parameters = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions monitor_guard_decides.
