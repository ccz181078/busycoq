(** The pair uses the repository's existing six-state binary context. *)
From BusyCoq Require Export BB62.
From BusyCoq.Eqv363470 Require Import BB92.
Notation state6 := BB62.state.
Notation A6 := BB62.A.
Notation B6 := BB62.B.
Notation C6 := BB62.C.
Notation D6 := BB62.D.
Notation E6 := BB62.E.
Notation F6 := BB62.F.
Module SourceCtx := BB62.BB62.
