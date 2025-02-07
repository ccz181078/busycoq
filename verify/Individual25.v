From BusyCoq Require Export Individual BB25.
Require Import Ascii.
Require Import String.

Module Individual25 := Individual BB25.
Export Individual25.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.
Notation "2" := S2 : sym_scope.
Notation "3" := S3 : sym_scope.
Notation "4" := S4 : sym_scope.

(* Make sure that [{{A}}>] still refers to the state, even if we shadowed
   [A] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).

Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).

Definition Sym_from_char(x:ascii):option Sym :=
match x with
| "0"%char => Some S0
| "1"%char => Some S1
| "2"%char => Some S2
| "3"%char => Some S3
| "4"%char => Some S4
| _ => None
end.

Definition dir_from_char(x:ascii):option dir :=
match x with
| "L"%char => Some L
| "R"%char => Some R
| _ => None
end.

Definition Q_from_char(x:ascii):option Q :=
match x with
| "A"%char => Some A
| "B"%char => Some B
| _ => None
end.

Definition trans_from_char(c0 c1 c2:ascii):option (Sym * dir * Q) :=
  match (Sym_from_char c0),(dir_from_char c1),(Q_from_char c2) with
  | Some o, Some d, Some s => Some (o,d,s)
  | _,_,_ => None
  end.

Definition trans_from_str(x:string): string*(option (Sym * dir * Q)) :=
match x with
| (String c0 (String c1 (String c2 x0))) =>
  (x0,trans_from_char c0 c1 c2)
| _ => (x,None)
end.

Definition skip_sep(x:string): string :=
match x with
| String ("_"%char) x0 => x0
| _ => x
end.

Definition Q_from_str(x:string) :=
  let (x,A0):=trans_from_str x in
  let (x,A1):=trans_from_str x in
  let (x,A2):=trans_from_str x in
  let (x,A3):=trans_from_str x in
  let (x,A4):=trans_from_str x in
  let x:=skip_sep x in
  (x,A0,A1,A2,A3,A4).

Definition TM_from_str(x:string):TM :=
  let '(x,A0,A1,A2,A3,A4):=Q_from_str x in
  let '(x,B0,B1,B2,B3,B4):=Q_from_str x in
  fun '(q,s) =>
  match q,s with
  | A,0 => A0  | A,1 => A1 | A,2 => A2 | A,3 => A3 | A,4 => A4
  | B,0 => B0  | B,1 => B1 | B,2 => B2 | B,3 => B3 | B,4 => B4
  end.

Definition Sym_to_str(x:Sym):string :=
match x with
| S0 => "0"
| S1 => "1"
| S2 => "2"
| S3 => "3"
| S4 => "4"
end.

Definition dir_to_str(x:dir):string :=
match x with
| L => "L"
| R => "R"
end.

Definition Q_to_str(x:Q):string :=
match x with
| A => "A"
| B => "B"
end.

Definition Trans_to_str(x:option (Sym*dir*Q)):string :=
match x with
| None => "---"
| Some (o,d,s) => (Sym_to_str o) ++ (dir_to_str d) ++ (Q_to_str s)
end.

Definition TM_Q_to_str(tm:TM)(q:Q):string :=
  (Trans_to_str (tm (q,S0))) ++
  (Trans_to_str (tm (q,S1))) ++
  (Trans_to_str (tm (q,S2))) ++
  (Trans_to_str (tm (q,S3))) ++
  (Trans_to_str (tm (q,S4))).

Definition TM_to_str(tm:TM):string :=
  (TM_Q_to_str tm A) ++ "_" ++
  (TM_Q_to_str tm B).

