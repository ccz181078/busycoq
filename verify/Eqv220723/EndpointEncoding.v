(* Literal source-table binding, using the same canonical encoding as
   bridge363/EndpointBinding.v, without importing its pair theorem. *)
From Coq Require Import String Ascii.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
Close Scope sym_scope.
Open Scope nat_scope.

Open Scope string_scope.

Definition state6_char (q : state6) : ascii :=
  match q with A6 => "A"%char | B6 => "B"%char | C6 => "C"%char |
               D6 => "D"%char | E6 => "E"%char | F6 => "F"%char end.
Definition binary_char (s : sym92) : ascii :=
  match s with S092 => "0"%char | S192 => "1"%char end.
Definition move_char (d : dir) : ascii := match d with L => "L"%char | R => "R"%char end.
Definition cell_string (tr : option (sym92 * dir * state6)) : string :=
  match tr with None => "---" | Some (s,d,q) =>
    String (binary_char s) (String (move_char d) (String (state6_char q) EmptyString)) end.
Definition row_string (tm : RI.TM) q :=
  cell_string (tm (q,S092)) ++ cell_string (tm (q,S192)).
Definition machine_string (tm : RI.TM) :=
  row_string tm A6 ++ "_" ++ row_string tm B6 ++ "_" ++ row_string tm C6 ++ "_" ++
  row_string tm D6 ++ "_" ++ row_string tm E6 ++ "_" ++ row_string tm F6.
