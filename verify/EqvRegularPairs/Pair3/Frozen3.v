(* Generated literal data; see generate.py and input_binding.json. *)
From Coq Require Import Lists.List String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition frozen3 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S092, L, C6)
| (B6, S092) => Some (S192, L, A6)
| (B6, S192) => Some (S192, R, F6)
| (C6, S092) => Some (S192, L, D6)
| (C6, S192) => Some (S192, R, F6)
| (D6, S092) => Some (S192, L, E6)
| (D6, S192) => Some (S092, L, A6)
| (E6, S092) => Some (S092, R, B6)
| (E6, S192) => None
| (F6, S092) => Some (S092, R, A6)
| (F6, S192) => Some (S192, R, E6)
end.

Definition mapped751 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S092, L, C6)
| (B6, S092) => Some (S192, L, A6)
| (B6, S192) => Some (S192, R, F6)
| (C6, S092) => Some (S192, L, D6)
| (C6, S192) => Some (S192, R, F6)
| (D6, S092) => Some (S192, R, F6)
| (D6, S192) => Some (S092, L, A6)
| (E6, S092) => Some (S092, R, B6)
| (E6, S192) => None
| (F6, S092) => Some (S092, R, A6)
| (F6, S192) => Some (S192, R, E6)
end.

Definition original751 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S092, L, C6)
| (B6, S092) => Some (S192, L, A6)
| (B6, S192) => Some (S192, R, E6)
| (C6, S092) => Some (S192, L, D6)
| (C6, S192) => Some (S192, R, E6)
| (D6, S092) => Some (S192, R, E6)
| (D6, S192) => Some (S092, L, A6)
| (E6, S092) => Some (S092, R, A6)
| (E6, S192) => Some (S192, R, F6)
| (F6, S092) => Some (S092, R, B6)
| (F6, S192) => None
end.

Definition frozen3_delta : DFA := fun p b =>
  let row := match p with
  | 0 => (0, 1)
  | 1 => (2, 3)
  | 2 => (4, 5)
  | 3 => (2, 3)
  | 4 => (4, 6)
  | 5 => (2, 7)
  | 6 => (8, 9)
  | 7 => (2, 7)
  | 8 => (4, 6)
  | 9 => (8, 9)
  | _ => (0,0)
  end in match b with S092 => fst row | S192 => snd row end.

Definition frozen3_invariant : list entry := [
  E A6 S092 0 0;
  E A6 S092 0 2;
  E A6 S092 0 8;
  E A6 S092 1 1;
  E A6 S092 1 2;
  E A6 S092 1 3;
  E A6 S092 1 5;
  E A6 S092 1 6;
  E A6 S092 1 7;
  E A6 S092 1 8;
  E A6 S092 1 9;
  E A6 S092 2 0;
  E A6 S092 2 1;
  E A6 S092 2 2;
  E A6 S092 2 3;
  E A6 S092 2 4;
  E A6 S092 2 5;
  E A6 S092 2 6;
  E A6 S092 2 7;
  E A6 S092 2 8;
  E A6 S092 2 9;
  E A6 S092 3 1;
  E A6 S092 3 2;
  E A6 S092 3 3;
  E A6 S092 3 5;
  E A6 S092 3 6;
  E A6 S092 3 7;
  E A6 S092 3 8;
  E A6 S092 3 9;
  E A6 S092 5 1;
  E A6 S092 5 2;
  E A6 S092 5 3;
  E A6 S092 5 5;
  E A6 S092 5 6;
  E A6 S092 5 7;
  E A6 S092 5 8;
  E A6 S092 5 9;
  E A6 S092 7 1;
  E A6 S092 7 2;
  E A6 S092 7 3;
  E A6 S092 7 5;
  E A6 S092 7 6;
  E A6 S092 7 7;
  E A6 S092 7 8;
  E A6 S092 7 9;
  E A6 S192 0 1;
  E A6 S192 0 2;
  E A6 S192 0 3;
  E A6 S192 0 7;
  E A6 S192 0 8;
  E A6 S192 0 9;
  E A6 S192 1 2;
  E A6 S192 1 3;
  E A6 S192 1 7;
  E A6 S192 1 8;
  E A6 S192 1 9;
  E A6 S192 2 0;
  E A6 S192 2 1;
  E A6 S192 2 2;
  E A6 S192 2 3;
  E A6 S192 2 4;
  E A6 S192 2 5;
  E A6 S192 2 6;
  E A6 S192 2 7;
  E A6 S192 2 8;
  E A6 S192 2 9;
  E A6 S192 3 2;
  E A6 S192 3 3;
  E A6 S192 3 7;
  E A6 S192 3 8;
  E A6 S192 3 9;
  E A6 S192 5 2;
  E A6 S192 5 3;
  E A6 S192 5 7;
  E A6 S192 5 8;
  E A6 S192 5 9;
  E A6 S192 7 2;
  E A6 S192 7 3;
  E A6 S192 7 7;
  E A6 S192 7 8;
  E A6 S192 7 9;
  E B6 S092 1 0;
  E B6 S092 1 1;
  E B6 S092 1 3;
  E B6 S092 1 5;
  E B6 S092 1 6;
  E B6 S092 1 7;
  E B6 S092 1 9;
  E B6 S092 2 0;
  E B6 S092 2 1;
  E B6 S092 2 2;
  E B6 S092 2 3;
  E B6 S092 2 4;
  E B6 S092 2 5;
  E B6 S092 2 6;
  E B6 S092 2 7;
  E B6 S092 2 8;
  E B6 S092 2 9;
  E B6 S092 3 1;
  E B6 S092 3 3;
  E B6 S092 3 5;
  E B6 S092 3 6;
  E B6 S092 3 7;
  E B6 S092 3 9;
  E B6 S092 5 0;
  E B6 S092 5 1;
  E B6 S092 5 2;
  E B6 S092 5 3;
  E B6 S092 5 4;
  E B6 S092 5 5;
  E B6 S092 5 6;
  E B6 S092 5 7;
  E B6 S092 5 8;
  E B6 S092 5 9;
  E B6 S092 7 1;
  E B6 S092 7 3;
  E B6 S092 7 5;
  E B6 S092 7 6;
  E B6 S092 7 7;
  E B6 S092 7 9;
  E B6 S192 0 5;
  E B6 S192 0 6;
  E B6 S192 0 7;
  E B6 S192 0 9;
  E B6 S192 2 0;
  E B6 S192 2 1;
  E B6 S192 2 2;
  E B6 S192 2 3;
  E B6 S192 2 4;
  E B6 S192 2 5;
  E B6 S192 2 6;
  E B6 S192 2 7;
  E B6 S192 2 8;
  E B6 S192 2 9;
  E B6 S192 3 0;
  E B6 S192 3 1;
  E B6 S192 3 2;
  E B6 S192 3 3;
  E B6 S192 3 4;
  E B6 S192 3 5;
  E B6 S192 3 6;
  E B6 S192 3 7;
  E B6 S192 3 8;
  E B6 S192 3 9;
  E B6 S192 5 0;
  E B6 S192 5 1;
  E B6 S192 5 2;
  E B6 S192 5 3;
  E B6 S192 5 4;
  E B6 S192 5 5;
  E B6 S192 5 6;
  E B6 S192 5 7;
  E B6 S192 5 8;
  E B6 S192 5 9;
  E B6 S192 7 0;
  E B6 S192 7 1;
  E B6 S192 7 2;
  E B6 S192 7 3;
  E B6 S192 7 4;
  E B6 S192 7 5;
  E B6 S192 7 6;
  E B6 S192 7 7;
  E B6 S192 7 8;
  E B6 S192 7 9;
  E C6 S092 0 2;
  E C6 S092 0 4;
  E C6 S092 0 8;
  E C6 S092 1 0;
  E C6 S092 1 2;
  E C6 S092 1 4;
  E C6 S092 1 8;
  E C6 S092 3 0;
  E C6 S092 3 2;
  E C6 S092 3 4;
  E C6 S092 3 8;
  E C6 S092 5 0;
  E C6 S092 5 2;
  E C6 S092 5 4;
  E C6 S092 5 8;
  E C6 S092 7 0;
  E C6 S092 7 2;
  E C6 S092 7 4;
  E C6 S092 7 8;
  E C6 S192 0 2;
  E C6 S192 0 4;
  E C6 S192 0 8;
  E C6 S192 1 2;
  E C6 S192 1 4;
  E C6 S192 1 8;
  E C6 S192 2 2;
  E C6 S192 2 4;
  E C6 S192 2 8;
  E C6 S192 3 2;
  E C6 S192 3 4;
  E C6 S192 3 8;
  E C6 S192 5 2;
  E C6 S192 5 4;
  E C6 S192 5 8;
  E C6 S192 7 2;
  E C6 S192 7 4;
  E C6 S192 7 8;
  E D6 S092 0 5;
  E D6 S092 0 6;
  E D6 S192 0 1;
  E D6 S192 0 5;
  E D6 S192 0 6;
  E D6 S192 1 1;
  E D6 S192 1 5;
  E D6 S192 1 6;
  E D6 S192 2 1;
  E D6 S192 2 5;
  E D6 S192 2 6;
  E D6 S192 3 1;
  E D6 S192 3 5;
  E D6 S192 3 6;
  E D6 S192 5 1;
  E D6 S192 5 5;
  E D6 S192 5 6;
  E D6 S192 7 1;
  E D6 S192 7 5;
  E D6 S192 7 6;
  E E6 S092 0 7;
  E E6 S092 0 9;
  E E6 S092 3 0;
  E E6 S092 3 1;
  E E6 S092 3 2;
  E E6 S092 3 3;
  E E6 S092 3 4;
  E E6 S092 3 5;
  E E6 S092 3 6;
  E E6 S092 3 7;
  E E6 S092 3 8;
  E E6 S092 3 9;
  E E6 S092 7 0;
  E E6 S092 7 1;
  E E6 S092 7 2;
  E E6 S092 7 3;
  E E6 S092 7 4;
  E E6 S092 7 5;
  E E6 S092 7 6;
  E E6 S092 7 7;
  E E6 S092 7 8;
  E E6 S092 7 9;
  E E6 S192 3 0;
  E E6 S192 3 1;
  E E6 S192 3 2;
  E E6 S192 3 3;
  E E6 S192 3 4;
  E E6 S192 3 5;
  E E6 S192 3 6;
  E E6 S192 3 7;
  E E6 S192 3 8;
  E E6 S192 3 9;
  E E6 S192 7 0;
  E E6 S192 7 1;
  E E6 S192 7 2;
  E E6 S192 7 3;
  E E6 S192 7 4;
  E E6 S192 7 5;
  E E6 S192 7 6;
  E E6 S192 7 7;
  E E6 S192 7 8;
  E E6 S192 7 9;
  E F6 S092 1 1;
  E F6 S092 1 2;
  E F6 S092 1 3;
  E F6 S092 1 4;
  E F6 S092 1 5;
  E F6 S092 1 6;
  E F6 S092 1 7;
  E F6 S092 1 8;
  E F6 S092 1 9;
  E F6 S092 3 0;
  E F6 S092 3 1;
  E F6 S092 3 2;
  E F6 S092 3 3;
  E F6 S092 3 4;
  E F6 S092 3 5;
  E F6 S092 3 6;
  E F6 S092 3 7;
  E F6 S092 3 8;
  E F6 S092 3 9;
  E F6 S092 5 0;
  E F6 S092 5 1;
  E F6 S092 5 2;
  E F6 S092 5 3;
  E F6 S092 5 4;
  E F6 S092 5 5;
  E F6 S092 5 6;
  E F6 S092 5 7;
  E F6 S092 5 8;
  E F6 S092 5 9;
  E F6 S092 7 0;
  E F6 S092 7 1;
  E F6 S092 7 2;
  E F6 S092 7 3;
  E F6 S092 7 4;
  E F6 S092 7 5;
  E F6 S092 7 6;
  E F6 S092 7 7;
  E F6 S092 7 8;
  E F6 S092 7 9;
  E F6 S192 1 2;
  E F6 S192 1 4;
  E F6 S192 1 5;
  E F6 S192 1 6;
  E F6 S192 1 7;
  E F6 S192 1 8;
  E F6 S192 1 9;
  E F6 S192 3 0;
  E F6 S192 3 1;
  E F6 S192 3 2;
  E F6 S192 3 3;
  E F6 S192 3 4;
  E F6 S192 3 5;
  E F6 S192 3 6;
  E F6 S192 3 7;
  E F6 S192 3 8;
  E F6 S192 3 9;
  E F6 S192 5 0;
  E F6 S192 5 1;
  E F6 S192 5 2;
  E F6 S192 5 3;
  E F6 S192 5 4;
  E F6 S192 5 5;
  E F6 S192 5 6;
  E F6 S192 5 7;
  E F6 S192 5 8;
  E F6 S192 5 9;
  E F6 S192 7 0;
  E F6 S192 7 1;
  E F6 S192 7 2;
  E F6 S192 7 3;
  E F6 S192 7 4;
  E F6 S192 7 5;
  E F6 S192 7 6;
  E F6 S192 7 7;
  E F6 S192 7 8;
  E F6 S192 7 9
].

Theorem frozen3_literal_binding : machine_string frozen3 = "1RB0LC_1LA1RF_1LD1RF_1LE0LA_0RB---_0RA1RE"%string.
Proof. reflexivity. Qed.

Theorem mapped751_literal_binding : machine_string mapped751 = "1RB0LC_1LA1RF_1LD1RF_1RF0LA_0RB---_0RA1RE"%string.
Proof. reflexivity. Qed.

Theorem original751_literal_binding : machine_string original751 = "1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---"%string.
Proof. reflexivity. Qed.

Example frozen3_invariant_size : List.length frozen3_invariant = 339.
Proof. reflexivity. Qed.
Example frozen3_terminal_entries : List.length (filter (fun a =>
  match frozen3 (control a,scanned a) with None => true | Some _ => false end) frozen3_invariant) = 20.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen3_check : check frozen3 10 frozen3_delta frozen3_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen3_reachable_invariant : forall c, RI.evstep frozen3 RI.c0 c ->
  represented frozen3_delta frozen3_invariant c.
Proof. apply (check_reachable_invariant _ _ _ _ frozen3_check). Qed.

Print Assumptions frozen3_literal_binding.
Print Assumptions mapped751_literal_binding.
Print Assumptions original751_literal_binding.
Print Assumptions frozen3_check.
Print Assumptions frozen3_reachable_invariant.
