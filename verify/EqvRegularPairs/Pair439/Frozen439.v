(* Generated literal data; see generate.py and input_binding.json. *)
From Coq Require Import Lists.List String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition frozen439 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, L, E6)
| (B6, S092) => Some (S192, R, C6)
| (B6, S192) => Some (S092, R, F6)
| (C6, S092) => Some (S092, L, D6)
| (C6, S192) => None
| (D6, S092) => Some (S192, R, F6)
| (D6, S192) => Some (S192, L, E6)
| (E6, S092) => Some (S092, L, F6)
| (E6, S192) => Some (S192, L, C6)
| (F6, S092) => Some (S192, L, D6)
| (F6, S192) => Some (S092, R, A6)
end.

Definition mapped600 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, L, E6)
| (B6, S092) => Some (S192, L, E6)
| (B6, S192) => Some (S092, R, F6)
| (C6, S092) => Some (S092, L, D6)
| (C6, S192) => None
| (D6, S092) => Some (S192, R, F6)
| (D6, S192) => Some (S192, L, E6)
| (E6, S092) => Some (S092, L, F6)
| (E6, S192) => Some (S192, L, C6)
| (F6, S092) => Some (S192, L, D6)
| (F6, S192) => Some (S092, R, A6)
end.

Definition original600 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, L, C6)
| (B6, S092) => Some (S192, L, C6)
| (B6, S192) => Some (S092, R, F6)
| (C6, S092) => Some (S092, L, F6)
| (C6, S192) => Some (S192, L, D6)
| (D6, S092) => Some (S092, L, E6)
| (D6, S192) => None
| (E6, S092) => Some (S192, R, F6)
| (E6, S192) => Some (S192, L, C6)
| (F6, S092) => Some (S192, L, E6)
| (F6, S192) => Some (S092, R, A6)
end.

Definition frozen439_delta : DFA := fun p b =>
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

Definition frozen439_invariant : list entry := [
  E A6 S092 0 0;
  E A6 S092 0 1;
  E A6 S092 0 3;
  E A6 S092 0 5;
  E A6 S092 0 7;
  E A6 S092 2 0;
  E A6 S092 2 1;
  E A6 S092 2 3;
  E A6 S092 2 5;
  E A6 S092 2 7;
  E A6 S092 4 0;
  E A6 S092 4 1;
  E A6 S092 4 3;
  E A6 S092 4 5;
  E A6 S092 4 7;
  E A6 S092 8 0;
  E A6 S092 8 1;
  E A6 S092 8 3;
  E A6 S092 8 5;
  E A6 S092 8 7;
  E A6 S192 2 0;
  E A6 S192 2 1;
  E A6 S192 2 2;
  E A6 S192 2 3;
  E A6 S192 2 5;
  E A6 S192 2 7;
  E A6 S192 4 0;
  E A6 S192 4 1;
  E A6 S192 4 2;
  E A6 S192 4 3;
  E A6 S192 4 5;
  E A6 S192 4 7;
  E A6 S192 8 0;
  E A6 S192 8 1;
  E A6 S192 8 2;
  E A6 S192 8 3;
  E A6 S192 8 5;
  E A6 S192 8 7;
  E B6 S092 1 0;
  E B6 S092 5 0;
  E B6 S092 6 0;
  E B6 S192 1 0;
  E B6 S192 1 1;
  E B6 S192 1 2;
  E B6 S192 1 3;
  E B6 S192 1 5;
  E B6 S192 1 7;
  E B6 S192 5 0;
  E B6 S192 5 1;
  E B6 S192 5 2;
  E B6 S192 5 3;
  E B6 S192 5 5;
  E B6 S192 5 7;
  E B6 S192 6 0;
  E B6 S192 6 1;
  E B6 S192 6 2;
  E B6 S192 6 3;
  E B6 S192 6 5;
  E B6 S192 6 7;
  E C6 S092 0 3;
  E C6 S092 0 7;
  E C6 S092 1 3;
  E C6 S092 1 7;
  E C6 S092 2 3;
  E C6 S092 2 7;
  E C6 S092 3 0;
  E C6 S092 3 3;
  E C6 S092 3 7;
  E C6 S092 4 3;
  E C6 S092 4 7;
  E C6 S092 5 3;
  E C6 S092 5 7;
  E C6 S092 6 3;
  E C6 S092 6 7;
  E C6 S092 7 0;
  E C6 S092 7 3;
  E C6 S092 7 7;
  E C6 S092 8 3;
  E C6 S092 8 7;
  E C6 S092 9 0;
  E C6 S092 9 3;
  E C6 S092 9 7;
  E C6 S192 0 3;
  E C6 S192 0 7;
  E C6 S192 1 3;
  E C6 S192 1 7;
  E C6 S192 2 3;
  E C6 S192 2 7;
  E C6 S192 3 3;
  E C6 S192 3 7;
  E C6 S192 4 3;
  E C6 S192 4 7;
  E C6 S192 5 3;
  E C6 S192 5 7;
  E C6 S192 6 3;
  E C6 S192 6 7;
  E C6 S192 7 3;
  E C6 S192 7 7;
  E C6 S192 8 3;
  E C6 S192 8 7;
  E C6 S192 9 3;
  E C6 S192 9 7;
  E D6 S092 0 2;
  E D6 S092 0 5;
  E D6 S092 1 1;
  E D6 S092 1 2;
  E D6 S092 1 3;
  E D6 S092 1 5;
  E D6 S092 1 7;
  E D6 S092 2 2;
  E D6 S092 2 5;
  E D6 S092 3 1;
  E D6 S092 3 2;
  E D6 S092 3 3;
  E D6 S092 3 5;
  E D6 S092 3 7;
  E D6 S092 4 2;
  E D6 S092 4 5;
  E D6 S092 5 1;
  E D6 S092 5 2;
  E D6 S092 5 3;
  E D6 S092 5 5;
  E D6 S092 5 7;
  E D6 S092 6 1;
  E D6 S092 6 2;
  E D6 S092 6 3;
  E D6 S092 6 5;
  E D6 S092 6 7;
  E D6 S092 7 1;
  E D6 S092 7 2;
  E D6 S092 7 3;
  E D6 S092 7 5;
  E D6 S092 7 7;
  E D6 S092 8 2;
  E D6 S092 8 5;
  E D6 S092 9 1;
  E D6 S092 9 2;
  E D6 S092 9 3;
  E D6 S092 9 5;
  E D6 S092 9 7;
  E D6 S192 0 2;
  E D6 S192 0 3;
  E D6 S192 0 5;
  E D6 S192 0 7;
  E D6 S192 1 0;
  E D6 S192 1 2;
  E D6 S192 1 3;
  E D6 S192 1 5;
  E D6 S192 1 7;
  E D6 S192 2 2;
  E D6 S192 2 3;
  E D6 S192 2 5;
  E D6 S192 2 7;
  E D6 S192 3 0;
  E D6 S192 3 2;
  E D6 S192 3 3;
  E D6 S192 3 5;
  E D6 S192 3 7;
  E D6 S192 4 2;
  E D6 S192 4 3;
  E D6 S192 4 5;
  E D6 S192 4 7;
  E D6 S192 5 0;
  E D6 S192 5 2;
  E D6 S192 5 3;
  E D6 S192 5 5;
  E D6 S192 5 7;
  E D6 S192 6 0;
  E D6 S192 6 2;
  E D6 S192 6 3;
  E D6 S192 6 5;
  E D6 S192 6 7;
  E D6 S192 7 0;
  E D6 S192 7 2;
  E D6 S192 7 3;
  E D6 S192 7 5;
  E D6 S192 7 7;
  E D6 S192 8 2;
  E D6 S192 8 3;
  E D6 S192 8 5;
  E D6 S192 8 7;
  E D6 S192 9 0;
  E D6 S192 9 2;
  E D6 S192 9 3;
  E D6 S192 9 5;
  E D6 S192 9 7;
  E E6 S092 0 3;
  E E6 S092 0 5;
  E E6 S092 0 7;
  E E6 S092 1 1;
  E E6 S092 1 3;
  E E6 S092 1 5;
  E E6 S092 1 7;
  E E6 S092 2 1;
  E E6 S092 2 3;
  E E6 S092 2 5;
  E E6 S092 2 7;
  E E6 S092 3 1;
  E E6 S092 3 3;
  E E6 S092 3 5;
  E E6 S092 3 7;
  E E6 S092 4 1;
  E E6 S092 4 3;
  E E6 S092 4 5;
  E E6 S092 4 7;
  E E6 S092 5 1;
  E E6 S092 5 3;
  E E6 S092 5 5;
  E E6 S092 5 7;
  E E6 S092 6 1;
  E E6 S092 6 3;
  E E6 S092 6 5;
  E E6 S092 6 7;
  E E6 S092 7 1;
  E E6 S092 7 3;
  E E6 S092 7 5;
  E E6 S092 7 7;
  E E6 S092 8 1;
  E E6 S092 8 3;
  E E6 S092 8 5;
  E E6 S092 8 7;
  E E6 S092 9 1;
  E E6 S092 9 3;
  E E6 S092 9 5;
  E E6 S092 9 7;
  E E6 S192 0 1;
  E E6 S192 0 3;
  E E6 S192 0 5;
  E E6 S192 0 7;
  E E6 S192 1 1;
  E E6 S192 1 3;
  E E6 S192 1 5;
  E E6 S192 1 7;
  E E6 S192 2 1;
  E E6 S192 2 3;
  E E6 S192 2 5;
  E E6 S192 2 7;
  E E6 S192 3 1;
  E E6 S192 3 3;
  E E6 S192 3 5;
  E E6 S192 3 7;
  E E6 S192 4 1;
  E E6 S192 4 3;
  E E6 S192 4 5;
  E E6 S192 4 7;
  E E6 S192 5 1;
  E E6 S192 5 3;
  E E6 S192 5 5;
  E E6 S192 5 7;
  E E6 S192 6 1;
  E E6 S192 6 3;
  E E6 S192 6 5;
  E E6 S192 6 7;
  E E6 S192 7 1;
  E E6 S192 7 3;
  E E6 S192 7 5;
  E E6 S192 7 7;
  E E6 S192 8 1;
  E E6 S192 8 3;
  E E6 S192 8 5;
  E E6 S192 8 7;
  E E6 S192 9 1;
  E E6 S192 9 3;
  E E6 S192 9 5;
  E E6 S192 9 7;
  E F6 S092 0 2;
  E F6 S092 1 1;
  E F6 S092 1 2;
  E F6 S092 1 3;
  E F6 S092 1 5;
  E F6 S092 1 7;
  E F6 S092 2 0;
  E F6 S092 2 1;
  E F6 S092 2 2;
  E F6 S092 2 3;
  E F6 S092 2 5;
  E F6 S092 2 7;
  E F6 S092 3 1;
  E F6 S092 3 2;
  E F6 S092 3 3;
  E F6 S092 3 5;
  E F6 S092 3 7;
  E F6 S092 4 2;
  E F6 S092 5 1;
  E F6 S092 5 2;
  E F6 S092 5 3;
  E F6 S092 5 5;
  E F6 S092 5 7;
  E F6 S092 6 1;
  E F6 S092 6 2;
  E F6 S092 6 3;
  E F6 S092 6 5;
  E F6 S092 6 7;
  E F6 S092 7 1;
  E F6 S092 7 2;
  E F6 S092 7 3;
  E F6 S092 7 5;
  E F6 S092 7 7;
  E F6 S092 8 0;
  E F6 S092 8 1;
  E F6 S092 8 2;
  E F6 S092 8 3;
  E F6 S092 8 5;
  E F6 S092 8 7;
  E F6 S092 9 1;
  E F6 S092 9 2;
  E F6 S092 9 3;
  E F6 S092 9 5;
  E F6 S092 9 7;
  E F6 S192 0 2;
  E F6 S192 1 2;
  E F6 S192 2 0;
  E F6 S192 2 1;
  E F6 S192 2 2;
  E F6 S192 2 3;
  E F6 S192 2 5;
  E F6 S192 2 7;
  E F6 S192 3 0;
  E F6 S192 3 1;
  E F6 S192 3 2;
  E F6 S192 3 3;
  E F6 S192 3 5;
  E F6 S192 3 7;
  E F6 S192 4 2;
  E F6 S192 5 2;
  E F6 S192 6 2;
  E F6 S192 7 0;
  E F6 S192 7 1;
  E F6 S192 7 2;
  E F6 S192 7 3;
  E F6 S192 7 5;
  E F6 S192 7 7;
  E F6 S192 8 0;
  E F6 S192 8 1;
  E F6 S192 8 2;
  E F6 S192 8 3;
  E F6 S192 8 5;
  E F6 S192 8 7;
  E F6 S192 9 0;
  E F6 S192 9 1;
  E F6 S192 9 2;
  E F6 S192 9 3;
  E F6 S192 9 5;
  E F6 S192 9 7
].

Theorem frozen439_literal_binding : machine_string frozen439 = "1RB1LE_1RC0RF_0LD---_1RF1LE_0LF1LC_1LD0RA"%string.
Proof. reflexivity. Qed.

Theorem mapped600_literal_binding : machine_string mapped600 = "1RB1LE_1LE0RF_0LD---_1RF1LE_0LF1LC_1LD0RA"%string.
Proof. reflexivity. Qed.

Theorem original600_literal_binding : machine_string original600 = "1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA"%string.
Proof. reflexivity. Qed.

Example frozen439_invariant_size : List.length frozen439_invariant = 344.
Proof. reflexivity. Qed.
Example frozen439_terminal_entries : List.length (filter (fun a =>
  match frozen439 (control a,scanned a) with None => true | Some _ => false end) frozen439_invariant) = 20.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen439_check : check frozen439 10 frozen439_delta frozen439_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen439_reachable_invariant : forall c, RI.evstep frozen439 RI.c0 c ->
  represented frozen439_delta frozen439_invariant c.
Proof. apply (check_reachable_invariant _ _ _ _ frozen439_check). Qed.

Print Assumptions frozen439_literal_binding.
Print Assumptions mapped600_literal_binding.
Print Assumptions original600_literal_binding.
Print Assumptions frozen439_check.
Print Assumptions frozen439_reachable_invariant.
