(* Generated literal data; see generate.py and input_binding.json. *)
From Coq Require Import Lists.List String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition frozen728 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S092, R, F6)
| (B6, S092) => Some (S092, R, C6)
| (B6, S192) => Some (S192, R, D6)
| (C6, S092) => Some (S092, L, D6)
| (C6, S192) => None
| (D6, S092) => Some (S192, L, E6)
| (D6, S192) => Some (S192, R, A6)
| (E6, S092) => Some (S192, L, A6)
| (E6, S192) => Some (S092, L, F6)
| (F6, S092) => Some (S092, R, D6)
| (F6, S192) => Some (S092, R, C6)
end.

Definition mapped772 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S092, R, F6)
| (B6, S092) => Some (S192, L, E6)
| (B6, S192) => Some (S192, R, D6)
| (C6, S092) => Some (S092, L, D6)
| (C6, S192) => None
| (D6, S092) => Some (S192, L, E6)
| (D6, S192) => Some (S192, R, A6)
| (E6, S092) => Some (S192, L, A6)
| (E6, S192) => Some (S092, L, F6)
| (F6, S092) => Some (S092, R, D6)
| (F6, S192) => Some (S092, R, C6)
end.

Definition original772 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S092, R, D6)
| (B6, S092) => Some (S192, L, C6)
| (B6, S192) => Some (S192, R, E6)
| (C6, S092) => Some (S192, L, A6)
| (C6, S192) => Some (S092, L, D6)
| (D6, S092) => Some (S092, R, E6)
| (D6, S192) => Some (S092, R, F6)
| (E6, S092) => Some (S192, L, C6)
| (E6, S192) => Some (S192, R, A6)
| (F6, S092) => Some (S092, L, E6)
| (F6, S192) => None
end.

Definition frozen728_delta : DFA := fun p b =>
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

Definition frozen728_invariant : list entry := [
  E A6 S092 0 0;
  E A6 S092 0 3;
  E A6 S092 0 7;
  E A6 S092 1 3;
  E A6 S092 1 7;
  E A6 S092 2 3;
  E A6 S092 2 7;
  E A6 S092 3 0;
  E A6 S092 3 1;
  E A6 S092 3 3;
  E A6 S092 3 5;
  E A6 S092 3 7;
  E A6 S092 4 3;
  E A6 S092 4 7;
  E A6 S092 5 3;
  E A6 S092 5 7;
  E A6 S092 6 0;
  E A6 S092 6 1;
  E A6 S092 6 3;
  E A6 S092 6 5;
  E A6 S092 6 7;
  E A6 S092 7 0;
  E A6 S092 7 1;
  E A6 S092 7 3;
  E A6 S092 7 5;
  E A6 S092 7 7;
  E A6 S092 8 3;
  E A6 S092 8 7;
  E A6 S092 9 0;
  E A6 S092 9 1;
  E A6 S092 9 3;
  E A6 S092 9 5;
  E A6 S092 9 7;
  E A6 S192 0 3;
  E A6 S192 0 7;
  E A6 S192 1 3;
  E A6 S192 1 7;
  E A6 S192 2 3;
  E A6 S192 2 7;
  E A6 S192 3 0;
  E A6 S192 3 1;
  E A6 S192 3 2;
  E A6 S192 3 3;
  E A6 S192 3 5;
  E A6 S192 3 7;
  E A6 S192 4 3;
  E A6 S192 4 7;
  E A6 S192 5 3;
  E A6 S192 5 7;
  E A6 S192 6 0;
  E A6 S192 6 1;
  E A6 S192 6 2;
  E A6 S192 6 3;
  E A6 S192 6 5;
  E A6 S192 6 7;
  E A6 S192 7 0;
  E A6 S192 7 1;
  E A6 S192 7 2;
  E A6 S192 7 3;
  E A6 S192 7 5;
  E A6 S192 7 7;
  E A6 S192 8 3;
  E A6 S192 8 7;
  E A6 S192 9 0;
  E A6 S192 9 1;
  E A6 S192 9 2;
  E A6 S192 9 3;
  E A6 S192 9 5;
  E A6 S192 9 7;
  E B6 S092 1 0;
  E B6 S092 3 0;
  E B6 S092 7 0;
  E B6 S092 9 0;
  E B6 S192 1 1;
  E B6 S192 1 3;
  E B6 S192 1 5;
  E B6 S192 1 7;
  E B6 S192 3 0;
  E B6 S192 3 1;
  E B6 S192 3 2;
  E B6 S192 3 3;
  E B6 S192 3 5;
  E B6 S192 3 7;
  E B6 S192 5 1;
  E B6 S192 5 3;
  E B6 S192 5 5;
  E B6 S192 5 7;
  E B6 S192 6 1;
  E B6 S192 6 3;
  E B6 S192 6 5;
  E B6 S192 6 7;
  E B6 S192 7 0;
  E B6 S192 7 1;
  E B6 S192 7 2;
  E B6 S192 7 3;
  E B6 S192 7 5;
  E B6 S192 7 7;
  E B6 S192 9 0;
  E B6 S192 9 1;
  E B6 S192 9 2;
  E B6 S192 9 3;
  E B6 S192 9 5;
  E B6 S192 9 7;
  E C6 S092 0 1;
  E C6 S092 0 3;
  E C6 S092 0 5;
  E C6 S092 0 7;
  E C6 S092 2 0;
  E C6 S092 2 1;
  E C6 S092 2 3;
  E C6 S092 2 5;
  E C6 S092 2 7;
  E C6 S092 4 0;
  E C6 S092 4 1;
  E C6 S092 4 3;
  E C6 S092 4 5;
  E C6 S092 4 7;
  E C6 S092 8 0;
  E C6 S092 8 1;
  E C6 S092 8 3;
  E C6 S092 8 5;
  E C6 S092 8 7;
  E C6 S192 0 0;
  E C6 S192 0 1;
  E C6 S192 0 2;
  E C6 S192 0 3;
  E C6 S192 0 5;
  E C6 S192 0 7;
  E C6 S192 4 0;
  E C6 S192 4 1;
  E C6 S192 4 2;
  E C6 S192 4 3;
  E C6 S192 4 5;
  E C6 S192 4 7;
  E D6 S092 0 1;
  E D6 S092 0 2;
  E D6 S092 0 3;
  E D6 S092 0 5;
  E D6 S092 0 7;
  E D6 S092 1 0;
  E D6 S092 1 2;
  E D6 S092 2 0;
  E D6 S092 2 1;
  E D6 S092 2 2;
  E D6 S092 2 3;
  E D6 S092 2 5;
  E D6 S092 2 7;
  E D6 S092 3 0;
  E D6 S092 3 1;
  E D6 S092 3 2;
  E D6 S092 3 3;
  E D6 S092 3 5;
  E D6 S092 3 7;
  E D6 S092 4 0;
  E D6 S092 4 1;
  E D6 S092 4 2;
  E D6 S092 4 3;
  E D6 S092 4 5;
  E D6 S092 4 7;
  E D6 S092 5 0;
  E D6 S092 5 2;
  E D6 S092 6 0;
  E D6 S092 6 2;
  E D6 S092 7 0;
  E D6 S092 7 1;
  E D6 S092 7 2;
  E D6 S092 7 3;
  E D6 S092 7 5;
  E D6 S092 7 7;
  E D6 S092 8 0;
  E D6 S092 8 1;
  E D6 S092 8 2;
  E D6 S092 8 3;
  E D6 S092 8 5;
  E D6 S092 8 7;
  E D6 S092 9 0;
  E D6 S092 9 1;
  E D6 S092 9 2;
  E D6 S092 9 3;
  E D6 S092 9 5;
  E D6 S092 9 7;
  E D6 S192 3 0;
  E D6 S192 3 1;
  E D6 S192 3 2;
  E D6 S192 3 3;
  E D6 S192 3 5;
  E D6 S192 3 7;
  E D6 S192 4 0;
  E D6 S192 4 1;
  E D6 S192 4 2;
  E D6 S192 4 3;
  E D6 S192 4 5;
  E D6 S192 4 7;
  E D6 S192 7 0;
  E D6 S192 7 1;
  E D6 S192 7 2;
  E D6 S192 7 3;
  E D6 S192 7 5;
  E D6 S192 7 7;
  E D6 S192 9 0;
  E D6 S192 9 1;
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
  E E6 S192 0 5;
  E E6 S192 1 1;
  E E6 S192 1 3;
  E E6 S192 1 5;
  E E6 S192 1 7;
  E E6 S192 2 1;
  E E6 S192 2 5;
  E E6 S192 3 1;
  E E6 S192 3 3;
  E E6 S192 3 5;
  E E6 S192 3 7;
  E E6 S192 4 1;
  E E6 S192 4 5;
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
  E E6 S192 8 5;
  E E6 S192 9 1;
  E E6 S192 9 3;
  E E6 S192 9 5;
  E E6 S192 9 7;
  E F6 S092 0 2;
  E F6 S092 1 2;
  E F6 S092 2 0;
  E F6 S092 2 1;
  E F6 S092 2 2;
  E F6 S092 2 3;
  E F6 S092 2 5;
  E F6 S092 2 7;
  E F6 S092 3 2;
  E F6 S092 4 2;
  E F6 S092 5 2;
  E F6 S092 6 2;
  E F6 S092 7 2;
  E F6 S092 8 0;
  E F6 S092 8 1;
  E F6 S092 8 2;
  E F6 S092 8 3;
  E F6 S092 8 5;
  E F6 S092 8 7;
  E F6 S092 9 2;
  E F6 S192 0 1;
  E F6 S192 0 2;
  E F6 S192 0 3;
  E F6 S192 0 5;
  E F6 S192 0 7;
  E F6 S192 1 2;
  E F6 S192 2 0;
  E F6 S192 2 1;
  E F6 S192 2 2;
  E F6 S192 2 3;
  E F6 S192 2 5;
  E F6 S192 2 7;
  E F6 S192 3 2;
  E F6 S192 4 1;
  E F6 S192 4 2;
  E F6 S192 4 3;
  E F6 S192 4 5;
  E F6 S192 4 7;
  E F6 S192 5 2;
  E F6 S192 6 2;
  E F6 S192 7 2;
  E F6 S192 8 0;
  E F6 S192 8 1;
  E F6 S192 8 2;
  E F6 S192 8 3;
  E F6 S192 8 5;
  E F6 S192 8 7;
  E F6 S192 9 2
].

Theorem frozen728_literal_binding : machine_string frozen728 = "1RB0RF_0RC1RD_0LD---_1LE1RA_1LA0LF_0RD0RC"%string.
Proof. reflexivity. Qed.

Theorem mapped772_literal_binding : machine_string mapped772 = "1RB0RF_1LE1RD_0LD---_1LE1RA_1LA0LF_0RD0RC"%string.
Proof. reflexivity. Qed.

Theorem original772_literal_binding : machine_string original772 = "1RB0RD_1LC1RE_1LA0LD_0RE0RF_1LC1RA_0LE---"%string.
Proof. reflexivity. Qed.

Example frozen728_invariant_size : List.length frozen728_invariant = 324.
Proof. reflexivity. Qed.
Example frozen728_terminal_entries : List.length (filter (fun a =>
  match frozen728 (control a,scanned a) with None => true | Some _ => false end) frozen728_invariant) = 12.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen728_check : check frozen728 10 frozen728_delta frozen728_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen728_reachable_invariant : forall c, RI.evstep frozen728 RI.c0 c ->
  represented frozen728_delta frozen728_invariant c.
Proof. apply (check_reachable_invariant _ _ _ _ frozen728_check). Qed.

Print Assumptions frozen728_literal_binding.
Print Assumptions mapped772_literal_binding.
Print Assumptions original772_literal_binding.
Print Assumptions frozen728_invariant_size.
Print Assumptions frozen728_terminal_entries.
Print Assumptions frozen728_check.
Print Assumptions frozen728_reachable_invariant.
