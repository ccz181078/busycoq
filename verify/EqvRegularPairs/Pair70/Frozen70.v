(* Generated literal data; see generate.py and input_binding.json. *)
From Coq Require Import Lists.List String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition frozen70 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, L, F6)
| (B6, S092) => Some (S192, L, C6)
| (B6, S192) => Some (S192, R, E6)
| (C6, S092) => Some (S192, L, D6)
| (C6, S192) => Some (S192, R, D6)
| (D6, S092) => Some (S192, L, A6)
| (D6, S192) => Some (S092, L, B6)
| (E6, S092) => Some (S092, R, C6)
| (E6, S192) => None
| (F6, S092) => Some (S192, R, C6)
| (F6, S192) => Some (S092, L, D6)
end.

Definition mapped223 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, L, F6)
| (B6, S092) => Some (S092, R, C6)
| (B6, S192) => Some (S192, R, E6)
| (C6, S092) => Some (S192, L, D6)
| (C6, S192) => Some (S192, R, D6)
| (D6, S092) => Some (S192, L, A6)
| (D6, S192) => Some (S092, L, B6)
| (E6, S092) => Some (S092, R, C6)
| (E6, S192) => None
| (F6, S092) => Some (S192, R, C6)
| (F6, S192) => Some (S092, L, D6)
end.

Definition original223 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, L, E6)
| (B6, S092) => Some (S092, R, C6)
| (B6, S192) => Some (S192, R, F6)
| (C6, S092) => Some (S192, L, D6)
| (C6, S192) => Some (S192, R, D6)
| (D6, S092) => Some (S192, L, A6)
| (D6, S192) => Some (S092, L, B6)
| (E6, S092) => Some (S192, R, C6)
| (E6, S192) => Some (S092, L, D6)
| (F6, S092) => Some (S092, R, C6)
| (F6, S192) => None
end.

Definition frozen70_delta : DFA := fun p b =>
  let row := match p with
  | 0 => (0, 1)
  | 1 => (2, 3)
  | 2 => (4, 5)
  | 3 => (6, 7)
  | 4 => (8, 9)
  | 5 => (2, 10)
  | 6 => (4, 5)
  | 7 => (6, 7)
  | 8 => (8, 9)
  | 9 => (11, 12)
  | 10 => (6, 13)
  | 11 => (4, 14)
  | 12 => (15, 16)
  | 13 => (6, 13)
  | 14 => (11, 12)
  | 15 => (4, 14)
  | 16 => (15, 16)
  | _ => (0,0)
  end in match b with S092 => fst row | S192 => snd row end.

Definition frozen70_invariant : list entry := [
  E A6 S092 0 0;
  E A6 S092 0 5;
  E A6 S092 0 14;
  E A6 S092 0 16;
  E A6 S192 0 3;
  E A6 S192 0 5;
  E A6 S192 0 7;
  E A6 S192 0 10;
  E A6 S192 0 12;
  E A6 S192 0 13;
  E A6 S192 0 14;
  E A6 S192 0 16;
  E A6 S192 1 3;
  E A6 S192 1 5;
  E A6 S192 1 7;
  E A6 S192 1 10;
  E A6 S192 1 12;
  E A6 S192 1 13;
  E A6 S192 1 14;
  E A6 S192 1 16;
  E A6 S192 2 1;
  E A6 S192 2 3;
  E A6 S192 2 5;
  E A6 S192 2 7;
  E A6 S192 2 9;
  E A6 S192 2 10;
  E A6 S192 2 12;
  E A6 S192 2 13;
  E A6 S192 2 14;
  E A6 S192 2 16;
  E A6 S192 3 3;
  E A6 S192 3 5;
  E A6 S192 3 7;
  E A6 S192 3 10;
  E A6 S192 3 12;
  E A6 S192 3 13;
  E A6 S192 3 14;
  E A6 S192 3 16;
  E A6 S192 5 3;
  E A6 S192 5 5;
  E A6 S192 5 7;
  E A6 S192 5 10;
  E A6 S192 5 12;
  E A6 S192 5 13;
  E A6 S192 5 14;
  E A6 S192 5 16;
  E A6 S192 6 1;
  E A6 S192 6 3;
  E A6 S192 6 5;
  E A6 S192 6 7;
  E A6 S192 6 9;
  E A6 S192 6 10;
  E A6 S192 6 12;
  E A6 S192 6 13;
  E A6 S192 6 14;
  E A6 S192 6 16;
  E A6 S192 7 3;
  E A6 S192 7 5;
  E A6 S192 7 7;
  E A6 S192 7 10;
  E A6 S192 7 12;
  E A6 S192 7 13;
  E A6 S192 7 14;
  E A6 S192 7 16;
  E A6 S192 10 3;
  E A6 S192 10 5;
  E A6 S192 10 7;
  E A6 S192 10 10;
  E A6 S192 10 12;
  E A6 S192 10 13;
  E A6 S192 10 14;
  E A6 S192 10 16;
  E A6 S192 13 3;
  E A6 S192 13 5;
  E A6 S192 13 7;
  E A6 S192 13 10;
  E A6 S192 13 12;
  E A6 S192 13 13;
  E A6 S192 13 14;
  E A6 S192 13 16;
  E B6 S092 0 4;
  E B6 S092 1 0;
  E B6 S092 1 4;
  E B6 S092 3 4;
  E B6 S092 5 4;
  E B6 S092 7 4;
  E B6 S092 10 4;
  E B6 S092 13 4;
  E B6 S192 0 0;
  E B6 S192 0 4;
  E B6 S192 0 8;
  E B6 S192 1 2;
  E B6 S192 1 4;
  E B6 S192 1 6;
  E B6 S192 1 8;
  E B6 S192 1 11;
  E B6 S192 1 12;
  E B6 S192 1 15;
  E B6 S192 1 16;
  E B6 S192 2 0;
  E B6 S192 2 2;
  E B6 S192 2 4;
  E B6 S192 2 6;
  E B6 S192 2 8;
  E B6 S192 2 11;
  E B6 S192 2 15;
  E B6 S192 3 0;
  E B6 S192 3 2;
  E B6 S192 3 4;
  E B6 S192 3 6;
  E B6 S192 3 8;
  E B6 S192 3 11;
  E B6 S192 3 15;
  E B6 S192 5 4;
  E B6 S192 5 8;
  E B6 S192 6 0;
  E B6 S192 6 2;
  E B6 S192 6 4;
  E B6 S192 6 6;
  E B6 S192 6 8;
  E B6 S192 6 11;
  E B6 S192 6 15;
  E B6 S192 7 0;
  E B6 S192 7 2;
  E B6 S192 7 4;
  E B6 S192 7 6;
  E B6 S192 7 8;
  E B6 S192 7 11;
  E B6 S192 7 15;
  E B6 S192 10 0;
  E B6 S192 10 2;
  E B6 S192 10 4;
  E B6 S192 10 6;
  E B6 S192 10 8;
  E B6 S192 10 11;
  E B6 S192 10 15;
  E B6 S192 13 0;
  E B6 S192 13 2;
  E B6 S192 13 4;
  E B6 S192 13 6;
  E B6 S192 13 8;
  E B6 S192 13 11;
  E B6 S192 13 15;
  E C6 S092 0 9;
  E C6 S092 2 0;
  E C6 S092 2 1;
  E C6 S092 2 2;
  E C6 S092 2 3;
  E C6 S092 2 4;
  E C6 S092 2 5;
  E C6 S092 2 6;
  E C6 S092 2 7;
  E C6 S092 2 8;
  E C6 S092 2 9;
  E C6 S092 2 10;
  E C6 S092 2 11;
  E C6 S092 2 12;
  E C6 S092 2 13;
  E C6 S092 2 14;
  E C6 S092 2 15;
  E C6 S092 2 16;
  E C6 S092 6 0;
  E C6 S092 6 1;
  E C6 S092 6 2;
  E C6 S092 6 3;
  E C6 S092 6 4;
  E C6 S092 6 5;
  E C6 S092 6 6;
  E C6 S092 6 7;
  E C6 S092 6 8;
  E C6 S092 6 9;
  E C6 S092 6 10;
  E C6 S092 6 11;
  E C6 S092 6 12;
  E C6 S092 6 13;
  E C6 S092 6 14;
  E C6 S092 6 15;
  E C6 S092 6 16;
  E C6 S192 0 1;
  E C6 S192 0 9;
  E C6 S192 1 3;
  E C6 S192 1 5;
  E C6 S192 1 7;
  E C6 S192 1 9;
  E C6 S192 1 10;
  E C6 S192 1 12;
  E C6 S192 1 13;
  E C6 S192 1 14;
  E C6 S192 1 16;
  E C6 S192 2 0;
  E C6 S192 2 1;
  E C6 S192 2 2;
  E C6 S192 2 3;
  E C6 S192 2 4;
  E C6 S192 2 5;
  E C6 S192 2 6;
  E C6 S192 2 7;
  E C6 S192 2 8;
  E C6 S192 2 9;
  E C6 S192 2 10;
  E C6 S192 2 11;
  E C6 S192 2 12;
  E C6 S192 2 13;
  E C6 S192 2 14;
  E C6 S192 2 15;
  E C6 S192 2 16;
  E C6 S192 3 1;
  E C6 S192 3 3;
  E C6 S192 3 5;
  E C6 S192 3 7;
  E C6 S192 3 9;
  E C6 S192 3 10;
  E C6 S192 3 12;
  E C6 S192 3 13;
  E C6 S192 3 14;
  E C6 S192 3 16;
  E C6 S192 5 9;
  E C6 S192 6 0;
  E C6 S192 6 1;
  E C6 S192 6 2;
  E C6 S192 6 3;
  E C6 S192 6 4;
  E C6 S192 6 5;
  E C6 S192 6 6;
  E C6 S192 6 7;
  E C6 S192 6 8;
  E C6 S192 6 9;
  E C6 S192 6 10;
  E C6 S192 6 11;
  E C6 S192 6 12;
  E C6 S192 6 13;
  E C6 S192 6 14;
  E C6 S192 6 15;
  E C6 S192 6 16;
  E C6 S192 7 1;
  E C6 S192 7 3;
  E C6 S192 7 5;
  E C6 S192 7 7;
  E C6 S192 7 9;
  E C6 S192 7 10;
  E C6 S192 7 12;
  E C6 S192 7 13;
  E C6 S192 7 14;
  E C6 S192 7 16;
  E C6 S192 10 1;
  E C6 S192 10 3;
  E C6 S192 10 5;
  E C6 S192 10 7;
  E C6 S192 10 9;
  E C6 S192 10 10;
  E C6 S192 10 12;
  E C6 S192 10 13;
  E C6 S192 10 14;
  E C6 S192 10 16;
  E C6 S192 13 1;
  E C6 S192 13 3;
  E C6 S192 13 5;
  E C6 S192 13 7;
  E C6 S192 13 9;
  E C6 S192 13 10;
  E C6 S192 13 12;
  E C6 S192 13 13;
  E C6 S192 13 14;
  E C6 S192 13 16;
  E D6 S092 0 6;
  E D6 S092 0 12;
  E D6 S092 0 15;
  E D6 S092 1 1;
  E D6 S092 1 3;
  E D6 S092 1 5;
  E D6 S092 1 6;
  E D6 S092 1 7;
  E D6 S092 1 9;
  E D6 S092 1 10;
  E D6 S092 1 12;
  E D6 S092 1 13;
  E D6 S092 1 14;
  E D6 S092 1 15;
  E D6 S092 1 16;
  E D6 S092 3 1;
  E D6 S092 3 3;
  E D6 S092 3 5;
  E D6 S092 3 6;
  E D6 S092 3 7;
  E D6 S092 3 9;
  E D6 S092 3 10;
  E D6 S092 3 12;
  E D6 S092 3 13;
  E D6 S092 3 14;
  E D6 S092 3 15;
  E D6 S092 3 16;
  E D6 S092 5 0;
  E D6 S092 5 1;
  E D6 S092 5 2;
  E D6 S092 5 3;
  E D6 S092 5 4;
  E D6 S092 5 5;
  E D6 S092 5 6;
  E D6 S092 5 7;
  E D6 S092 5 8;
  E D6 S092 5 9;
  E D6 S092 5 10;
  E D6 S092 5 11;
  E D6 S092 5 12;
  E D6 S092 5 13;
  E D6 S092 5 14;
  E D6 S092 5 15;
  E D6 S092 5 16;
  E D6 S092 7 1;
  E D6 S092 7 3;
  E D6 S092 7 5;
  E D6 S092 7 6;
  E D6 S092 7 7;
  E D6 S092 7 9;
  E D6 S092 7 10;
  E D6 S092 7 12;
  E D6 S092 7 13;
  E D6 S092 7 14;
  E D6 S092 7 15;
  E D6 S092 7 16;
  E D6 S092 10 1;
  E D6 S092 10 3;
  E D6 S092 10 5;
  E D6 S092 10 6;
  E D6 S092 10 7;
  E D6 S092 10 9;
  E D6 S092 10 10;
  E D6 S092 10 12;
  E D6 S092 10 13;
  E D6 S092 10 14;
  E D6 S092 10 15;
  E D6 S092 10 16;
  E D6 S092 13 1;
  E D6 S092 13 3;
  E D6 S092 13 5;
  E D6 S092 13 6;
  E D6 S092 13 7;
  E D6 S092 13 9;
  E D6 S092 13 10;
  E D6 S092 13 12;
  E D6 S092 13 13;
  E D6 S092 13 14;
  E D6 S092 13 15;
  E D6 S092 13 16;
  E D6 S192 0 6;
  E D6 S192 0 15;
  E D6 S192 1 0;
  E D6 S192 1 4;
  E D6 S192 1 6;
  E D6 S192 1 8;
  E D6 S192 1 15;
  E D6 S192 2 6;
  E D6 S192 2 15;
  E D6 S192 3 1;
  E D6 S192 3 2;
  E D6 S192 3 3;
  E D6 S192 3 4;
  E D6 S192 3 5;
  E D6 S192 3 6;
  E D6 S192 3 7;
  E D6 S192 3 8;
  E D6 S192 3 9;
  E D6 S192 3 10;
  E D6 S192 3 11;
  E D6 S192 3 12;
  E D6 S192 3 13;
  E D6 S192 3 14;
  E D6 S192 3 15;
  E D6 S192 3 16;
  E D6 S192 5 0;
  E D6 S192 5 1;
  E D6 S192 5 2;
  E D6 S192 5 3;
  E D6 S192 5 4;
  E D6 S192 5 5;
  E D6 S192 5 6;
  E D6 S192 5 7;
  E D6 S192 5 8;
  E D6 S192 5 9;
  E D6 S192 5 10;
  E D6 S192 5 11;
  E D6 S192 5 12;
  E D6 S192 5 13;
  E D6 S192 5 14;
  E D6 S192 5 15;
  E D6 S192 5 16;
  E D6 S192 6 6;
  E D6 S192 6 15;
  E D6 S192 7 0;
  E D6 S192 7 1;
  E D6 S192 7 2;
  E D6 S192 7 3;
  E D6 S192 7 4;
  E D6 S192 7 5;
  E D6 S192 7 6;
  E D6 S192 7 7;
  E D6 S192 7 8;
  E D6 S192 7 9;
  E D6 S192 7 10;
  E D6 S192 7 11;
  E D6 S192 7 12;
  E D6 S192 7 13;
  E D6 S192 7 14;
  E D6 S192 7 15;
  E D6 S192 7 16;
  E D6 S192 10 4;
  E D6 S192 10 6;
  E D6 S192 10 8;
  E D6 S192 10 15;
  E D6 S192 13 0;
  E D6 S192 13 1;
  E D6 S192 13 2;
  E D6 S192 13 3;
  E D6 S192 13 4;
  E D6 S192 13 5;
  E D6 S192 13 6;
  E D6 S192 13 7;
  E D6 S192 13 8;
  E D6 S192 13 9;
  E D6 S192 13 10;
  E D6 S192 13 11;
  E D6 S192 13 12;
  E D6 S192 13 13;
  E D6 S192 13 14;
  E D6 S192 13 15;
  E D6 S192 13 16;
  E E6 S092 1 0;
  E E6 S092 1 2;
  E E6 S092 1 4;
  E E6 S092 1 6;
  E E6 S092 1 8;
  E E6 S092 1 11;
  E E6 S092 1 15;
  E E6 S092 3 1;
  E E6 S092 3 2;
  E E6 S092 3 3;
  E E6 S092 3 4;
  E E6 S092 3 5;
  E E6 S092 3 6;
  E E6 S092 3 7;
  E E6 S092 3 8;
  E E6 S092 3 9;
  E E6 S092 3 10;
  E E6 S092 3 11;
  E E6 S092 3 12;
  E E6 S092 3 13;
  E E6 S092 3 14;
  E E6 S092 3 15;
  E E6 S092 3 16;
  E E6 S092 5 0;
  E E6 S092 5 1;
  E E6 S092 5 2;
  E E6 S092 5 3;
  E E6 S092 5 4;
  E E6 S092 5 5;
  E E6 S092 5 6;
  E E6 S092 5 7;
  E E6 S092 5 8;
  E E6 S092 5 9;
  E E6 S092 5 10;
  E E6 S092 5 11;
  E E6 S092 5 12;
  E E6 S092 5 13;
  E E6 S092 5 14;
  E E6 S092 5 15;
  E E6 S092 5 16;
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
  E E6 S092 7 10;
  E E6 S092 7 11;
  E E6 S092 7 12;
  E E6 S092 7 13;
  E E6 S092 7 14;
  E E6 S092 7 15;
  E E6 S092 7 16;
  E E6 S092 10 2;
  E E6 S092 10 4;
  E E6 S092 10 6;
  E E6 S092 10 8;
  E E6 S092 10 11;
  E E6 S092 10 15;
  E E6 S092 13 0;
  E E6 S092 13 1;
  E E6 S092 13 2;
  E E6 S092 13 3;
  E E6 S092 13 4;
  E E6 S092 13 5;
  E E6 S092 13 6;
  E E6 S092 13 7;
  E E6 S092 13 8;
  E E6 S092 13 9;
  E E6 S092 13 10;
  E E6 S092 13 11;
  E E6 S092 13 12;
  E E6 S092 13 13;
  E E6 S092 13 14;
  E E6 S092 13 15;
  E E6 S092 13 16;
  E E6 S192 3 9;
  E E6 S192 3 12;
  E E6 S192 3 14;
  E E6 S192 3 16;
  E F6 S092 0 7;
  E F6 S092 0 10;
  E F6 S092 0 12;
  E F6 S092 0 13;
  E F6 S092 0 16;
  E F6 S092 1 3;
  E F6 S092 1 7;
  E F6 S092 1 10;
  E F6 S092 1 12;
  E F6 S092 1 13;
  E F6 S092 1 16;
  E F6 S092 3 3;
  E F6 S092 3 7;
  E F6 S092 3 10;
  E F6 S092 3 12;
  E F6 S092 3 13;
  E F6 S092 3 16;
  E F6 S092 5 3;
  E F6 S092 5 7;
  E F6 S092 5 10;
  E F6 S092 5 12;
  E F6 S092 5 13;
  E F6 S092 5 16;
  E F6 S092 7 3;
  E F6 S092 7 7;
  E F6 S092 7 10;
  E F6 S092 7 12;
  E F6 S092 7 13;
  E F6 S092 7 16;
  E F6 S092 10 3;
  E F6 S092 10 7;
  E F6 S092 10 10;
  E F6 S092 10 12;
  E F6 S092 10 13;
  E F6 S092 10 16;
  E F6 S092 13 3;
  E F6 S092 13 7;
  E F6 S092 13 10;
  E F6 S092 13 12;
  E F6 S092 13 13;
  E F6 S092 13 16;
  E F6 S192 0 7;
  E F6 S192 0 10;
  E F6 S192 0 12;
  E F6 S192 0 13;
  E F6 S192 0 16;
  E F6 S192 1 7;
  E F6 S192 1 10;
  E F6 S192 1 12;
  E F6 S192 1 13;
  E F6 S192 1 16;
  E F6 S192 2 7;
  E F6 S192 2 10;
  E F6 S192 2 12;
  E F6 S192 2 13;
  E F6 S192 2 16;
  E F6 S192 3 7;
  E F6 S192 3 10;
  E F6 S192 3 12;
  E F6 S192 3 13;
  E F6 S192 3 16;
  E F6 S192 5 7;
  E F6 S192 5 10;
  E F6 S192 5 12;
  E F6 S192 5 13;
  E F6 S192 5 16;
  E F6 S192 6 7;
  E F6 S192 6 10;
  E F6 S192 6 12;
  E F6 S192 6 13;
  E F6 S192 6 16;
  E F6 S192 7 7;
  E F6 S192 7 10;
  E F6 S192 7 12;
  E F6 S192 7 13;
  E F6 S192 7 16;
  E F6 S192 10 7;
  E F6 S192 10 10;
  E F6 S192 10 12;
  E F6 S192 10 13;
  E F6 S192 10 16;
  E F6 S192 13 7;
  E F6 S192 13 10;
  E F6 S192 13 12;
  E F6 S192 13 13;
  E F6 S192 13 16
].

Theorem frozen70_literal_binding : machine_string frozen70 = "1RB1LF_1LC1RE_1LD1RD_1LA0LB_0RC---_1RC0LD"%string.
Proof. reflexivity. Qed.

Theorem mapped223_literal_binding : machine_string mapped223 = "1RB1LF_0RC1RE_1LD1RD_1LA0LB_0RC---_1RC0LD"%string.
Proof. reflexivity. Qed.

Theorem original223_literal_binding : machine_string original223 = "1RB1LE_0RC1RF_1LD1RD_1LA0LB_1RC0LD_0RC---"%string.
Proof. reflexivity. Qed.

Example frozen70_invariant_size : List.length frozen70_invariant = 596.
Proof. reflexivity. Qed.
Example frozen70_terminal_entries : List.length (filter (fun a =>
  match frozen70 (control a,scanned a) with None => true | Some _ => false end) frozen70_invariant) = 4.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen70_check : check frozen70 17 frozen70_delta frozen70_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen70_reachable_invariant : forall c, RI.evstep frozen70 RI.c0 c ->
  represented frozen70_delta frozen70_invariant c.
Proof. apply (check_reachable_invariant _ _ _ _ frozen70_check). Qed.

Print Assumptions frozen70_literal_binding.
Print Assumptions mapped223_literal_binding.
Print Assumptions original223_literal_binding.
Print Assumptions frozen70_check.
Print Assumptions frozen70_reachable_invariant.
Print Assumptions frozen70_invariant_size.
Print Assumptions frozen70_terminal_entries.
