From BusyCoq Require Import CTL33.

Definition sym_id(x:Sym):Uint63.int :=
N_to_int (
match x with
| S0 => 0
| S1 => 1
| S2 => 2
end).

Definition n_sym := N_to_int 3.

Lemma tm1: ~halts (TM_from_str "1RB2LA1LA_0LA0RC0LC_---2RA1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;5;6;7;7;0;7;7;7;7;7;7;0;8;2;1;7;7;7;7;9;10;7;11;7;7;7;7;7;7;7] [0;1;2;3;4;5;6;7;8;3;3;3;3;9;3;3;10;11;3;3;3;12;13;14;15;16;17;3;3;3;11;18;19;3;16;5;3;3;3;20;1;21;6;18;22;3;3;3;3;9;3;3;10;11;20;11;10;15;3;9;3;3;3;11;7;23;15;3;9;15;16;17] sym_id n_sym). Time Qed.



