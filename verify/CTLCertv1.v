From BusyCoq Require Import CTL62.

Definition sym_id(x:Sym):Uint63.int :=
match x with
| S0 => int0
| S1 => int1
end.

Definition n_sym := N_to_int 2.

Lemma tm1: ~halts (TM_from_str "1RB0LA_1LB0LC_0LD1LA_1RE---_0RE1RF_1LC0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;2;3;6;7;8;8;2;3;8;8;8;8] [0;1;2;3;4;5;6;6;1;0;6;6;6;6] sym_id n_sym). Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RC_1RC1RF_1LD1RC_0LA0LE_1RA1LE_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;6;9;0;1;4;2;0;10;2;6] [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] sym_id n_sym). Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1LF_1LC0RD_---1LA_1LE0RE_1LA1RA_1LB0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;8;9;7;10;1;2;3;8;8;11;7;0;12;13;14;2;3;0;1;15;16;17;18;19;18;0;12;19;18;15;18] [0;1;2;3;4;5;4;6;0;1;7;5;7;5;0;1] sym_id n_sym). Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0RF_0RC0RC_0LD0RA_0LE1LD_1RA1LD_---0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;5;13;14;15;9;10;16;10;10;13;9;17;1;18;10;6;1;2;19;2;5;14;9;20;19;2;21;11;10;13;22;13;15] [0;1;2;3;4;4;5;6;4;4;4;4;4;7;0;1] sym_id n_sym). Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB0LF_1LB0LC_1RD1LA_0RD1RE_0RF---_0LA0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;5;7;2;3;6;6;2;3] [0;1;2;3;4;5;6;7;1;8;7;7;8;1;7;7;6;7] sym_id n_sym). Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0LF_1LB0LC_1RD1LA_0RD1RE_0RF---_0LA0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;5;7;2;3;6;6;2;3] [0;1;2;3;4;5;6;7;1;8;7;7;8;1;7;7;6;7] sym_id n_sym). Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1LF_0LC0RD_---0RD_1LE0RE_1LA1RA_1LB0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;8;9;7;10;7;2;3;8;8;11;7;0;12;13;14;2;3;0;1;15;16;17;18;19;18;0;12;19;18;15;18] [0;1;2;3;4;5;4;6;0;1;7;5;7;5;0;1] sym_id n_sym). Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB0LF_1LC1RB_1LA0LD_1RE1LD_0RC0RB_---1LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] [0;1;2;3;2;4;5;0;5;6;7;8;0;2;7;7;7;9;7;10;7;8] sym_id n_sym). Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB0LF_1LC1RB_1LA0LD_1RE1LD_0RC0RB_---0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] [0;1;2;3;2;4;5;0;5;6;7;8;0;2;7;7;7;9;7;10;7;8] sym_id n_sym). Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB---_1LC1RE_0LC0LD_1LA1LF_0RE0RB_0LA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;1;3;3;3] [0;1;2;3;1;0;3;3] sym_id n_sym). Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LC1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LC1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB0LD_1LC0RE_1LA1RC_1LC1LD_1RF1RB_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;5;1;5;1;5;5] [0;1;2;0;3;0;3;3] sym_id n_sym). Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0RC_1LC0LA_0LE1RD_1RF0RB_1RA1LE_---1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;8;9;10;11;0;1;4;4;12;13;10;11;14;15;4;4;16;5;0;1;17;18;4;4;4;5;10;11] [0;1;2;3;4;5;6;7;8;8;9;10;11;12;0;1;8;8;8;8;13;14;8;8;15;16;8;8;4;5;8;8;17;18;8;8;11;12] sym_id n_sym). Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB0LC_1LA0LA_1RC0RD_1RE0RE_1LF1RE_---0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;0;1;4;4;4;6;4;4] [0;1;2;3;4;5;6;7;8;9;10;11;0;1;12;3;9;9;9;9;9;13;14;3;4;5;8;9;15;16;9;9;10;11] sym_id n_sym). Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0LF0LA_---1RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0LF0LA_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0RF0LA_---1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB1LA_1RC0RD_1RD1RF_1LE1RD_0LB0LA_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;4;5;0;5;6;7;8;0;9;7;7;7;10;2;4;7;5] [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] sym_id n_sym). Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD1LC_1LE0RB_---0LA_1LE1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB0RD_1LC0RC_0RC1RD_0RA1LE_0LE0LF_1LA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;5;1;3;5;5;3;1] [0;1;2;3;4;1;3;3;5;1;2;3] sym_id n_sym). Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RE_1LC---_0LC1LD_1RA0LC_0RE1RF_1RB0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0RE0RB_0LA1RF_---0LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;1;3;3;3] [0;1;2;0;2;2] sym_id n_sym). Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0RE0RB_0LA0RF_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;0;1;4;4] [0;1;2;0;2;2] sym_id n_sym). Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0RE0RB_0LA0RF_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;1;3;3;3] [0;1;2;0;2;2] sym_id n_sym). Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB0RA_1RC0LD_1LB---_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;5;5;1;0;5;5] [0;1;2;1;3;4;1;4;4;4] sym_id n_sym). Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0RA_1RC1LE_1LD---_1RF0RB_0LE0LD_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;5;5;1;0;5;5] [0;1;2;1;3;4;5;4;4;4;2;1] sym_id n_sym). Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB1LA_0RC0LF_1LC1LD_0RE0LF_1RB1RE_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;2;3;7;8;4;9;2;3;4;6] [0;1;2;3;2;2;4;5;6;2;0;1;2;3] sym_id n_sym). Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB0RC_1LC1RF_1LD1RC_0LA0LE_1RA1LE_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;6;9;0;1;4;2;0;10;2;6] [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] sym_id n_sym). Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB0LB_1RC1LC_1LD1RE_1RF0LA_1RD0RA_---1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;0;4;0;4;5;6;0;1;5;6] [0;1;2;3;4;5;6;7;8;8;9;7;10;1;2;3;8;8;11;7;0;12;13;14;2;3;0;1;15;16;17;18;19;18;0;12;19;18;15;18] sym_id n_sym). Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB0LB_1RC1LC_1LD1RE_0RF0LA_1RD0RA_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;0;4;0;4;5;6;0;1;5;6] [0;1;2;3;4;5;6;7;8;8;9;7;10;1;2;3;8;8;11;7;0;12;13;14;2;3;0;1;15;16;17;18;19;18;0;12;19;18;15;18] sym_id n_sym). Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE1LF_0RE1RA_0RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;4;4;4;4] sym_id n_sym). Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE1RF_0RE1RA_1LF0LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE1RF_0RE1RA_0LF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;3;3;0;1] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RF_0RE1RA_1LC---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB0RA_1LC---_1LF0LD_1RE0RC_0RE1RA_0LF0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;3;3;2;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB0RA_1LC---_0LF0LD_1RE0RB_0RE1RA_0LF0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB0RF_1LC---_0LC0LD_1RE0RB_0RE1RA_1RB0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0RF_1LC---_0LC0LD_1RE0RB_0RE1RA_1RB0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE1RA_------") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB0LE_0RC1LF_1RD1RB_0LA0RB_1LB---_0LB0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;0;2;3;2;2;4;2;5;5;5] [0;1;2;1;0;3;4;5;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB1LC_1LC0RD_1LA0LC_1RE1RF_1LA1RB_---0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;0;2;5;6;7;8;8;2;7;7;8;2] [0;1;2;3;4;5;6;7;2;8;0;4;6;6;6;0;6;9;4;5] sym_id n_sym). Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB1LC_1LC0RD_1LA0LC_1RE0RF_1LA1RB_---1RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;5;1;6;0;5;7;6;6;1;3] [0;1;2;3;4;5;6;7;2;8;0;4;6;6;6;0;6;2] sym_id n_sym). Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB0LE_0LC0RF_1RD0RC_1LE---_0LE1LA_0RF1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;3;3;2;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1LD_0RC0LA_1LA0RE_0LA1LD_1RF1LE_---0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;1;7;5;3;1;8;9;7;7;7;9;1;3] [0;1;2;3;4;5;6;7;4;4;0;8;0;7;9;3;4;4;4;3] sym_id n_sym). Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE1LF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB1LD_0RC0LD_1LA0RE_0LA1LD_1RF1LE_---0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;1;7;5;0;1;8;9;7;7;7;9;1;3] [0;1;2;3;4;5;6;7;4;4;0;8;0;7;9;3;4;4;4;3] sym_id n_sym). Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB0RE_0LC1LD_---1LD_0LE0LB_1RF1RE_1RA1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB0RE_0LC1RB_---1LD_0LE0LB_1RF1RE_1RA1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD---_1LF0RB_1LD1RE_0LA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;2;3;1;4;5;4;4;6;3;3;6] [0;1;2;3;2;2;4;1;0;1] sym_id n_sym). Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_0LE0LF_1RA1RE_0LC1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;2;2;4;1;5;3;2;3] sym_id n_sym). Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_0LE0LF_1RA1RE_0LC1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;2;2;4;1;5;3;2;3] sym_id n_sym). Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB1LA_1LC0RE_1LF1LD_0LE0LC_1RA1RE_---1RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;2;2;4;1;5;6;2;3;4;1] sym_id n_sym). Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB1LA_1LC0RE_0LF1LD_0LE0LC_1RA1RE_---1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;2;2;4;1;5;3;2;3] sym_id n_sym). Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB---_1LC---_0LC0LD_1RE0RB_0RE1RF_1RB0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB0RF_1LC---_0LC0LD_1RE0RB_0RE1RF_1RB0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE1RF_1RB0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB0RF_0RC1RE_1LD---_0LD1LA_0LA0RE_1RE0RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;4;4;4;4] [0;1;2;1;3;4;2;1;5;5;5;5] sym_id n_sym). Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD1LC_0LE0RB_---0LA_1LE1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;0;1;4;1;4;4] sym_id n_sym). Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB0RA_1LC1RA_0RA0LD_1LC0LE_---1LF_1RA0RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;4;4;7;0;4;4] [0;1;2;3;4;1;5;6;7;8;9;10;5;3;1;1;11;12;11;13;11;12;14;6;12;12;11;12;15;16;12;10;12;12] sym_id n_sym). Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB1LA_1RC0RE_1RD---_0LA0LD_1LF1RE_1LD0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;8;6;4;5;6;8;6;8] [0;1;2;3;2;2;4;5;6;1;2;3;0;1] sym_id n_sym). Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD0LA_1LA1LF_1LC1RE_---0LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] [0;1;2;3;2;4;5;0;5;6;7;8;0;9;7;7;7;10;2;4;7;5] sym_id n_sym). Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB0RA_0LB1RC_1LD---_0LD0LE_1RF0RC_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB0LE_0LC0RF_0RF0LD_0LE---_1LA1LB_0RA0RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;3;7;1;8;9;10;11;12;13;14;15;15;16;17;18;19;20;17;21;22;16;23;24;25;26;27;28;29;30;31;5;32;33;23;33;32;15;31;3;34;26;27;28;35;15;29;20;12;11;36;9;20;37;23;33;7;5;27;28;34;26;17;29;29;30;38;29;37;37;23;24] [0;1;2;3;4;5;4;6;6;7;0;8;6;6;6;6;6;6] sym_id n_sym). Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB0LE_0LC0RF_0RF0LD_0LE---_1LA1LB_0RA1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;3;7;8;9;10;4;11;12;13;14;5;15;16;16;17;18;19;20;21;21;19;22;5;7;23;24;13;25;26;17;7;7;7;21;27;19;28;21;29;25;26;20;16;22;21;30;10;7;7;28;28;17;7;15;21] [0;1;2;3;4;5;3;3;3;6;0;3;3;3] sym_id n_sym). Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB0LE_0LC0RF_1RA0LD_0LE---_1LA1LB_0RA0RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;2;6;7;1;8;9;7;10;11;12;13;14;14;15;2;3;16;17;18;19;20;21;22;23;24;25;26;27;28;5;29;20;30;20;31;23;24;5;32;14;26;19;33;12;34;9;19;35;20;20;36;5;30;20;31;23;16;26;26;27;16;37;38;26;35;35;16;37;15;20;20;21] [0;1;2;3;4;5;4;6;6;7;8;9;6;6;6;6;0;1;6;6] sym_id n_sym). Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB1RA_0RC0LE_1LC1LD_0RA0LE_---0LF_1RB1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;2;3;7;8;4;9;2;3;4;6] [0;1;2;3;2;2;4;5;6;2;0;1;2;3] sym_id n_sym). Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB1LA_1LC0RE_1LF1LD_1RA0LC_1RA1RE_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;2;2;4;1;5;3;2;3] sym_id n_sym). Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB0LE_1RC1RB_1RD1LC_0LE0RB_1LF1RE_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_0RE0LC_1RF0LE_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;3;3;0;1] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA0LE_1LF1RE_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;4;3;3;0;1] [0;1;2;3;4;4;5;1;4;4;6;3;2;3] sym_id n_sym). Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB0LD_0RC0RB_1LD1RC_1RD0LE_1RF1LE_---1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;0;2;3;4;3;3;0;1] [0;1;2;3;4;5;0;6;2;7;8;9;0;1;2;7;8;8;4;2] sym_id n_sym). Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB0RE_1LC1LD_---1RD_0LE0LB_1RF1RE_1RA1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;6;5;6;5;5;2;3] sym_id n_sym). Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB1RE_0LC0RE_1RE0LD_1LE---_0RA1LF_0LE0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;0;2;3;2;2;4;2;5;5;5] [0;1;2;1;0;3;4;5;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_1RF1RE_1RB1LA_---1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;0;2;5;6;7;8;8;2;7;7;8;2] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_0RF1RE_1RB1LA_---1RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;5;1;6;0;5;7;6;6;2;3] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0LE1RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB1RD_1RC0RF_0RD0RD_0LE0RB_0LA1LE_---0RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;5;13;14;15;9;10;16;10;10;13;9;17;1;18;10;6;1;2;19;2;5;14;9;20;19;2;21;11;10;13;22;13;15] [0;1;2;3;4;4;5;6;4;4;4;4;4;7;0;1] sym_id n_sym). Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB0RA_0RC0RA_0LC1LD_1LE---_0LF0LA_1RA0LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;3;4;5;6;7;8;9;3;10;11;9;9;1;9;9;12;3;9;9;1;3] [0;1;2;3;4;4;5;6;4;4;0;4;7;1;4;4] sym_id n_sym). Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB0RA_0RC0RA_0LC1LD_1LE---_0LF0LA_1RA0RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;3;4;5;6;7;8;9;3;10;11;9;9;1;9;9;12;3;9;9;2;3] [0;1;2;3;4;4;5;6;4;4;0;4;7;1;4;4] sym_id n_sym). Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0RA_1LC0LE_0LC1LD_0RB0LC_1RF---_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;3;3;0;1] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB1LA_1RC0RD_0LD---_1LE1RD_1LF0RB_0LA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;4;1;5;6;5;5;7;4;4;7] [0;1;2;3;2;2;4;1;0;1] sym_id n_sym). Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB0LF_0LC1RA_1LD1RD_0RB0LE_0RD0LA_---0LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;5;6;4;4;4;4;4;7;0;1] [0;1;2;3;4;1;3;3;5;6;7;1;8;3;9;10;9;10;11;3;12;3;13;6;14;6;3;3;15;6;16;10;9;10] sym_id n_sym). Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB0LC_1LC0RD_1RF1LA_0RD1RE_0RF0RE_0LA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;2;3;0;1;6;6] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB0LC_1LC0RD_0LC1LA_0RD1RE_0RF0RE_0LA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;3;3;0;1] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RD0LE_0LC1RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;2;4;4;4] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RD0LE_0RC1RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;2;4;4;4] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_0RE1LD_---1RF_1RB1LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;5;1;6;0;5;7;6;6;2;3] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1LD0LE_0LF1LD_1RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;4;5;2;2;5;0] [0;1;2;3;4;1;5;3;6;7;6;7;6;6;8;6;4;3] sym_id n_sym). Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1LD0LE_0LF1RC_1RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;4;5;2;2;5;0] [0;1;2;3;4;1;5;3;6;7;6;7;6;6;8;6;4;3] sym_id n_sym). Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA---_1LE1RD_1LF0RB_0LA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;2;3;1;4;5;4;4;6;3;3;6] [0;1;2;3;2;2;4;1;0;1] sym_id n_sym). Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0RF_1LE1RD_0LB0LA_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;6;8;4;9;0;10;4;5;2;6] [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] sym_id n_sym). Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0RF_1LE1RD_0LB0LA_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;6;8;4;9;0;10;4;5;2;6] [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] sym_id n_sym). Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB0LC_1LC0RD_0LC1LA_0RD1RE_1RF0RE_1LC---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1LC_1RB0LC_0RF1LE_---1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;5;1;6;0;5;7;6;6;2;3] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB0RA_1RC---_1LC0LD_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;5;5;1;0;5;5] [0;1;2;1;3;4;1;4;4;4] sym_id n_sym). Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB0RF_0LC1RE_1RD1LB_0RE0RA_---1LC_1RA1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;0;1;4;4;6;1;4;4] [0;1;2;3;4;5;0;1;4;4;4;1] sym_id n_sym). Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB0LD_1RC0RE_0LA1RF_1LA1LD_0RC0RB_---1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;1;3;3;3] [0;1;2;0;2;2] sym_id n_sym). Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB0LD_1RC0RE_0LA0RF_1LA1LD_0RC0RB_---0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;0;1;4;4] [0;1;2;0;2;2] sym_id n_sym). Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB0LD_1RC0RE_0LA0RF_1LA1LD_0RC0RB_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;1;3;3;3] [0;1;2;0;2;2] sym_id n_sym). Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB1LB_0LC0RE_0RA1LD_1LC0RF_0LB0RD_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;3;3;5;6;7;1;8;3;9;10;9;10;11;3;12;3;13;6;14;6;3;3;15;6;16;10;9;10] [0;1;2;3;4;4;5;6;4;4;4;4;4;7;0;1] sym_id n_sym). Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB1RC_1LC0RA_0RE0LD_0LB1LE_0LD0RF_0RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;3;3;3;6;0;3;3;3] [0;1;2;3;4;5;6;3;7;8;9;10;4;11;12;13;14;5;15;16;16;17;18;19;20;21;21;19;22;5;7;23;24;13;25;26;17;7;7;7;21;27;19;28;21;29;25;26;20;16;22;21;30;10;7;7;28;28;17;7;15;21] sym_id n_sym). Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB1RC_1LC0RA_0RE0LD_0LB0LA_0LD0RF_0RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;6;7;0;8;6;6;6;6;6;6] [0;1;2;3;4;5;6;3;7;1;8;9;10;11;12;13;14;15;15;16;17;18;19;20;17;21;22;16;23;24;25;26;27;28;29;30;31;5;32;33;23;33;32;15;31;3;34;26;27;28;35;15;29;20;12;11;36;9;20;37;23;33;7;5;27;28;34;26;17;29;29;30;38;29;37;37;23;24] sym_id n_sym). Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB1RC_1LC0RA_0RE0LD_0LB0LA_1LB0RF_0RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;6;7;8;9;6;6;6;6;0;1;6;6] [0;1;2;3;4;5;2;6;7;1;8;9;7;10;11;12;13;14;14;15;2;3;16;17;18;19;20;21;22;23;24;25;26;27;28;5;29;20;30;20;31;23;24;5;32;14;26;19;33;12;34;9;19;35;20;20;36;5;30;20;31;23;16;26;26;27;16;37;38;26;35;35;16;37;15;20;20;21] sym_id n_sym). Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1RE_---1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB1LA_0RC0LF_0LD1RC_0RE1RA_1LE1LB_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;4;3;5;7;2;3] [0;1;2;3;2;2;4;5;6;2;0;1;2;3] sym_id n_sym). Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_0LE0RB_---0LA_0LE0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB0RA_0RC---_1LB1LD_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;3;3;1;0] [0;1;2;1;3;4;1;1;4;4] sym_id n_sym). Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB0LA_1LC0LF_1LA0LD_1RE---_0RE0RB_0LD1LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;2;3;2;3;6;6;6;6] [0;1;2;3;1;0;4;4;4;4] sym_id n_sym). Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LE_0LC0RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LE_0RC0RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB0RA_1LC---_1RE1LD_1RE0LC_0LD0RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;2;3;0;1;6;6] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB0RA_1LC---_0RE1LD_1RE0LC_0LD0RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;2;3;0;1;6;6] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB0RA_1LC---_0RE1LD_1RE0LC_0LD0RF_1LC1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;2;3;0;1;6;6] [0;1;2;3;4;5;2;6;2;6;7;8;2;6;7;7;7;7] sym_id n_sym). Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LC_---0RF_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LC_0RE0RF_1LE1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;3;3;2;3] [0;1;2;3;3;4;2;3;5;5;5;5] sym_id n_sym). Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD1LC_1LA1RD_1RF1LE_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;5;1;4;4;6;3;2;3] [0;1;2;0;3;4;3;3;0;1] sym_id n_sym). Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB0RA_1LC1RA_0RE1LD_1RE0LF_0LF0RB_0LC---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;3;3;2;3] [0;1;2;3;4;5;2;3;2;3;6;6;6;6] sym_id n_sym). Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB0RB_1LC1RB_---0LD_1LE0LE_1RD0LF_1RF0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;0;1;4;4;4;6;4;4] [0;1;2;3;4;5;6;1;7;8;9;10;5;11;8;8;8;8;8;12;13;3;14;3;7;8;15;16;4;5;8;8;9;10] sym_id n_sym). Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB1RA_1LC1LF_0LE0LD_0RB0LC_0RA0LF_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;2;2] [0;1;2;0;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB1LA_1RC0RD_1LD1RF_1LE1RD_0LB0LA_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;4;5;0;5;6;7;8;0;9;7;7;7;10;2;4;7;5] [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] sym_id n_sym). Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB1LF_1RC1RA_1RD0LA_0LE0RC_---1LA_0LD1LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;5;4;4;0;1] [0;1;2;3;4;5;0;6;7;7;8;9;1;3;7;7;10;11;1;7;7;7;12;13;4;5;0;7] sym_id n_sym). Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB0RB_1LC1RF_1RA0LD_1LE0LE_0RA0LE_1RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;7;4;4;0;1] [0;1;2;3;4;5;6;6;7;8;4;9;6;6;5;3;2;3;10;6;6;11;5;3] sym_id n_sym). Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB0RB_1LC1RC_1RA0LD_1LE1LF_0RA0LE_---1RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;7;4;4;0;1] [0;1;2;3;4;5;6;6;7;8;4;9;6;6;10;3;2;3;11;6;4;9;6;12;10;3] sym_id n_sym). Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB0RB_1LC1RC_1RA0LD_1LE0LF_0RA0LE_---0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;7;4;4;0;1] [0;1;2;3;4;5;6;6;7;8;4;9;6;6;5;3;2;3;10;6;6;11;5;3] sym_id n_sym). Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB---_1LC0LE_0LC1LD_1LE0LD_1RF---_0RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;1;3;3;3] [0;1;2;3;1;4;3;2;4;4] sym_id n_sym). Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1LA0LF_1RA1RE_1LC1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;0;1;4;1;4;4] sym_id n_sym). Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB1LE_1RC0RF_0RD0RD_0LE0RB_0LA1LE_---0RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;5;13;14;15;9;10;16;10;10;13;9;17;1;18;10;6;1;2;19;2;5;14;9;20;19;2;21;11;10;13;22;13;15] [0;1;2;3;4;4;5;6;4;4;4;4;4;7;0;1] sym_id n_sym). Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB1LC_0LC0RD_1LA0LC_1RB0RE_---1RF_1LC0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;5;6;7;8;9;10;5;3;1;1;11;12;11;13;11;12;14;6;12;12;11;12;15;16;12;10;12;12] [0;1;2;3;4;5;4;6;4;4;4;4;7;0;4;4] sym_id n_sym). Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RB0LE_1LF1LD_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD0LA_1RE0LF_1LC1RE_---0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] [0;1;2;3;4;5;6;0;4;4;4;7;6;8;4;9;0;10;4;5;2;6] sym_id n_sym). Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD0LA_1RE0LF_1LC1RE_---1LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] [0;1;2;3;4;5;6;0;4;4;4;7;6;8;4;9;0;10;4;5;2;6] sym_id n_sym). Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB0LE_1RC0RF_1RD0RC_1LE---_0LE1LA_0RF1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;3;2;4;4] [0;1;2;1;3;4;2;1;5;5;5;5] sym_id n_sym). Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB0RA_0LC---_1LD1RC_0LD0LE_1RF0RC_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;3;3;2;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB1RC_1LC0RA_0RE0LD_0LB1LE_0LD0RF_1RD---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;3;3;3;6;0;3;3;3] [0;1;2;3;4;5;2;3;6;7;8;9;10;11;12;5;13;6;6;14;15;6;16;17;18;5;6;19;20;21;16;22;17;23;24;24;16;25;20;21;18;16;26;9;24;24;23;23;27;11;14;6;13;16;15;16] sym_id n_sym). Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB1RC_1LC0RA_0RE0LD_0LB0LA_0LD0RF_1RD---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;6;7;0;8;6;6;6;6;6;6] [0;1;2;3;0;1;4;3;5;6;6;7;8;9;10;11;12;13;9;9;14;6;15;16;17;18;17;18;6;19;20;6;21;22;23;6;6;8;12;13;6;7;24;18;10;11;6;19;25;21;17;26;21;22] sym_id n_sym). Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB1RC_1LC0RA_0RE0LD_0LB0LA_1LB0RF_1RD---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;6;7;8;9;6;6;6;6;0;1;6;6] [0;1;2;1;3;4;5;6;7;8;9;8;10;11;12;4;13;14;15;13;16;17;18;19;20;21;14;20;22;5;20;21;15;23;24;14;25;13;4;26;20;20;22;5;9;8;27;5;27;5;5;6;10;11;10;11] sym_id n_sym). Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RA0LE_0LF1LD_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;0;1;4;4] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB0RF_0RC1RE_1LD---_0LD1LA_1LF0RE_1RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;1;7;5;4;6;6;6;6] [0;1;2;3;4;5;2;3;6;7;8;8;2;3;8;8;8;8] sym_id n_sym). Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD1LC_1LE0RB_---0LA_1LE1RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB1LA_1RC0RD_1LD0LB_0LA1RE_1RF0RC_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;5;8;9;10;11;0;1;10;11;12;13;10;10;14;15;0;1;4;5;10;10;16;17;10;10;18;11;10;10] [0;1;2;3;4;5;6;7;8;8;9;10;11;12;0;1;8;8;8;8;13;14;8;8;15;16;8;8;4;5;8;8;17;18;8;8;11;12] sym_id n_sym). Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB---_1RC0LD_1LB0RF_0LD1LE_0LA0LE_0RF1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;3;4;2;1;4;4] [0;1;2;3;1;4;3;3;0;1] sym_id n_sym). Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB0LF_0RC0LE_1LD1RC_1LB0RE_0RB0LA_---1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;5;6;4;4;4;4;7;8;4;4;0;1] [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;10;18;10;10;14;19;20;21;10;11;16;22;6;23;24;25;10;18;2;26;10;18;27;28;2;3;10;10;2;3;29;30;2;31;10;11;2;23;10;18;14;19;10;10;14;32;14;33;2;34;2;31] sym_id n_sym). Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB0RF_1LC1RB_0RE0LD_1LB1LD_---0RA_1RE1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;0;1;4;1;4;4] [0;1;2;0;3;0;3;3] sym_id n_sym). Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB0RF_0LC1RE_1RD1LB_1RD0RA_---1LC_1RA1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;0;1;4;4;6;1;4;4] [0;1;2;3;4;5;0;1;4;4;4;1] sym_id n_sym). Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB0RE_0RC0RE_1LD---_0LD1LA_1RF0RC_0LA0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;4;4;4;4] [0;1;2;1;3;4;2;1;5;5;5;5] sym_id n_sym). Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB1LA_0RC0LF_1LD1RE_1LD1LB_1RB1RE_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;5;6;4;4;4;7;8;9;4;10;4;11;12;3;5;13;2;3;4;5;12;7] [0;1;2;3;2;2;4;0;5;2;2;3] sym_id n_sym). Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB0LD_1RC1LB_1LA0RE_1LF1LA_1RB1RE_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB1LA_0LC0RF_1LD1RC_---0LE_1RF0LC_1RA1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;4;1;5;1;5;1;5;5] sym_id n_sym). Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB0LF_0LC0RE_0RE0LD_1LE---_0RA0RF_1LA1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;0;1;4;3;5;6;6;7;8;9;10;11;12;13;9;9;14;6;15;16;17;18;17;18;6;19;20;6;21;22;23;6;6;8;12;13;6;7;24;18;10;11;6;19;25;21;17;26;21;22] [0;1;2;3;4;5;4;6;6;7;0;8;6;6;6;6;6;6] sym_id n_sym). Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB0LF_0LC0RE_0RE0LD_1LE---_0RA1RC_1LA1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;2;3;6;7;8;9;10;11;12;5;13;6;6;14;15;6;16;17;18;5;6;19;20;21;16;22;17;23;24;24;16;25;20;21;18;16;26;9;24;24;23;23;27;11;14;6;13;16;15;16] [0;1;2;3;4;5;3;3;3;6;0;3;3;3] sym_id n_sym). Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB0LF_0LC0RE_1RA0LD_1LE---_0RA0RF_1LA1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;2;3;6;7;8;9;10;9;11;12;13;5;14;15;16;14;17;18;19;20;21;22;15;21;23;6;21;22;16;24;25;15;26;14;5;27;21;21;23;6;10;9;28;6;28;6;6;7;11;12;11;12] [0;1;2;3;4;5;4;6;6;7;8;9;6;6;6;6;0;1;6;6] sym_id n_sym). Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB---_0RC0RF_1LD1LA_0LD1LE_0LA0LE_0RF0RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;1;3;3;3] [0;1;2;3;1;0;3;3] sym_id n_sym). Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB---_0LC0LD_1LE0RD_1RC1RE_0RF0LB_1LC0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;6;7;8;9;6;6;6;6;0;1;6;6] [0;1;2;1;3;4;5;6;7;8;9;8;10;11;12;4;13;14;15;13;16;17;18;19;20;21;14;20;22;5;20;21;15;23;24;14;25;13;4;26;20;20;22;5;9;8;27;5;27;5;5;6;10;11;10;11] sym_id n_sym). Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB---_0LC1LF_1LE0RD_1RC1RE_0RF0LB_0LB0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;3;3;3;6;0;3;3;3] [0;1;2;3;4;5;2;3;6;7;8;9;10;11;12;5;13;6;6;14;15;6;16;17;18;5;6;19;20;21;16;22;17;23;24;24;16;25;20;21;18;16;26;9;24;24;23;23;27;11;14;6;13;16;15;16] sym_id n_sym). Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB---_0LC0LD_1LE0RD_1RC1RE_0RF0LB_0LB0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;6;7;0;8;6;6;6;6;6;6] [0;1;2;3;0;1;4;3;5;6;6;7;8;9;10;11;12;13;9;9;14;6;15;16;17;18;17;18;6;19;20;6;21;22;23;6;6;8;12;13;6;7;24;18;10;11;6;19;25;21;17;26;21;22] sym_id n_sym). Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB0LD_0RC0RE_1LD---_0LD1LA_0RE1RF_1RC0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;4;3;2;4;4] [0;1;2;1;3;4;2;1;5;5;5;5] sym_id n_sym). Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD0LA_1RA1LF_1LC1RE_---0LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;0;4;4;4;7;4;8;4;9;4;10;4;5;4;11;4;8] [0;1;2;3;2;4;5;0;5;6;7;8;0;9;7;7;7;10;2;4;7;5] sym_id n_sym). Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB0RA_0RC1RA_1LD---_0LD0LE_1RF0RB_0RF1LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;3;3;1;0;3;3] [0;1;2;1;3;4;5;4;4;4;2;1] sym_id n_sym). Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB0RA_0RC---_1LD1RA_0LD0LE_1RF0RB_0RF1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;3;3;1;0] [0;1;2;1;3;4;5;4;4;4;2;1] sym_id n_sym). Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB0RA_0RC---_1LD0RB_0LD0LE_1RF1LB_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;3;3;1;0] [0;1;2;1;3;4;1;5;4;4;4;4] sym_id n_sym). Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB0RA_0RC---_1LD---_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;3;3;1;0] [0;1;2;1;3;4;1;4;4;4] sym_id n_sym). Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB0RD_0RC0RF_0LD1RF_0RE1LC_1RC---_1RA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;2;3;4;2;4;4] [0;1;2;3;4;5;2;3;2;3;6;7;7;8;6;7;9;9;9;9] sym_id n_sym). Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB0RE_0LC0RA_1LD0LC_1RB1LC_---1RF_1LC0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;5;6;7;8;9;10;5;3;1;1;11;12;11;13;11;12;14;6;12;12;11;12;15;16;12;10;12;12] [0;1;2;3;4;5;4;6;4;4;4;4;7;0;4;4] sym_id n_sym). Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB1LA_1LB0RC_1LD1RC_---1LE_1LF0RB_0LA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;2;7;8;9;0;1;2;7;8;8;4;2] [0;1;2;3;2;2;2;0] sym_id n_sym). Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB0LE_1LC0RF_1RD0RC_1LE---_0LE1LA_0RF1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;3;3;2;3] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB0RF_1LC0RE_0LC0LD_1LA---_0RE1RF_0RA1LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;5;1;3;5;5;3;1] [0;1;2;3;4;1;3;3;5;1;2;3] sym_id n_sym). Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RF_0RE1LD_1LC1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;4;4;4;4] [0;1;2;1;3;4;2;1;4;4] sym_id n_sym). Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LC_1LA1RD_0RF1LE_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;5;1;5;1;5;5] [0;1;2;0;3;0;3;3] sym_id n_sym). Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LC_1LA1RD_1RF1RB_---1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;1;6;1;2;3;6;6] [0;1;2;0;3;0;3;3] sym_id n_sym). Time Qed.

Lemma tm171: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LC_1LA1RD_0RF1RB_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;1;5;1;5;1;5;5] [0;1;2;0;3;0;3;3] sym_id n_sym). Time Qed.

Lemma tm172: ~halts (TM_from_str "1RB0RF_0RC0RC_0LD0RA_0LE1LD_1RA1RC_---0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;5;13;14;15;9;10;16;10;10;13;9;17;1;18;10;6;1;2;19;2;5;14;9;20;19;2;21;11;10;13;22;13;15] [0;1;2;3;4;4;5;6;4;4;4;4;4;7;0;1] sym_id n_sym). Time Qed.

Lemma tm173: ~halts (TM_from_str "1RB---_1LC0LE_0LC1LD_1LE0LD_1LA1RF_0RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;3;4;5;4;4;4;2;1] [0;1;2;3;4;5;3;2;1;6;6;6;6;6] sym_id n_sym). Time Qed.

Lemma tm174: ~halts (TM_from_str "1RB---_1LC1RB_1LA0LD_1RE1LD_1RF0LC_0RB0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;4;1;0;1] [0;1;2;2;3;1;4;5;4;4;6;3;3;6] sym_id n_sym). Time Qed.

Lemma tm175: ~halts (TM_from_str "1RB1RA_0RC0LE_1LD1RA_1LD1LB_---0LF_1RB1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;5;6;4;4;4;7;8;9;4;10;4;11;12;3;5;13;2;3;4;5;12;7] [0;1;2;3;2;2;4;0;5;2;2;3] sym_id n_sym). Time Qed.

Lemma tm176: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RF---_0RF1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;1;0;3;3] [0;1;2;1;1;3;3;3] sym_id n_sym). Time Qed.

Lemma tm177: ~halts (TM_from_str "1RB0LD_0LC0RD_1RA1LC_0LB0RE_1LB0RF_---1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;10;18;10;10;14;19;20;21;10;11;16;22;6;23;24;25;10;18;2;26;10;18;27;28;2;3;10;10;2;3;29;30;2;31;10;11;2;23;10;18;14;19;10;10;14;32;14;33;2;34;2;31] [0;1;2;3;4;4;5;6;4;4;4;4;7;8;4;4;0;1] sym_id n_sym). Time Qed.

Lemma tm178: ~halts (TM_from_str "1RB---_0LC1RF_1LD1LB_0RE0LB_1LB0RA_0RB0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;0;3;4;5;5;1;5;5] [0;1;0;2;3;2;2;4;2;5;5;5] sym_id n_sym). Time Qed.

Lemma tm179: ~halts (TM_from_str "1RB0RE_1LC1RB_0RA0LD_1LB1LD_0RF1RA_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;0;2;3;1;3;3] [0;1;2;3;4;5;5;1;4;4;0;6;2;7;5;6] sym_id n_sym). Time Qed.

Lemma tm180: ~halts (TM_from_str "1RB1LA_0RC0RD_0RD---_1LE1RD_1LF0RB_0LA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;2;3;1;4;5;4;4;6;3;3;6] [0;1;2;3;2;2;4;1;0;1] sym_id n_sym). Time Qed.

Lemma tm181: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_1LF1LD_---1RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;4;3;3;0;2] sym_id n_sym). Time Qed.

Lemma tm182: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_1LF1LD_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm183: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm184: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm185: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---0RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm186: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm187: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm188: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1RE1LF_1RA1RE_0LC0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm189: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1RE0LF_1RA1RE_1LC1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;2;3;0;1;4;1;4;4] sym_id n_sym). Time Qed.

Lemma tm190: ~halts (TM_from_str "1RB1LA_0LC0RE_0LF0LD_1RE1LC_1RA1RE_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm191: ~halts (TM_from_str "1RB1LA_0LC0RE_0LF0LD_1RE1LC_1RA1RE_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm192: ~halts (TM_from_str "1RB1LA_0LC0RE_0RF0LD_1RE1LC_1RA1RE_---1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;0;3;0;3;3] [0;1;0;2;3;1;3;3] sym_id n_sym). Time Qed.

Lemma tm193: ~halts (TM_from_str "1RB1LA_1RC0LD_0LA0RD_0LC0RE_1LC0RF_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;10;18;10;10;14;19;20;21;10;11;16;22;6;23;24;25;10;18;2;26;10;18;27;28;2;3;10;10;2;3;29;30;2;31;10;11;2;23;10;18;14;19;10;10;14;32;14;33;2;34;2;31] [0;1;2;3;4;4;5;6;4;4;4;4;7;8;4;4;0;1] sym_id n_sym). Time Qed.

