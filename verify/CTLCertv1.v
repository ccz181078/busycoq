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

Lemma tm194: ~halts (TM_from_str "1RB1LE_0RC1RB_1LD1RB_1LA1LD_0LD0LF_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;5;6;4;4;4;7;8;9;10;11;4;4;12;13;4;4;4;14;4;15;4;0;2;16;17;18;19;20;4;4;4;21;4;4;4;5;4;22;8;23;4;12] [0;1;2;3;2;2;2;4;5;6;7;8;2;9;10;11;2;12;2;13;14;2;15;16;17;18;19;1;2;20;3;2;2;21;9;18;2;22;8;2;23;24;17;20;2;25;22;25;2;7;10;26;2;8] sym_id n_sym). Time Qed.

Lemma tm195: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RA0LE_1LF---_0LC0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;7;11;7;7;7;7;12;13;14;7;5;15;16;17;7;18;19;20;7;7;7;21;7;7;22;7;6;13;23;7;24;18;25;26;7;27;7;28;7;21;23;29;30;7;31;7;32;7;7;33;3;27;7;28;7;34;30;35;36;7;37;34;38;39;7;40;7;7;41;7;42;43;7;10;7;29;44;45;7;46;44;47;48;7;7;34;7] [0;1;2;3;4;5;6;7;7;8;9;10;7;11;7;7;12;7;13;14;15;7;16;7;7;17;7;18;19;20;7;21;7;22;23;7;24;3;25;26;27;7;28;7;29;7;30;17;4;31;7;32;19;20;7;33;7;34;7;22;7;35;36;37;38;39;40;7;41;42;7;42;13;43;15;7;44;45;6;7;46;47;7;34;7;7;36;37;7;48;49;50;51;52;53;42;54;7;55;56;15;7;57;46;7;7;46;47;7;58;7;59;49;50;7;60;61;62;63;3;64;7;30;65;7;7;4;66;11;67;68;69;70;10;71;62;72;73;74;7;13;75;7;76;16;77;68;69;46;78;79;20;80;69;51;81;82;7;25;83;84;85;7;7;46;78;79;20;29;46;80;69] sym_id n_sym). Time Qed.

Lemma tm196: ~halts (TM_from_str "1RB1RE_0LC1RA_0RD1LC_1LA1LB_0RA0RF_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;6;8;9;6;6;6;10;11;12;13;6;14;15;16;17;18;19;6;6;20;21;6;6;22;23;6;24;6;6;25;6;1;6;26;6;16;27;28;6;5;6;29;12;30;10;31;32;6;6;33;34;35;2;3;6;36;6;26;6;29;37;14;6;38;6;8;6;39;6;22;17;40;6;41;6;42;2;43;6;44;6;39] [0;1;2;3;4;5;4;6;4;4;7;8;9;10;4;11;4;12;4;4;4;13;14;15;16;17;4;18;4;19;4;20;4;4;21;22;23;15;2;24;4;6;4;4;4;25;4;4;4;26;4;27;4;28;29;8;30;31;4;4;4;4;4;32;4;33;16;24] sym_id n_sym). Time Qed.

Lemma tm197: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD0RE_1RD0LA_1RF1LE_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;0;0;1;9;10;2;3;8;8;9;10;2;11;6;7] [0;1;2;3;4;5;6;7;8;8;0;4;0;7;9;3;8;8;4;3] sym_id n_sym). Time Qed.

Lemma tm198: ~halts (TM_from_str "1RB1LF_1RC0RB_1RD1RC_0LE---_1LA1RE_1LE0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;12;14;15;12;16;12;17;18;12;19;12;12;12;18;12;20;21;22;23;19;24;9;12;11;6;25;12;26;27;24;10;13;9;28;29;12;12;6;12;30;2;19;10;12;31;6;12;3;28;24] [0;1;2;3;2;2;4;5;2;6;2;7;2;8;9;10;2;11;2;12;2;13;2;12;2;14;15;1;2;16;2;17;2;6;2;18;2;19;2;17] sym_id n_sym). Time Qed.

Lemma tm199: ~halts (TM_from_str "1RB0RD_1RC0LD_0RD1RF_1LE0LA_0LF---_0RB0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;5;6;4;4;7;8;9;10;4;4;11;12;4;4;13;14;4;4;15;6;4;4;16;12;7;8;4;4] [0;1;2;3;4;5;6;7;8;7;9;9;10;11;12;7;13;1;14;5;15;7;16;16;17;7;9;7;8;7;18;3;19;3;7;7;6;7;20;7;21;22;15;7;23;3;24;3;20;7] sym_id n_sym). Time Qed.

Lemma tm200: ~halts (TM_from_str "1RB1LD_0RC0RB_1LC1RA_---0LE_1RB1LF_1RC0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;0;4;5;6;7;8;9;10;9;11;0;4;12;13;0;14;0;15;0;16;9;17;18;8;7;3;19;20;21;3;0;15;22;23;24;25;26;27;22;4;28;29;7;8;30;31;0;32;9;33;34;35;36;37;0;15;38;37;0;15;19;39;0;15;0;40;41;42;30;1;7;3;28;1;43;44;7;3;22;45;43;20;22;46;26;47;2;8;0;32;48;49;22;50;51;39;2;8;22;52;0;32] [0;1;2;3;4;4;5;6;4;4;4;7;8;9;4;4;4;4;10;1;4;11;12;4;4;13;14;4;4;15;12;4] sym_id n_sym). Time Qed.

Lemma tm201: ~halts (TM_from_str "1RB0LC_1LA0RA_1RD1LC_0RE1LA_1RF1LE_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;4;7;8;9;10;11;4;12;13;14;5;15;16;17;18;19;4;5;4;20;21;22;4;23;24;25;4;26;27;28;8;9;4;4;29;30;31;32;4;33;34;35;4;4;4;4;24;36;4;5;4;37;5;38;39;40;4;41;5;42;16;17;34;35;43;44;45;46;4;47;24;25;48;49;50;51;4;52;53;54;4;4;55;56;57;58;4;59;53;54;4;60;29;30;61;62;4;63;4;37;4;4;4;37;4;4;39;40;64;63;65;66;4;67;68;69;70;71;4;72;4;73;74;75;76;77;4;78;10;79;4;78;10;11;4;55;4;55;4;4;10;79;4;4;80;81;4;82;16;17;4;4;4;25;48;49] [0;1;2;3;4;5;6;7;8;8;9;10;11;12;13;14;8;8;15;16;17;18;8;8;19;20;8;21;22;3;8;8;8;23;8;8;24;25;26;27;27;25;28;7;7;29;30;31;32;33;34;31;8;8;8;35;4;36;9;31;8;8;37;38;8;8;39;40;32;41;8;3;42;43;44;45;46;25;8;47;6;48;49;50;8;8;8;25;8;8;51;52;8;53;4;36;54;55;8;56;57;58;8;59;16;40;39;60;8;21;22;40;8;59;32;61;62;63;64;7;65;66;8;50;44;45;46;67;8;8;11;12;13;68;34;58;22;60] sym_id n_sym). Time Qed.

Lemma tm202: ~halts (TM_from_str "1RB0LA_0RC1LE_1RD0RD_0LE1RF_---1LA_1RC1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;0;1;6;7;8;9;6;6;6;2;6;10;11;12;6;7;6;13;6;6;6;6] [0;1;2;3;4;5;6;7;8;7;7;9;3;1;7;7;7;7;10;7;11;7;2;12;7;10] sym_id n_sym). Time Qed.

Lemma tm203: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA0LA_0RF1RE_0RB1RE_---1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;4;4;7;8;4;9;4;10;11;12;4;13;4;14;4;15;4;16;4;4;17;18;19;20;4;21;4;22;4;23;4;24;25;26;4;27;25;4;4;8;4;28;4;29;30;31;4;4;32;33;4;4;34;35;4;1;4;36;4;37;4;38;4;39;11;4;4;40;4;41;4;36;42;43;4;44;4;45;2;4;4;46;4;22] [0;1;2;3;4;5;4;6;4;4;7;4;8;9;4;10;4;11;4;12;13;14;4;15;4;16;4;17;4;18;4;19;20;21;22;23;24;25;26;4;4;27;28;29;4;30;4;31;4;32;4;33;4;34;35;36;37;38;4;39;40;4;41;42;4;43;4;44;4;45;4;46;4;47;4;48;49;45;4;50;4;51;4;52;4;53;4;54;4;55;4;56;57;4;24;4;4;36;4;58;4;59;60;14;4;61;4;62;63;4;20;64;41;4;4;65;66;4;4;67;4;68;4;69;4;70;4;71;4;72;73;74;4;75;76;77;2;78;8;4;79;80;4;81;4;82;4;83;4;84;85;23;4;86;28;87;4;88;4;89;4;90;4;91;4;92;93;4;37;94;4;95;96;81;4;97;8;98;99;61;4;100;37;4;4;101;4;102;4;103;104;4;4;105;4;9;4;106;4;107;4;108;4;109;110;4;4;111;4;112;113;4;4;114;115;4;4;116;76;117;4;118;4;119;120;4;4;121;4;122;4;123;4;124;4;125;126;127;128;129;4;130;131;14;28;132;133;134;135;136;4;25;4;137;4;138;4;139;4;140;141;78;4;142;4;143;4;144;4;145;4;146;4;147;35;4;63;82;93;43;4;94;4;148;96;4;4;98;99;4;26;100;104;15;4;42;49;4] sym_id n_sym). Time Qed.

Lemma tm204: ~halts (TM_from_str "1RB0LD_1RC1LB_0LA0RF_1LE1LD_1RF1LA_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;8;8;8;9;10;11;12;8;8;8;13;14;15;8;16;17;7;8;18;8;19;20;10;8;21;9;8;22;23;8;8;24;25;22;23;26;27;28;27;8;29;30;31;8;32;33;34;8;35;8;8;36;8;37;38;8;18;39;8;40;41;8;21;8;8;8;42;43;44;8;8;8;45;46;23;8;47;48;25;49;47;8;8;50;8;51;52;8;29;8;53;8;13;54;8;55;38;8;8;8;8;8;56;8;8] [0;1;2;3;4;5;6;7;4;4;4;4;8;9;10;11;0;12;13;14;4;15;4;16;2;3;4;17;18;19;4;20;2;21;4;4;22;23;24;25;26;4;26;27;4;28;4;29;8;30;31;32;8;33;10;11;4;4;4;34;13;14;35;36;13;14;4;16;4;4;4;37;4;38;4;4;6;39;4;4] sym_id n_sym). Time Qed.

Lemma tm205: ~halts (TM_from_str "1RB1LD_1RC1RE_1RD0RB_1LE0LD_1RF0LA_---0RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;8;10;8;11;8;8;8;8;12;8;13;8;8;14;8;15;8;16;17;8;8;18;19;20;21;22;23;24;8;25;26;27;8;28;8;29;30;31;32;33;34;8;35;36;37;8;38;8;39;8;8;40;8;41;42;43;44;45;8;46;8;47;8;48;8;49;8;50;8;51;52;7;53;8;8;54;8;55;8;56;26;57;8;58;59;8;60;8;8;61;19;62;44;63;8;64;8;65;66;8;67;8;68;8;32;8;69;69;8;70;8;33;8;8;71;27;72;73;19;74;44;75;8;76;8;77;8;78;8;79;19;80;21;81;82;83;32;16;26;27;17;57;8;7;8;84;8;85;86;8;87;88;8;29;8;89;8;41;76;42;8;8;8;90;82;31;37;33;52;8;8;91;92;8;93;93;8;94;95;8;8;96;8;97;98;93;8;99;8;8] [0;1;2;3;4;5;6;7;8;9;10;11;7;12;7;7;13;14;15;7;13;16;17;7;7;18;19;20;21;7;22;23;19;9;22;24;25;7;26;7;27;28;7;7;29;7;30;31;32;33;7;34;22;35;22;36;7;37;37;7;37;37;38;7;39;37;40;7;7;41;28;7;42;43;19;9;7;44;19;45;46;47;7;7;13;37;48;7;49;50;51;7;52;7;53;50;22;24;54;7;55;7;22;56;57;7;58;59;60;61;46;62;30;63;7;64;60;65;7;66;67;7;68;7;69;7;70;7;71;7;72;7;73;7;59;7;7;74;75;59;76;77;78;79;57;74;7;7;7;80;7;81;82;7;83;50;84;7;85;7;86;7;87;7;7;88;89;90;91;92;93;94;76;95;7;7;96;7;97;61;98;7;99;7;100;7;101;7;102;7;103;7;7;104;105;7;7;106;107;7;108;109;108;7;7;107;110;90;7;111;7;112;113;114;7;115;7;116;7;117;97;7;118;7;119;7;120;7;121;7;122;7;123;7;124;7;7;7;7;7;125;7;7;126;7;7;7;127;7;128;7;129;113;130;91;131;7;132;133;7;134;135;136;7;135;6;7;127;7;137;7;125;108;138;113;139;7;140;141;6;142;7;7;126;7;128] sym_id n_sym). Time Qed.

Lemma tm206: ~halts (TM_from_str "1RB0LF_1RC---_0RD0RF_1LE1RC_1LA0RA_0LE0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;4;9;10;11;12;4;13;14;2;15;16;7;4;4;4;4;17;18;6;19;4;9;4;4;20;3;21;11;4;5;2;15] [0;1;2;3;4;5;6;7;8;5;5;5;9;1;10;11;12;5;6;13;14;5;15;5;5;5;16;11;5;5;17;1;18;5;19;5;5;5;20;5;5;5] sym_id n_sym). Time Qed.

Lemma tm207: ~halts (TM_from_str "1RB0LC_1RC1RD_0LD1LC_1RE0LC_0RF---_0RA1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;7;8;9;7;7;10;7;7;7;5;7;6;11;7;7;12;7;13;7;14;15;16;17;18;19;14;7;20;7;21;11;22;7;23;24;25;9;9;7;7;7;4;26;27;7;28;29;25;7;16;7;4] [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;12;13;20;21;22;13;13;13;23;24;6;25;26;27;28;29;30;13;31;32;33;24;6;34;35;36;37;38;39;40;41;15;13;13;42;43;44;13;45;46;47;48;49;24;50;51;52;53;54;43;55;13;56;57;58;17;59;60;13;13;45;61;62;24;44;13;13;63;64;48;48;13;65;66;67;68;6;69;6;70;71;13;72;73;74;17;75;53;76;13;77;78;79;80;13;81;77;78;82;80;41;83;13;84;37;85;65;43;86;24;76;13;86;63;55;13;87;88;89;48;89;73;90;91;92;24;50;70;22;13;93;24;37;91;6;44;94;13;95;17;6;27;96;13;97;9;98;99;86;13;100;101;13;13;102;80;45;103;92;24;104;68;100;105;13;43;22;43;13;13;106;13;107;13;108;68;109;13;41;110;111;80;41;112;8;9;113;66;114;78;89;115;26;27;96;27;116;27;90;117;50;99;118;17;119;25;120;13;121;122;119;69;77;78;59;123;124;36;125;13;37;117;126;44;127;15;89;128;116;27;22;27;129;27;130;24;98;70;131;36;79;48;132;133;114;78;134;135;102;80;13;136;113;43] sym_id n_sym). Time Qed.

Lemma tm208: ~halts (TM_from_str "1RB0RA_1LC0LD_1RA0LB_0LE0RC_1RC1LF_0RC---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;3;4;5;0;3;6;7;8;9;9;9;10;9;9;9;9;3;6] [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;11;11;11;11;7;8;11;11] sym_id n_sym). Time Qed.

Lemma tm209: ~halts (TM_from_str "1RB0RA_1LC0LD_1RA0LB_0LE0RC_1RC0LF_1LC---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;3;4;5;0;3;6;7;8;9;9;9;10;9;9;9;9;3;6] [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;8;8;8;8;7;8] sym_id n_sym). Time Qed.

Lemma tm210: ~halts (TM_from_str "1RB0RC_0RC0LD_1LA1RE_0LA1LD_0RF0RD_---1LC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;5;6;7;8;0;1;4;3;9;10;11;6;12;12;13;6;12;12;12;12;13;6] [0;1;2;3;4;5;6;7;4;4;0;8;0;9;10;11;4;4;10;11;8;12;6;7;6;7] sym_id n_sym). Time Qed.

Lemma tm211: ~halts (TM_from_str "1RB0RC_0RC0LD_1LA0RE_0LA1LD_1RF1LE_---0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;1;7;5;0;1;8;9;10;10;8;9;11;3;10;10;2;3] [0;1;2;3;4;5;6;7;4;4;0;8;0;9;10;11;4;4;10;11;4;12;6;7;6;7] sym_id n_sym). Time Qed.

Lemma tm212: ~halts (TM_from_str "1RB---_1LC0RD_1LD0LC_1RB0RE_0RF0LB_1LB0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;8;8;11;8;7;8;8;8] [0;1;2;3;4;5;6;7;8;9;10;11;4;12;6;13;14;15;10;11;16;17;18;16;19;20;6;13;21;22;23;24;8;25;10;11;26;27;24;28;29;21;21;30;19;20;24;31;29;21;32;33;29;34;24;35;16;36;37;38;23;24;24;35;16;39;18;16;16;36;40;40;23;24;40;41;40;40;19;20;40;40;24;35] sym_id n_sym). Time Qed.

Lemma tm213: ~halts (TM_from_str "1RB1RA_0LC0RE_1LD1RC_1RA0LC_1RA0RF_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;2;4;5;6;7;8;2;9;10;11;2;12;2;13;14;2;15;16;17;18;19;20;2;21;22;2;2;23;24;18;2;25;26;2;2;3;27;28;2;4;17;21;2;13;2;29;2;12;30;29;2;31;10;32;2;29;10;11;2;8] [0;1;2;3;4;5;6;7;4;4;4;4;8;9;10;11;4;4;12;13;4;14;15;16;4;17;18;19;4;20;20;21;22;23;4;4;4;4;24;25;4;4;26;27;4;4;0;1;4;5;28;29;4;30;31;32;4;33;34;6;4;4;4;4;35;36;4;4;4;4;4;4;37;38;4;14;39;15;4;20] sym_id n_sym). Time Qed.

Lemma tm214: ~halts (TM_from_str "1RB---_1RC0RC_1LD0RA_1RE0LD_0RF0RB_0LC1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;7;4;15;16;7;17;5;18;3;8;9;12;8;12;13;19;20;12;13;4;21;17;5;20;20;20;20;22;7;12;13] [0;1;2;3;4;5;6;6;7;8;9;10;6;6;6;6;11;10;12;1;4;3;12;1;0;1] sym_id n_sym). Time Qed.

Lemma tm215: ~halts (TM_from_str "1RB0LA_0RC0RE_0LD1RE_1LA0RF_1RD0RD_1RE---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;3;7;8;9;7;9;5;4;10;11;3;7;8;12;13;9;5;13;13;13;13] [0;1;2;3;4;5;6;6;7;8;9;10;6;6;6;6;9;10;0;1;4;3] sym_id n_sym). Time Qed.

Lemma tm216: ~halts (TM_from_str "1RB0LA_0RC0RE_0LD1RE_1LA0RF_1RD0RD_1LB---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;3;7;8;9;7;9;5;4;10;11;3;7;8;12;13;9;5;13;13;13;13] [0;1;2;3;4;5;6;6;7;8;9;10;6;6;6;6;9;10;0;1;4;3] sym_id n_sym). Time Qed.

Lemma tm217: ~halts (TM_from_str "1RB0RB_1LC1RC_1RA1RD_1LF1LE_---0LD_0RA0LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;4;4;0;9;0;1;2;3] [0;1;2;3;4;5;4;4;4;4;6;7;8;9;10;4;11;3;12;3;4;13;14;7;6;5;11;3;8;15;2;3] sym_id n_sym). Time Qed.

Lemma tm218: ~halts (TM_from_str "1RB0LD_1RC1RA_1RD0RA_0RE0RD_1LF---_0LF1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;7;11;12;12;13;9;9;9;9;14;9;14;9;15;16;17;9;9;9;18;9;19;20;11;9;9;9;9;21;21;9;22;23;24;9;19;25;9;9;26;23;27;28;24;9;10;29;26;30;6;29] [0;1;2;3;4;5;6;7;8;9;10;7;11;12;7;7;13;14;10;7;15;16;17;18;19;7;7;7;7;7;8;9;10;7;20;21;22;23;24;12;7;7;19;7;25;12;26;7;27;28;29;30;31;16;20;32;22;23;33;34;35;23;13;14;7;7;7;7;7;7;36;12;37;38;33;39;35;23;19;7] sym_id n_sym). Time Qed.

Lemma tm219: ~halts (TM_from_str "1RB1RE_0LC1LB_1RD1LB_1RA1RD_0RD0RF_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;6;8;6;9;6;6;10;11;12;13;6;14;15;16;17;18;16;6;6;19;17;20;17;21;6;22;23;6;6;24;6;25;6;16;26;27;2;5;6;28;12;1;10;29;19;6;6;30;31;32;6;4;2;28;9;14;6;15] [0;1;2;3;4;4;5;6;4;4;4;7;8;9;10;11;4;4;12;13;4;4;4;14;4;15;4;0;2;16;17;18;19;20;4;4;4;21;4;4;4;5;4;22;8;23;4;12] sym_id n_sym). Time Qed.

Lemma tm220: ~halts (TM_from_str "1RB1LA_0RC1LE_1LD0RF_1RE1RB_---0LA_1RD1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;0;0;1;9;10;2;3;8;8;9;10;2;11;6;7] [0;1;2;3;4;5;6;7;4;4;0;8;0;7;9;3;4;4;4;3] sym_id n_sym). Time Qed.

Lemma tm221: ~halts (TM_from_str "1RB1LE_1RC0RB_0RD1RC_0LE---_1LF0LF_1LA1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;12;14;15;12;16;12;17;18;12;19;12;12;12;18;12;20;21;22;23;19;24;9;12;11;6;25;12;26;27;24;10;13;9;28;29;12;12;6;12;30;2;19;10;12;31;6;12;3;28;24] [0;1;2;3;2;2;4;5;2;6;2;7;2;8;9;10;2;11;2;12;2;13;2;12;2;14;15;1;2;16;2;17;2;6;2;18;2;19;2;17] sym_id n_sym). Time Qed.

Lemma tm222: ~halts (TM_from_str "1RB1RD_1LC1LB_0RA0LC_---0RE_1RF1RE_1RC0LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;3;4;3;3;3;5;3;6;7;8;3;9;3;10;3;3;0;11;3;12;3;13;3;14;3;15;3;16;7;13] [0;1;2;3;4;5;6;7;4;4;4;6;4;8;9;10;4;11;12;13;6;14;4;13;15;4;16;17;9;18;19;20;4;4;4;21;6;22;23;24;25;26;27;28;29;30;31;4;27;32;4;5;6;33;34;4;4;35;36;13;6;37;38;4;4;39;40;41;42;4;34;17;43;4;40;44;45;46;34;6;36;13;6;47;48;4;49;46;6;50;51;24;52;53;9;53;54;55;56;24;9;30;57;55;4;5;6;58;16;4;16;59;31;4;60;4;29;53;4;61;45;46;27;62;4;27] sym_id n_sym). Time Qed.

Lemma tm223: ~halts (TM_from_str "1RB1RA_1LC1LD_0RA0LD_0RB0LE_1LF1RC_---0LA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;0;8;0;9;10;11;4;4;10;11;4;11;6;7] [0;1;2;3;4;3;5;6;7;8;0;1;9;3;7;7;10;6;4;8;3;6] sym_id n_sym). Time Qed.

Lemma tm224: ~halts (TM_from_str "1RB1RD_1RC0LA_1LD0RA_0LE1LB_---1LF_1RF0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;8;9;8;10;8;10;4;11;12;13;4;14;4;4;4;15;16;17;6;18;8;19;8;20;21;22;4;4;12;13;8;23;8;24;8;25;26;27;11;14;26;27;0;28;16;17;2;29;30;31;0;32;26;33;2;29;30;34;35;36;0;34;30;31] [0;1;2;3;4;5;6;7;0;8;6;9;10;3;11;12;2;3;13;12;4;5;14;15;16;11;14;14;14;14;17;11;4;18;4;18;19;20;14;20;21;22;10;23;14;12;19;15] sym_id n_sym). Time Qed.

Lemma tm225: ~halts (TM_from_str "1RB0RD_1LC0RE_0LD0LB_1RA0LB_1RF---_0LF0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;0;2;3;4;5;6;3;7;7;4;5;7;7;7] [0;1;2;3;4;5;6;7;7;8;9;3;7;10;7;7;11;3;2;1;12;7;4;8;6;3] sym_id n_sym). Time Qed.

Lemma tm226: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA0LA_0RF1LE_0RB1RE_---1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;4;4;7;8;4;9;4;10;11;12;4;13;4;14;4;15;4;16;4;4;17;18;19;20;4;21;4;22;4;23;4;24;25;26;4;27;25;4;4;8;4;28;4;29;30;31;4;4;32;33;4;4;34;35;4;1;4;36;4;37;4;38;4;39;11;4;4;40;4;41;4;36;42;43;4;44;4;45;2;4;4;46;4;22] [0;1;2;3;4;5;4;6;4;4;7;4;8;9;4;10;4;11;4;12;13;14;4;15;4;16;4;17;4;18;4;19;20;21;22;23;24;25;26;4;4;27;28;29;4;30;4;31;4;32;4;33;4;34;35;36;37;38;4;39;40;4;41;42;4;43;4;44;4;45;4;46;4;47;4;48;49;45;4;50;4;51;4;52;4;53;4;54;4;55;4;56;57;4;24;4;4;36;4;58;4;59;60;14;4;61;4;62;63;4;20;64;41;4;4;65;66;4;4;67;4;68;4;69;4;70;4;71;4;72;73;74;4;75;76;77;2;78;8;4;79;80;4;81;4;82;4;83;4;84;85;23;4;86;28;87;4;88;4;89;4;90;4;91;4;92;93;4;37;94;4;95;96;81;4;97;8;98;99;61;4;100;37;4;4;101;4;102;4;103;104;4;4;105;4;9;4;106;4;107;4;108;4;109;110;4;4;111;4;112;113;4;4;114;115;4;4;116;76;117;4;118;4;119;120;4;4;121;4;122;4;123;4;124;4;125;126;127;128;129;4;130;131;14;28;132;133;134;135;136;4;25;4;137;4;138;4;139;4;140;141;78;4;142;4;143;4;144;4;145;4;146;4;147;35;4;63;82;93;43;4;94;4;148;96;4;4;98;99;4;26;100;104;15;4;42;49;4] sym_id n_sym). Time Qed.

Lemma tm227: ~halts (TM_from_str "1RB0LA_1LC1RE_0LC0LD_1LA1RD_0RF---_0RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;4;5;6;2;2;3;3;7;8;2;9;2;7;2] [0;1;2;3;4;5;3;3;6;7;3;3;2;3;8;9;7;10;11;3;12;3;13;5;14;3;9;3;15;7;12;3] sym_id n_sym). Time Qed.

Lemma tm228: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LC_0RE0LB_1LB1RF_0LB---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;11;11;12;11;7;8;11;11;11;11] [0;1;2;3;4;5;6;7;8;9;10;11;4;12;6;13;14;15;10;11;16;17;18;16;19;20;6;13;21;22;23;24;8;25;10;11;26;27;24;28;29;21;21;30;19;20;24;31;29;21;32;33;29;34;24;35;16;36;37;38;23;24;24;35;16;39;18;16;16;36;40;40;23;24;40;41;40;40;19;20;40;40;24;35] sym_id n_sym). Time Qed.

Lemma tm229: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RA_1LA---_0RC0LF_0LD1LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;5;8;9;10;11;9;12;13;14;15;9;9;16;17;9;18;19;5;20;21;22;5;9;23;24;9;6;25;26;5;5;27;28;5;29;13;5;8;29;13;9;30;16;17;31;9;32;15;5;33;34;5;6;9;9;30;22;5;35;15;5;36;37;5;38;39;5;40;41;5;9;42;43;39;5;44;45;46;41;5;47;15;48;5;49;50;37;5;5;51;48;5;45;46;52;39;53;5;5;54;55;39;53;5] [0;1;2;3;4;5;6;7;8;9;10;8;11;8;8;12;8;8;8;8;13;5;8;14;8;8;8;15;16;8;17;18;8;19;2;8;8;20;21;8;14;4;18;19] sym_id n_sym). Time Qed.

Lemma tm230: ~halts (TM_from_str "1RB0LE_1LC1RF_1RE0LD_0LE1LD_1RC0RA_---0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;8;12;13;14;8;8;15;16;17;18;19;20;21;22;8;9;10;1;23;24;8;25;8;26;2;27;8;28;6;2;19;15;8;29;30;12;4;31;32;4;33;34;8;35;31;36;37;38;39;19;40;21;8;8;4;31;8;35;41;17;8;30;8;8;8;12;8;8;28;26;8;8] [0;1;2;3;4;5;6;7;8;8;8;9;10;11;12;13;8;8;14;15;8;8;8;16;17;18;19;1;8;8;8;20;21;22;8;8;8;23;24;25;4;5;8;8;8;26;27;28;8;8;29;30;10;11;8;8;8;31;8;8;32;33;17;18;8;8;34;35;8;8;24;25] sym_id n_sym). Time Qed.

Lemma tm231: ~halts (TM_from_str "1RB0LE_1LC0RF_1RE0LD_0LE1LD_1RC0RA_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;8;8;16;17;18;19;20;21;8;22;23;24;8;9;10;1;25;26;12;27;8;28;2;12;8;29;6;2;30;18;20;16;8;31;8;13;4;32;33;4;26;12;32;34;8;8;35;25;18;23;8;8;8;36;8;8;37;20;8;8] [0;1;2;3;4;5;6;7;8;8;8;9;10;11;12;13;8;8;14;15;8;8;8;16;17;18;19;1;8;8;8;20;21;22;8;8;8;23;24;25;4;5;8;8;8;26;27;28;8;8;29;30;10;11;8;8;8;31;8;8;32;33;17;18;8;8;34;35;8;8;24;25] sym_id n_sym). Time Qed.

Lemma tm232: ~halts (TM_from_str "1RB0LC_1RC0RB_1LA0LD_0LE0RA_1RA1LF_0RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;4;12;6;13;14;15;10;11;16;17;18;16;19;20;6;13;21;22;23;24;8;25;10;11;26;27;24;28;29;21;21;30;19;20;24;31;29;21;32;33;29;34;24;35;16;36;37;38;23;24;24;35;16;39;18;16;16;36;40;40;23;24;40;41;40;40;19;20;40;40;24;35] [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;11;11;12;11;7;8;11;11;11;11] sym_id n_sym). Time Qed.

Lemma tm233: ~halts (TM_from_str "1RB0LC_1RC0RB_1LA0LD_0LE0RA_1RA0LF_1LA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;4;12;6;13;14;15;10;11;16;17;18;16;19;20;6;13;21;22;23;24;8;25;10;11;26;27;24;28;29;21;21;30;19;20;24;31;29;21;32;33;29;34;24;35;16;36;37;38;23;24;24;35;16;39;18;16;16;36;40;40;23;24;40;41;40;40;19;20;40;40;24;35] [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;8;8;11;8;7;8;8;8] sym_id n_sym). Time Qed.

Lemma tm234: ~halts (TM_from_str "1RB---_0LC0LD_0RE1LD_1LE0LE_1RF0LA_1LB0RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;7;8;9;10;6;6;6;6;11;10;12;13;4;3;12;13;12;13;2;3] [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;7;4;15;16;7;17;5;18;3;8;9;12;8;12;13;19;20;12;13;4;21;17;5;20;20;20;20;22;7;12;13] sym_id n_sym). Time Qed.

Lemma tm235: ~halts (TM_from_str "1RB0RE_0LC0RD_1LA1LC_1RE0RE_0LF1LB_1RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;0;1;10;7;2;3;11;11;0;1;10;7;11;11] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm236: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_1RE0RE_0LF1LB_1RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;0;0;1;9;7;2;3;10;10;9;7;10;10] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm237: ~halts (TM_from_str "1RB1RA_1LC0RE_1RA0LD_1LC1RD_1RA0RF_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;2;4;5;6;7;8;2;9;10;11;2;12;2;13;14;2;15;16;17;18;19;20;2;21;22;2;2;23;24;18;2;25;26;2;2;3;27;28;2;4;17;21;2;13;2;29;2;12;30;29;2;31;10;32;2;29;10;11;2;8] [0;1;2;3;4;5;6;7;4;4;4;4;8;9;10;11;4;4;12;13;4;14;15;16;4;17;18;19;4;20;20;21;22;23;4;4;4;4;24;25;4;4;26;27;4;4;0;1;4;5;28;29;4;30;31;32;4;33;34;6;4;4;4;4;35;36;4;4;4;4;4;4;37;38;4;14;39;15;4;20] sym_id n_sym). Time Qed.

Lemma tm238: ~halts (TM_from_str "1RB1RA_1LC0RE_1RA0LD_1LC1RB_1RA0RF_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;2;4;5;6;7;8;2;9;10;11;2;12;2;13;14;2;15;16;17;18;19;20;2;21;22;2;2;23;24;18;2;25;26;2;2;3;27;28;2;4;17;21;2;13;2;29;2;12;30;29;2;31;10;32;2;29;10;11;2;8] [0;1;2;3;4;5;6;7;4;4;4;4;8;9;10;11;4;4;12;13;4;14;15;16;4;17;18;19;4;4;20;21;22;23;4;4;4;4;24;25;4;4;26;27;4;4;0;1;4;5;28;29;4;30;31;32;4;33;34;35;4;4;4;4;36;37;4;4;4;4;8;9;4;4;38;39;4;14;40;41;4;4;20;21] sym_id n_sym). Time Qed.

Lemma tm239: ~halts (TM_from_str "1RB0LF_1LC0RB_0LE0LD_1LA0LA_0RA1LD_1LD---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;7;8;9;10;6;6;6;6;9;10;0;1;4;3] [0;1;2;3;4;5;6;3;7;8;9;7;9;5;4;10;11;3;7;8;12;13;9;5;13;13;13;13] sym_id n_sym). Time Qed.

Lemma tm240: ~halts (TM_from_str "1RB0LF_1LC0RB_0LE0LD_1LA0LA_0RA1LD_1RC---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;7;8;9;10;6;6;6;6;9;10;0;1;4;3] [0;1;2;3;4;5;6;3;7;8;9;7;9;5;4;10;11;3;7;8;12;13;9;5;13;13;13;13] sym_id n_sym). Time Qed.

Lemma tm241: ~halts (TM_from_str "1RB1LF_1RC0LD_1RD0RC_1LB0LE_0LA0RB_0RB---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;4;12;6;13;14;15;10;11;16;17;18;16;19;20;6;13;21;22;23;24;8;25;10;11;26;27;24;28;29;21;21;30;19;20;24;31;29;21;32;33;29;34;24;35;16;36;37;38;23;24;24;35;16;39;18;16;16;36;40;40;23;24;40;41;40;40;19;20;40;40;24;35] [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;11;11;12;11;7;8;11;11;11;11] sym_id n_sym). Time Qed.

Lemma tm242: ~halts (TM_from_str "1RB0LF_1RC0LD_1RD0RC_1LB0LE_0LA0RB_1LB---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;4;12;6;13;14;15;10;11;16;17;18;16;19;20;6;13;21;22;23;24;8;25;10;11;26;27;24;28;29;21;21;30;19;20;24;31;29;21;32;33;29;34;24;35;16;36;37;38;23;24;24;35;16;39;18;16;16;36;40;40;23;24;40;41;40;40;19;20;40;40;24;35] [0;1;2;1;3;4;5;1;6;5;7;8;9;10;5;1;8;8;11;8;7;8;8;8] sym_id n_sym). Time Qed.

Lemma tm243: ~halts (TM_from_str "1RB0LC_1RC0RA_1LD0RE_0LA0LC_1RF---_0LF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;0;2;3;4;5;6;3;7;7;4;5;7;7;7] [0;1;2;3;4;5;6;7;7;8;9;3;7;10;7;7;11;3;2;1;12;7;4;8;6;3] sym_id n_sym). Time Qed.

Lemma tm244: ~halts (TM_from_str "1RB1LD_1LB0RC_1LA1RC_1LE0LF_0LA0LE_---0RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;6;8;9;10;11;11;2;12;9;13;14;15;6;16;11;11;4;17;6;8;6;8;11;18;2;19;9;20;11;21;6;22;4;23;14;24;9;25;2;3;11;18;4;26;9;10] [0;1;2;3;2;2;4;5;2;2;6;7;8;9;4;10;11;12;2;13;14;5;8;9;4;10;4;2;2;2] sym_id n_sym). Time Qed.

Lemma tm245: ~halts (TM_from_str "1RB0RB_1LC1RF_1RA0LD_1LE1LC_0RA0LE_1RA---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;4;4;0;9;0;1;2;3] [0;1;2;3;4;5;4;4;4;4;6;7;8;9;10;4;11;3;12;3;4;13;14;7;6;5;5;3;8;15;2;3] sym_id n_sym). Time Qed.

Lemma tm246: ~halts (TM_from_str "1RB0RB_1LC1RC_1RA0LD_1LE1LF_0RA0LE_---0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;4;4;0;9;0;1;2;3] [0;1;2;3;4;5;4;4;4;4;6;7;8;9;10;4;11;3;12;3;4;13;14;7;6;5;5;3;8;15;2;3] sym_id n_sym). Time Qed.

Lemma tm247: ~halts (TM_from_str "1RB0RB_1LC1RC_1RA0LD_1LE0LF_0RA0LE_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;8;4;4;0;9;0;1;2;3] [0;1;2;3;4;5;6;4;6;6;7;8;6;6;9;10;11;6;12;3;13;3;6;14;15;8;7;5;12;3;9;16;2;3] sym_id n_sym). Time Qed.

Lemma tm248: ~halts (TM_from_str "1RB0LA_1LC1RF_0LC0LD_0LE1RE_1LA---_0RF0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;4;5;6;2;2;3;7;2;3;8;9;2;10;2;11;2;8;2] [0;1;2;3;2;3;4;5;6;7;8;9;4;5;10;9;11;9;9;9;12;9;13;14;15;9;5;9;9;9;16;6;10;9] sym_id n_sym). Time Qed.

Lemma tm249: ~halts (TM_from_str "1RB0RC_1RC0RA_1LD1RB_1RD1RE_---0LF_0LA1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;8;8;12;13;8;8;14;15;6;16;8;8;17;18;19;20;21;8;8;22;23;24;8;25;26;27;28;8;8;21;29;1;6;30;31;18;8;8;32;33;34;5;8;8;34;35;21;8;12;36;8;8;22;8;8;28;8;8;37;38;8;39;40;16;8;41;8;9;8;13;8;25] [0;1;2;3;4;5;6;7;4;4;8;9;4;4;4;10;4;11;12;13;14;15;16;17;4;4;4;18;4;4;19;20;4;21;22;23;24;25;4;4;4;26;2;3;4;4;4;27;4;28;29;30;31;32;4;33;31;34;4;4;4;35;4;4;24;36;14;37;4;27;19;38;4;10;4;39;40;41;4;28;4;4;4;18] sym_id n_sym). Time Qed.

Lemma tm250: ~halts (TM_from_str "1RB1RE_1LC0RF_1RE0LD_1LC1RB_---1RA_1RA0RD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;2;2;2;4;5;6;7;8;2;9;10;11;2;12;2;13;14;2;15;16;17;18;19;20;2;21;22;2;2;23;24;18;2;25;26;2;2;3;27;28;2;4;17;21;2;13;2;29;2;12;30;29;2;31;10;32;2;29;10;11;2;8] [0;1;2;3;4;5;6;7;4;4;4;4;8;9;10;11;4;4;12;13;4;14;15;16;4;17;18;19;4;4;20;21;22;23;4;4;4;4;24;25;4;4;26;27;4;4;0;1;4;5;28;29;4;30;31;32;4;33;34;35;4;4;4;4;36;37;4;4;4;4;8;9;4;4;38;39;4;14;40;41;4;4;20;21] sym_id n_sym). Time Qed.

Lemma tm251: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1LC_1RB0RF_1RF1RA_---1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;1;7;8;0;1;9;10;11;11;0;1;9;10;2;3;11;11] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm252: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1LC_1RB0LC_1RF1RA_---1LB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;3;0;2;5;6;7;8;7;2;7;7;8;2] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm253: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1LC_1RB0LC_0RF1RA_---1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;0;5;1;6;0;5;7;6;6;2;3] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm254: ~halts (TM_from_str "1RB0LB_0LC1RE_1LD1RC_---0LE_1RA0RF_1LB1RA") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;4;5;4;4;6;7;8;9;4;10;4;4;11;12;2;13;4;4;14;15;16;1;4;4;17;18;4;19;20;21;2;22;2;23;4;4;14;24;17;25;4;26;27;28;29;22;30;23;4;4;2;31;8;32;8;33;11;25;27;34;4;35;14;36;14;37;11;18;4;19] [0;1;2;3;4;4;5;6;4;4;7;8;9;10;4;4;11;12;13;14;15;6;4;4;16;17;4;4;18;19;7;8;4;4;20;21;4;4;22;23;4;4;24;25;4;4;26;27;4;4;28;29;4;4;30;10;4;4;31;25;4;4;7;8] sym_id n_sym). Time Qed.

Lemma tm255: ~halts (TM_from_str "1RB1RC_1LC---_0RF0LD_1LE0LC_1RF1RE_0RA1LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;5;6;5;7;5;5;5;8;2;3;9;10;5;11;12;13;14;15;16;5;16;6;9;5;5;5;5;10] [0;1;2;3;4;5;6;6;7;1;8;6;6;6;9;6;10;6;11;6;6;5;4;6] sym_id n_sym). Time Qed.

Lemma tm256: ~halts (TM_from_str "1RB1LA_0RC1LD_0LD0RE_1LA0LA_1RF1LE_---1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;0;0;1;9;10;2;3;8;8;0;11;1;12;1;12;6;7] [0;1;2;3;4;5;6;7;4;4;0;4;0;7;8;3;4;3] sym_id n_sym). Time Qed.

Lemma tm257: ~halts (TM_from_str "1RB0LD_0RC0LB_1RD1RE_1LB1LD_---0RF_1RA1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;3;4;3;3;3;5;3;6;7;8;3;9;3;10;3;3;0;11;3;12;3;13;3;14;3;15;3;16;7;13] [0;1;2;3;4;5;6;7;4;4;4;6;4;8;9;10;4;11;12;13;6;14;4;13;15;4;16;17;18;19;20;21;4;4;4;22;12;13;6;23;24;25;26;27;28;29;30;31;32;4;28;33;4;5;6;34;35;4;4;36;37;13;6;38;39;4;4;40;41;42;43;4;35;17;44;4;41;45;46;47;35;6;37;13;17;48;49;4;50;47;6;51;52;25;53;54;18;54;55;56;57;25;18;31;58;56;4;5;6;59;16;4;16;60;32;4;61;4;30;54;4;62;46;47;28;63;4;28] sym_id n_sym). Time Qed.

Lemma tm258: ~halts (TM_from_str "1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;6;7;1;8;6;6;6;9;6;10;6;11;6;6;5;4;6] [0;1;2;3;4;5;5;6;5;7;5;5;5;8;2;3;9;10;5;11;12;13;14;15;16;5;16;6;9;5;5;5;5;10] sym_id n_sym). Time Qed.

Lemma tm259: ~halts (TM_from_str "1RB1LE_1RC0RB_1RD1RC_1LA---_1LF0LF_1LA1RF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;12;13;12;14;15;12;16;12;17;18;12;19;12;12;12;18;12;20;21;22;23;19;24;9;12;11;6;25;12;26;27;24;10;13;9;28;29;12;12;6;12;30;2;19;10;12;31;6;12;3;28;24] [0;1;2;3;2;2;4;5;2;6;2;7;2;8;9;10;2;11;2;12;2;13;2;12;2;14;15;1;2;16;2;17;2;6;2;18;2;19;2;17] sym_id n_sym). Time Qed.

Lemma tm260: ~halts (TM_from_str "1RB0LE_0RC0RA_1LD0RA_1LA0LC_1LF---_0RF0LD") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;7;8;9;3;7;10;7;7;11;3;2;1;12;7;4;8;6;3] [0;1;0;2;3;4;5;6;3;7;7;4;5;7;7;7] sym_id n_sym). Time Qed.

Lemma tm261: ~halts (TM_from_str "1RB0LE_1RC1LB_0LD0RE_0RF1LA_1RD1LE_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;11;0;1;12;10;8;8;10;11;6;7;12;10;4;5] [0;1;2;3;4;5;4;4;4;4;0;6;7;8;4;8;9;6;0;6] sym_id n_sym). Time Qed.

Lemma tm262: ~halts (TM_from_str "1RB0LE_1RC1LB_0LD1RD_0RF1LA_1RD1LE_---0RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;8;10;0;1;2;11;8;8;8;10;2;11;6;7] [0;1;2;3;4;5;4;4;4;4;0;6;7;8;4;8;9;6;0;6] sym_id n_sym). Time Qed.

Lemma tm263: ~halts (TM_from_str "1RB1LE_1LC0RF_---0LD_0LE0LE_1LA1LB_1RA1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;7;8;9;10;7;11;7;7;7;7;12;1;13;14;15;7;7;14;7;16;7;7;7;17;18;19;6;7;7;20;7;7;13;14] [0;1;2;3;4;5;6;7;6;8;9;10;6;6;2;11;6;1;12;13;6;14;6;1;6;15;16;17;18;19;6;20;21;14;6;13;22;23;6;5;9;24;6;25;6;26;2;27;6;28;6;29;6;28;6;23;18;30;16;31;6;20;6;32;16;33;6;29] sym_id n_sym). Time Qed.

Lemma tm264: ~halts (TM_from_str "1RB0LE_1RC0RA_1LD0RB_1LB0LC_1LF---_0LD0LE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;9;10;7;11;7;7;7;7;12;13;14;7;5;15;16;17;7;18;19;20;7;7;7;21;7;7;22;7;6;13;23;7;24;18;25;26;7;27;7;28;7;21;23;29;30;7;31;7;32;7;7;33;34;27;7;28;7;35;30;6;7;36;37;7;38;35;39;40;7;41;7;7;42;7;43;44;7;10;7;29;45;46;7;47;45;48;49;7;7;35;7] [0;1;2;3;4;5;6;7;7;8;9;10;7;11;7;7;12;7;13;14;15;7;16;7;7;17;7;18;19;20;7;21;7;22;23;7;24;3;25;26;27;7;28;7;29;7;30;17;4;31;7;32;19;20;7;33;7;34;7;22;7;35;36;37;38;39;40;7;41;42;7;42;13;43;15;7;44;45;6;7;46;47;7;34;7;7;36;37;7;48;49;50;51;52;53;42;54;7;55;56;15;7;57;46;7;7;46;47;7;58;7;59;49;50;7;60;61;62;63;3;64;7;30;65;7;7;4;66;11;67;68;69;70;10;71;62;72;73;74;7;13;75;7;76;16;77;68;69;46;78;79;20;80;69;51;81;82;7;25;83;84;85;7;7;46;78;79;20;29;46;80;69] sym_id n_sym). Time Qed.

Lemma tm265: ~halts (TM_from_str "1RB1LA_0RC1RE_0RD0LA_1LD1LB_---0LF_1LC1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;8;5;9;10;8;8;11;1;8;8;8;8;12;13;14;1;8;8;15;5;0;1;4;5] [0;1;2;3;4;5;6;7;4;5;8;9;10;10;0;1;10;10;11;12;10;10;10;10;4;5] sym_id n_sym). Time Qed.

Lemma tm266: ~halts (TM_from_str "1RB1LD_1RC1RA_1LA0RB_---0LE_1LF1LE_0RC1RB") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;7;8;4;9;4;10;4;11;4;12;0;13;4;14;4;15;4;16;4;17;4;1;4;18;4;19;4;20;4;5;4;21;4;10] [0;1;2;3;4;5;6;7;4;4;8;1;4;9;10;11;4;12;13;12;4;14;15;16;17;18;4;19;20;21;4;22;23;5;4;1;24;25;26;9;4;27;28;29;30;27;4;25;4;31;32;33;4;3;34;31;4;16;35;14;4;33;36;22;4;21;37;19;4;7;4;18;4;29;4;11] sym_id n_sym). Time Qed.

Lemma tm267: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LC0RE_1RF---_0RB0RE") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;7;8;9;10;7;11;7;7;12;7;13;14;15;7;16;7;7;17;7;18;19;20;7;21;7;22;23;7;24;3;25;26;27;7;28;7;29;7;30;17;4;31;7;32;19;20;7;33;7;34;7;22;7;35;36;37;38;39;40;7;41;42;7;42;13;43;15;7;44;45;6;7;46;47;7;34;7;7;36;37;7;48;49;50;51;52;53;42;54;7;55;56;15;7;57;46;7;7;46;47;7;58;7;59;49;50;7;60;61;62;63;3;64;7;30;65;7;7;4;66;11;67;68;69;70;10;71;62;72;73;74;7;13;75;7;76;16;77;68;69;46;78;79;20;80;69;51;81;82;7;25;83;84;85;7;7;46;78;79;20;29;46;80;69] [0;1;2;3;4;5;6;7;8;9;10;7;11;7;7;7;7;12;13;14;7;5;15;16;17;7;18;19;20;7;7;7;21;7;7;22;7;6;13;23;7;24;18;25;26;7;27;7;28;7;21;23;29;30;7;31;7;32;7;7;33;3;27;7;28;7;34;30;35;36;7;37;34;38;39;7;40;7;7;41;7;42;43;7;10;7;29;44;45;7;46;44;47;48;7;7;34;7] sym_id n_sym). Time Qed.

Lemma tm268: ~halts (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1RF1RA_0LE1LF") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;4;5;6;4;4;7;8;9;10;11;12;4;13;14;12;15;16;17;18;4;13;19;13;20;18;21;12;22;13;23;24;25;6;21;12;26;27;28;12;21;12;29;30;31;32;4;4;33;34;35;36;37;18;29;30;38;39;4;4;40;41;29;30;42;39;4;4;43;44;45;46;4;4;47;48;14;12;49;50;4;4;14;12;51;3;29;30;52;39;14;12;53;54;14;12;55;56;21;12;4;4;14;12;57;56;21;12;58;56;21;12;21;12] [0;1;2;3;4;4;5;6;4;4;7;8;9;10;4;4;11;12;4;4;13;14;15;16;17;18;19;20;21;22;4;4;23;24;4;4;25;26;4;4;27;28;4;4;29;22;15;30;17;31;19;32;33;34;15;35;17;36;19;32;23;37;25;38;27;12;4;4;39;26;23;40;25;14;17;41;42;22;19;32;17;43;25;44;4;4;25;45;33;22;46;34;4;4] sym_id n_sym). Time Qed.

Lemma tm269: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA0RE_0RF1RE_0RB1LB_---1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;6;7;4;4;4;4;4;4;8;9;10;11;5;12;4;4;13;14;10;15;4;16;17;18;4;19;4;4;4;4;20;21;22;23;6;24;6;25;4;26;4;27;28;29;30;31;32;4;6;33;4;34;10;35;4;4;36;37;4;34;5;12;4;4;38;39;4;4;40;41;17;1;17;42;4;43;44;45;46;47;48;4;4;4;49;50;4;4;51;52;4;16;4;4;53;42;4;4;54;55;4;4;4;56;44;57;58;4;59;60;4;5;4;4;53;25] [0;1;2;3;4;5;4;6;4;4;7;4;8;9;4;10;4;11;4;12;13;14;4;15;4;16;4;17;4;18;4;19;20;21;22;23;24;25;26;4;4;27;28;29;4;30;4;31;4;32;4;33;4;34;35;36;37;38;4;39;40;4;41;42;4;43;4;44;4;45;4;46;4;47;4;48;49;45;4;50;4;51;4;52;4;53;4;54;4;55;4;56;57;4;24;4;4;36;4;58;4;59;60;14;4;61;4;62;63;4;20;64;41;4;4;65;66;4;4;67;4;68;4;69;4;70;4;71;4;72;73;74;4;75;76;77;2;78;8;4;79;80;4;81;4;82;4;83;4;84;85;23;4;86;28;87;4;88;4;89;4;90;4;91;4;92;93;4;37;94;4;95;96;81;4;97;8;98;99;61;4;100;37;4;4;101;4;102;4;103;104;4;4;105;4;9;4;106;4;107;4;108;4;109;110;4;4;111;4;112;113;4;4;114;115;4;4;116;76;117;4;118;4;119;120;4;4;121;4;122;4;123;4;124;4;125;126;127;128;129;4;130;131;14;28;132;133;134;135;136;4;25;4;137;4;138;4;139;4;140;141;78;4;142;4;143;4;144;4;145;4;146;4;147;35;4;63;82;93;43;4;94;4;148;96;4;4;98;99;4;26;100;104;15;4;42;49;4] sym_id n_sym). Time Qed.

Lemma tm270: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA0LA_0RF1RE_0RB1LB_---1RC") c0.
Proof. solve_cert (MITMDFA 100000 100000 [0;1;2;3;4;5;4;6;4;4;4;4;7;8;4;9;4;10;11;12;4;13;4;14;4;15;4;16;4;4;17;18;19;20;4;21;4;22;4;23;4;24;25;26;4;27;25;4;4;8;4;28;4;29;30;31;4;4;32;33;4;4;34;35;4;1;4;36;4;37;4;38;4;39;11;4;4;40;4;41;4;36;42;43;4;44;4;45;2;4;4;46;4;22] [0;1;2;3;4;5;4;6;4;4;7;4;8;9;4;10;4;11;4;12;13;14;4;15;4;16;4;17;4;18;4;19;20;21;22;23;24;25;26;4;4;27;28;29;4;30;4;31;4;32;4;33;4;34;35;36;37;38;4;39;40;4;41;42;4;43;4;44;4;45;4;46;4;47;4;48;49;45;4;50;4;51;4;52;4;53;4;54;4;55;4;56;57;4;24;4;4;36;4;58;4;59;60;14;4;61;4;62;63;4;20;64;41;4;4;65;66;4;4;67;4;68;4;69;4;70;4;71;4;72;73;74;4;75;76;77;2;78;8;4;79;80;4;81;4;82;4;83;4;84;85;23;4;86;28;87;4;88;4;89;4;90;4;91;4;92;93;4;37;94;4;95;96;81;4;97;8;98;99;61;4;100;37;4;4;101;4;102;4;103;104;4;4;105;4;9;4;106;4;107;4;108;4;109;110;4;4;111;4;112;113;4;4;114;115;4;4;116;76;117;4;118;4;119;120;4;4;121;4;122;4;123;4;124;4;125;126;127;128;129;4;130;131;14;28;132;133;134;135;136;4;25;4;137;4;138;4;139;4;140;141;78;4;142;4;143;4;144;4;145;4;146;4;147;35;4;63;82;93;43;4;94;4;148;96;4;4;98;99;4;26;100;104;15;4;42;49;4] sym_id n_sym). Time Qed.


