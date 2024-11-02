From BusyCoq Require Import CTL62.

Ltac solve_cert := Nsolve_cert.

Lemma nonhalt75739: ~halts (TM_from_str "1RB1RC_1RC0RB_0LD0RA_1LE1RD_0LF0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt75740: ~halts (TM_from_str "1RB1LD_1RC0RB_1LD0RE_---0LB_1LA1LF_0LE1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 23 320 3 1 4 0). Time Qed.

Lemma nonhalt75741: ~halts (TM_from_str "1RB0RE_1RC0RF_1LD1LF_---0LE_1RA1RB_1LE0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 21 320 3 1 8 0). Time Qed.

Lemma nonhalt75742: ~halts (TM_from_str "1RB0RD_1LC1LE_1RA0LB_0RC1RE_1LD1RF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt75743: ~halts (TM_from_str "1RB1RD_1RC0RB_0LD0RA_1LF1RE_0LA---_0LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt75744: ~halts (TM_from_str "1RB0LE_0RC1RC_1LD0RA_1LA0RF_0LD---_0RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt75745: ~halts (TM_from_str "1RB1LF_1RC1RE_0RD1RF_0LE0RA_1LD---_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 2 6 0). Time Qed.

Lemma nonhalt75746: ~halts (TM_from_str "1RB1LD_1RC0RA_0LA0RF_0RE0LB_1LA0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75747: ~halts (TM_from_str "1RB---_1LC0LE_1LA1LD_1RE1RD_1LF0RD_1LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt75748: ~halts (TM_from_str "1RB1LE_0RC1RB_0LD0RB_0LA1LD_1LF0RE_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt75749: ~halts (TM_from_str "1RB0LE_1RC---_1RD1RA_0RE0RF_1LF0RC_0LA0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt75750: ~halts (TM_from_str "1RB0LB_0LC0RE_1LA1RD_1LA---_1RF1RC_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 17 320 3 2 12 0). Time Qed.

Lemma nonhalt75751: ~halts (TM_from_str "1RB0RD_0RC1RF_1LD1LE_1RE1LD_1RA0LC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75752: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE0LB_1RF1LB_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75753: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE0RF_1LA1LB_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75754: ~halts (TM_from_str "1RB0LE_0RC0RF_1RD0RD_1LE---_1LF1LA_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75755: ~halts (TM_from_str "1RB1RC_1LC0LF_1LD0RA_1LE0LB_1RF---_0LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75756: ~halts (TM_from_str "1RB0LD_1RC0RF_0RD0LA_1RE1LA_1LF---_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75757: ~halts (TM_from_str "1RB0RE_1LC0RF_1RA0LD_1LE1LC_1RC1LE_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75758: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA0LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75759: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA0LF_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75760: ~halts (TM_from_str "1RB1LD_1RC0RC_1LD0RE_0LB1RB_1LF0LA_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75761: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE1RF_1LA1LB_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75762: ~halts (TM_from_str "1RB0RE_0RC0LF_1RD1LF_0LE---_1RF1LE_1RA0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75763: ~halts (TM_from_str "1RB---_0RC0RA_1LD1LE_1RE1LD_1RF0LC_1RB0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75764: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA1LF_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75765: ~halts (TM_from_str "1RB0RB_1LC---_1LF1LD_1RE0LC_0RA0RF_1RD1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75766: ~halts (TM_from_str "1RB0RD_0RC0RF_1LD1LE_1RE1LD_1RA0LC_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75767: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD0RF_1LE1LA_1RA1LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75768: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD1RF_1LE1LA_1RA1LE_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75769: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA1LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75770: ~halts (TM_from_str "1RB---_1RC1RD_1LD1RC_1LE0RB_0LF0LC_1LA0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75771: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE1RF_1LA1LB_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75772: ~halts (TM_from_str "1RB1LA_1RC0LF_0RD0RA_1RE1RC_1LF---_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75773: ~halts (TM_from_str "1RB---_1LC0RF_1LE0LD_1LB1RD_0LF1LA_1RD1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75774: ~halts (TM_from_str "1RB0LE_0RC0RF_1RD1RB_1LE---_1LF1LA_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75775: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_0LE0LB_1LF0LF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75776: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD0RF_1LE1LA_1RA1LE_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75777: ~halts (TM_from_str "1RB0RD_0RC0RF_1LD1LE_1RE1LD_1RA0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75778: ~halts (TM_from_str "1RB1LA_1RC0LF_0RD0RA_1RE0RE_1LF---_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75779: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD1RF_1LE1LA_1RA1LE_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75780: ~halts (TM_from_str "1RB0RE_0LC---_1RE1LD_1LE1LF_1RF0RC_1RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75781: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE1RF_1LA1LB_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75782: ~halts (TM_from_str "1RB---_0RC1RA_1LD1LE_1RE1LD_1RF0LC_1RB0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75783: ~halts (TM_from_str "1RB0LE_0LC0RF_0RE1RD_1RC---_1LF1LA_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75784: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA1LF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75785: ~halts (TM_from_str "1RB0RD_0RC1RF_1LD1LE_1RE1LD_1RA0LC_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75786: ~halts (TM_from_str "1RB0RE_1RC0LF_1RD0RA_1LE---_0RA1LF_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75787: ~halts (TM_from_str "1RB0RD_0RC1RF_1LD1LE_1RE1LD_1RA0LC_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75788: ~halts (TM_from_str "1RB---_0LC1LB_1RE1LD_1LA0RD_0RF1RE_0LB0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75789: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE0RF_1LA1LB_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75790: ~halts (TM_from_str "1RB0LE_1RC0RF_1LD---_0RF1LE_1LF1LA_1RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75791: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD1RF_1LE1LA_1RA1LE_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75792: ~halts (TM_from_str "1RB1LA_1RC0LF_0LD0RA_0RF1RE_1RD---_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75793: ~halts (TM_from_str "1RB0RE_0RC0LF_1RD1LF_1LE---_1RF1LE_1RA0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75794: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA1LF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75795: ~halts (TM_from_str "1RB0LF_1LC0RE_1LA0LD_1LB1RD_1RD1RB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75796: ~halts (TM_from_str "1RB1LF_1RC0RA_1RD0LF_1RE0RB_0LA---_1LB1LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75797: ~halts (TM_from_str "1RB0RD_0RC1RF_1LD1LE_1RE1LD_1RA0LC_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75798: ~halts (TM_from_str "1RB0LE_1RC0RF_0LD---_1RF1LE_1LF1LA_1RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75799: ~halts (TM_from_str "1RB---_1LC1RB_1LE0RD_1LA1RC_1LF0LB_0LD0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75800: ~halts (TM_from_str "1RB---_0LC1RF_1LD0LB_1LE0RF_1LA0LC_1RC1RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75801: ~halts (TM_from_str "1RB1LD_1LC0RD_1LA0LB_0LE0RE_1RB1LF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75802: ~halts (TM_from_str "1RB0RD_0RC0RF_1LD1LE_1RE1LD_1RA0LC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75803: ~halts (TM_from_str "1RB0LD_1LC0RA_1LA1RD_0RE0LE_1LA1RF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75804: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE0RF_1LA1LB_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75805: ~halts (TM_from_str "1RB0LF_1LC0RE_1LD0LB_1RB1LE_0LA0RA_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75806: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_0RE0LB_0LA1LF_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75807: ~halts (TM_from_str "1RB0LB_0RC1LE_1RD1RF_1LD0RB_0LA---_1LF0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75808: ~halts (TM_from_str "1RB1LE_0RC1RB_0LD0RB_0LA1LD_1LF0RE_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75809: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA1LF_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75810: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE1RF_1LA1LB_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75811: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_0LA0LF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75812: ~halts (TM_from_str "1RB1LD_1LC---_1RD1LC_1RE0LA_1RF0RC_0RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75813: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD0RF_1LE1LA_1RA1LE_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75814: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE0LB_1RF1LB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75815: ~halts (TM_from_str "1RB1LD_0LC---_1RD1LC_1RE0LA_1RF0RC_0RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75816: ~halts (TM_from_str "1RB---_1LC1RD_1RF0LD_0RE0LE_1LC1RA_1RB0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75817: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_0LE0LB_1LF1LD_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75818: ~halts (TM_from_str "1RB0LA_1RC---_0RD1RC_1LE1RA_0LF1LE_0RC0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75819: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA1RD_0RE0LE_1LA0RF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75820: ~halts (TM_from_str "1RB0RD_0RC1RF_1LD1LE_1RE1LD_1RA0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75821: ~halts (TM_from_str "1RB0LD_1RC0RF_0RD0LA_1RE1LA_0LF---_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75822: ~halts (TM_from_str "1RB0LA_1LC---_0RD1RC_1LE1RA_0LF1LE_0RC0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75823: ~halts (TM_from_str "1RB---_1RC1RD_1LD1RC_1LE0RB_0LF0LC_1LA1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75824: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_1LB0RF_1LA1LB_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75825: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD1RF_1LE1LA_1RA1LE_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75826: ~halts (TM_from_str "1RB1LD_1LC0RD_1LA0LB_0LE0RE_1RB0LF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75827: ~halts (TM_from_str "1RB0RE_1LC---_0RE1LD_1LE1LF_1RF0RC_1RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75828: ~halts (TM_from_str "1RB1RC_1LC1RB_1LD0RA_1LE0LB_1RC0LF_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75829: ~halts (TM_from_str "1RB0LD_1RC0RE_1LA0RF_1LE1LA_1RA1LE_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75830: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD1RF_1LE1LA_1RA1LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75831: ~halts (TM_from_str "1RB---_0RC1RA_1LD1LE_1RE1LD_1RF0LC_0LB0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75832: ~halts (TM_from_str "1RB1RE_1LC---_1LF1LD_1RE0LC_0RA0RF_1RD1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75833: ~halts (TM_from_str "1RB1LD_1LC0RD_1RA0LB_0LE0RE_1RB1LF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75834: ~halts (TM_from_str "1RB1LA_1RC0LE_1RD0RA_0RE1RF_1LA1LB_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 3 2 8 0). Time Qed.

Lemma nonhalt75835: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_0LE0LB_1RA---_1RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 18 320 3 1 8 0). Time Qed.

Lemma nonhalt75836: ~halts (TM_from_str "1RB1LE_0RC1RA_1RD1RF_1LB0RA_1LD0LE_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt75837: ~halts (TM_from_str "1RB1RA_1RC0LD_1LB0RF_0LE0RD_1LB0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 21 320 3 1 6 0). Time Qed.

Lemma nonhalt75838: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0LF_0LB1LD_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75839: ~halts (TM_from_str "1RB1RC_1LC1LB_1RD0LB_---1RE_0RE1RF_0RA1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 2 0). Time Qed.

Lemma nonhalt75840: ~halts (TM_from_str "1RB0LC_1RC1LD_1LA1LC_0RD1RE_0RF1RD_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 2 0). Time Qed.

Lemma nonhalt75841: ~halts (TM_from_str "1RB1RC_1LC1LB_1RD0LB_---1LE_0RE1RF_0RA1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 2 0). Time Qed.

Lemma nonhalt75842: ~halts (TM_from_str "1RB0LC_1RC1RD_1LA1LC_0RD1RE_0RF1RD_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 2 0). Time Qed.

Lemma nonhalt75843: ~halts (TM_from_str "1RB0RA_1LC1RF_1RB0LD_0LE---_1LB1LE_1LA0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt75844: ~halts (TM_from_str "1RB---_0LC0RC_1LE0LD_1LC0RF_0RD0LA_1RD1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75845: ~halts (TM_from_str "1RB0LF_0RC0LC_0LD1RA_1LE0RC_1LA1LD_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75846: ~halts (TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RE0RE_0RA0LB_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75847: ~halts (TM_from_str "1RB0LF_0LC0LB_1RC0RD_1RE---_1LA0RA_0LE1RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 2 6 0). Time Qed.

Lemma nonhalt75848: ~halts (TM_from_str "1RB1RA_1RC1LD_1LB0RF_1RE0RE_1LB0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt75849: ~halts (TM_from_str "1RB---_0RC1RF_1LD0RD_0LE1RD_0RA0LC_1RA1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75850: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_1LB0LF_1RD1RF_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt75851: ~halts (TM_from_str "1RB---_1LC0RC_0RF0LD_1LE1LF_1LC0LE_1RB1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 22 320 3 1 6 0). Time Qed.

Lemma nonhalt75852: ~halts (TM_from_str "1RB1RE_0LC0RF_1LE1LD_1LB---_0RA0LA_0RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt75853: ~halts (TM_from_str "1RB1RF_1LC0RE_0RD0LC_1LA---_1RA1RD_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt75854: ~halts (TM_from_str "1RB0RE_1LC0RB_0LD0LB_1RE1RB_1RF1RB_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 22 320 3 1 6 0). Time Qed.

Lemma nonhalt75855: ~halts (TM_from_str "1RB0LD_1RC0RA_0LA1RE_1LA0RE_1LF---_0LB0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75856: ~halts (TM_from_str "1RB1RA_1RC0LD_1LB0RE_1LF1LB_0RA---_1RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt75857: ~halts (TM_from_str "1RB0LC_1LA0RF_1LD1LE_1RA0RE_0LB0LE_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt75858: ~halts (TM_from_str "1RB0RD_1LC1RA_1LD0LC_1RE0LA_1RF0RA_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt75859: ~halts (TM_from_str "1RB1LE_1RC0LB_0RD---_1LE1RA_1LB0RF_1LA1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75860: ~halts (TM_from_str "1RB0LE_0LC1RE_1LD1RC_---1LA_0RF1RE_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 7 320 3 1 12 0). Time Qed.

Lemma nonhalt75861: ~halts (TM_from_str "1RB1RE_0LC0RC_1RA1RD_1LE---_1RA0LF_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt75862: ~halts (TM_from_str "1RB---_1LC0LE_1RD0LD_0LE0RF_1LB1LC_1RC0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 19 320 3 1 8 0). Time Qed.

Lemma nonhalt75863: ~halts (TM_from_str "1RB0LD_1RC---_0LA1RD_0RA1LE_1RF0LF_1LC0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 21 320 3 1 6 0). Time Qed.

Lemma nonhalt75864: ~halts (TM_from_str "1RB1LF_0RC1RA_0RD---_1LD0LE_1LA0LE_0RC0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75865: ~halts (TM_from_str "1RB1LF_1LC0RE_---1LD_1LE0LA_1LA1RE_0LD0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 9 320 3 1 1 0). Time Qed.

Lemma nonhalt75866: ~halts (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD0LC_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75867: ~halts (TM_from_str "1RB0LB_1RC1LC_1LD0RC_1LE1RB_0LA1LF_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt75868: ~halts (TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75869: ~halts (TM_from_str "1RB1RC_1RC0RB_0LD0RA_1LE1RD_1LF0LC_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 22 320 3 1 6 0). Time Qed.

Lemma nonhalt75870: ~halts (TM_from_str "1RB1LC_1LC0LB_0LE1LD_1RB---_1LF0RF_1RE0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 17 320 3 2 12 0). Time Qed.

Lemma nonhalt75871: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1RC_1LE0LA_---1LF_1RC0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt75872: ~halts (TM_from_str "1RB1RC_1LC0LC_1LD0RA_1RC0LE_0LF---_1LC1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt75873: ~halts (TM_from_str "1RB0LE_1RC1RA_1LD0RF_0LE0RE_0RA1LC_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75874: ~halts (TM_from_str "1RB0LF_1LC1RC_1LD0RB_1LE1LD_0LA1LA_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75875: ~halts (TM_from_str "1RB0RD_0LC---_1LF1LD_0RE0LC_1RA1LE_1LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75876: ~halts (TM_from_str "1RB0LE_1RC0RA_1LD0RB_0LB1LE_1LB0LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75877: ~halts (TM_from_str "1RB0RD_1LC0RB_0LD1LD_0LE0LF_0RA1LB_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75878: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA1RB_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75879: ~halts (TM_from_str "1RB0LF_0LC0RE_0LA1LD_1RB1LB_1RD0RD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75880: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_1LE0LB_1RF---_1RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 21 320 3 1 6 0). Time Qed.

Lemma nonhalt75881: ~halts (TM_from_str "1RB1LA_1LC0RD_1RD1LC_1RF0RE_---0RF_1LF0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75882: ~halts (TM_from_str "1RB0LB_1LC0LE_0LA1RD_1LB0RE_1LF0RA_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 17 320 3 2 12 0). Time Qed.

Lemma nonhalt75883: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD---_1LE0LD_0RA0LF_1LD1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 22 320 3 1 6 0). Time Qed.

Lemma nonhalt75884: ~halts (TM_from_str "1RB1RE_0LC0LD_1LE1LD_0LE1LB_1RA1LF_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 18 320 3 1 8 0). Time Qed.

Lemma nonhalt75885: ~halts (TM_from_str "1RB1LE_0LC0RB_1RD1LA_1RA0LD_1LF1LD_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75886: ~halts (TM_from_str "1RB1RF_0LC---_1RA1LD_0LE1LE_1RC0LE_0RC0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75887: ~halts (TM_from_str "1RB0LC_1LA---_0LD1RB_0LE0LD_1RE0RF_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75888: ~halts (TM_from_str "1RB---_1RC0RD_0LD1RE_0RA0LC_1LD1RF_0RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt75889: ~halts (TM_from_str "1RB1LE_0LC0RB_1RD1LA_1RA0LD_0LF1LD_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75890: ~halts (TM_from_str "1RB1LE_0LC0RB_1RD1LA_1RA---_0LD1LF_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75891: ~halts (TM_from_str "1RB---_1RC0RA_1LC0LD_1RA1LE_0LF0RE_0LB0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75892: ~halts (TM_from_str "1RB1LC_0LA1RA_0LD1LF_1LE---_0RB0LE_1LE0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75893: ~halts (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA---_0LF0LF_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75894: ~halts (TM_from_str "1RB0LA_1RC1LE_0LD0RC_1RF1LB_0LF1LA_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75895: ~halts (TM_from_str "1RB0LD_1RC0RE_1LA0RA_0LC0LD_1RF0LD_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75896: ~halts (TM_from_str "1RB0RE_1LC1RA_1RA1LD_0LB0RA_0RF1LD_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75897: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_1LB1LD_0RF0LE_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 18 320 3 1 8 0). Time Qed.

Lemma nonhalt75898: ~halts (TM_from_str "1RB---_1RC1LE_0LD0RC_1RA1LB_0LA1LF_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75899: ~halts (TM_from_str "1RB0LF_0RC1RB_0LD1RA_1LE0RC_1LA1LD_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75900: ~halts (TM_from_str "1RB0LA_1RC1LE_0LD0RC_1RA1LB_0LF1LA_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75901: ~halts (TM_from_str "1RB0RD_1LC---_1LF1LD_0RE0LC_1RA1LE_1LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75902: ~halts (TM_from_str "1RB0RE_1LC1RA_1LD0LD_1RA0RE_1RF0LB_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt75903: ~halts (TM_from_str "1RB---_0RC1RF_1LD1RB_1LE0LD_0LA0LC_1RC0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75904: ~halts (TM_from_str "1RB---_1LC0RD_0LD0LC_1LA1RE_1LF0RE_1RF1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75905: ~halts (TM_from_str "1RB0RC_0LC1RE_0RD0LB_1RA---_1LC1RF_0RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75906: ~halts (TM_from_str "1RB0LE_1RC---_1RD0RA_1LA0RF_0LA1RD_1RE0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75907: ~halts (TM_from_str "1RB1RE_1LC0RF_0LD1LC_0RE1LB_1RA0LD_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75908: ~halts (TM_from_str "1RB0LF_1LC0RE_1LE1LD_0LC1LC_1RB1LA_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt75909: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1RE0LB_1LA0RA_1LC0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt75910: ~halts (TM_from_str "1RB0RC_1RC1RD_1LD0RA_0LF0LE_---1LC_1LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt75911: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RD_0LE0RA_0LF1RC_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 1 8 0). Time Qed.

Lemma nonhalt75912: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1RB0LF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75913: ~halts (TM_from_str "1RB0RF_1LC0LE_1RD0LB_0RB1RA_1LB0RA_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75914: ~halts (TM_from_str "1RB0LD_1RC0RC_1RD1RC_1LE1RF_---1LA_1LE0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt75915: ~halts (TM_from_str "1RB0LD_1RC0RA_0LA0RF_1LA1RE_1LE0LB_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75916: ~halts (TM_from_str "1RB1RB_0RC0RB_1LD0RA_0LE---_1LF0LC_1RC0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75917: ~halts (TM_from_str "1RB0LB_0LC0RE_1LA1RD_0LE---_1RF1RC_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75918: ~halts (TM_from_str "1RB0LF_1RC1LE_1RD0RA_0LB---_1RA1LB_0RE0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt75919: ~halts (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_1LC0RD_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75920: ~halts (TM_from_str "1RB---_0LC0RE_0RD1LC_0LE1LD_1RA0LF_1RC0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75921: ~halts (TM_from_str "1RB0LA_1LC1RD_0RB0LC_1LA1RE_1LF0RD_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75922: ~halts (TM_from_str "1RB0RD_1LC0LC_1RE1LD_0LB0LF_0RA0RC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75923: ~halts (TM_from_str "1RB0LA_0RC1RE_1LC1LD_1LA---_1RF0RE_1LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75924: ~halts (TM_from_str "1RB0LB_1LC0LC_0RD1RC_1LE1RE_1LF0RA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt75925: ~halts (TM_from_str "1RB0RA_1LC0RA_1LF0LD_1LE---_0RE0LB_1LA1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75926: ~halts (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_1LC0RD_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75927: ~halts (TM_from_str "1RB1LA_0RC0RD_1LD0LE_1RE1RD_1LF0LA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75928: ~halts (TM_from_str "1RB1LB_0LC0RE_1LE0LD_1LC---_1RF0LE_1LA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75929: ~halts (TM_from_str "1RB---_0RC1LE_0RD0RC_1RE1RA_1LF0LE_1RD0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75930: ~halts (TM_from_str "1RB1LF_0RC0RE_1LD1LA_1LE0LD_0RA0LC_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75931: ~halts (TM_from_str "1RB1RC_0LC---_1LD0RC_1LE1RA_0RF0LE_1LC1RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75932: ~halts (TM_from_str "1RB1LF_1RC0LD_0RD0RD_1LE0RA_1LA---_1LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt75933: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_0LE0LB_0RA---_1RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75934: ~halts (TM_from_str "1RB1LF_1LC0LB_0RD1LA_1LE0RE_1RD0RA_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 13 320 3 1 4 0). Time Qed.

Lemma nonhalt75935: ~halts (TM_from_str "1RB1LD_1RC0LB_0LA---_0LE1LA_1LF0RF_1RE0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 23 320 3 2 6 0). Time Qed.

Lemma nonhalt75936: ~halts (TM_from_str "1RB0LF_1RC0RB_0LD0RA_1LE1RD_0LF0LC_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75937: ~halts (TM_from_str "1RB0RA_1LC---_0LD1RC_0LE0RB_0LF0RC_1RF0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75938: ~halts (TM_from_str "1RB0RA_0RC1RE_1LD1RF_0RE1LC_---1RC_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt75939: ~halts (TM_from_str "1RB1LE_0LC0RA_1LF1LD_1LA1LC_0LB---_0LD1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt75940: ~halts (TM_from_str "1RB1LE_1LC0RD_1LA0LB_0LC0RE_0RC0LF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75941: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD1LA_1LA0LD_0RF---_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75942: ~halts (TM_from_str "1RB0LF_1LC0RB_1RD1LB_1RE1RC_1LF---_1RD0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt75943: ~halts (TM_from_str "1RB---_1RC1LE_0LD0RC_1RF1LB_0LA1LF_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75944: ~halts (TM_from_str "1RB0LE_1LC0LD_1RD0RC_1LA1RA_1LF0LE_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75945: ~halts (TM_from_str "1RB0RC_1LC1RE_1RA0LD_0RA0LE_0LA0RF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75946: ~halts (TM_from_str "1RB0RB_1LC0LB_1RD1LA_1LC0RE_0RF---_1RC1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75947: ~halts (TM_from_str "1RB0LF_1LC0LB_0LD1LA_1LE0RE_1RD0RA_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75948: ~halts (TM_from_str "1RB1LA_0RC0RE_0LD---_1LE0LD_0RA0LF_1LD0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt75949: ~halts (TM_from_str "1RB1RC_1RC0RA_1LD0RD_0RA0LE_1LC0LF_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75950: ~halts (TM_from_str "1RB1RA_1RC0LD_1LB0RE_0LF1LB_0RA---_1LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75951: ~halts (TM_from_str "1RB0LA_1RC1LE_0LD0RC_1RA1LB_1LF1LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75952: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD---_1LF1LE_0RA0LD_1LE0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75953: ~halts (TM_from_str "1RB0RC_1LA0LD_---1LB_0LE0LD_1RE0RF_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 3 2 3 0). Time Qed.

Lemma nonhalt75954: ~halts (TM_from_str "1RB1LF_0RC0RE_1LD0LA_1LE0LD_0RA0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75955: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_1LE0LB_0RF---_1RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75956: ~halts (TM_from_str "1RB1RC_1LC0RA_1RD0LC_1RE---_0RF1LE_1LB1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75957: ~halts (TM_from_str "1RB0LC_1LA1RE_0RD0LF_0RB---_1RA0RC_0LC1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75958: ~halts (TM_from_str "1RB0RF_1RC---_0LD1LD_1RA1LE_1LD0LC_0RD1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75959: ~halts (TM_from_str "1RB0LF_1RC---_0LD0RA_0RE1LD_0LA1LE_1RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75960: ~halts (TM_from_str "1RB---_0RC0LC_1LD0LE_0RE1LA_1LC0RF_1RE0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75961: ~halts (TM_from_str "1RB1LF_0RC0RE_1LD1LA_1LE0LD_0RA0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75962: ~halts (TM_from_str "1RB0RD_1RC1RE_0RD1RF_0LE0RA_1LF---_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75963: ~halts (TM_from_str "1RB1RD_0RC0LD_1LD0RB_1LE---_0LA1LF_0RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75964: ~halts (TM_from_str "1RB---_1LC1RC_0RE0LD_1LB0LB_0RF1RB_1LC0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75965: ~halts (TM_from_str "1RB---_0RC1RA_0RD0RC_1RE0LE_1LF0LE_1RB0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75966: ~halts (TM_from_str "1RB0LC_1LA1LE_1LD---_1LB0RF_0LD1RD_0RE1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75967: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0RE_0RF0LC_0LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75968: ~halts (TM_from_str "1RB0RD_0LC1RE_1LF1RD_1LB1RF_---0RC_0LA0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt75969: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_1LB1LD_0RF1RB_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75970: ~halts (TM_from_str "1RB0RF_1RC1RA_1LD0RD_1LC0LE_1RB1LE_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt75971: ~halts (TM_from_str "1RB1LD_1RC0RF_0RD---_1LE0LE_0LF1LA_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75972: ~halts (TM_from_str "1RB0LE_1RC0RF_0LD1RE_0LA1LD_1RC0RB_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75973: ~halts (TM_from_str "1RB1RD_1RC0RB_0LD0RA_1LE1RD_0LF0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75974: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA1LF_0LB0RA_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75975: ~halts (TM_from_str "1RB0RA_0LC0RE_1LD1RC_0LE0LB_1RA0LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75976: ~halts (TM_from_str "1RB1LC_0RC1RD_1LD0LF_1LE0RB_1LA0LD_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt75977: ~halts (TM_from_str "1RB1LE_0RC0LE_1LD1RB_0LA---_0LF0RA_0RC0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75978: ~halts (TM_from_str "1RB0RA_0LC0RE_1LF1RD_0LE---_1RA1RC_1RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75979: ~halts (TM_from_str "1RB---_0RC1RB_0RD0RC_1RE1LF_1LE0LD_1LA1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75980: ~halts (TM_from_str "1RB0RA_0LC0RF_1LE1RD_1LE---_1RB0LB_1RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75981: ~halts (TM_from_str "1RB0RE_1LC1RA_1RA1LD_0LB0RA_1RF1LD_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75982: ~halts (TM_from_str "1RB1LF_1LC0RC_0RA0LD_1LE1LA_1LC0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75983: ~halts (TM_from_str "1RB---_1LC1RF_1RD1LC_0LE0LD_1RE1LB_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75984: ~halts (TM_from_str "1RB---_1RC1RD_1RD0RC_0LE0RB_1LF1RE_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75985: ~halts (TM_from_str "1RB0RB_1RC0LD_1LB0RE_1LA1LB_0RF---_1RB1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75986: ~halts (TM_from_str "1RB1LB_1RC0LA_1RD1RC_1LB1RE_1LA0RF_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt75987: ~halts (TM_from_str "1RB1LA_1RC0RF_1LC0LD_1RE1LD_1LA0RB_---0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75988: ~halts (TM_from_str "1RB1RF_1RC0RF_1RD1LC_0LE0RA_---0LC_1LE1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75989: ~halts (TM_from_str "1RB0LB_0RC1LB_0LD0RA_1LE---_0LA1LF_1LD1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt75990: ~halts (TM_from_str "1RB1LF_1LC0RC_0RA0LD_1LE1LA_1LC0LE_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75991: ~halts (TM_from_str "1RB1RD_1RC0RB_0LD0RA_1LF1RE_1LF---_1RC0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75992: ~halts (TM_from_str "1RB0RC_1LC0RE_1RD0LD_0RB1LE_1RF0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75993: ~halts (TM_from_str "1RB---_1RC0RB_0LD0RF_1LE1RD_0LA0LC_1RB1RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75994: ~halts (TM_from_str "1RB0RD_1RC1RE_0LD1RD_0RA0LB_1LF---_0LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75995: ~halts (TM_from_str "1RB1RD_0LC1LB_1LD1LC_1RE0LB_---0RF_1RA0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75996: ~halts (TM_from_str "1RB1RC_1RC0RB_0LD0RA_1LE1RD_1LF0LC_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75997: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_0LE0LB_0RA---_1RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75998: ~halts (TM_from_str "1RB1RE_0RC1LC_1RD1RE_1LB0LD_0RF0RB_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt75999: ~halts (TM_from_str "1RB1RE_1LC0RF_0LD0RD_0RE1LB_1RA0LD_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76000: ~halts (TM_from_str "1RB---_0LC0RE_0LF1LD_1RB1LB_1RD0RD_1LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76001: ~halts (TM_from_str "1RB1RD_1LC0RD_0LD1LA_1RA0LE_1LF0LB_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76002: ~halts (TM_from_str "1RB1LA_1RC0LD_0RD---_1RE0LB_1LA0RF_0LF0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76003: ~halts (TM_from_str "1RB0RC_1LC1LF_1RD0LB_---0RE_1RB1RA_1LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76004: ~halts (TM_from_str "1RB1RD_1RC0RB_0LD0RA_1LF1RE_1LF---_0LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76005: ~halts (TM_from_str "1RB1LE_0LC0RA_1RD1LC_1RE1RA_0RF0LA_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76006: ~halts (TM_from_str "1RB1LF_1RC0RE_0RD1RF_0LE0RA_1LF---_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76007: ~halts (TM_from_str "1RB---_1RC0RB_0LD0RF_1LE1RD_0LA0LC_1RB1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76008: ~halts (TM_from_str "1RB0LD_0RC1RA_0RD0RC_1RE0RF_1LA0LE_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76009: ~halts (TM_from_str "1RB0RB_1LC1RE_0LD0LB_1LA1RB_0RA0RF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76010: ~halts (TM_from_str "1RB0LD_1RC0RA_0LA0RE_1LA1RE_1LF---_0RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76011: ~halts (TM_from_str "1RB1LA_1RC0RC_1RD1RC_1LE0LA_---1LF_0RD0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76012: ~halts (TM_from_str "1RB0LD_1RC---_1LA1RF_1LE1LD_0LA0RE_1RB1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76013: ~halts (TM_from_str "1RB1LA_0RC0RE_0LD---_1LE0LD_0RA0LF_1LD1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76014: ~halts (TM_from_str "1RB1LC_1LA0RD_1LB0LD_0LF0RE_0RD1RE_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76015: ~halts (TM_from_str "1RB1LA_1RC0RE_0LD---_1LF1LE_0RA0LD_1LE0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76016: ~halts (TM_from_str "1RB1RE_1LC0RE_1RD1LC_0LF0RA_1LF1RA_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76017: ~halts (TM_from_str "1RB1LA_0RC0RE_0LD---_1LE0LD_0RA0LF_1LD1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76018: ~halts (TM_from_str "1RB---_0RC1LB_1LC1LD_1RE1RF_1LF0RD_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76019: ~halts (TM_from_str "1RB0LE_1RC---_0RD1RF_1LE1LB_0LA0RB_0LE0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76020: ~halts (TM_from_str "1RB0RA_1RC0RA_1LD1RA_---0LE_1LB0LF_0LE1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76021: ~halts (TM_from_str "1RB1LD_1RC0RA_0LA0RE_1RE0LB_0RA0LF_---1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76022: ~halts (TM_from_str "1RB0LE_0LC1LE_1LD1RC_---1LA_0RF1RE_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76023: ~halts (TM_from_str "1RB0RD_1RC0LD_1LB1RA_0RF0LE_0LD1LE_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76024: ~halts (TM_from_str "1RB---_0RC0LF_1RD1RA_0LE0RE_1LB1LD_0LE1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76025: ~halts (TM_from_str "1RB1RF_0RC1LC_1RD1LE_1LB0LD_0RA---_0RE0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76026: ~halts (TM_from_str "1RB0LE_1RC1RA_1LD0RF_0LE1LD_0RA1LC_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76027: ~halts (TM_from_str "1RB1RC_1RC0RB_0LD0RA_1LE1RD_0LF0LC_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76028: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_0LE0LB_0RA---_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76029: ~halts (TM_from_str "1RB0RC_1LC1RF_0RE0LD_0LC0LA_1RA1RE_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76030: ~halts (TM_from_str "1RB---_1RC0LD_0LD0RC_1RA1LE_1LF1LB_1RE1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 22 320 3 1 6 0). Time Qed.

Lemma nonhalt76031: ~halts (TM_from_str "1RB1RD_1RC0RB_0LD0RA_1LE1RD_0LF0LC_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76032: ~halts (TM_from_str "1RB0LA_0LC0RB_0RA1LD_0LE1LF_1LA1RE_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76033: ~halts (TM_from_str "1RB0RB_1LC1RE_0LD0LB_1LA0LE_0RA0RF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76034: ~halts (TM_from_str "1RB---_0RC0RE_1LD1LF_1LE0LD_0RF0LC_1RB1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76035: ~halts (TM_from_str "1RB0LE_0RC0RD_1LA0RA_1RC1RF_1LA0LE_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76036: ~halts (TM_from_str "1RB1RF_1RC---_1LD1RA_1RB0LE_1LF1LE_0LD0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76037: ~halts (TM_from_str "1RB1RD_1RC0RB_0LD0RA_1LF1RE_0LA---_1RC0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76038: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD---_1LE0LD_0RA0LF_1LD1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76039: ~halts (TM_from_str "1RB0RF_1RC1RA_0LD0RB_---0RE_1LF0LC_1LB0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 1 8 0). Time Qed.

Lemma nonhalt76040: ~halts (TM_from_str "1RB1LD_0RC0LF_1RD0RC_1LE0LB_0LA0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76041: ~halts (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RE0LD_0RA1RF_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76042: ~halts (TM_from_str "1RB1LE_0RC0RB_1LD1RB_0LA---_1RA0LF_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76043: ~halts (TM_from_str "1RB---_0RC1RA_0RD0RC_1RE0LF_1LE0LD_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76044: ~halts (TM_from_str "1RB0RA_1LC1RA_0LA0LD_1LE0LB_0RB0LF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76045: ~halts (TM_from_str "1RB1RF_1RC---_0RD1RA_1LE0RE_0LF1RE_0RB0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76046: ~halts (TM_from_str "1RB---_0RC1LC_0RD0LA_0RE0RD_1LE0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76047: ~halts (TM_from_str "1RB0RE_0RC---_1LD0LC_1RA0LE_1RF0RD_1LC1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76048: ~halts (TM_from_str "1RB0RB_1RC1RE_1LD1RC_0RB0LC_1RF0RA_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76049: ~halts (TM_from_str "1RB0RA_0LC0RE_1LD1RC_0LE0LB_1RA1RF_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76050: ~halts (TM_from_str "1RB0LF_1LC0RD_1LF1LA_---0RE_0RB0RF_0LA1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76051: ~halts (TM_from_str "1RB0RF_1RC0LC_1LD0LA_0RA0LE_0LD0LB_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76052: ~halts (TM_from_str "1RB0RD_0RC0RB_1LD1RA_0LE---_1LF0LE_1RB0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76053: ~halts (TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76054: ~halts (TM_from_str "1RB0LF_0LC0RE_0LA1LD_1RB1LB_1RD0RD_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76055: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA0LE_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76056: ~halts (TM_from_str "1RB---_0RC0RE_1LD0LF_1LE0LD_0RF0LC_1RB1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76057: ~halts (TM_from_str "1RB1LB_0LC0RE_0LD0RC_1LA0LF_1RA0RA_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76058: ~halts (TM_from_str "1RB1LB_1RC0LA_1RD1RC_0RE1RE_1LA0RF_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76059: ~halts (TM_from_str "1RB0LF_0RC1LB_0LD1LC_1RE0LA_1RF---_0LB0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76060: ~halts (TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA0LB_1RB1RD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76061: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_0LB0RA_0LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76062: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1LA0LF_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76063: ~halts (TM_from_str "1RB1RD_1LC1RE_0RD0LB_1RF1RA_0RC---_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76064: ~halts (TM_from_str "1RB---_0RC1LB_0RD0LA_0RE0RD_1LE0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76065: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA1RE_1RB1LA_1LD1RF_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76066: ~halts (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD0RD_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76067: ~halts (TM_from_str "1RB1LD_1RC0RB_1LD0LD_0LE0RA_1LA1LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76068: ~halts (TM_from_str "1RB---_0RC0RC_0RD0LE_1LD0LE_1RA0LF_1LA1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76069: ~halts (TM_from_str "1RB0LA_0RC0RB_1RD1LD_0RE0LD_1LF1RA_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76070: ~halts (TM_from_str "1RB0RC_1LC0LA_0LE1RD_0RF0RB_1RA1LE_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76071: ~halts (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD0RD_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76072: ~halts (TM_from_str "1RB0LF_1RC1LA_0RD0RC_1LE1RC_0LB---_1LB0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76073: ~halts (TM_from_str "1RB---_1RC0RA_1RD0LD_1LE0LB_0RB0LF_0LE0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76074: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA1RB_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76075: ~halts (TM_from_str "1RB0RA_1LC0RF_1RB0LD_0LE---_1LB1LE_0RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76076: ~halts (TM_from_str "1RB0LF_0RC1LC_0LD1LC_1RE0LA_1RF---_0LB0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76077: ~halts (TM_from_str "1RB0LE_0RC0RB_1LD1RF_0LE---_1LA0LE_1RB0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76078: ~halts (TM_from_str "1RB0LA_1RC1RA_0RD0RF_1LE0RB_1LE1LB_---1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76079: ~halts (TM_from_str "1RB0LD_1LC---_1RA1LC_0LE0LD_1RE0RF_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76080: ~halts (TM_from_str "1RB0LF_1LC1RC_1LD0RB_1LE1LD_1RC1LA_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76081: ~halts (TM_from_str "1RB0RA_1LC0RD_0LD0LD_1RE0LF_1RF---_1LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76082: ~halts (TM_from_str "1RB1LB_1LC0RE_1RD0RA_1LA0LD_1RF0RE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76083: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76084: ~halts (TM_from_str "1RB1LE_0RC---_1LD1RF_0LA0RB_0LA0RF_0RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76085: ~halts (TM_from_str "1RB1LD_1RC0RA_1LD1RB_1RC0LE_---0LF_1LA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt76086: ~halts (TM_from_str "1RB0LC_1LA1RE_0LD---_1LB1LD_1LF0LF_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76087: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_0LB0LB_0LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76088: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0LF_0LB0LB_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76089: ~halts (TM_from_str "1RB1RC_0RC0LC_1RD1RE_1LE0RF_0LB1LD_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76090: ~halts (TM_from_str "1RB1LC_0RC0RB_0LD0RE_1LE1LE_1LA0LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76091: ~halts (TM_from_str "1RB1LB_1LC0RE_1RD1LC_1LA0LD_1RF0RE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76092: ~halts (TM_from_str "1RB0RA_1LC0LC_0LE0RD_1RA1LC_1LD1LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76093: ~halts (TM_from_str "1RB---_1RC0LF_1RD0RB_0RE0LC_1RF0RA_1LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76094: ~halts (TM_from_str "1RB0LF_0RC0RB_1LD0RA_0LE---_1LC1RF_1LA1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76095: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD1LA_1RA0RA_0RF---_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76096: ~halts (TM_from_str "1RB---_1RC0RD_1LD0RF_1RA0LE_0LD1RC_1RE0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76097: ~halts (TM_from_str "1RB1LB_0LC0RE_0LD0RC_1LA0LF_1RA0RA_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76098: ~halts (TM_from_str "1RB0LC_1RC---_1LD1RF_1LE0RA_0LA0LA_1RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76099: ~halts (TM_from_str "1RB1RC_1LC0LB_1RE0LD_1LB1LF_1RA0RC_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76100: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RF_0LA---_0LB0RA_0RC0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76101: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA0RC_1LE0RE_1LC0LF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76102: ~halts (TM_from_str "1RB0RC_1LA0LD_1RF1LB_1RE1LD_0LA0RA_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76103: ~halts (TM_from_str "1RB1LF_1RC1RE_0RD1RF_0LE0RA_1LF---_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76104: ~halts (TM_from_str "1RB1LA_0LC0LB_1RC1LD_1LA1RE_1RF0RE_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76105: ~halts (TM_from_str "1RB1LC_0LA0RB_1RD1LE_1LA0RD_1RF0LC_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76106: ~halts (TM_from_str "1RB0LA_0RC---_0RD0RF_1LE1RE_0LE1LF_0LA1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76107: ~halts (TM_from_str "1RB0LE_1LC1RB_1RD0RC_1LA1RA_1LF0LE_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76108: ~halts (TM_from_str "1RB1RF_1LC1RA_1RD0LC_1LE0RB_0LB0LE_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt76109: ~halts (TM_from_str "1RB1RA_1LC0RF_1RD0LB_---1RE_0RA1LB_1LB0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt76110: ~halts (TM_from_str "1RB0LC_1LC0RB_0LD0LB_1RA1LE_1RF1LA_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 16 0). Time Qed.

Lemma nonhalt76111: ~halts (TM_from_str "1RB1LE_1LC0RA_1LA1LD_0LC1LC_1RB0LF_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt76112: ~halts (TM_from_str "1RB0RE_1LC1RA_1RA1LD_0LB0LF_0RA0RC_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 6 320 3 2 6 0). Time Qed.

Lemma nonhalt76113: ~halts (TM_from_str "1RB0LC_0RC0RC_1LD0RE_1LE---_1RA1LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76114: ~halts (TM_from_str "1RB1RF_1LC1LE_1RD0LB_---0RA_1LC0LF_1RB0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76115: ~halts (TM_from_str "1RB0LD_0RC1RA_0RD0RC_1RE1RF_1LA0LE_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76116: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76117: ~halts (TM_from_str "1RB0RA_0RC0RA_1RD0RF_1LE1RF_0LA0LD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76118: ~halts (TM_from_str "1RB0RC_1LC0RB_0LF0LD_0LE---_1LC1LA_0RA1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76119: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD0RC_1LA0LD_0RF---_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76120: ~halts (TM_from_str "1RB0LD_1LC0RC_1RD1RC_1LE1RF_---1LA_1LE0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt76121: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76122: ~halts (TM_from_str "1RB1LC_1LA0RE_1RD0RD_1LA0LD_0RF---_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76123: ~halts (TM_from_str "1RB0RF_1RC0LB_0RD1RE_1LD1LB_---0RF_0LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76124: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA1RF_0RE0LD_0LC0RD_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76125: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1RE0LB_1RA0RA_1LC0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 6 0). Time Qed.

Lemma nonhalt76126: ~halts (TM_from_str "1RB0LA_1RC0RD_0LB1RE_1LD0LA_---1RF_0RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76127: ~halts (TM_from_str "1RB0LE_0RC0RA_0RD1RF_1LE0LD_1LA0LD_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76128: ~halts (TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA1RB_0LB0RA_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76129: ~halts (TM_from_str "1RB0LB_0LC0RF_1LA0RD_1RE---_1LA0LA_1RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76130: ~halts (TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA1RB_0LB0LB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76131: ~halts (TM_from_str "1RB0RA_0LC0RF_1LE1RD_1LE---_0LF0LB_1RA0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76132: ~halts (TM_from_str "1RB0LD_0RC1RF_0RD0RC_1RE0LE_1LA0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76133: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0LD_0RF0RF_1RC0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76134: ~halts (TM_from_str "1RB1LE_0RC0LF_1LD0RD_0LA1RB_1RA0LB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76135: ~halts (TM_from_str "1RB0RD_0RC0RB_1LD1RA_0LE0RF_1LA0LE_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76136: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RF_0LA---_1RA0LB_0LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76137: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0LD_1LC0RF_1RC0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76138: ~halts (TM_from_str "1RB0LA_0RC0RD_1LA1RF_1LE0RB_1LE1LA_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76139: ~halts (TM_from_str "1RB0LA_0RC1RF_1RD1LC_0RE1RA_1LE0LC_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76140: ~halts (TM_from_str "1RB0LA_0RC0RB_1RD1RA_0RE0LD_1LF1RA_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76141: ~halts (TM_from_str "1RB0LC_1RC1LA_0RD0LE_1LE0RE_0LB0LF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76142: ~halts (TM_from_str "1RB0RF_1RC1RD_1LD0RA_1RB0LE_1LB1LC_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76143: ~halts (TM_from_str "1RB---_1LC0RE_1RE1LD_1RB1LC_1RA0LF_0RC0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76144: ~halts (TM_from_str "1RB1RF_1LC---_1RD1LC_0LE0LD_1RE1LA_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76145: ~halts (TM_from_str "1RB---_1RC0RA_1LD0RC_1RE0LD_1LF1RF_0RB0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76146: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD1RE_0LA0RB_0RD0LC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76147: ~halts (TM_from_str "1RB0LF_1LC0RA_---0LD_1RE1LD_0RD1RB_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76148: ~halts (TM_from_str "1RB0RB_0RC0LD_1RD1RF_1LE1RB_1LA0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76149: ~halts (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD1RB_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76150: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0LF_1RA0LB_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76151: ~halts (TM_from_str "1RB0LE_0RC---_1RD0RA_1LA0RC_1LF1LF_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76152: ~halts (TM_from_str "1RB0LC_1RC1LA_0RD0LE_1LE0RF_0LB---_0LB1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76153: ~halts (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD0LC_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76154: ~halts (TM_from_str "1RB0LD_1RC0RE_1LA0RA_0LC0LD_1RF0RD_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76155: ~halts (TM_from_str "1RB---_1RC1LB_1LD1RC_0RE0RD_1LE0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76156: ~halts (TM_from_str "1RB0LC_1RC1LA_0RD0LF_1LE0RE_0LB1RC_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76157: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_1LC0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76158: ~halts (TM_from_str "1RB0LF_1LC0RB_0RE0LD_1LA---_1LD1RB_0LC0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76159: ~halts (TM_from_str "1RB0LA_1LC1RC_0RE0LD_1LA0RD_1RD0RF_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76160: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD0RD_0LA0LF_0LB0RA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 3 320 3 2 4 0). Time Qed.

Lemma nonhalt76161: ~halts (TM_from_str "1RB0LD_1LC0RA_1RD0LB_0LE1RC_---1LF_0RD1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76162: ~halts (TM_from_str "1RB1LF_1LC0RE_---1LD_1LA1LD_0LA1RB_1RE0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76163: ~halts (TM_from_str "1RB0LD_0RC---_0RD1RC_1RE0LF_1LF0RD_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76164: ~halts (TM_from_str "1RB0LF_0LC0RE_0LA1LD_1RB1LB_1RD0RD_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76165: ~halts (TM_from_str "1RB1RC_1LB1LC_1RD0LC_0RB0RE_---1RF_1RC0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76166: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA0RC_1LE0RE_1LC0LF_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76167: ~halts (TM_from_str "1RB1LE_0LC0RA_1LF1LD_1LA1LC_0LB---_0LD0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76168: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1LA0LF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76169: ~halts (TM_from_str "1RB1LA_1RC1RF_0LD0LA_1LE1RD_1LD1LC_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76170: ~halts (TM_from_str "1RB1RD_1LC---_0LD0LD_0LE0RF_1RE0RF_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76171: ~halts (TM_from_str "1RB1LD_1RC1RB_0LD1LE_0LE1LA_1LF0RE_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76172: ~halts (TM_from_str "1RB0LD_1LC1RC_1LD0RB_---1LE_1LF1LE_0LA1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76173: ~halts (TM_from_str "1RB1LC_0LC1LB_1RD0LB_1LA0RE_---0RF_0RD0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76174: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1RB0LF_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76175: ~halts (TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RC1RA_1LC0LF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76176: ~halts (TM_from_str "1RB1LC_0RC0RB_0LD0RE_1LE0RC_1LA0LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76177: ~halts (TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LB1LC_1RB0RF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76178: ~halts (TM_from_str "1RB0RC_1LA0LD_1RF1LB_1RE1LD_1LB0RA_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76179: ~halts (TM_from_str "1RB---_1LC1RF_1LE0RD_1RA0LB_0LD0LD_1RC0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76180: ~halts (TM_from_str "1RB---_1LC1RC_0RE0LD_1LB0LB_0RF1RB_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76181: ~halts (TM_from_str "1RB1RC_1LC1LF_0RD0LD_1LB1LE_1RF---_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76182: ~halts (TM_from_str "1RB0RF_1RC0LC_0LD0RA_1LE1LB_1LB0LD_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76183: ~halts (TM_from_str "1RB1LF_0RC---_1RD0RC_1LE0RC_0LA0LE_1LE0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76184: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1LF_1RA0RE_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76185: ~halts (TM_from_str "1RB1LE_1LC0RD_1LA1LC_0LA1RB_1RD0LF_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76186: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1RB0LF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76187: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1LA_1RA0RB_0RE0LF_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76188: ~halts (TM_from_str "1RB0LF_1RC---_0LD0RA_0RE1LE_0LA1LE_1RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76189: ~halts (TM_from_str "1RB0RA_1LC0RD_1LA0LB_1RA0LE_1LD0LF_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76190: ~halts (TM_from_str "1RB---_1LC0RE_0RD0LB_0RF1LA_0LE1LD_0LA1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76191: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA0RC_1LE0RE_1LC1LF_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76192: ~halts (TM_from_str "1RB0RF_1RC0LB_0RD0RE_1LD1LB_---1RA_1RD1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt76193: ~halts (TM_from_str "1RB0LD_1LC1RC_1LD0RB_---1LE_1LF1LE_1RC1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76194: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA0LE_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76195: ~halts (TM_from_str "1RB0LE_0RC0RE_0LD1LF_1LA1LB_1RA0LC_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 18 320 3 1 8 0). Time Qed.

Lemma nonhalt76196: ~halts (TM_from_str "1RB1RD_0RC0RF_0LD1RA_1LE0LB_1RB0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76197: ~halts (TM_from_str "1RB---_1LC0RF_1LD1LB_0RE0LE_1LC1LA_1RC1RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76198: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA1LD_0LC1RA_0RA0RF_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76199: ~halts (TM_from_str "1RB0RF_0LB1LC_1RD0LA_1LB0RE_0RF---_1RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76200: ~halts (TM_from_str "1RB---_0RC1LF_0RD0LE_1LE1RA_1RB1LE_1LC0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76201: ~halts (TM_from_str "1RB1LE_1LC0RD_1LA1LC_1LB1RB_1RD0LF_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76202: ~halts (TM_from_str "1RB0LE_0RC1RD_1LC1LA_1RB0RB_1LF0LA_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76203: ~halts (TM_from_str "1RB---_0LC0RE_0LF1LD_1RB1LB_1RD0RD_1RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76204: ~halts (TM_from_str "1RB0RC_0LC0RF_1LE0LD_1LC---_1LA0RA_0RB0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76205: ~halts (TM_from_str "1RB0LC_1RC0RD_1LB0LE_1LA1RD_1LF1RB_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76206: ~halts (TM_from_str "1RB1LD_1RC1RB_1LD1RE_1RB0LA_1LA1RF_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76207: ~halts (TM_from_str "1RB0RD_1RC0RB_0LD0RA_1LF1RE_1LF---_0LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76208: ~halts (TM_from_str "1RB---_0LC0RF_0LD0RC_1LE0LA_1RB1LB_1RE0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76209: ~halts (TM_from_str "1RB0LC_0RC1RD_1LA0LE_1RC0RF_1LC0RD_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76210: ~halts (TM_from_str "1RB---_1LC1RC_0RE0LD_1LB0LB_0RF0LE_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76211: ~halts (TM_from_str "1RB0LF_1LC0RD_1RF1LA_---0RE_0RB0RF_0LA1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76212: ~halts (TM_from_str "1RB1RC_0RC0LC_1RD1RA_1LE1RF_0RA0LD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76213: ~halts (TM_from_str "1RB1LA_1RC0RC_1RD0RD_1LE0LA_0LF1LD_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76214: ~halts (TM_from_str "1RB---_0RC0RC_0RD0LE_1LD0LE_1RA0LF_0LA1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76215: ~halts (TM_from_str "1RB---_0LC0RE_0RD1LD_0LE1LD_1RA0LF_1RC0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76216: ~halts (TM_from_str "1RB1RD_1LC1RB_0RA0LB_1RE0RF_---1RF_1RA0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76217: ~halts (TM_from_str "1RB---_1LC1RD_1RF0LD_1LE0RE_0RB0LB_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76218: ~halts (TM_from_str "1RB1LA_0RC1LF_0RD0LA_1LE1RE_1RB---_1LC0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76219: ~halts (TM_from_str "1RB0RC_1LC0LA_0LE1RD_0RF0RB_1RA1LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76220: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA1RB_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76221: ~halts (TM_from_str "1RB1LB_0LC0RE_0LD0RC_1LA0LF_1RA0RA_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76222: ~halts (TM_from_str "1RB0RE_1LC0RA_0LA1LD_1LA0LF_1RA0LD_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76223: ~halts (TM_from_str "1RB1LC_1RC0LB_0RD1RE_1LD1LB_---0RF_0LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76224: ~halts (TM_from_str "1RB1LC_0RC0RB_0LD0RE_1LE0RF_1LA0LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76225: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RD_0LA0RE_1RD0LF_0LE1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76226: ~halts (TM_from_str "1RB1LF_1LC0RE_---1LD_1LA1LD_1LB1RB_1RE0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76227: ~halts (TM_from_str "1RB---_1RC0RA_1LC0LD_1RA1LE_0LF0LD_0LB0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76228: ~halts (TM_from_str "1RB---_1RC0LE_0RD1RD_1LB0RF_1LD0LB_0LF0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76229: ~halts (TM_from_str "1RB---_1LC0RD_1RD1LC_1RE0LE_1RA0LF_0LC0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76230: ~halts (TM_from_str "1RB1RC_0RC1RB_1RD1RA_1LE1RF_0RA0LD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76231: ~halts (TM_from_str "1RB0RA_1RC0RA_1LD0RB_0LE0LC_0LA1LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76232: ~halts (TM_from_str "1RB0RC_1LC0LF_1LD0LB_0LE1LF_1RE0RA_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76233: ~halts (TM_from_str "1RB---_1RC0RA_1LD0LE_0LF0LE_1RA1LD_0LB0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76234: ~halts (TM_from_str "1RB0LB_1RC0LE_1RD0RF_1LB0RB_1LA0LD_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76235: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1LA0LF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 8 0). Time Qed.

Lemma nonhalt76236: ~halts (TM_from_str "1RB1RE_1LC1LB_1RD0LB_---1RE_0RF0RC_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76237: ~halts (TM_from_str "1RB0RE_1LC1RD_---0LD_1RA0LA_0LD0RF_1RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76238: ~halts (TM_from_str "1RB1LE_1LC1RC_0RA0RD_0LF0RB_1LD---_1LA0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76239: ~halts (TM_from_str "1RB0LC_1LA0RD_1LD---_1LE0RA_0LF0LF_1LB0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76240: ~halts (TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LA1LB_1RA0RF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76241: ~halts (TM_from_str "1RB1RF_1LC---_1RA0LD_1RE0LC_1LF0RE_1RA1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 1 8 0). Time Qed.

Lemma nonhalt76242: ~halts (TM_from_str "1RB1RF_1RC1LB_1RD0RA_0LE0LB_---1LD_0RC0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 18 320 3 1 8 0). Time Qed.

Lemma nonhalt76243: ~halts (TM_from_str "1RB1LD_1RC0RD_1LD0RE_0LB0LA_1RB0RF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76244: ~halts (TM_from_str "1RB1LC_0RC0LE_1RD0LA_1LB1RC_1LF0LF_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 1 8 0). Time Qed.

Lemma nonhalt76245: ~halts (TM_from_str "1RB0RF_1RC0RD_1LD0RA_0LB0LE_1RB1LD_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76246: ~halts (TM_from_str "1RB1LE_1RC1RD_1LD1LC_1LA0RA_0LD0LF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76247: ~halts (TM_from_str "1RB---_1LC1RD_0LD0LC_0LE1LF_1RF1RA_1RE0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76248: ~halts (TM_from_str "1RB0LA_0RC0RE_0LD1RA_1LA1LF_1RF---_1RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76249: ~halts (TM_from_str "1RB---_0LC0LB_0LD1LC_1RD0RE_0LF1RF_1RA0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76250: ~halts (TM_from_str "1RB0RC_1LC0RE_0LA0LD_1RA1LC_1RA0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76251: ~halts (TM_from_str "1RB1RC_1LC1LB_1LD0RD_1RA1LE_0LC0LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76252: ~halts (TM_from_str "1RB0LE_0RC0RD_1LA0LB_1LC1RB_1LC0LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76253: ~halts (TM_from_str "1RB1LC_0RC0RB_0RD1RE_1LE1LF_1LD0LA_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76254: ~halts (TM_from_str "1RB1RF_0RC0RE_1LD0RA_1LD1LA_---1LF_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76255: ~halts (TM_from_str "1RB1RF_1LC1LE_---0LD_0LE0RC_1RF1LD_0RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 4 0). Time Qed.

Lemma nonhalt76256: ~halts (TM_from_str "1RB0LB_1LC1RD_1LF1LA_0RA0RE_0RB---_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76257: ~halts (TM_from_str "1RB0RC_1LA0LE_1LD1RC_0RB0LB_1LF1RA_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76258: ~halts (TM_from_str "1RB1RF_1LC0LD_1RE1RD_---0LE_1RF0RF_1LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76259: ~halts (TM_from_str "1RB1LE_1RC0RF_1LD1LF_1LA0LA_1LB1LA_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76260: ~halts (TM_from_str "1RB0RA_0LC0RF_1LD1RC_1RE0LB_---1LC_1RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76261: ~halts (TM_from_str "1RB1RC_1LC0RA_1RB0LD_1LE1LF_0RE0LB_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 1 16 0). Time Qed.

Lemma nonhalt76262: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD1RF_---0LA_1LC0RD_1RA1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76263: ~halts (TM_from_str "1RB1LA_1LA0RC_0RD1RC_1LE0LA_0LD0LF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76264: ~halts (TM_from_str "1RB0RA_1LC0RE_0LD0LB_0LE1LD_1RA0LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76265: ~halts (TM_from_str "1RB1RD_1LC1RF_0RB1LD_1RA1LE_0LC0LB_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76266: ~halts (TM_from_str "1RB0RC_1RC---_0RD1RC_1LE1RA_0LE0LF_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76267: ~halts (TM_from_str "1RB0LB_1LC1LB_1RE1LD_1LA1RD_---0RF_1RE0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76268: ~halts (TM_from_str "1RB1RC_1LC1LE_1RE0LD_1LB0LF_1LB0RA_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 12 0). Time Qed.

Lemma nonhalt76269: ~halts (TM_from_str "1RB0RE_1RC0LD_1RD0LA_1LB0LB_1RF---_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76270: ~halts (TM_from_str "1RB---_1LC0LE_1RF0LD_0RE1RD_1LA1LB_0RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76271: ~halts (TM_from_str "1RB1RD_1LC1LB_0RA0LB_0RE0LE_---0RF_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76272: ~halts (TM_from_str "1RB---_1LC0LC_1RD0LD_0LE0RF_1LC0RA_1RC1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76273: ~halts (TM_from_str "1RB0RB_1RC1RB_1LD1LF_---0LE_1LD0LF_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76274: ~halts (TM_from_str "1RB1LD_1RC0RC_1LA1RC_1RE0LA_1LA0LF_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76275: ~halts (TM_from_str "1RB1LA_1LC0RD_1LE1RA_1RC1RD_---0LF_1LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76276: ~halts (TM_from_str "1RB1RD_1LC0LF_1LD0LB_1RA0RE_0RC0RA_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76277: ~halts (TM_from_str "1RB1LA_1LA0RC_1RD1RC_1LE1RA_---0LF_1LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76278: ~halts (TM_from_str "1RB1LB_0RC0RB_1RD1LD_1LE---_0LF0LE_1RF1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 2 3 0). Time Qed.

Lemma nonhalt76279: ~halts (TM_from_str "1RB0LE_1RC1RA_0LD0RE_1LA1LD_1LD0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 17 320 3 2 12 0). Time Qed.

Lemma nonhalt76280: ~halts (TM_from_str "1RB0RD_1LC1RA_---1LA_1LE1RD_0LC0LF_1RF0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 2 6 0). Time Qed.

Lemma nonhalt76281: ~halts (TM_from_str "1RB0LC_1LA1RB_0LD1LC_1RE1LF_0RE0RB_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76282: ~halts (TM_from_str "1RB0RA_1LC0RE_1LD0LB_1LE0LF_1RA0LD_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76283: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD1LC_1RE0RE_1LA1RE_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76284: ~halts (TM_from_str "1RB---_1LC1RB_1RB0LD_0LB0RE_1RF0RA_1RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76285: ~halts (TM_from_str "1RB0RA_1LC0RD_1LA0LB_1RA0LE_1LD1LF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76286: ~halts (TM_from_str "1RB1LD_1LC0RF_1LD0LC_0LE0LD_1RE0RA_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76287: ~halts (TM_from_str "1RB0LB_1RC1LC_1LD0RC_1LE1RB_0LA1LF_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76288: ~halts (TM_from_str "1RB0LC_1LA0LE_1RC0RD_1LB1RD_0RF1LE_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76289: ~halts (TM_from_str "1RB0RB_1LC1RB_0RE1LD_1RD0LE_1RF1LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76290: ~halts (TM_from_str "1RB0RA_1LC0RE_1RA0LD_1LE1LB_0RB0LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76291: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA0LC_1LC0RE_1RD1RF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76292: ~halts (TM_from_str "1RB0LE_1RC1RF_1LD---_0RE1RA_1RD1LF_0RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76293: ~halts (TM_from_str "1RB0RF_0RC1RD_1LD0RA_0LE0LD_1RA0LC_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76294: ~halts (TM_from_str "1RB0LA_1RC1RA_0RD1RF_1LE0RB_1LE1LB_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76295: ~halts (TM_from_str "1RB1RA_1LC0LE_1RD1LB_0LF0RA_1LC1LD_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76296: ~halts (TM_from_str "1RB0LE_1RC0RF_0RD1RA_1LE---_0LF1LA_0LA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76297: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LC_1RB0LE_1LC0RF_1RE0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76298: ~halts (TM_from_str "1RB0LB_1RC1LC_1LD0RC_1LE0RC_0LA1LF_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 12 0). Time Qed.

Lemma nonhalt76299: ~halts (TM_from_str "1RB0LB_1RC1LC_1LD0RC_1LE0RC_0LA1LF_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 12 0). Time Qed.

Lemma nonhalt76300: ~halts (TM_from_str "1RB0RF_0RC0RA_1RD0LD_1LE0RB_1LC1LB_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 12 0). Time Qed.

Lemma nonhalt76301: ~halts (TM_from_str "1RB1RA_1LC0RA_---1LD_0LE0LB_0LF1LE_1LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76302: ~halts (TM_from_str "1RB0RC_1LA---_1RE1LD_0LC1LF_1RA0RE_1LC0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76303: ~halts (TM_from_str "1RB---_1RC1RD_1LD0LF_0RB1LE_1LC0LA_0LD0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76304: ~halts (TM_from_str "1RB0LB_0RC0RE_1LD0RA_0LA1LC_1RC1RF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76305: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA1RD_0LA---_1RF0LE_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76306: ~halts (TM_from_str "1RB1RF_1RC0RD_1RD1LC_0LE0RA_---0LC_1LE1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76307: ~halts (TM_from_str "1RB0RC_1LC0LB_1RA0LD_1LB0RE_1RD0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76308: ~halts (TM_from_str "1RB0RE_1LC0RD_1LA0RB_1LB1RA_1RF0LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76309: ~halts (TM_from_str "1RB0LF_0RC---_0RD0LA_1RE0RE_0LA0RA_1LE1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76310: ~halts (TM_from_str "1RB0LC_1LA0LE_1RC0RD_1LB1RD_---1LF_0RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76311: ~halts (TM_from_str "1RB1RF_1RC1LB_1LD0RA_1LF0LE_---0LC_1LA1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76312: ~halts (TM_from_str "1RB0LE_1RC1LC_1RD0LF_1LA0RB_---0LD_1RF0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76313: ~halts (TM_from_str "1RB0LC_1RC1RE_1LD0RF_---1LB_1RB0LD_1RF1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76314: ~halts (TM_from_str "1RB1LF_1RC1RA_1LC0RD_---0RE_0RC1LF_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76315: ~halts (TM_from_str "1RB1LD_0LC0RE_---1RD_1LA0LF_1RD1RE_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76316: ~halts (TM_from_str "1RB1LF_1LC0LB_0LD1LA_1LE0RE_1RD0RA_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76317: ~halts (TM_from_str "1RB0LC_0RC1RD_1LD0RB_1LE0RB_1LA0LF_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76318: ~halts (TM_from_str "1RB1LE_0LC0RF_---1RD_1LA1LB_1LA0LD_1RE1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76319: ~halts (TM_from_str "1RB0LE_1RC1RD_1LB0RF_0RA1LA_0LD1LB_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76320: ~halts (TM_from_str "1RB1RA_0LC0LF_1RD1LB_1LE0RA_---1LC_0RC1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76321: ~halts (TM_from_str "1RB0RE_0RC1RF_1LD---_0LE1LF_0LF1LE_1RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 2 4 0). Time Qed.

Lemma nonhalt76322: ~halts (TM_from_str "1RB1LD_1LC0RE_---1LD_1LA0LF_1RD1RE_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76323: ~halts (TM_from_str "1RB1RC_1LC0LE_1RD0RC_1RE1RA_1RF1LB_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76324: ~halts (TM_from_str "1RB0RF_1LC1RA_---1LD_0LE1LC_1LF0LA_1RB1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76325: ~halts (TM_from_str "1RB---_0RC1RD_1LD0RF_0LE0LD_1RA0LC_1RB0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76326: ~halts (TM_from_str "1RB0LA_0RC1RD_1LC1LA_---1LE_0LA1RF_1RA0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76327: ~halts (TM_from_str "1RB1RF_1LC0RD_0LD1LB_1RE0LE_0RB0RA_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76328: ~halts (TM_from_str "1RB0RB_0RC1RF_1LD0LF_0LE---_1RB0LC_1RA1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76329: ~halts (TM_from_str "1RB0LC_1LC1RC_1RE1LD_1LE0LA_0RA0LF_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76330: ~halts (TM_from_str "1RB0RF_1LC0RD_0LD1LB_1RE0LE_0RB0RA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76331: ~halts (TM_from_str "1RB1LD_1RC0RC_1LD0LE_1LA0LE_1LF0RA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76332: ~halts (TM_from_str "1RB1LB_0RC0RB_1LC0LD_0LE1LF_1RF0LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76333: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_1RC0LC_0RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76334: ~halts (TM_from_str "1RB0LB_1LC1LF_0LA0RD_1RB1RE_0RB1RC_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76335: ~halts (TM_from_str "1RB0LE_0RC1RD_1LA0RA_1RC---_1RD0LF_0LA1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76336: ~halts (TM_from_str "1RB1RC_0LC0RF_1RD0LB_1LE0RA_1LC0LE_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76337: ~halts (TM_from_str "1RB1RE_0RC0LF_1LD0RA_0LA1LB_1RB---_1LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76338: ~halts (TM_from_str "1RB0LE_1RC---_1LD0RD_1RF0LA_0LD1RB_0RC1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76339: ~halts (TM_from_str "1RB---_0RC0LE_1LD0RD_1RB1RA_1LD1LF_0LD1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76340: ~halts (TM_from_str "1RB1RD_1LC---_0LF0RA_0RE1RC_1LC1LE_1RD0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76341: ~halts (TM_from_str "1RB---_0RC0RB_1LC0RD_1RE0LD_1LF0RA_1LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76342: ~halts (TM_from_str "1RB1LA_1RC0RE_1RD0RB_0LA0RD_0RF1LD_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76343: ~halts (TM_from_str "1RB0LC_0RC1RD_1LD1LE_0LA0RF_1LD---_1RC1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76344: ~halts (TM_from_str "1RB0RA_1RC1LE_1LD1LA_0LA1LE_0LC1LF_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76345: ~halts (TM_from_str "1RB0LB_1LC1LF_0LA0RD_1RF1RE_0RB1RC_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76346: ~halts (TM_from_str "1RB1RD_1LC---_0LF0RA_0RE1RC_1LC1LB_1RE0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76347: ~halts (TM_from_str "1RB1RD_1LC---_0LF0RA_0RE1RC_1LC1LE_1RE0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76348: ~halts (TM_from_str "1RB---_1LC0RC_1RE0LD_1RA0LF_0RB1RA_0LC1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76349: ~halts (TM_from_str "1RB1LB_0LC0RE_1LE1LD_1LC---_1LF0RA_1RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76350: ~halts (TM_from_str "1RB0LE_0RC0RB_1LC1LD_0RA1RF_0LF---_1RD0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76351: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_---1LE_0LC1RA_0LC0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76352: ~halts (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD1LB_---0RA_0RB1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76353: ~halts (TM_from_str "1RB0LC_0RC1RD_1LD1LC_0LA0RE_0RF1RB_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76354: ~halts (TM_from_str "1RB0LC_0RC---_1RD0LF_0RE0RD_1LE0LF_0LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76355: ~halts (TM_from_str "1RB0LA_1LC0RF_1LE0LD_1LC---_0RE1LA_0LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76356: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_1RC0LC_0RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76357: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_1RB0LC_0RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76358: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_0RA0LC_0RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76359: ~halts (TM_from_str "1RB1RA_0RC0LF_0LD0RA_1LE---_0LA1LB_0LD0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76360: ~halts (TM_from_str "1RB0LA_1RC0RE_1LD1RE_1LD1LA_0RF0RD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76361: ~halts (TM_from_str "1RB1LD_1RC0LD_1LA0RE_0LB0LA_1RA0RF_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76362: ~halts (TM_from_str "1RB1LF_1LC0RE_1LA0LD_1LC---_0LF0RB_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76363: ~halts (TM_from_str "1RB---_0RC0LE_1LD0RD_1RB1RD_1LA1LF_0LD1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76364: ~halts (TM_from_str "1RB1LF_1LC1RE_1RD0LD_1RA0LB_0RD0RA_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76365: ~halts (TM_from_str "1RB---_0RC0LD_1LA0RF_1LF1LE_0LF1LB_1RB1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76366: ~halts (TM_from_str "1RB0LB_1LC1LB_0LA0RD_1RF1RE_0RB1RC_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76367: ~halts (TM_from_str "1RB1RE_0RC0LF_1LD0RA_0LA1LB_1RB---_1LE1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76368: ~halts (TM_from_str "1RB0LC_0RC1RD_1LD1LE_0LA0RF_1LD---_1RE1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76369: ~halts (TM_from_str "1RB0LB_1LC---_1RF1LD_1RE0LE_0LC0RC_1LA0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76370: ~halts (TM_from_str "1RB1RA_0RC0LE_1LD0RA_0LA1LB_0LF0RE_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76371: ~halts (TM_from_str "1RB---_1RC0RF_1LD1RF_1LD1LE_1RB0LE_0RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76372: ~halts (TM_from_str "1RB0RE_0LC0LB_1RC1LD_0LE1RF_1LB---_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76373: ~halts (TM_from_str "1RB0LA_1LC0RF_1LE0LD_1LC---_1RB1LA_0LE0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76374: ~halts (TM_from_str "1RB0LA_0LC0RD_1LE0RD_1LB0RC_1LF---_1RC1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76375: ~halts (TM_from_str "1RB1RA_0RC0LD_1LA0RA_0LF1LE_0LA1LB_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76376: ~halts (TM_from_str "1RB1LF_0LC0RD_1LE0RD_1LB0RC_1LA---_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76377: ~halts (TM_from_str "1RB---_0RC0LD_1LA0RF_1LA1LE_0LF1LB_1RB1RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76378: ~halts (TM_from_str "1RB1RD_1LC1LF_0LE0RA_0RB1RC_1RD0LB_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76379: ~halts (TM_from_str "1RB0LB_1RC0LD_1RD1LF_1LA1RE_0RB0RC_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76380: ~halts (TM_from_str "1RB---_1LC0LA_1LE1RD_0RE0RC_1LF0RD_0LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76381: ~halts (TM_from_str "1RB0LF_1LC---_0LA0RD_1RB1RE_0RF1RC_1LC1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76382: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_0RA0LC_0RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76383: ~halts (TM_from_str "1RB1RD_1LC1LF_0LE0RA_0RB1RC_1RB0LB_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76384: ~halts (TM_from_str "1RB---_0RC0LF_1LD0RE_0LE1LB_1RB1RE_1LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76385: ~halts (TM_from_str "1RB1LF_1RC0LF_0RD0RE_1LE---_1RA0RD_0LB0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76386: ~halts (TM_from_str "1RB0LC_0RC1RD_1LD1LC_0LA0RE_0RF0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76387: ~halts (TM_from_str "1RB0LD_0RC0RB_1LC0LD_0LE1LF_1RF0LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76388: ~halts (TM_from_str "1RB0LC_0RC1RD_1LD1LC_0LA0RE_1RF1RB_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76389: ~halts (TM_from_str "1RB1RD_1LC---_0LF0RA_0RE1RC_1LC1LB_1RD0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76390: ~halts (TM_from_str "1RB---_0RC0RB_1LC1RD_0RA1LE_0LF0LE_1LB0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76391: ~halts (TM_from_str "1RB0RF_1LC---_0LE0LD_1RE1LC_1RA0LC_1RD1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76392: ~halts (TM_from_str "1RB0RB_0LC0RE_1LE1LD_1LC---_1LA0RF_1RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76393: ~halts (TM_from_str "1RB0LC_0RC0LA_1RD0LA_1RE---_1LB1RF_1LB0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76394: ~halts (TM_from_str "1RB0LA_1LC0RF_1LE0LD_1LC---_1RB1LA_0LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76395: ~halts (TM_from_str "1RB1RA_0RC0LF_0LD0RA_1LE---_0LA1LB_0LD1LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76396: ~halts (TM_from_str "1RB0LF_1LC---_0LA0RD_1RF1RE_0RF1RC_1LC1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76397: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_1RB0LC_0RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76398: ~halts (TM_from_str "1RB0LF_0RC1LF_1RD---_1LE0RE_1RA0LF_0LB0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76399: ~halts (TM_from_str "1RB1RD_1LC---_0LF0RA_0RE1RC_1LC1LB_1RB0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76400: ~halts (TM_from_str "1RB1RD_0RC0LE_1LD0RA_1RB---_1LA1LF_0LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76401: ~halts (TM_from_str "1RB---_0RC0LE_1LD0RD_1RB1RA_1LA1LF_0LD1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76402: ~halts (TM_from_str "1RB1RA_0RC0LF_0LD0RA_1LE---_0LA1LB_0LD0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76403: ~halts (TM_from_str "1RB1LF_1LC0RE_1LA0LD_1LC---_0LA0RB_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76404: ~halts (TM_from_str "1RB0LB_1LC0RE_0LA1LD_1LA---_1LD0RF_0RB1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76405: ~halts (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RF0RE_1RC0RC_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76406: ~halts (TM_from_str "1RB0LC_0RC---_1RD1LD_0RE0RD_1LE0LF_0LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76407: ~halts (TM_from_str "1RB1RA_0RC0LE_1LD0RA_1RB---_1LD1LF_0LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76408: ~halts (TM_from_str "1RB0LC_0RC0LA_1RD0LA_1RE---_1LC1RF_1LB0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76409: ~halts (TM_from_str "1RB1RA_0RC0LE_1LD0RA_0LA1LB_0LF1LD_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76410: ~halts (TM_from_str "1RB1RA_0RC0LD_1LA0RA_0LE0RD_1LF---_0LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76411: ~halts (TM_from_str "1RB1RF_0RC0LD_1LA0RA_1LF1LE_0LA1LB_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76412: ~halts (TM_from_str "1RB0LA_1RC0RF_1LD1RE_1LD1LA_---0RD_0RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76413: ~halts (TM_from_str "1RB0LE_0RC1LE_1RD---_1LA0RF_0LB0RE_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76414: ~halts (TM_from_str "1RB0LB_1LC1LB_0LA0RD_0RF1RE_0RB1RC_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76415: ~halts (TM_from_str "1RB0LB_1LC1LB_0LA0RD_0RF1RE_0RB1RC_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76416: ~halts (TM_from_str "1RB1RA_0RC0LD_1LA0RA_1LF1LE_0LA1LB_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76417: ~halts (TM_from_str "1RB1RD_0RC0LE_1LD0RA_1RB---_1LD1LF_0LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76418: ~halts (TM_from_str "1RB---_0RC0LD_1LA0RF_1LA1LE_0LF1LB_1RB1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76419: ~halts (TM_from_str "1RB---_0RC0LF_1LD0RE_0LE1LB_1RB1RA_1LE1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76420: ~halts (TM_from_str "1RB1RD_1LC1LF_0LE0RA_0RB1RC_1RF0LB_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76421: ~halts (TM_from_str "1RB---_0LC0RC_1LF0LD_1LE1LA_1LB0RF_1RE0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 20 320 3 1 2 0). Time Qed.

Lemma nonhalt76422: ~halts (TM_from_str "1RB1RF_0RC0LD_1LA0RA_1LA1LE_0LA1LB_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76423: ~halts (TM_from_str "1RB1RA_0RC0LE_1LD0RA_0LA1LB_1LF1LD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76424: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LC_0LE0RF_0RA0LC_0RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76425: ~halts (TM_from_str "1RB0LF_1LC---_0LA0RD_1RB1RE_0RF1RC_1LC1LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76426: ~halts (TM_from_str "1RB---_0RC0LF_1LD0RE_0LE1LB_1RB1RA_1LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76427: ~halts (TM_from_str "1RB0LC_0RC1RA_1RD0LF_0RE0RD_1LE1LB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76428: ~halts (TM_from_str "1RB0LA_0LC0RD_1LE0RD_1LB0RC_1LF---_0RF1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76429: ~halts (TM_from_str "1RB1RD_1LC---_0LF0RA_0RE1RC_1LC1LE_1RB0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76430: ~halts (TM_from_str "1RB0LB_1LC1LB_0LA0RD_0RE0LD_1RF---_0RB1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76431: ~halts (TM_from_str "1RB1RA_0RC0LD_1LA0RA_0LF1LE_0LA1LB_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76432: ~halts (TM_from_str "1RB0LC_0RC---_1RD0LA_1LA1RE_1LA1RF_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76433: ~halts (TM_from_str "1RB0LA_0LC0RD_1LE0RD_1LB0RC_1LF---_1RB1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 2 4 0). Time Qed.

Lemma nonhalt76434: ~halts (TM_from_str "1RB1LA_1RC0RF_1LD0RC_1LE0LD_0LA1LC_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76435: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA0RE_1LE1LC_0RC0LF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76436: ~halts (TM_from_str "1RB0RD_1LC1LC_1RE1LD_1LC0LB_---1RF_0RA1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76437: ~halts (TM_from_str "1RB0LC_0LC0RE_1RF1LD_1LA1LC_---1RA_1RB1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76438: ~halts (TM_from_str "1RB0RE_1RC---_0LD1RA_0LA1LD_1LF0RF_1LC0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76439: ~halts (TM_from_str "1RB0LD_1LC0RC_---1RA_1RF1LE_1LA1LD_0LC1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76440: ~halts (TM_from_str "1RB1RC_1LC0LE_1RD0LB_---1RA_1LC0RF_1RE1LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76441: ~halts (TM_from_str "1RB0LD_1RC1RF_1LA0RE_0LF1LB_1RA---_0RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76442: ~halts (TM_from_str "1RB1RD_0RC0RF_0LD1RA_1LE0RB_1RB0LE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76443: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA1RD_0LE1RF_1LC1LE_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76444: ~halts (TM_from_str "1RB0LC_1LC0RB_0LD0LB_0RA1LE_1LA0LF_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76445: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA1RD_0LE0RF_1LC1LE_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 12 320 3 2 6 0). Time Qed.

Lemma nonhalt76446: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_1LB1LD_1RF1RB_1LB0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76447: ~halts (TM_from_str "1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_0LA0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76448: ~halts (TM_from_str "1RB0LC_1RC0RF_1LD0RD_0RE0LE_1LA1RC_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76449: ~halts (TM_from_str "1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_1RD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76450: ~halts (TM_from_str "1RB0RF_1LC0RD_1RD0LC_0RE0RC_0LB1RA_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76451: ~halts (TM_from_str "1RB0LD_1LC0RD_1RE1RB_0RB1RF_0LA1LE_---0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76452: ~halts (TM_from_str "1RB0RA_1LC0LB_1RE0LD_1LE1LF_1LA0RC_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76453: ~halts (TM_from_str "1RB0LF_1LC1RA_0RB1LD_1RE1LE_---0LA_1RC1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76454: ~halts (TM_from_str "1RB0LE_1LC1LA_0RD1RC_1LA1RB_0LA1LF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76455: ~halts (TM_from_str "1RB0RB_1LC0LD_0LF1LA_1RE1LD_1RA0RA_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76456: ~halts (TM_from_str "1RB0LE_1LC1LA_0RD1RC_1LA0RE_0LA1LF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76457: ~halts (TM_from_str "1RB0LE_0LB0RC_1RD---_1LA1RE_1LF0RF_0RD0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76458: ~halts (TM_from_str "1RB1LA_1LC0RC_0RA0LD_1LE---_1LA0LF_0LB1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76459: ~halts (TM_from_str "1RB0RB_0RC1RF_1RD0LE_1RE0RA_1LC0LE_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 20 320 3 1 12 0). Time Qed.

Lemma nonhalt76460: ~halts (TM_from_str "1RB1RF_1LC---_0LD1LC_1LE0RF_0RD0LE_1LD1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76461: ~halts (TM_from_str "1RB0RF_0RC1RD_1LD0RA_0LE0LD_1RA0LC_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76462: ~halts (TM_from_str "1RB1RA_1LC0LE_1RD1LB_0LF0RA_1LC1LD_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76463: ~halts (TM_from_str "1RB0LA_0RC0RA_0LD1RE_1LA0RB_1RD0RF_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76464: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD1LB_1RD1LE_1RF0LB_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76465: ~halts (TM_from_str "1RB1RC_1LA0RF_0RD1LD_1RA0LE_0LC1LA_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76466: ~halts (TM_from_str "1RB0LC_0LC0RD_1LE1LA_1RA1LD_0RF0LD_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76467: ~halts (TM_from_str "1RB0LC_1LA0RF_1LD0RD_0RE0LE_1LA1RC_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76468: ~halts (TM_from_str "1RB0RA_1LC0RD_1LF0LD_1LE0LB_1RA1LD_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76469: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD1LF_0RD0LB_1RB1RA_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 2 12 0). Time Qed.

Lemma nonhalt76470: ~halts (TM_from_str "1RB1RA_1LC0LE_1RD1LB_1LF0RA_1LC1LD_---1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76471: ~halts (TM_from_str "1RB0LD_1LC1RB_---1LA_1RE1LD_0LB1RF_1RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76472: ~halts (TM_from_str "1RB---_1RC0RA_0RD1RE_1LE0RB_0LF0LE_1RB0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76473: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0LA_1LF1LC_---0RF_1LD1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76474: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1LA1LF_---0LA_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76475: ~halts (TM_from_str "1RB1RA_0RC1LB_1LD0LD_1RE1LC_0RA1RF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76476: ~halts (TM_from_str "1RB1LA_1RC1RF_0LD0LA_1LE1RD_1RD1LC_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76477: ~halts (TM_from_str "1RB0RD_1LC1RA_1RB1LC_1LE1RD_1LA1LF_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76478: ~halts (TM_from_str "1RB1LB_1RC0LD_0RD1RF_1RE0LA_0LA0RB_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76479: ~halts (TM_from_str "1RB0LD_1LC1RB_---1LA_1RE1LD_1LC1RF_1RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76480: ~halts (TM_from_str "1RB1RA_1LC0RC_---1RD_1RB0LE_1RA1LF_1LD1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76481: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA0LD_1LA0RF_1RE1RA_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76482: ~halts (TM_from_str "1RB0RF_1LC0LE_1LA0LD_0RE1LD_1LB1RA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76483: ~halts (TM_from_str "1RB0RD_1LC0LE_1LD0LB_1RA0LC_1LF0RC_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76484: ~halts (TM_from_str "1RB---_1RC0RF_0LD0RA_0LB1LE_1RC0LC_1LD1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76485: ~halts (TM_from_str "1RB0RB_1LC1RB_0RE1LD_1LA0LE_1RF1LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76486: ~halts (TM_from_str "1RB1RC_1LC0RA_1RD0LC_1RE---_0RF1LE_1LF1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76487: ~halts (TM_from_str "1RB0RD_1LC0RB_0LD0LB_1RE1RB_0RF1RA_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76488: ~halts (TM_from_str "1RB1RE_1LC0RF_1RA0LD_0LE1LA_0RC1LC_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76489: ~halts (TM_from_str "1RB0LD_0LC0RC_1RD1LB_1RE0LF_1LC1RC_---1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76490: ~halts (TM_from_str "1RB0RD_1LC0LD_1LD1LC_1RA1LE_0LF0LB_---1RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76491: ~halts (TM_from_str "1RB0LE_1LC0RA_0LF1RD_---1RE_1LA1RC_1LE1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76492: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1RA1LE_0LF0LA_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76493: ~halts (TM_from_str "1RB0LE_1RC1RF_0RD0RE_1LE0RA_0LA0LD_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76494: ~halts (TM_from_str "1RB0LD_0LC0RB_1RE1RD_1LA0LB_0RF---_1RA0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76495: ~halts (TM_from_str "1RB0RF_1LC0LF_0LE0LD_0RE0LB_1RF---_1RA0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76496: ~halts (TM_from_str "1RB0LD_1LC0RC_---1RA_1RF1LE_1LA1LD_1RB1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76497: ~halts (TM_from_str "1RB1RC_1LC0LF_0RA1LD_1LB0LE_1RA---_0LC0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76498: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RA_0LA0LE_---1LC_1LB0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76499: ~halts (TM_from_str "1RB0RE_0RC1RD_1LD0RA_0LE0LD_1RF0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76500: ~halts (TM_from_str "1RB1RB_1LC1RF_---1LD_0LE1LC_1LA0LF_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76501: ~halts (TM_from_str "1RB0LF_1LC0RE_1LA1LD_0LB1RB_0RD1RC_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76502: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD1LB_0RA1LE_1RF0LB_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76503: ~halts (TM_from_str "1RB0LF_0RC0RB_1LD0RA_1LE---_0LA1LB_1LE0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76504: ~halts (TM_from_str "1RB0LC_0RC1RE_1LD0LE_0LA---_1RF1LC_1RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76505: ~halts (TM_from_str "1RB0RE_1LC1RE_1LB0LD_1RA1LD_1LF0RC_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76506: ~halts (TM_from_str "1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB1LF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76507: ~halts (TM_from_str "1RB1LF_1LC0RA_1LA0LD_1LE1RA_0LB0LE_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76508: ~halts (TM_from_str "1RB0RC_1LC1LB_1RF0RD_1LE1RD_0RD0LB_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76509: ~halts (TM_from_str "1RB0LE_0RC0LF_0RD0RF_1LD0LE_1LB---_0LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76510: ~halts (TM_from_str "1RB1LC_1LC0RD_1RD1LA_1RF0LE_0RC0LC_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76511: ~halts (TM_from_str "1RB0LD_1RC0RF_1RD1LD_1LE1LC_1LA1RE_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76512: ~halts (TM_from_str "1RB1LD_1LC0LB_0RA1LA_0LE---_1LF0RF_1RE0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76513: ~halts (TM_from_str "1RB1RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76514: ~halts (TM_from_str "1RB0RF_1LC1RD_1RA0LD_1LE0RE_0RB0LB_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76515: ~halts (TM_from_str "1RB0RD_1RC0RA_1LD0LA_0LF0LE_0RF0LC_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 18 320 3 1 6 0). Time Qed.

Lemma nonhalt76516: ~halts (TM_from_str "1RB---_0LC0RD_0LF0LD_0RE0LB_1LB0RA_1RF0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76517: ~halts (TM_from_str "1RB0LB_0RC0RE_1LD0RA_0LA1LC_1RC0RF_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76518: ~halts (TM_from_str "1RB1RE_0LC1LB_1RE0LD_0RE1RF_1LA0RD_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76519: ~halts (TM_from_str "1RB0LE_1LC0RD_1LA0LC_1RE1RA_0LA0RF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 320 3 1 8 0). Time Qed.

Lemma nonhalt76520: ~halts (TM_from_str "1RB0LE_1LC0RE_1LA0LD_1RA0LC_1RA1RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76521: ~halts (TM_from_str "1RB1RA_1LC0LF_---1LD_1RE0LE_1LA1LB_0LE0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 6 0). Time Qed.

Lemma nonhalt76522: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD1RC_1RA1LF_---0RC_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76523: ~halts (TM_from_str "1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_0LA0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76524: ~halts (TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA0RB_1RB1RD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76525: ~halts (TM_from_str "1RB1RD_1RC0LB_0RD---_1LE0RA_1LB0LF_1RD1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76526: ~halts (TM_from_str "1RB---_0RC1RB_1LD1RC_1LE0LE_0LF0LC_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76527: ~halts (TM_from_str "1RB0RC_1LC0RB_1LD0LD_1RE0LB_1RB0RF_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76528: ~halts (TM_from_str "1RB1RB_1RC0RD_1LD0LF_1LE1RD_---1LC_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76529: ~halts (TM_from_str "1RB1LA_0RC0RF_1LD1RC_1LE1LF_---1LA_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76530: ~halts (TM_from_str "1RB1RF_0RC0RD_1LD0RA_1LE1LF_---1LA_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76531: ~halts (TM_from_str "1RB0RF_0RC1LF_1LD---_0LE1RF_1RE0LD_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 1 4 0). Time Qed.

Lemma nonhalt76532: ~halts (TM_from_str "1RB1RD_1LC0RC_1RE0LD_0LC0RF_0RB1RA_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76533: ~halts (TM_from_str "1RB1LA_1LA1RC_0RA0RD_1LE1RD_1LC1LF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76534: ~halts (TM_from_str "1RB---_0RC0LE_1RD0LC_1LB0RF_1LC1LF_0LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76535: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1RA1LE_1LF0LA_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76536: ~halts (TM_from_str "1RB0LC_0LC0RD_1RD1LD_1RE0LA_0RA1RF_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76537: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD1RC_1LA1LF_---0RC_1LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76538: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD1RC_1RA1LF_---0RC_1LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76539: ~halts (TM_from_str "1RB1RE_1LC1LF_1RD0LB_---1RE_0RA0RF_1LC0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 1 8 0). Time Qed.

Lemma nonhalt76540: ~halts (TM_from_str "1RB0RC_1LC0LB_1RA0LD_1LB0RE_1RD1RF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76541: ~halts (TM_from_str "1RB1LF_1RC0LF_1RD1RB_1RE0RC_1LF---_1LA1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76542: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1LA1LF_---0LA_1LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76543: ~halts (TM_from_str "1RB0LB_1LC1RF_---0LD_0LE0RA_1LA1LE_0LD1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76544: ~halts (TM_from_str "1RB---_0LC0LE_1RE1RD_1LE0RA_1RF0LF_0LD0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76545: ~halts (TM_from_str "1RB0LC_1RC0LF_1LD0RE_0LA1LA_0RB---_0LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76546: ~halts (TM_from_str "1RB0RC_0LC0LB_1RC1LD_1LA1RE_1RF0RE_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76547: ~halts (TM_from_str "1RB0RB_1LC1RB_1RF1LD_1LA0LE_1RF1LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76548: ~halts (TM_from_str "1RB1RD_0LC1LB_1RD1LA_1LA0RE_0RD1RF_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76549: ~halts (TM_from_str "1RB---_0LC1RE_1LC1LD_1RB1LF_0RB0RE_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76550: ~halts (TM_from_str "1RB0LC_1RC1RE_1LA0LD_1LA0RA_1RD0RF_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76551: ~halts (TM_from_str "1RB0LB_0LC0RF_1LE0RD_0RC1RD_1LF---_0LA1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76552: ~halts (TM_from_str "1RB1LA_1LC1RF_0LA1LD_1RE0LA_---0RC_1RD0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76553: ~halts (TM_from_str "1RB1LC_0LC0RE_1LA0RD_1LB1RC_1RF0RF_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76554: ~halts (TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76555: ~halts (TM_from_str "1RB---_1RC0LB_0RD0RC_0LE1LB_1LE1LF_0LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76556: ~halts (TM_from_str "1RB0LD_1LC1RB_---1LA_1RE1LD_1RF1RF_1RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76557: ~halts (TM_from_str "1RB0LB_1RC0LA_1RD0RA_0RE1RF_1LE1RB_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76558: ~halts (TM_from_str "1RB0LF_1LC1RF_---1LD_1LE0LA_0RA0LC_1RE1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76559: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1RA1LE_0LF0LA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76560: ~halts (TM_from_str "1RB0LC_1RC1RE_1LA0LD_1LA0RA_1RD0RF_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76561: ~halts (TM_from_str "1RB---_1LC0RD_0LD1LA_1LF0RE_1LB1RB_0RE0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76562: ~halts (TM_from_str "1RB---_1RC0LF_0RD0RD_1RE0LA_1RF0LB_1LE0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76563: ~halts (TM_from_str "1RB1LF_0LC0LE_1LA0RD_0RE---_1LB1RA_1LC0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76564: ~halts (TM_from_str "1RB0LC_0RC1RA_0LD0LE_1LA---_1RF1LF_0RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76565: ~halts (TM_from_str "1RB1LA_1LB1RC_---0RD_1LE1RD_1RA1LF_0LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76566: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD1RC_1LA1LF_---0RC_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76567: ~halts (TM_from_str "1RB0RC_1LA0LE_1LD1RC_1RA0LB_1LF1RA_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76568: ~halts (TM_from_str "1RB1LF_1LC0RC_0LE1RD_0RB1RD_---0LA_0LA1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76569: ~halts (TM_from_str "1RB0LA_0RC0RB_0LD1LA_1LD1LE_0LF1RA_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76570: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0LE_0LE0RA_1RA1LA_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76571: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LE_1LD1RC_1LA0LF_0RF0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76572: ~halts (TM_from_str "1RB---_1LC0RD_0LD1LB_0RA0RE_1LF1RF_0LC0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76573: ~halts (TM_from_str "1RB0LE_1LC1RA_0RB1LD_1RE1LF_1RC1LA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76574: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1LA1LE_0LF0LA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76575: ~halts (TM_from_str "1RB1LA_0RC0RF_1LD1RC_1LE1LF_---1RA_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76576: ~halts (TM_from_str "1RB0RF_0LC0RD_1LD1LC_0RE0LC_---1RA_0RC1RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76577: ~halts (TM_from_str "1RB1LA_1LB1RC_---0RD_1LE1RD_1RA1LF_1LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76578: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1RA1LF_---0LA_1LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76579: ~halts (TM_from_str "1RB1LA_1LB1RC_---0RD_1LE1RD_1LA1LF_0LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76580: ~halts (TM_from_str "1RB1LA_1LA1RC_0LD0RD_1LE1RD_1LC1LF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76581: ~halts (TM_from_str "1RB1LA_1LA1RC_1RB0RD_1LE1RD_1LC1LF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76582: ~halts (TM_from_str "1RB1LA_0LC1RF_1LD1RC_---1LE_1RC0LA_1RE0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76583: ~halts (TM_from_str "1RB1RB_1RC0RD_1RD0LF_1LE1RD_---1LC_1RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76584: ~halts (TM_from_str "1RB1LA_1LC1RF_---1LD_1RE0LA_1LC1RE_1RD0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76585: ~halts (TM_from_str "1RB1LA_1LB1RC_---0RD_1LE1RD_1LA1LF_1LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76586: ~halts (TM_from_str "1RB1LE_1RC0LD_1RD0RA_1LA1LB_1LC0LF_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76587: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1RA1LF_---0LA_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76588: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1LA1LE_1LF0LA_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76589: ~halts (TM_from_str "1RB0RB_1LC1RB_1RF1LD_1RD0LE_1RF1LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76590: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RD_1LC0LA_1RB0RF_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76591: ~halts (TM_from_str "1RB1LA_1LA1RC_1LE0RD_1LE1RD_1LC1LF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76592: ~halts (TM_from_str "1RB0LB_1RC0LA_1RD0RA_1RE1RF_1LB0LC_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76593: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0LA_1RF1LC_---0RF_1LD1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76594: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1LE_0LE0LA_1RA0LC_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76595: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RC_1LA1LE_0LF0LA_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76596: ~halts (TM_from_str "1RB0LB_1RC1LD_0RD1RF_0RE1LB_1LA1RE_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 2 12 0). Time Qed.

Lemma nonhalt76597: ~halts (TM_from_str "1RB1LE_1RC0LF_1RD---_1LA0RB_1RD1LA_0RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76598: ~halts (TM_from_str "1RB1RA_1RC0RE_0LD---_0RA1LE_1LC0LF_1RD1LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76599: ~halts (TM_from_str "1RB1LD_1RC0LE_1LA0LF_---1LE_0LC1RA_0LC0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76600: ~halts (TM_from_str "1RB1LA_0RC1LE_1RD1RC_1LE0RE_1LF0LA_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76601: ~halts (TM_from_str "1RB0LE_0RC1RC_1RD1LA_1LB0RC_1LF1LC_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76602: ~halts (TM_from_str "1RB0LD_0LC1RD_1LA1LC_1RF0RE_1LB1RE_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76603: ~halts (TM_from_str "1RB1RE_0LC0LC_1LD1LC_1RA0RF_---1RF_0RD1LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76604: ~halts (TM_from_str "1RB0LE_0RC1RC_1RD1LA_1LA0RC_1LF1LC_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76605: ~halts (TM_from_str "1RB0RF_1LC1RE_1LA0RD_0RA1LB_---1RD_0RA0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76606: ~halts (TM_from_str "1RB0RF_1RC1RE_0LD0LD_1LA1LD_---1RF_0RA1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76607: ~halts (TM_from_str "1RB1RA_1LC0RC_1LF0LD_1RE1LD_0RA1LC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76608: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_---1LE_0LC1LE_0LC0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76609: ~halts (TM_from_str "1RB---_0RC0RD_0LD0RB_1LE0LE_1RF0LD_0RD1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76610: ~halts (TM_from_str "1RB1LA_0RC1LF_1RD1RC_1RE0RF_0LB---_1LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76611: ~halts (TM_from_str "1RB---_0RC0RD_0LD0RB_1LE0LE_1RF0LD_0RB1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76612: ~halts (TM_from_str "1RB0RF_1LC1RD_1LA1LC_---1RE_0RA1LB_0RA0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 3 0). Time Qed.

Lemma nonhalt76613: ~halts (TM_from_str "1RB1LE_0LC1RD_1LC1LA_0RB0RD_0LF0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76614: ~halts (TM_from_str "1RB0LA_1RC1RA_0RD0RE_1LE0RB_1LF1LA_---1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76615: ~halts (TM_from_str "1RB0LF_1RC---_1LD0RA_1RA1LE_1RC1LD_0RD0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76616: ~halts (TM_from_str "1RB0LD_1RC0LE_1LD0RE_1LB0LA_1RB1RF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 12 0). Time Qed.

Lemma nonhalt76617: ~halts (TM_from_str "1RB0LD_1RC0LF_1LD1RA_0RB0RE_1RD1LC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76618: ~halts (TM_from_str "1RB0LE_1LC0RC_0RA0LD_1LB1LA_1LF---_1RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76619: ~halts (TM_from_str "1RB0RB_1LC0RC_0RE0LD_1LB1LE_1RB0LF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 1 4 0). Time Qed.

Lemma nonhalt76620: ~halts (TM_from_str "1RB0LD_1LC0RE_1LA1LD_0LB0RF_1LB1RC_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76621: ~halts (TM_from_str "1RB1LF_1LC0RD_1LA0LD_1LB1RE_0RE0RA_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76622: ~halts (TM_from_str "1RB---_1LC0LB_0LD1LA_1LE0RE_1RD0RF_1RB1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76623: ~halts (TM_from_str "1RB0RE_0RC---_1LD0LC_1RA1LE_1LC0RF_1RD1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 18 320 3 1 8 0). Time Qed.

Lemma nonhalt76624: ~halts (TM_from_str "1RB---_1RC0LE_1RD0RE_1LB1RA_1RB1LF_0LF0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76625: ~halts (TM_from_str "1RB---_1LC0RC_1RE0LD_0LB1RD_0LF0LE_1RF0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76626: ~halts (TM_from_str "1RB1LA_1LC0RF_---0LD_1RE0LE_1LA1LB_1RB1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76627: ~halts (TM_from_str "1RB0LC_1LA0RF_1RD0LB_0RE0RE_1RA0LF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76628: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA0LC_1LC0RE_1RD0RF_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76629: ~halts (TM_from_str "1RB0RF_0LC---_1RD1LC_1RE0RE_0LC1RA_1LE0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76630: ~halts (TM_from_str "1RB0LA_0RC0RB_0LD1LF_1LD1LE_0LF1RA_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76631: ~halts (TM_from_str "1RB1RD_1RC0LC_0LD0RA_1LB0RE_1RF---_1LB0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76632: ~halts (TM_from_str "1RB1LC_1LC0LB_0LE0LD_0LB---_1LF0RF_1RE0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76633: ~halts (TM_from_str "1RB0LA_0RC0RB_0LD1LA_1LD1LE_0LF1RA_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76634: ~halts (TM_from_str "1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76635: ~halts (TM_from_str "1RB1LF_1RC0LE_0RD1RD_1LB0RA_0RB0LB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76636: ~halts (TM_from_str "1RB0LE_0LC1RD_1LE0RD_0RB0RF_1LA0LC_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 2 8 0). Time Qed.

Lemma nonhalt76637: ~halts (TM_from_str "1RB0LD_1RC0RF_1LA0RD_1LC1LE_0LC---_1LC0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76638: ~halts (TM_from_str "1RB1LB_0RC0LF_0RD1RF_0LE0LA_1LF---_1RC0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76639: ~halts (TM_from_str "1RB0LE_1LC1RA_0RB1LD_0LE1LF_1RC1LA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76640: ~halts (TM_from_str "1RB0LB_1RC0RE_1LD0RB_1LB0LC_1RA0LF_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 13 320 3 2 4 0). Time Qed.

Lemma nonhalt76641: ~halts (TM_from_str "1RB0LC_1LC0RB_0LF0LD_0LE---_1LC1LA_0RA1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76642: ~halts (TM_from_str "1RB---_1RC0RB_1LD1LB_1RE0LD_0RF0RA_0LC1RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76643: ~halts (TM_from_str "1RB1LD_1RC1LB_0LB0RD_1LE0RC_1LF---_1LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76644: ~halts (TM_from_str "1RB---_1RC1RF_0RD0RE_1LE0RB_0LF0RF_1RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76645: ~halts (TM_from_str "1RB0LC_1LC0RF_0LA1LD_0RE1LB_0RA1RD_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76646: ~halts (TM_from_str "1RB0RD_1LC1RE_1LD0LC_1RA0LB_0RA0LF_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76647: ~halts (TM_from_str "1RB0LD_1LB0RC_1RA1LC_1LE1LA_0RF0LC_---1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76648: ~halts (TM_from_str "1RB1LE_1LC0LB_1RD0RC_0LA0RC_1LF---_1LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76649: ~halts (TM_from_str "1RB1LB_0LC0LE_1LA1RD_1RE---_0RF0LA_1RC0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76650: ~halts (TM_from_str "1RB0RE_1LC0RD_0LE0LD_1RA0LC_1RB1RF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76651: ~halts (TM_from_str "1RB1RF_0RC1RE_1LD0RA_1LD1LA_---1RF_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76652: ~halts (TM_from_str "1RB1LC_1LC0RD_1RE1RB_0RB1RF_0LA1LE_---0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 12 320 3 2 8 0). Time Qed.

Lemma nonhalt76653: ~halts (TM_from_str "1RB0LD_0RC0RD_1LA1LF_1LE0RB_1LA0LC_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76654: ~halts (TM_from_str "1RB0LB_0LC0RF_1LA0RD_1RE---_0LF0LA_1RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76655: ~halts (TM_from_str "1RB0LC_1LC1RF_1LE0RD_0LB0RB_1LA---_1LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76656: ~halts (TM_from_str "1RB1RE_1LC0RE_1RA0LD_1RC1LA_0RC0LF_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76657: ~halts (TM_from_str "1RB1LB_1LA0RC_1LD0RB_0LE0LD_0RA0LF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 3 1 3 0). Time Qed.

Lemma nonhalt76658: ~halts (TM_from_str "1RB0LC_0RC0RB_0RD1RC_0LE1LF_1LF---_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76659: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RA_0LE0LA_1RC1RF_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76660: ~halts (TM_from_str "1RB1LE_1RC0RB_1LD0RA_1LA0LC_0LD0RF_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76661: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD1RF_0LE---_1LA0LF_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76662: ~halts (TM_from_str "1RB0LE_1RC0LD_1LB0RE_1RF0LC_1RD---_0RA0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76663: ~halts (TM_from_str "1RB1RA_0RC---_1RD0LC_0RE0RD_1LF0RA_1LF1LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76664: ~halts (TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RE0RF_1LC0RC_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76665: ~halts (TM_from_str "1RB0LE_1RC0RE_0RD---_1LA0LD_1RF0RA_1LD1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76666: ~halts (TM_from_str "1RB0LE_0RC1RF_1LD0RD_1LE1RE_1RA0LE_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76667: ~halts (TM_from_str "1RB0LE_0RC1RF_1LD0RD_1LE1RE_1RA0LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76668: ~halts (TM_from_str "1RB0RA_1LC1LA_1RD0LC_0RE0RF_0LB1RC_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76669: ~halts (TM_from_str "1RB1RE_0RC0RD_1LD0RA_0LE0RE_1RF0LC_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76670: ~halts (TM_from_str "1RB0LE_0RC0RC_1RD0LF_1RE0LA_1LD0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76671: ~halts (TM_from_str "1RB1LD_1RC0RE_0LA---_1RE1LA_1RA0LF_0RD0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76672: ~halts (TM_from_str "1RB0LE_0RC0LC_1LD0RA_1LE---_1LF1LC_0LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76673: ~halts (TM_from_str "1RB0RB_1RC1RE_0LD---_1RA1LD_1LF0RF_0LB0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76674: ~halts (TM_from_str "1RB1RC_1RC1LA_1LD0RF_---0LE_0LD0LF_1RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76675: ~halts (TM_from_str "1RB1LE_1RC0LA_1RD0RA_1LB1RF_0LE0LD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 2 8 0). Time Qed.

Lemma nonhalt76676: ~halts (TM_from_str "1RB1LD_1RC0LA_0LB0RC_1LE1LA_1RF---_0RB1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76677: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD0RC_1LA0LC_1LD---_0RC1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76678: ~halts (TM_from_str "1RB1RE_1LC0RF_1RD1LB_---1RA_1LF0LD_1RD0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76679: ~halts (TM_from_str "1RB0LC_0LA0RB_1RA1LD_1LE1LC_1RF---_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76680: ~halts (TM_from_str "1RB1LB_1LC0RB_1LD0RB_0LE1LF_1RA0LA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76681: ~halts (TM_from_str "1RB0LF_1RC0RA_1RD1RB_0LE0RE_1LB0RF_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76682: ~halts (TM_from_str "1RB1RC_1RC0RF_1LD0RF_---0LE_0LD0LF_1RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76683: ~halts (TM_from_str "1RB0LF_1RC---_0RD1RD_1LE0RE_0RA0LC_0LA1LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76684: ~halts (TM_from_str "1RB1LF_1LC1RE_1LD0LC_1LA---_0RA0RE_1LF0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76685: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RB_1LA0LE_0RC1LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76686: ~halts (TM_from_str "1RB1RE_1LC0RA_0RD0LD_1LE0LF_1LA0LB_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 2 8 0). Time Qed.

Lemma nonhalt76687: ~halts (TM_from_str "1RB---_0RC0LC_1RD0LA_1LE0LF_1LB1LD_1LD0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76688: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD0RC_1LA0LC_1LD---_1LB1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76689: ~halts (TM_from_str "1RB0LF_1RC---_0RD0RC_0LE1LF_1LE0LA_1LB1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76690: ~halts (TM_from_str "1RB1LC_1LC0RA_1RE0LD_1LC0LB_---1RF_1RD1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76691: ~halts (TM_from_str "1RB0LD_1RC1RE_0LD---_1RF1LE_0RA1LA_0RD1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76692: ~halts (TM_from_str "1RB0LE_1LC0RC_0RA0LD_1LB1LA_1LF---_0RD0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76693: ~halts (TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RE0RF_1LC0RC_---1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76694: ~halts (TM_from_str "1RB1LB_1LC0RB_1LD0RB_0LE1LF_1RA0LA_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76695: ~halts (TM_from_str "1RB1LD_1LC1RE_---0RA_1LA0RF_1RD0RD_1RC0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 4 0). Time Qed.

Lemma nonhalt76696: ~halts (TM_from_str "1RB0RB_1LC0RA_1LA0LD_1LE---_0LF1RE_0LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 3 1 6 0). Time Qed.

Lemma nonhalt76697: ~halts (TM_from_str "1RB0RB_1LC0RA_1LA0LD_1LE---_0LF1RF_0LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 3 1 6 0). Time Qed.

Lemma nonhalt76698: ~halts (TM_from_str "1RB1LA_0LC0RD_1LA1RC_1RF0RE_1LE1LB_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76699: ~halts (TM_from_str "1RB0LE_1LC0LB_1RD0LB_0RA0RE_1RF---_0RC0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76700: ~halts (TM_from_str "1RB1RF_1LC0RD_0LA0LD_1RE0LC_1RB0RA_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76701: ~halts (TM_from_str "1RB0LC_1LC1RC_1RE1LD_1LE0LA_0RA1LF_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76702: ~halts (TM_from_str "1RB0LF_0RC0RB_0LD1LA_1LD1LE_0LA1RA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76703: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD1LE_0LA1RF_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76704: ~halts (TM_from_str "1RB0RF_1LC1RF_0LD0LB_1RE0RD_0RA0RD_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76705: ~halts (TM_from_str "1RB0LB_1RC0RE_1LD1RA_---0LA_0LA0RF_1RB0RC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 21 320 3 1 4 0). Time Qed.

Lemma nonhalt76706: ~halts (TM_from_str "1RB0RD_1LC1LE_1RD1LB_1RA1LD_1LF0RF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76707: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_0LA1RF_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76708: ~halts (TM_from_str "1RB---_1RC0RF_0RD0LE_1LC1RD_1RA0LC_1LD1RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 14 320 3 2 3 0). Time Qed.

Lemma nonhalt76709: ~halts (TM_from_str "1RB1LD_0RC0RA_1RD0LE_1LB1RF_0LA---_1RC0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76710: ~halts (TM_from_str "1RB---_0RC1RB_1RD0LE_0LC0RD_1RC1LF_1LA1LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76711: ~halts (TM_from_str "1RB0RF_1LC0RC_1RE0LD_1LC0LB_1RD1RA_---1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76712: ~halts (TM_from_str "1RB---_0RC1RC_1LD0RD_0RE0LB_1RA0LF_0LE1LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76713: ~halts (TM_from_str "1RB1RA_1LC0RF_0LB1LD_0LE0LD_1LA---_0RB0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76714: ~halts (TM_from_str "1RB0LA_1RC0RC_1LD0RA_1LA0LE_---0LF_1LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt76715: ~halts (TM_from_str "1RB---_1RC1RA_1RD0RF_1LE0RC_1RB0LF_0LD1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt76716: ~halts (TM_from_str "1RB0LC_0RC0RB_0RD1RC_1LE1LF_1RF---_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 3 2 8 0). Time Qed.

Lemma nonhalt76717: ~halts (TM_from_str "1RB0RF_1LC---_0LD0LC_0RE1RA_1RE1LD_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76718: ~halts (TM_from_str "1RB0RA_1RC0RD_1LB---_1RA1LE_0LD1LF_1LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt76719: ~halts (TM_from_str "1RB---_1RC0LF_1RD0LF_1RE0RA_1LF0RB_0LB1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76720: ~halts (TM_from_str "1RB1LF_1RC0RC_0RD0LA_1RE1RB_1LC---_1RD1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 1 16 0). Time Qed.

Lemma nonhalt76721: ~halts (TM_from_str "1RB0LA_1RC0LD_0RD0RC_1RE1LF_1LB---_1RF1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76722: ~halts (TM_from_str "1RB0RC_1LC0LD_0RD0LD_0LB1RE_0RF---_0RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76723: ~halts (TM_from_str "1RB1RD_1RC0LC_0LD0RA_1LB0RE_1RF---_0LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76724: ~halts (TM_from_str "1RB0LB_0RC1LB_1LD1RD_1LA1RE_---0RF_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76725: ~halts (TM_from_str "1RB0RE_0LC0LE_1LD1LC_1RA1LF_0RA0RD_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76726: ~halts (TM_from_str "1RB1LD_1LC---_0LD0LC_0RE1RA_1RE0RF_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76727: ~halts (TM_from_str "1RB0RA_1LC0RC_1RA1LD_0LC1LE_1LC0LF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 8 0). Time Qed.

Lemma nonhalt76728: ~halts (TM_from_str "1RB0RC_1RC0RF_1LD1RE_---0LE_1RB0LB_0LE0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76729: ~halts (TM_from_str "1RB---_1LC1LD_0LD1LB_1RE0LB_1RF1RD_0RA0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76730: ~halts (TM_from_str "1RB0LA_0RC0RB_0LD1LA_1LD1LE_1LF1RA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76731: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_0LA1RF_0RE0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76732: ~halts (TM_from_str "1RB0RD_1RC0LF_0LD0RA_1RC0LE_1LB1LE_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76733: ~halts (TM_from_str "1RB---_1RC0RC_0LD0RB_0RA1LE_0LF1LC_0LC0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76734: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD0LE_0RE0LF_1LA1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76735: ~halts (TM_from_str "1RB1RA_1LC1RF_1LE0LD_0LC0LB_0RA0RD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76736: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD0LE_1RA0LF_1LA1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76737: ~halts (TM_from_str "1RB1RE_1LC0RF_1RD1LB_---1RA_1LF1RB_1RD0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76738: ~halts (TM_from_str "1RB0RF_1LC0RC_1RE0LD_1LC0LB_1RD1RA_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76739: ~halts (TM_from_str "1RB0RB_1LC1RB_1LF0LD_1RD0RE_1RA1LE_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76740: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RB_1LA0LE_0RC0LF_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76741: ~halts (TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1RC_1RD0LE_0RC0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76742: ~halts (TM_from_str "1RB0LE_1LC0RF_0LD1LD_1RA0LB_0LA0RD_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76743: ~halts (TM_from_str "1RB0LF_1LC1RB_---1LD_1LA1RE_0RF0RD_0LD0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76744: ~halts (TM_from_str "1RB0LD_1RC0RF_1LD0RE_0LE1LA_1RA0LD_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76745: ~halts (TM_from_str "1RB1RE_1LC0RA_1LA0LD_0LB0LF_0RA1LB_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76746: ~halts (TM_from_str "1RB1LE_0LC1RD_1LC1LA_0RB0RD_0LA0LF_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 4 0). Time Qed.

Lemma nonhalt76747: ~halts (TM_from_str "1RB1LA_1RC0RD_0LA1RD_1RF0RE_1LF0LA_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76748: ~halts (TM_from_str "1RB1LD_0LC---_1RF0LD_1RE1LC_1LA0RD_0RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76749: ~halts (TM_from_str "1RB---_1RC0RD_1LD1RE_0LF0LC_0LE0RA_0RB0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76750: ~halts (TM_from_str "1RB0LE_1RC1RA_0LD0RE_1LA1LD_1RC0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76751: ~halts (TM_from_str "1RB1LA_1RC0RD_0LA1RD_0RF0RE_1LC0LA_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76752: ~halts (TM_from_str "1RB---_1LC0RB_1LD0LD_0RE1LE_1LA0LF_1RF1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 3 2 16 0). Time Qed.

Lemma nonhalt76753: ~halts (TM_from_str "1RB1RA_1LC0RA_1LF1LD_1RE0RF_---1LA_1RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76754: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD1RF_1LE0RF_1LA---_0LF1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 22 320 3 2 4 0). Time Qed.

Lemma nonhalt76755: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_1LD0LA_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76756: ~halts (TM_from_str "1RB1RC_1LC0RA_1RD0LB_---0RE_1LE0RF_0LE1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76757: ~halts (TM_from_str "1RB0LE_0LC1RF_1LA0RD_1RC0RB_0RB0LC_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76758: ~halts (TM_from_str "1RB0LF_1LC0RE_0RA1LD_1LE---_0LC0RA_1LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76759: ~halts (TM_from_str "1RB0RB_0LC1RD_1RA1LC_0RF0RE_1LB0LC_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76760: ~halts (TM_from_str "1RB1RA_1LC0RA_1LF1LD_1RE0RF_---1RA_1RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76761: ~halts (TM_from_str "1RB1RC_1RC0RD_1LD0LE_1LC1LA_1RF1LE_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76762: ~halts (TM_from_str "1RB1LA_1RC0RD_0LA1RD_1RF0RE_1LC0LA_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76763: ~halts (TM_from_str "1RB0LA_1RC0RA_1LD0RF_0LA0LE_0LA1LD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76764: ~halts (TM_from_str "1RB1LC_0LA0RC_1RD1LE_---1RA_0RF1LB_0LA0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76765: ~halts (TM_from_str "1RB0RB_0LC1RD_1RA1LC_1RF0RE_1LB0LC_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76766: ~halts (TM_from_str "1RB0RB_1LC1RB_1LF0LD_1RE1LD_0RD1RA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76767: ~halts (TM_from_str "1RB1LD_1LC0RF_1LE0RA_0LC---_1LA1LB_1RC1RB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76768: ~halts (TM_from_str "1RB1LC_1LA0RC_1RD1LE_---0RE_0RA0LF_1RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 2 8 0). Time Qed.

Lemma nonhalt76769: ~halts (TM_from_str "1RB0LE_1LC0RA_0RD1LB_1LA1RD_1LF0RA_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76770: ~halts (TM_from_str "1RB0LB_1LC0RF_1LE0LD_0LB0LF_1RF---_1RA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76771: ~halts (TM_from_str "1RB1LA_1LC0RC_---1RD_1RF0RE_1LE0LA_0RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76772: ~halts (TM_from_str "1RB0RF_0LC---_1RD1LC_1RE0RE_0LC1RA_1LB0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76773: ~halts (TM_from_str "1RB0RB_0LC1RD_1RA1LC_1RF0RE_1LF0LC_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 9 320 3 1 8 0). Time Qed.

Lemma nonhalt76774: ~halts (TM_from_str "1RB0RE_1RC1RF_0LD1LF_---1LE_1RF0LE_1RA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76775: ~halts (TM_from_str "1RB1LD_1RC0LA_1RD0LB_1LB0LE_1LF0RF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76776: ~halts (TM_from_str "1RB1LD_1LC0RA_1RF1LA_1RE0LA_0RC1RD_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76777: ~halts (TM_from_str "1RB0LA_1RC0LA_0RD1RF_1LE0RE_1LA1RA_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt76778: ~halts (TM_from_str "1RB0LF_0RC1RD_1LA0RB_0LE1RA_0LC1LD_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt76779: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD0RD_1LE1RE_1RA0LE_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76780: ~halts (TM_from_str "1RB0LF_0LC0LB_1RC0RD_1RE---_1LA0RA_0LE0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76781: ~halts (TM_from_str "1RB1LC_1LC1RF_1LC0LD_1LE0LD_1LA---_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76782: ~halts (TM_from_str "1RB---_1LC0RC_1RE0LD_0LB0RC_0LF0LE_1RF0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76783: ~halts (TM_from_str "1RB1RC_1LC1RF_1RE0LD_1LE1LC_1RA0LB_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76784: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1RF0LE_0RB0RF_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76785: ~halts (TM_from_str "1RB1LA_1LC0RE_1RD0LB_0LA1RC_1RF0LB_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 14 320 3 2 16 0). Time Qed.

Lemma nonhalt76786: ~halts (TM_from_str "1RB1LA_1RC0RF_1LD1RF_---1LE_1LC0LA_1RE0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76787: ~halts (TM_from_str "1RB0RD_1LC1LE_1LD1LB_1RA1LD_1LF0RF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76788: ~halts (TM_from_str "1RB0LC_1RC1RE_1LA0LD_1LA0RA_1RB1RF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76789: ~halts (TM_from_str "1RB0RA_0LC0RA_1RF1LD_1LE---_1LC0RF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76790: ~halts (TM_from_str "1RB0LA_0RC0RE_0RD1RD_1LA1RC_1LF---_1LF0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76791: ~halts (TM_from_str "1RB0RB_1LC1RB_1LF0LD_1RE1LD_1RE1RA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76792: ~halts (TM_from_str "1RB0RC_1LC0LF_0RE0LD_1LB0LA_---1RA_0LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 15 320 3 2 16 0). Time Qed.

Lemma nonhalt76793: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA1LD_1LE1RF_0RA1RD_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76794: ~halts (TM_from_str "1RB1RC_0LA0LF_1RD---_0RE0LE_1RF0RA_1LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76795: ~halts (TM_from_str "1RB0LE_0RC1RD_1LA0RA_1RC1RE_0LA0RF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76796: ~halts (TM_from_str "1RB1LA_1RC0RC_1LD0RE_---1LE_1RF0LA_0RA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76797: ~halts (TM_from_str "1RB0LA_1RC0LE_1RD0RA_1RE1RB_0LF1LB_---1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76798: ~halts (TM_from_str "1RB1RF_1RC1RA_1LD0LE_1RB0LC_1LD0RD_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76799: ~halts (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_0RA1LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76800: ~halts (TM_from_str "1RB1RE_0LC0RC_1LE0RD_1LB---_1RA0RF_1RE0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76801: ~halts (TM_from_str "1RB1RC_1LA1RD_1LF0RD_1LE1RA_1LC---_0RD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76802: ~halts (TM_from_str "1RB0RF_1LC0RA_1RD0LC_0RE0LA_0LB1RA_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt76803: ~halts (TM_from_str "1RB---_1RC0RF_1LD0RA_0LF0LE_0LF1LD_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76804: ~halts (TM_from_str "1RB1LB_1LC0RB_1LD1RA_0LE1LF_1RA0LA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76805: ~halts (TM_from_str "1RB0LB_1RC1RD_1RD0RA_1LE0RA_---0LF_0LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76806: ~halts (TM_from_str "1RB---_1RC0LD_0LD0RC_1RA1LE_1LF1LB_0LD1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76807: ~halts (TM_from_str "1RB1LB_1LC0RB_1LD1RA_0LE1LF_1RA0LA_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76808: ~halts (TM_from_str "1RB1RC_1LC0RE_---1LD_1RB0LD_0RD1RF_1RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76809: ~halts (TM_from_str "1RB1LE_0LC1LF_1LD0RC_1RE0LB_---1RC_1LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76810: ~halts (TM_from_str "1RB0LE_1RC0LE_1RD0RF_1LE0RA_0LA1LB_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76811: ~halts (TM_from_str "1RB0LA_1RC1LE_0RD1RF_1LE0RE_1LA1RA_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76812: ~halts (TM_from_str "1RB0RF_0RC---_1LD1RF_1LE0RE_1RA0LC_0RE0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76813: ~halts (TM_from_str "1RB1RE_0RC1RC_1LD1RA_1LE---_1LF0RC_0RC0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76814: ~halts (TM_from_str "1RB1RE_0LC0RA_0LD1LC_1LA1LE_1RF0LB_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76815: ~halts (TM_from_str "1RB1LE_1RC0RB_1LD0RE_1LF0LE_1LA0LC_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76816: ~halts (TM_from_str "1RB0LA_1RC1LE_0RD1RF_1LE0RE_1LA1RA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76817: ~halts (TM_from_str "1RB1LC_1LC1RE_1LA0LD_0LC0LB_0RA0RF_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 6 320 3 2 6 0). Time Qed.

Lemma nonhalt76818: ~halts (TM_from_str "1RB0RB_1LC0RF_1RC0LD_0LC1RE_0RA---_1RE1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76819: ~halts (TM_from_str "1RB0LA_1RC0RA_1LD1RF_0LA0LE_0LA1LD_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76820: ~halts (TM_from_str "1RB1RE_1LC1LE_0RD0LB_0RA1RD_1LF0RC_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76821: ~halts (TM_from_str "1RB0LD_0RC0RE_1RD0LE_1LA0LD_1RF---_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76822: ~halts (TM_from_str "1RB1LF_0LC1LA_1LE0RD_1RC1RA_1LD0LB_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76823: ~halts (TM_from_str "1RB0RD_1LC1LE_0LC1RA_0RB1LA_1LF0RA_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 3 2 4 0). Time Qed.

Lemma nonhalt76824: ~halts (TM_from_str "1RB1RE_1LC0RA_1LA0LD_0LB1LE_1RD1LF_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76825: ~halts (TM_from_str "1RB0LD_1RC0RF_0RD---_1LE1RF_1LA0RA_0RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76826: ~halts (TM_from_str "1RB0LF_0LC1LE_1RD1LB_0RE0RC_0LA0RC_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76827: ~halts (TM_from_str "1RB0LA_1RC0LA_0RD1RF_1LE0RE_1LA1RA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76828: ~halts (TM_from_str "1RB0LC_1RC0RE_1LD0RC_1LA0LA_---0RF_1RC0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76829: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD0RD_1LE1RE_1RA0LE_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 6 0). Time Qed.

Lemma nonhalt76830: ~halts (TM_from_str "1RB0LB_1RC1RD_1LC0RB_1LE0LC_0LA1LF_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76831: ~halts (TM_from_str "1RB---_0RC0LC_1RD0RF_1LE0LD_0LF0LD_1RE1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt76832: ~halts (TM_from_str "1RB1LB_0LC0LA_1RD0LC_1RE0RC_1LB1RF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76833: ~halts (TM_from_str "1RB1LB_1RC1LA_1RD0RE_1LB0RF_---0LB_1LE1RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76834: ~halts (TM_from_str "1RB1LD_1LC1RA_1LE1RD_---0RB_0LA0LF_1LC0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt76835: ~halts (TM_from_str "1RB0RD_1LC0LB_0LD0LB_1RC1RE_1RF---_0RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76836: ~halts (TM_from_str "1RB0LA_1RC0RA_1LD0RF_0LA0LE_1RD1LD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76837: ~halts (TM_from_str "1RB1RC_1RC1RD_1LD0RF_---1LE_1RC0LE_0RE1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76838: ~halts (TM_from_str "1RB0LA_1LC0RD_---1LA_0RA1RE_1RF1RB_1RB1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76839: ~halts (TM_from_str "1RB0LB_1LC0RE_0LA1LD_1LA1LE_0RB0LF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76840: ~halts (TM_from_str "1RB---_1RC0RD_1LD1RE_0LF0LC_0LE0RA_0RB0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76841: ~halts (TM_from_str "1RB0LA_0RC0RB_1LC0LD_0LE1LB_1RF1LF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76842: ~halts (TM_from_str "1RB0LF_0RC---_1RD0RD_1LE0RA_0LA1LC_0LC1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76843: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE1LB_1RF0LA_0RE1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76844: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE0LD_1RF0LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76845: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE0LD_1RF0LA_0RE0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76846: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE0LD_1RF0LA_0RF1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76847: ~halts (TM_from_str "1RB0RA_1LB0LC_1LD0RF_0LE0LD_1RE0RA_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76848: ~halts (TM_from_str "1RB0LC_0RC---_1RD---_0RE0RD_1LE0LF_0LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76849: ~halts (TM_from_str "1RB0LF_0RC---_1RD0RD_1LE0RA_0LA1LC_0LC0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76850: ~halts (TM_from_str "1RB0LC_0RC1LF_1RD---_0RE0RD_1LE1RB_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76851: ~halts (TM_from_str "1RB---_0RC0RB_1LC0RD_1RE1LE_0LF0RA_1LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76852: ~halts (TM_from_str "1RB1RF_0RC0RB_1LC0LD_0LE0LD_1LF0LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76853: ~halts (TM_from_str "1RB---_1RC0RB_1LD0RA_1RE0LC_0RE0LF_1RA0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76854: ~halts (TM_from_str "1RB1LD_0RC0RB_1LC0RA_0LE---_1LF0LE_1RC1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76855: ~halts (TM_from_str "1RB0RA_0RC0RB_1LC0RD_1RA1LE_0LF---_1LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76856: ~halts (TM_from_str "1RB0LF_0RC0RB_1LC0LD_1LE1LB_1RE0RA_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76857: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE1LB_1RF0LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76858: ~halts (TM_from_str "1RB1RF_0RC0RB_1LC0LD_0LE1LB_1LF0LA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76859: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD1LA_1RC0LD_0RF1RE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76860: ~halts (TM_from_str "1RB1LB_0RC---_1RD0LC_0RE0RD_1LE0LF_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76861: ~halts (TM_from_str "1RB0RC_0LC---_1LD1LB_0LE0LD_1RE0RF_0RA1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76862: ~halts (TM_from_str "1RB0RE_1LC0LD_1RD1LA_1RC0LB_0RF1RE_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76863: ~halts (TM_from_str "1RB0RC_0LC---_1LD1LB_0LE0LD_1RE0RF_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76864: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE1LB_1RF0LA_0RE0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76865: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_0LE1LB_1RF0LA_0RF1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 3 0). Time Qed.

Lemma nonhalt76866: ~halts (TM_from_str "1RB0RE_1LC0RA_1RE0LD_0RE0LB_0LB1RF_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76867: ~halts (TM_from_str "1RB1LB_0LC0LA_1RD0LC_1RE0RC_1LB0RF_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76868: ~halts (TM_from_str "1RB0LA_1RC0RA_1LD1RF_0LA0LE_1RD1LD_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76869: ~halts (TM_from_str "1RB0RD_1LC1LE_1RA0LB_0RC0RF_0LB1RC_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76870: ~halts (TM_from_str "1RB0LE_1LC0LF_1LD1LB_0RA0LA_1RD---_1LB0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76871: ~halts (TM_from_str "1RB0LF_0RC1LD_0RD1RC_1LE0LF_1LB---_1RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 21 320 3 1 16 0). Time Qed.

Lemma nonhalt76872: ~halts (TM_from_str "1RB1LE_0RC0RF_1LD0RC_1LA0LC_0RD---_0RC1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76873: ~halts (TM_from_str "1RB1LE_0RC0RF_1LD0RC_1LA0LC_0RD---_1LB1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76874: ~halts (TM_from_str "1RB0RF_1RC1RA_0LD0RD_1LA0RE_1LC---_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76875: ~halts (TM_from_str "1RB1LE_1RC0RE_1RD---_1LA0LD_0RB0LF_1RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76876: ~halts (TM_from_str "1RB0LA_1LC---_1LF0LD_1RD0RE_0RC0RF_1LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76877: ~halts (TM_from_str "1RB0LC_1RC---_1LD1LE_1LF0LC_0LA0RE_0LE0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76878: ~halts (TM_from_str "1RB0RB_0LC0RA_1LA1LD_1LE0LF_1LC0LD_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76879: ~halts (TM_from_str "1RB0LA_1LC---_1LC0LD_1RD0RE_0RC0RF_1LF1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76880: ~halts (TM_from_str "1RB1RD_1RC0RA_0RD0RF_0RE0LD_1LF0RA_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76881: ~halts (TM_from_str "1RB0LC_1RC1LE_1LA1LD_0LA0RD_---1LF_0LD0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76882: ~halts (TM_from_str "1RB1RD_1LC0LC_0RA0LB_1RE0RF_1RA0RD_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76883: ~halts (TM_from_str "1RB0RF_0RC0RE_0RD0LC_1LE0RF_1LF---_1RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76884: ~halts (TM_from_str "1RB0LA_1LB0LC_1RC0RD_0RB0RE_1LE1RF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76885: ~halts (TM_from_str "1RB1RD_1LC0LC_0RA0LB_1RE1RF_1RA0RD_0LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76886: ~halts (TM_from_str "1RB0RB_0LC0RA_1LA1LD_1LE1LF_1LC0LD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76887: ~halts (TM_from_str "1RB---_1RC0RF_1RD1RF_1LE0LE_0RC0LD_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76888: ~halts (TM_from_str "1RB0LA_1LB0LC_1RD0RE_1RC---_0RB0RF_1LF1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76889: ~halts (TM_from_str "1RB0RE_1RC1RE_1LD0LD_0RB0LC_1RA1RF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76890: ~halts (TM_from_str "1RB1RF_1LC0RA_1LA1RD_---1RE_0RF0RC_0RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76891: ~halts (TM_from_str "1RB0RE_1RC1RE_1LD0LD_0RB0LC_1RA0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76892: ~halts (TM_from_str "1RB1RF_1RC0RA_1RD1RA_1LE0LE_0RC0LD_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76893: ~halts (TM_from_str "1RB0RF_1RC0RA_1RD1RA_1LE0LE_0RC0LD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76894: ~halts (TM_from_str "1RB0RA_1LC0LE_0RD0LD_0LB1RA_---1LF_1LF1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 2 6 0). Time Qed.

Lemma nonhalt76895: ~halts (TM_from_str "1RB1LE_1RC0RD_1RD0RA_1LD1RA_0LF1LA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76896: ~halts (TM_from_str "1RB---_1LC1LD_1LF0RD_0RF1RE_1RC1RB_1LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76897: ~halts (TM_from_str "1RB0LF_1RC0RE_1LD---_1LA1LE_1RA1RF_0LB1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76898: ~halts (TM_from_str "1RB0LE_1RC0RD_1LD---_1RA1RE_0LB1LF_1LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76899: ~halts (TM_from_str "1RB0RC_1LC1RF_1LD1RA_0LE0LF_---1LF_0LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76900: ~halts (TM_from_str "1RB0LD_1RC0RF_1LD---_0LB1LE_1LA1LF_1RA1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76901: ~halts (TM_from_str "1RB0LD_1RC1RF_1LD---_1LE1LD_0RB1LA_1RA0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76902: ~halts (TM_from_str "1RB0RC_0RC1RF_1LD1RA_0LE0LF_---1LF_0LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76903: ~halts (TM_from_str "1RB0LA_0RC0RE_1LD0RF_0LE1LE_0LC1RA_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76904: ~halts (TM_from_str "1RB0LA_0RC1LE_1RD1RF_1LE0LB_1RA1LA_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76905: ~halts (TM_from_str "1RB1LE_1LB0RC_0RF1RD_0RB1LA_0LF---_1LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76906: ~halts (TM_from_str "1RB0RC_0RC0LC_1LD1RE_1LB0LF_0RA1RC_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76907: ~halts (TM_from_str "1RB0LA_0RC0RE_1LD0RF_0LE0LA_0LC1RA_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76908: ~halts (TM_from_str "1RB1LE_1RC0LF_1RD0RB_0LA1LF_---0LB_1RB1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76909: ~halts (TM_from_str "1RB1RC_1LB0RA_1LD1RA_---0LE_1LF1LD_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76910: ~halts (TM_from_str "1RB1LE_1RC0RD_1RD0RA_1LE1RA_0LF1LA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76911: ~halts (TM_from_str "1RB---_1RC0RF_1LD0RA_0LF0LE_1RD1LD_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76912: ~halts (TM_from_str "1RB---_1RC1RE_1LD0RF_1LA0LE_1LC1LF_0RD1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76913: ~halts (TM_from_str "1RB1LF_1RC0RE_1RD0RA_1LE0LA_---1RA_0LD1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76914: ~halts (TM_from_str "1RB1LC_0RC0LC_1LD1RE_1LB0LA_0RF1RC_---0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76915: ~halts (TM_from_str "1RB1LC_0LC1RF_1RE1RD_0RB0LD_1LA0RC_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76916: ~halts (TM_from_str "1RB---_0RC1RF_1LD1RA_0LE0LF_0RA1LF_0LD0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76917: ~halts (TM_from_str "1RB0LB_1LC0RF_1LE0LD_0LB0LF_0LF---_1RA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76918: ~halts (TM_from_str "1RB1LE_1LC0RD_---1LA_1RE1RD_0LA0LF_0RA1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 1 6 0). Time Qed.

Lemma nonhalt76919: ~halts (TM_from_str "1RB0RA_1RC0LB_1RD---_0RE1RF_1LE0LB_1RF1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76920: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1LC_1LD1LE_0LF---_1LB0LE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76921: ~halts (TM_from_str "1RB---_0RC1RE_1LC0LD_1RA0LD_1RE1RF_1RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76922: ~halts (TM_from_str "1RB1RA_1LC1RD_1LA0LC_1RD1RE_0RF---_1RC0RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76923: ~halts (TM_from_str "1RB1RF_0RC0RB_1LD1LE_1RD0LC_1RF1LC_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 16 0). Time Qed.

Lemma nonhalt76924: ~halts (TM_from_str "1RB0LA_1LC1RE_0LD1LB_1LA---_0RF0RE_1LF0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 5 320 3 2 3 0). Time Qed.

Lemma nonhalt76925: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD---_1LF1RE_0RA0RD_1LA0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76926: ~halts (TM_from_str "1RB0RD_1LC---_1LE1RD_0RF0RC_1LF0RF_1RA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 1 4 0). Time Qed.

Lemma nonhalt76927: ~halts (TM_from_str "1RB0RE_1LC0RB_1LD0LD_1RA0LB_---0RF_1RB0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76928: ~halts (TM_from_str "1RB1LC_1RC0LA_1RD1RE_1LB0RE_0RB0LF_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 2 12 0). Time Qed.

Lemma nonhalt76929: ~halts (TM_from_str "1RB0LA_1LC0RD_---1LA_0RA1RE_1RF1RB_1LD1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76930: ~halts (TM_from_str "1RB1LB_1RC0RD_1LD1RE_0LD0LA_0RC1RF_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 1 8 0). Time Qed.

Lemma nonhalt76931: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LF_1RA0LA_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 15 320 3 1 3 0). Time Qed.

Lemma nonhalt76932: ~halts (TM_from_str "1RB0LB_1RC1RD_1RD1LB_1LE0RA_---0LF_0LE0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76933: ~halts (TM_from_str "1RB0LA_1RC1RE_1LD0LE_---1LA_1LC1RF_0RE0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt76934: ~halts (TM_from_str "1RB---_0RC0LD_0LD1RA_1LE0RF_1RC0LB_1RD0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76935: ~halts (TM_from_str "1RB0RF_1RC0RE_0RD0RB_1LE0RA_0LA0LE_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76936: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0LF_1LE0LB_0LA0LD_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76937: ~halts (TM_from_str "1RB0RD_0RC0RA_1LD0RE_0LE0LD_1RA0RF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76938: ~halts (TM_from_str "1RB0RB_1LC1RD_1RE0LD_0LE1LF_1LB0RA_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76939: ~halts (TM_from_str "1RB0RB_1LC0RF_1RE0LD_0LE---_1LB0RA_1RB1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76940: ~halts (TM_from_str "1RB0LD_1LC0RF_1LA1RD_0LB1LE_---0LB_1RC0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76941: ~halts (TM_from_str "1RB0LD_1LC1RA_0RD1LA_1RE1LE_1RF0LC_---0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76942: ~halts (TM_from_str "1RB0LD_1RC1LE_1LA0RE_1LB0LB_0RA1RF_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76943: ~halts (TM_from_str "1RB0RE_1RC0RA_0LC1LD_1RE0LB_1LC0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 4 0). Time Qed.

Lemma nonhalt76944: ~halts (TM_from_str "1RB0LC_1RC0RA_1LD1LF_1RE0LA_1RB1LE_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 1 4 0). Time Qed.

Lemma nonhalt76945: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD1LF_1LA0LE_1RB0LC_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 1 4 0). Time Qed.

Lemma nonhalt76946: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD1LF_1RA0LE_1RB0LC_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 1 4 0). Time Qed.

Lemma nonhalt76947: ~halts (TM_from_str "1RB0LC_1RC0RA_1LD1LF_1LE0LA_1RB1LE_---0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 1 4 0). Time Qed.

Lemma nonhalt76948: ~halts (TM_from_str "1RB0RD_1LC1LE_0RF0LD_1RE1LD_1RA0LB_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76949: ~halts (TM_from_str "1RB0LC_0LC1RF_1LE0LD_1LC0RE_1RD0RA_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 22 320 3 2 4 0). Time Qed.

Lemma nonhalt76950: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD0RF_1LA1LC_---1RA_1RD0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76951: ~halts (TM_from_str "1RB0RA_0RC0RE_1LD---_0LE1LF_1RA1LD_1LE0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt76952: ~halts (TM_from_str "1RB0LD_1RC0RE_1LA0RA_0LC0LD_1RF0RA_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 1 8 0). Time Qed.

Lemma nonhalt76953: ~halts (TM_from_str "1RB---_0LC0RE_1LA1LD_1LB0LB_1LD1RF_1LC1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 2 6 0). Time Qed.

Lemma nonhalt76954: ~halts (TM_from_str "1RB0LD_1RC0LF_1LA0RE_1LB0LB_0RA---_1LB1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76955: ~halts (TM_from_str "1RB1RD_1LC1RE_0RF1RA_1LE0RC_---1LF_1RD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 8 0). Time Qed.

Lemma nonhalt76956: ~halts (TM_from_str "1RB0LE_1LC0RF_1LA0RD_1RC1LE_0LB---_1RC0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76957: ~halts (TM_from_str "1RB1LD_1LC0RA_1RE0LD_0LE---_1LB0RF_1RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 6 0). Time Qed.

Lemma nonhalt76958: ~halts (TM_from_str "1RB0LA_0RC1LF_1RD1RE_1LE0LB_---0RF_1RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 1 2 0). Time Qed.

Lemma nonhalt76959: ~halts (TM_from_str "1RB1RC_0RC1RF_1LD0RF_1LE---_1RA0LE_0LF1RE") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 22 320 3 1 4 0). Time Qed.

Lemma nonhalt76960: ~halts (TM_from_str "1RB1LD_1RC1LE_0RD0RF_1LA1RE_---0LA_1RB0RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt76961: ~halts (TM_from_str "1RB0LF_1RC---_0RD0LE_1LC1RE_0LF0RB_0LA1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 2 6 0). Time Qed.

Lemma nonhalt76962: ~halts (TM_from_str "1RB---_0RC1RD_0LD0RF_1LE1RA_1RF0LE_1RC1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76963: ~halts (TM_from_str "1RB---_0RC0RB_0RD1LD_1LE1LA_0LF0LE_1LC1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 2 6 0). Time Qed.

Lemma nonhalt76964: ~halts (TM_from_str "1RB0LE_1LC0RD_1LA1LC_0RB1RB_0LC0LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 2 4 0). Time Qed.

Lemma nonhalt76965: ~halts (TM_from_str "1RB0LD_1RC0RD_1LA0RE_0LA1LA_0RB0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 2 4 0). Time Qed.

Lemma nonhalt76966: ~halts (TM_from_str "1RB0LB_1LC0RF_0LD1LC_1RE0LC_1RA---_0RC0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt76967: ~halts (TM_from_str "1RB1RA_1LC0RE_1RA0LD_0LC1LC_0RA0RF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 2 4 0). Time Qed.

Lemma nonhalt76968: ~halts (TM_from_str "1RB0LE_1LC0RD_1LA0LD_0RB1RB_0LC0LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 2 4 0). Time Qed.

Lemma nonhalt76969: ~halts (TM_from_str "1RB0RE_1LC0LA_1RA0LD_0LC0LB_1RC0RF_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt76970: ~halts (TM_from_str "1RB0LE_1LC---_1LF1RD_1LD0RE_0RD0LB_0LA0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76971: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_1RA---_1RE0LF_0LE0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76972: ~halts (TM_from_str "1RB---_1RC0LC_1LD0RF_0LE1LD_1RA0LD_0RD0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt76973: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA0RE_0LA1LA_0RB0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 2 4 0). Time Qed.

Lemma nonhalt76974: ~halts (TM_from_str "1RB0RD_1LC0RE_1RA0LD_0LC1LC_0RA0RF_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 5 320 3 2 4 0). Time Qed.

Lemma nonhalt76975: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_0LC1RF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76976: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RE_0RA1LC_0RF0LD_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76977: ~halts (TM_from_str "1RB1RA_1LC0RB_0LD1LD_0LE1LF_0RA1LB_1LE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt76978: ~halts (TM_from_str "1RB---_1RC0RA_1RD0LF_1RE0RB_1LC0LD_0LC0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt76979: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_0RB1LF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76980: ~halts (TM_from_str "1RB---_1RC1LE_0RD0RB_1LA0RF_1RE0LF_0LE0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt76981: ~halts (TM_from_str "1RB0LA_0RC1LD_0RD1RC_1LE0LF_1LB---_1RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76982: ~halts (TM_from_str "1RB0LD_0LC1RA_1LF0RD_0LE0RB_1LA---_0LA1LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76983: ~halts (TM_from_str "1RB1RE_0RC0RB_1RD1LF_0LA1RA_1LF---_0LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76984: ~halts (TM_from_str "1RB1LE_1LC0RB_1LD1LD_0RA0LC_1LF---_0LD1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76985: ~halts (TM_from_str "1RB0RF_1RC0LE_1RD0RA_1LB0LC_0LB0LD_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt76986: ~halts (TM_from_str "1RB1RB_0LC0RA_1LF1RD_1RE---_0RB1RC_1RA0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76987: ~halts (TM_from_str "1RB0LE_1LC1RA_1RF1LD_1LA0LA_1LF0RA_---0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76988: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1RE0RC_---0RF_0RB0RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76989: ~halts (TM_from_str "1RB1LD_0RC1RE_1RD1RD_1LA1RF_---0RF_0RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76990: ~halts (TM_from_str "1RB1RF_1RC1RA_1LD0LE_1RB0LC_1LD0RA_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76991: ~halts (TM_from_str "1RB0LE_1RC---_1LD0RC_1LF1LA_0RE1LC_0LA1LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76992: ~halts (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RF0RE_0RB0LE_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 17 320 3 1 1 0). Time Qed.

Lemma nonhalt76993: ~halts (TM_from_str "1RB0LC_1RC1RE_1LA0LD_1LA0RE_1RB1RF_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 18 320 3 1 16 0). Time Qed.

Lemma nonhalt76994: ~halts (TM_from_str "1RB0LF_1LC0RF_---0LD_1LE1LA_0RA0LB_1RA1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76995: ~halts (TM_from_str "1RB0LA_1RC1RC_0LD0RB_1LA1RE_1RF---_0RC1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76996: ~halts (TM_from_str "1RB---_1LC0RE_0RD1LB_1RF0LE_0RA0LC_0RB1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76997: ~halts (TM_from_str "1RB0RE_1RC---_0LD1RA_0LA1LD_1LF0RF_1LC0RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 16 320 3 1 4 0). Time Qed.

Lemma nonhalt76998: ~halts (TM_from_str "1RB0LA_1RC0RB_0RD1RA_1LE1RB_0LF1LC_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt76999: ~halts (TM_from_str "1RB1LC_0LA1LE_1RD1LF_1LB1RC_---0LF_0LB0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt77000: ~halts (TM_from_str "1RB0RC_0RC0LE_1RD1RA_1LB1LC_1LF0LE_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt77001: ~halts (TM_from_str "1RB1LD_0RC1RE_1LB1RD_1LA1RF_---0RF_0RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 20 320 3 2 6 0). Time Qed.

Lemma nonhalt77002: ~halts (TM_from_str "1RB0LA_0RC0LE_0LD1RE_1LA0RE_1RD0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt77003: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA1LE_0RE0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 3 1 3 0). Time Qed.

Lemma nonhalt77004: ~halts (TM_from_str "1RB0LC_1RC1RB_0LD0RB_---1LE_1LA0LF_0LB1LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 3 1 3 0). Time Qed.

Lemma nonhalt77005: ~halts (TM_from_str "1RB0RF_1LC1RA_1RD0LC_1LE0RB_0LB0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 1 8 0). Time Qed.

Lemma nonhalt77006: ~halts (TM_from_str "1RB---_1LC1RF_1RD0LC_1LE0RB_0LB0LE_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 1 8 0). Time Qed.

Lemma nonhalt77007: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA0RF_---0LE_1LF0RC_0LA1LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 1 8 0). Time Qed.

Lemma nonhalt77008: ~halts (TM_from_str "1RB---_1RC0LD_0RD0RC_1RE1LF_1LB0RE_1LD1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 1 8 0). Time Qed.

Lemma nonhalt77009: ~halts (TM_from_str "1RB0LA_1RC---_0LD1RF_0RE0RD_1LE0LA_0RA1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 3 1 8 0). Time Qed.

Lemma nonhalt77010: ~halts (TM_from_str "1RB1RC_0LA1LF_1RD0RB_1RE0RA_0LF---_0LB1LB") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 3 0). Time Qed.

Lemma nonhalt77011: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LB_1LA0LB_1RF1RA_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 8 320 3 1 3 0). Time Qed.

Lemma nonhalt77012: ~halts (TM_from_str "1RB0LB_1LC0LB_1RD0LB_0RA1RE_0RF---_0RD1RC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 12 320 3 1 16 0). Time Qed.

Lemma nonhalt77013: ~halts (TM_from_str "1RB0RD_0LC1RA_---1LA_1LE1RD_0LA0LF_0RE0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 10 320 3 2 6 0). Time Qed.

Lemma nonhalt77014: ~halts (TM_from_str "1RB0RF_1RC0RD_1LD1LB_1RE0LC_0LA0RA_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 2 8 0). Time Qed.

Lemma nonhalt77015: ~halts (TM_from_str "1RB1LE_0LC1RD_1LC1LA_0RB0RD_0LF0LE_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 1 6 2 0). Time Qed.

Lemma nonhalt77016: ~halts (TM_from_str "1RB0RF_1LC---_0RE1LD_0LC0LD_1RE1RA_1RA0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 1 6 2 0). Time Qed.

Lemma nonhalt77017: ~halts (TM_from_str "1RB0RB_1RC0RA_1LD---_0RF1LE_0LD0LE_1RF1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 1 6 2 0). Time Qed.

Lemma nonhalt77018: ~halts (TM_from_str "1RB0RA_1RC0RA_1LD---_0RF1LE_0LD0LE_1RF1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 1 6 2 0). Time Qed.

Lemma nonhalt77019: ~halts (TM_from_str "1RB0RF_1LC---_0RE1LD_0LC0LD_1RE1RA_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 1 6 2 0). Time Qed.

Lemma nonhalt77020: ~halts (TM_from_str "1RB0RB_1LC1LF_0RE1LD_0LC0LD_1RE1RA_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77021: ~halts (TM_from_str "1RB0RF_1LC---_0RE1LD_0LC0LD_1RE1RA_1LC0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77022: ~halts (TM_from_str "1RB0LF_1RC---_0RD0RC_0LE1LF_1LE1RD_1LB0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77023: ~halts (TM_from_str "1RB0LB_1RC1LD_1LA---_1RD1RE_1RF0LE_0RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77024: ~halts (TM_from_str "1RB0LD_0LC1RE_1LC1LD_1LA0LA_---0RF_0RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77025: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_0LA1RF_1RD0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77026: ~halts (TM_from_str "1RB0RF_1LC---_0RE1LD_0LC0LD_1RE1RA_1LC0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77027: ~halts (TM_from_str "1RB1RF_0LC1RE_1LC1LD_1LA0LA_0RB0RE_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77028: ~halts (TM_from_str "1RB---_0RC1LC_0RD0LA_0RE0LB_1LE0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77029: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LE_1LD1RC_1LA0LF_1RA0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77030: ~halts (TM_from_str "1RB0RA_1LC---_0LD0LC_0RE1RA_1RE0RF_0LF0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77031: ~halts (TM_from_str "1RB0RF_1LC---_0LD0LC_0RE1RA_1RE0RF_0LF0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77032: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD0LE_1RA0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77033: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD0LE_1RA0LF_1LA0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77034: ~halts (TM_from_str "1RB0LA_0LC1RE_1LC1LD_1LA0LA_---0RF_0RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77035: ~halts (TM_from_str "1RB0RA_1LC---_0LD0LC_0RE1RA_1RE0RF_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77036: ~halts (TM_from_str "1RB0LF_1RC---_0RD0RC_0LE1LF_1LE0LA_1LB0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77037: ~halts (TM_from_str "1RB0LA_1LB1LC_0LD1RA_1RE---_0RF0RE_0LB1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77038: ~halts (TM_from_str "1RB0RD_1LC0RB_0LD0LC_1LE1RF_1RA---_1LF1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77039: ~halts (TM_from_str "1RB0LC_0RC0RB_1LC1LD_1LE1RA_1LF---_1RF0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77040: ~halts (TM_from_str "1RB1LC_0LC---_1LD0RC_0LE0LD_0RF1RC_1RF1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77041: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD0LE_0RE0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77042: ~halts (TM_from_str "1RB1LA_0RC0RB_1LC1RD_1LA1LE_1LF0LE_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77043: ~halts (TM_from_str "1RB0LF_1RC---_0RD0RC_0LE1LF_1LE0LA_1LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77044: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_0RF0LF_0LA0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77045: ~halts (TM_from_str "1RB1LD_1LC---_0LD0LC_0RE1RA_1RE0RF_0LF0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77046: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD0LE_0RE0LF_1LA0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77047: ~halts (TM_from_str "1RB---_0RC0RB_1LC1RD_1LF1LE_1LF0LE_0LA1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77048: ~halts (TM_from_str "1RB0RF_1LC---_0LD0LC_0RE1RA_1RE0RF_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77049: ~halts (TM_from_str "1RB0RF_1LC---_0LD0LC_0RE1RA_1RE1LD_0LF0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77050: ~halts (TM_from_str "1RB---_1LC0RD_0LD0LC_1LA1RE_1LE1LF_1LC0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77051: ~halts (TM_from_str "1RB0LE_0RC0RB_1LC1RD_1LD1LA_1LF0LE_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 3 4 0). Time Qed.

Lemma nonhalt77052: ~halts (TM_from_str "1RB1LE_0RC0RB_1RD0RF_0LA---_0LE1RA_1LF1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 1 5 4 0). Time Qed.

Lemma nonhalt77053: ~halts (TM_from_str "1RB0LF_0RC0RB_1LC0LD_1LE0LD_1RE0RA_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77054: ~halts (TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_1LE0LD_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 3 4 0). Time Qed.

Lemma nonhalt77055: ~halts (TM_from_str "1RB0LE_0RC1RE_0RD0RE_1LA---_0LF1RA_0RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77056: ~halts (TM_from_str "1RB0RA_0RC0RB_1LC0LD_1LE0LD_1RA0LF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77057: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_1RA1LE_1LF1RC_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77058: ~halts (TM_from_str "1RB0LE_0RC1RE_0RD0RE_1LE---_0LF1RA_0RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77059: ~halts (TM_from_str "1RB1LB_1LC---_1RD0RA_0LE0LD_1RE0RF_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77060: ~halts (TM_from_str "1RB1LB_0RC---_1RD0LC_0RE0RD_1LE0LF_0LA1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77061: ~halts (TM_from_str "1RB---_0LC1RD_0RD1LC_1RE0LB_0RF1RB_1RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77062: ~halts (TM_from_str "1RB---_1LC1RF_1RE0RD_1RD1LB_0LD0LE_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77063: ~halts (TM_from_str "1RB0LE_0RC1RE_1RD0RE_1RE---_0LF1RA_0RA1LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77064: ~halts (TM_from_str "1RB0RF_1LC1RA_1RE0LD_0LB0LC_0RA0RB_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77065: ~halts (TM_from_str "1RB1LE_1RC---_0RD0RC_1LD0LA_1LF1RD_0LB0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77066: ~halts (TM_from_str "1RB0LB_1RC0LE_0RD---_1RE0LA_1RF0LA_1LA0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77067: ~halts (TM_from_str "1RB0LA_0RC0RB_1LC0LD_0LE0LD_1RF1LF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77068: ~halts (TM_from_str "1RB0LD_1LC0RC_1LE0RD_1LA0RB_0LF---_1LD0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77069: ~halts (TM_from_str "1RB---_1LC1LB_1RD0RB_0LE0LD_1RE0RF_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77070: ~halts (TM_from_str "1RB---_1LC1LB_1RE0LD_0LC0LF_0RC1RF_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 6 3 0). Time Qed.

Lemma nonhalt77071: ~halts (TM_from_str "1RB0LA_0RC0RB_0LD1LF_0LE1RA_0RA1LD_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 6 4 0). Time Qed.

Lemma nonhalt77072: ~halts (TM_from_str "1RB1LE_0RC1RA_1RD---_1LA0RD_0LF0LE_1RF0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77073: ~halts (TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1LA0LF_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77074: ~halts (TM_from_str "1RB0RF_1LC0RA_0LD0LC_0RE1RA_1RE0RB_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77075: ~halts (TM_from_str "1RB0RA_1LC---_0LD0LC_0RE1RA_1RE1RF_0RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77076: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD1LE_0LF1RF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77077: ~halts (TM_from_str "1RB0RA_1LC---_0LD0LC_0RE1RA_1RE1RF_1LD1LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77078: ~halts (TM_from_str "1RB---_1LC0RB_1RF1LD_0LE0LD_1RE0RB_0RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77079: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_1LF0LF_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77080: ~halts (TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1LA1LF_---1RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77081: ~halts (TM_from_str "1RB1RF_1LC0RA_0LD0LC_0RE1RA_1RE0RB_---1LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77082: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_1LF0LF_0LA0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77083: ~halts (TM_from_str "1RB1LF_0RC0RB_1LC0LD_1LA0RE_1RE0RC_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 3 4 0). Time Qed.

Lemma nonhalt77084: ~halts (TM_from_str "1RB1RD_1LB0LC_1LD0RF_0LE0LD_1RE0RA_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77085: ~halts (TM_from_str "1RB---_0RC1LB_0RD0LA_0RE0LB_1LE0LF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 2 320 1 6 4 0). Time Qed.

Lemma nonhalt77086: ~halts (TM_from_str "1RB0RD_1LC1LE_1RA0LB_1LD1LC_1LF0RF_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 3 4 0). Time Qed.

Lemma nonhalt77087: ~halts (TM_from_str "1RB---_1RC0LF_1LD1RA_0LE0LD_1RE0RB_1LF0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 3 4 0). Time Qed.

Lemma nonhalt77088: ~halts (TM_from_str "1RB1LA_1LC1RE_1RD0LB_---1RE_0LA1RF_0RE0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 1 3 4 0). Time Qed.

Lemma nonhalt77089: ~halts (TM_from_str "1RB0RA_0RC0RB_1LC0LD_1LE1LB_1RA0LF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77090: ~halts (TM_from_str "1RB---_0RC0RB_1LC1RD_0RA1LE_0LF0LE_1RD0LA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77091: ~halts (TM_from_str "1RB0RA_0RC0RB_1LC0LD_1LE0LD_1RA1LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77092: ~halts (TM_from_str "1RB0LC_0RC---_1RD---_0RE0RD_1LE0LF_0LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77093: ~halts (TM_from_str "1RB0LA_1RC1RE_0LD0RD_1LD1LA_1LF0RE_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77094: ~halts (TM_from_str "1RB0RA_0RC0RB_1LC0LD_1LE1LB_1RA1LF_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77095: ~halts (TM_from_str "1RB0LA_1RC1RE_0LD0RD_1LD1LA_---0RF_0RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77096: ~halts (TM_from_str "1RB0LA_0LC1RD_1LE1LA_0RC0RD_1LF---_1LC0LC") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77097: ~halts (TM_from_str "1RB0RE_0RC0LB_1LD1RE_1LB---_0RF1RA_0LC0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 1 6 4 0). Time Qed.

Lemma nonhalt77098: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1LE0RC_1RF1RC_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77099: ~halts (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RF0LE_0RC0RE_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77100: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1LE0RC_1RE0RF_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77101: ~halts (TM_from_str "1RB0LB_0LC1LE_1RC0RD_1LB1RD_0LF0RA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77102: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_---1RE_0RF0RC_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77103: ~halts (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RF0LE_---0RB_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77104: ~halts (TM_from_str "1RB1LA_1LC0RC_---1RD_0RF0RE_1LE0LA_1RA1RF") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77105: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1RE0RC_---0RF_0LB0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77106: ~halts (TM_from_str "1RB0RC_1RC0RA_1LD0LF_---0LE_0LF1LE_1RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77107: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1RE0RC_---0RF_1LC0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77108: ~halts (TM_from_str "1RB0RB_0RC1RE_1LC0LD_1RB1LD_0RF0LA_---1RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77109: ~halts (TM_from_str "1RB1LE_0LC1RD_0RA1LD_1LA0RD_---0LF_0LB0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 1 6 6 0). Time Qed.

Lemma nonhalt77110: ~halts (TM_from_str "1RB---_0LC1LF_1LC0LD_1RE0LF_0RB0RE_1LD1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77111: ~halts (TM_from_str "1RB1LF_1LC0RA_0LD0LC_0RE1RA_1RE0RB_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77112: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LF_1LD1LE_1RC1RF_1LA0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77113: ~halts (TM_from_str "1RB0RB_0RC0RA_1LD---_0LE0LD_0RF1RC_1RF1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77114: ~halts (TM_from_str "1RB---_0RC0RB_0LD1LA_1LD1LE_0LA1LF_0LE0LF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77115: ~halts (TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1LA1RF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77116: ~halts (TM_from_str "1RB0RB_0RC0RB_1LD---_0LE0LD_0RF1RC_1RF1RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77117: ~halts (TM_from_str "1RB1RD_0LC1LD_1LC1LA_1LE0LD_1RF---_0RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 2 320 1 5 4 0). Time Qed.

Lemma nonhalt77118: ~halts (TM_from_str "1RB1LB_0RC0RB_1LD0RE_0LD1RA_1LF---_1LF1LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 2 5 4 0). Time Qed.

Lemma nonhalt77119: ~halts (TM_from_str "1RB---_0RC0RB_1RD0RF_0LD1LE_0LE1RA_1LF1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 2 5 4 0). Time Qed.

Lemma nonhalt77120: ~halts (TM_from_str "1RB1LB_0RC0RB_1RD0RE_0LE---_1LE1LF_0LF1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 2 5 4 0). Time Qed.

Lemma nonhalt77121: ~halts (TM_from_str "1RB1LB_0RC0RB_1LD0RE_0LD1RA_1LE0RF_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 2 5 4 0). Time Qed.

Lemma nonhalt77122: ~halts (TM_from_str "1RB0LC_1LA1RD_1LA1RB_1RB1RE_---0RF_1RB0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 2 5 3 0). Time Qed.

Lemma nonhalt77123: ~halts (TM_from_str "1RB0RD_1LC1RE_1RB0LD_1LC1RB_1RB1RF_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 2 5 3 0). Time Qed.

Lemma nonhalt77124: ~halts (TM_from_str "1RB1LE_1RC0RF_1LD1RB_0LB0LA_0LA0RD_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 2 5 3 0). Time Qed.

Lemma nonhalt77125: ~halts (TM_from_str "1RB1LE_1RC0RF_1LD1RB_1LE0LA_0LA0RD_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 2 5 3 0). Time Qed.

Lemma nonhalt77126: ~halts (TM_from_str "1RB1RE_1LC1RA_1RB0LD_1LC1RB_---0RF_1RB0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 2 5 3 0). Time Qed.

Lemma nonhalt77127: ~halts (TM_from_str "1RB1LD_1RC0RF_0LD1RB_0LA0RE_1LD0LA_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 320 2 5 3 0). Time Qed.

Lemma nonhalt77128: ~halts (TM_from_str "1RB0LA_1RC0LC_1RD1LE_0LE1RF_---1LA_1LC0RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 2 3 3 0). Time Qed.

Lemma nonhalt77129: ~halts (TM_from_str "1RB0RE_0LC0LA_1RE1LD_1LB---_0LF0RA_1LF0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 2 6 4 0). Time Qed.

Lemma nonhalt77130: ~halts (TM_from_str "1RB1LF_1LC---_0LD1LC_0LE0LD_1LF1RA_1RF0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 320 2 6 4 0). Time Qed.

Lemma nonhalt77131: ~halts (TM_from_str "1RB0LD_1LC0RD_0LC1LA_0LA1RE_0RB0RF_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 3 3 0). Time Qed.

Lemma nonhalt77132: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_0LE1LE_1RE0LF_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 2 6 3 0). Time Qed.

Lemma nonhalt77133: ~halts (TM_from_str "1RB1RD_1LC1LD_---1LA_1RF1LE_1RA0LB_0LC0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 2 320 2 6 3 0). Time Qed.

Lemma nonhalt77134: ~halts (TM_from_str "1RB1LA_0RC1LC_1LB1LD_0RE0LF_0LC1RD_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 2 3 4 0). Time Qed.

Lemma nonhalt77135: ~halts (TM_from_str "1RB1RC_0LA1RA_0LD0RE_0RA1LC_---0RF_1LB1RF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 2 3 4 0). Time Qed.

Lemma nonhalt77136: ~halts (TM_from_str "1RB0LD_1RC0LD_1LD0RB_1RE0LE_1RF0LB_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 2 3 4 0). Time Qed.

Lemma nonhalt77137: ~halts (TM_from_str "1RB1LE_0RC---_1LD0RF_0LA0RD_0RE0LF_0LB0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 320 2 3 4 0). Time Qed.

Lemma nonhalt77138: ~halts (TM_from_str "1RB1LD_0RC0RF_1LC1RA_1LE0LA_0LA0LE_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 2 3 4 0). Time Qed.

Lemma nonhalt77139: ~halts (TM_from_str "1RB1LB_1RC0LB_1LA1RD_1RF0RE_1LC0RC_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 320 2 3 4 0). Time Qed.

Lemma nonhalt77140: ~halts (TM_from_str "1RB---_1RC0RE_1LD0RA_0LE0LC_0RB0LF_1LD0RD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 3 4 0). Time Qed.

Lemma nonhalt77141: ~halts (TM_from_str "1RB---_1RC0RE_1LD0RA_0LE0LC_0RB0LF_1LD0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 3 4 0). Time Qed.

Lemma nonhalt77142: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD0RF_1LA0LC_1LD---_1RB0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 3 4 0). Time Qed.

Lemma nonhalt77143: ~halts (TM_from_str "1RB0LB_0RC0RE_0LD0RA_1LE0LC_1RB0LF_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 3 4 0). Time Qed.

Lemma nonhalt77144: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD0RF_1LA0LC_1LD---_1RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 3 4 0). Time Qed.

Lemma nonhalt77145: ~halts (TM_from_str "1RB0LD_0RC0RE_0LD0RA_1LE0LC_1RB0LF_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 3 4 0). Time Qed.

Lemma nonhalt77146: ~halts (TM_from_str "1RB0LE_1LC1RA_---1LD_0RB1LF_1RD1LA_0LD0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 8 320 2 6 4 0). Time Qed.

Lemma nonhalt77147: ~halts (TM_from_str "1RB1LC_1LA0LD_1LB0LF_0LB1LE_0RF---_0RD1RF") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 6 320 2 4 4 0). Time Qed.

Lemma nonhalt77148: ~halts (TM_from_str "1RB0LA_0LC0RF_---1LD_1LE0LA_0LF0LB_0RA1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77149: ~halts (TM_from_str "1RB0LB_1RC0RA_0RD0RF_1LD1RE_1LB0LE_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77150: ~halts (TM_from_str "1RB0LA_0LC0RF_---1LD_1LE1LF_1RB0LB_0RA1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77151: ~halts (TM_from_str "1RB0LB_0LC0RE_---1LD_1LA0LF_0RF1RA_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77152: ~halts (TM_from_str "1RB0LA_0LC0RF_---1LD_1LE0LA_1RB0LB_0RA1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77153: ~halts (TM_from_str "1RB0LA_0LC0RF_---1LD_1LE1LF_0LF0LB_0RA1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77154: ~halts (TM_from_str "1RB0LB_0LC0RE_---1LD_1LA1LE_0RF1RF_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77155: ~halts (TM_from_str "1RB0LA_0LC0RF_---1LD_1LE0LA_1RB0LB_0RA1RE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77156: ~halts (TM_from_str "1RB0LB_0LC0RE_---1LD_1LA0LF_0RF1RF_1RB0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 8 320 2 4 4 0). Time Qed.

Lemma nonhalt77157: ~halts (TM_from_str "1RB0RA_1RC---_1LD1RF_1RF1LE_0LC0LE_1RF0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 2 6 3 0). Time Qed.

Lemma nonhalt77158: ~halts (TM_from_str "1RB0RE_0LC0RD_1RD1LC_1LE1LE_1RF0LD_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 10 320 2 3 4 0). Time Qed.

Lemma nonhalt77159: ~halts (TM_from_str "1RB1LA_1LC1LC_1RD0LB_---1RE_1RF0RC_0LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 10 320 2 3 4 0). Time Qed.

Lemma nonhalt77160: ~halts (TM_from_str "1RB0RA_1RC---_1LD1RF_1RA1LE_0LC0LE_1RF0RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 2 6 3 0). Time Qed.

Lemma nonhalt77161: ~halts (TM_from_str "1RB0RE_0LC0RD_0LD1LC_1LE1LE_1RF0LD_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 10 320 2 3 4 0). Time Qed.

Lemma nonhalt77162: ~halts (TM_from_str "1RB0LF_1RC0RC_0LD1RE_0LA1LD_---0RF_1RA0RC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77163: ~halts (TM_from_str "1RB0RF_0LC0RD_1LA1LC_0LD1RE_1RA0RB_---0LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77164: ~halts (TM_from_str "1RB0RC_1RC1RF_0LD0RE_1LB1LD_0LE1RA_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77165: ~halts (TM_from_str "1RB1RA_1LC0LF_0RA0LD_0RD1LE_1LB0LC_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77166: ~halts (TM_from_str "1RB1RA_1LC1LF_0RA0LD_0RD1LE_1LB0LC_---0RE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77167: ~halts (TM_from_str "1RB1RF_0LC0RD_1LA1LC_0LD1RE_1RA0RB_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77168: ~halts (TM_from_str "1RB0RC_1RC0RF_0LD0RE_1LB1LD_0LE1RA_---0LD") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77169: ~halts (TM_from_str "1RB0RD_1RC0LA_1RD0RD_0LE1RF_0LB1LE_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 320 2 1 2 4). Time Qed.

Lemma nonhalt77170: ~halts (TM_from_str "1RB0RA_0LC0LA_0LD1LB_1RE1LF_1RE1LA_---1LC") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 2 1 2 4). Time Qed.

Lemma nonhalt77171: ~halts (TM_from_str "1RB0RE_1RC0LB_1LD1RF_0LE1LD_1RE1RA_---0RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 2 1 2 1). Time Qed.

Lemma nonhalt77172: ~halts (TM_from_str "1RB0RE_1RC0LB_1LD1RF_0LE1LD_1RE1RA_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 2 1 2 1). Time Qed.

Lemma nonhalt77173: ~halts (TM_from_str "1RB0RE_1RC0LB_1LD1RF_0LE1LD_1RE1RA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 2 1 2 1). Time Qed.

Lemma nonhalt77174: ~halts (TM_from_str "1RB0LB_0LC0RF_1LC1LD_1LE0LC_1LA---_1RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 2 1 2 1). Time Qed.

Lemma nonhalt77175: ~halts (TM_from_str "1RB1LF_1RC0LE_1LD0RA_---1LE_1LA1LB_0LB1LD") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 4 320 2 1 4 1). Time Qed.

Lemma nonhalt77176: ~halts (TM_from_str "1RB1RF_1RC---_0RD1RC_0RE1RA_1LE0LA_0LE1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt77177: ~halts (TM_from_str "1RB0LE_1RC---_1RD0LD_1LE0RF_0LA1LE_0RE0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt77178: ~halts (TM_from_str "1RB0RC_1RC1LF_0RD0RA_1LE1RF_1RB1LD_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 21 320 3 2 4 0). Time Qed.

Lemma nonhalt77179: ~halts (TM_from_str "1RB1LD_0RC0RF_0RD0RE_1RE1LA_0LA1LE_---0LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt77180: ~halts (TM_from_str "1RB1RA_1RC---_1RD0RF_1LE0RC_1RA0LF_0LD1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt77181: ~halts (TM_from_str "1RB1RF_1LC---_0RD1RC_0RE1RA_1LE0LA_0LE1RD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt77182: ~halts (TM_from_str "1RB1RA_0RC1RD_1LA1RA_1LE0LF_1LD0RE_---1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 2 6 0). Time Qed.

Lemma nonhalt77183: ~halts (TM_from_str "1RB1RC_0RC1RD_1LA1RA_1LE0LF_1LD0RE_---1LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 5 320 3 2 6 0). Time Qed.

Lemma nonhalt77184: ~halts (TM_from_str "1RB1LD_1RC1RF_0RD1LE_0LE---_1LF0RA_1RE0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt77185: ~halts (TM_from_str "1RB1LB_0RC---_1RD0RE_1LE0LA_1LF0RF_0RD0LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 8 0). Time Qed.

Lemma nonhalt77186: ~halts (TM_from_str "1RB0LD_1LC0RB_0LF0RD_1LA0LE_1LB---_0RA1LD") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 1 3 0). Time Qed.

Lemma nonhalt77187: ~halts (TM_from_str "1RB0LF_0LC0RC_1RE0RD_0RB---_1RF0RA_1LA1LE") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 14 320 3 2 8 0). Time Qed.

Lemma nonhalt77188: ~halts (TM_from_str "1RB0RA_0RC0RE_1RD---_0LE1LF_1RA1LD_1LE0LF") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt77189: ~halts (TM_from_str "1RB0LE_1RC1RF_1RD0RE_1LA0RC_0LD1RD_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 24 320 3 2 16 0). Time Qed.

Lemma nonhalt77190: ~halts (TM_from_str "1RB0LF_0RC1RB_1LD0RB_1LE---_1LA0RA_0LB0LC") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 6 320 3 2 12 0). Time Qed.

Lemma nonhalt77191: ~halts (TM_from_str "1RB1RD_0RC---_1LC1RA_1LF0RE_1LE0LA_0RD0LF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77192: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD1RC_0RE1RF_1LE0LA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77193: ~halts (TM_from_str "1RB---_0LB1LC_0LD1LB_1LE0RF_1RD0LA_1RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77194: ~halts (TM_from_str "1RB---_0RC1RF_1RD0LE_1LC0RA_1LC0LE_0RF1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77195: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD0LB_0RA0LE_1RC0RF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77196: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD0LB_0RA0LE_1LC0RF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77197: ~halts (TM_from_str "1RB0RF_1RC0LE_0RD0LD_1RE0RA_1LB0LE_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77198: ~halts (TM_from_str "1RB0RA_1LC0RA_0LD0RD_1LA0LE_1LB0LF_1LB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77199: ~halts (TM_from_str "1RB---_1RC0LE_0RD0LF_1RE0RF_1LB0LE_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77200: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD0LB_0RA0LA_1RC0RF_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77201: ~halts (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA0LD_1RA0RF_1LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77202: ~halts (TM_from_str "1RB0RF_1RC0LE_0RD0LA_1RE0RA_1LB0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77203: ~halts (TM_from_str "1RB1RF_1RC0LE_0RD0LD_1RE0RA_1LB0LE_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77204: ~halts (TM_from_str "1RB0RA_1LC0RA_0LD0RD_1LA0LE_1LB0LF_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77205: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD0LB_0RA0LA_1RC1RF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77206: ~halts (TM_from_str "1RB0RA_1LC0RA_0LF0RD_1RB0LE_1LB---_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77207: ~halts (TM_from_str "1RB0RA_1LC0RA_0LF0RD_1LB0LE_1LB---_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77208: ~halts (TM_from_str "1RB---_1RC0LE_0RD0LD_1RE0RF_1LB0LE_1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77209: ~halts (TM_from_str "1RB0RF_1RC0LE_0RD0LD_1RE0RA_1LB0LE_1RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77210: ~halts (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA0LD_1RA1RF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77211: ~halts (TM_from_str "1RB---_1LC0RF_0LD0RD_1LF0LE_1LB0LA_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77212: ~halts (TM_from_str "1RB0LD_0RC0LE_1RD0RE_1LA0LD_1RA0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77213: ~halts (TM_from_str "1RB0LD_0RC0LC_1RD0RE_1LA0LD_1RA0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77214: ~halts (TM_from_str "1RB0RA_1LC0RA_0LD0RD_1LA0LE_1LB1LF_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77215: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD0LB_0RA0LA_1RC0RF_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 3 0). Time Qed.

Lemma nonhalt77216: ~halts (TM_from_str "1RB0RD_1LC1RB_1RD0LB_1RC1RE_1RF0RA_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77217: ~halts (TM_from_str "1RB1RA_1LC0LF_---0LD_1LE0LB_0RA0LA_1RF1RE") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77218: ~halts (TM_from_str "1RB---_0RC1RF_1RD0LE_1LE0RA_1LC0LE_0RF1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77219: ~halts (TM_from_str "1RB---_0LB1LC_0LD1LB_1LE0RF_1RF0LA_1RD0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77220: ~halts (TM_from_str "1RB1RD_1LC0RF_1RD1LD_0RE0LB_---1RF_1RA1LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 4 0). Time Qed.

Lemma nonhalt77221: ~halts (TM_from_str "1RB0LD_1LC0RF_0LE0RA_1LB---_1LF0LA_1RB0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77222: ~halts (TM_from_str "1RB0LD_0RC0LE_1RD0RE_1LA0LD_1RA1RF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77223: ~halts (TM_from_str "1RB0LD_0RC0LE_1RD0RE_1LA0LD_1LA0RF_1RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77224: ~halts (TM_from_str "1RB0LB_1RC0LA_0RD1RD_1LB0RE_0RF---_1RD1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 8 0). Time Qed.

Lemma nonhalt77225: ~halts (TM_from_str "1RB1RF_1RC0LE_0RD0LA_1RE0RA_1LB0LE_0LD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77226: ~halts (TM_from_str "1RB---_1RC0LE_0RD0LF_1RE0RF_1LB0LE_1LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77227: ~halts (TM_from_str "1RB0RE_1LC0LB_1RD0LB_0RA0LE_1RC1RF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77228: ~halts (TM_from_str "1RB0RA_1LC0RA_0LF0RD_1LB1LE_0RF---_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 2 0). Time Qed.

Lemma nonhalt77229: ~halts (TM_from_str "1RB0LB_1RC0LA_0RD1RD_1LB0RE_0RF---_0LB1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 24 320 2 1 8 0). Time Qed.

Lemma nonhalt77230: ~halts (TM_from_str "1RB0LB_1RC0RE_1LD0RB_1LB0LC_1RA1RF_---0LD") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 8 0). Time Qed.

Lemma nonhalt77231: ~halts (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE1LF_1LB0RB_---0RA") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 8 0). Time Qed.

Lemma nonhalt77232: ~halts (TM_from_str "1RB0RE_0LC0LB_1RF1RD_1RE---_1LB0RC_0RA0RA") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 6 0). Time Qed.

Lemma nonhalt77233: ~halts (TM_from_str "1RB---_1LC0RD_0LD0LC_1RE1RA_0RF0RF_1RC0RB") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 6 0). Time Qed.

Lemma nonhalt77234: ~halts (TM_from_str "1RB1RE_0RC0RC_1RD0RF_0LA0LD_1RF---_1LD0RA") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 6 0). Time Qed.

Lemma nonhalt77235: ~halts (TM_from_str "1RB1RE_1LC0RC_1RA1LD_0LC0LB_1RF0RA_---0RD") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 6 0). Time Qed.

Lemma nonhalt77236: ~halts (TM_from_str "1RB1LD_1RC1RE_1LA0RA_0LA0LC_1RF0RB_---0RD") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 6 0). Time Qed.

Lemma nonhalt77237: ~halts (TM_from_str "1RB---_1RC0LB_0RD0LF_0LE1RF_1LB0RF_1RE0RA") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 4 0). Time Qed.

Lemma nonhalt77238: ~halts (TM_from_str "1RB1RF_1LC1RA_---0LD_0LE1LE_0RF0LA_0RA0LB") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 21 320 2 1 3 0). Time Qed.

Lemma nonhalt77239: ~halts (TM_from_str "1RB0RD_1RC1RD_1RD0RF_0LE1RA_1LC1LE_---0LE") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 24 320 2 1 16 0). Time Qed.

Lemma nonhalt77240: ~halts (TM_from_str "1RB0LF_1LC0LC_1RA0LD_1RE0LB_1RF---_0RC0RE") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 24 320 2 1 16 0). Time Qed.

Lemma nonhalt77241: ~halts (TM_from_str "1RB1RC_1RC0RF_0LD1RE_1LB1LD_1RA0RC_---0LD") c0.
Proof. solve_cert (RWL_mod 1000001 3000000 3000000 24 320 2 1 16 0). Time Qed.

Lemma nonhalt77242: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA0RC_0LF1LE_0LA0LE_---0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 56 3200 2 1 4 0). Time Qed.

Lemma nonhalt77243: ~halts (TM_from_str "1RB---_0RC1RF_1LD1RA_1RE0LD_0RB1LF_1RE0LC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 42 3200 2 1 16 0). Time Qed.

Lemma nonhalt77244: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE1LE_0LB0LF_0LB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 56 3200 2 1 4 0). Time Qed.

Lemma nonhalt77245: ~halts (TM_from_str "1RB1LA_0RC0RF_1RD0LE_1RE0RA_1LC0LE_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 56 3200 2 1 4 0). Time Qed.

Lemma nonhalt77246: ~halts (TM_from_str "1RB1RB_0RC0RF_1RD0LE_1RE0RA_1LC0LE_0RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 56 3200 2 1 4 0). Time Qed.

Lemma nonhalt77247: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD0LF_0RE1RF_1LE0LA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 4 0). Time Qed.

Lemma nonhalt77248: ~halts (TM_from_str "1RB1LB_0LC0RC_0LD1LC_1RE1LE_0RF0LA_---1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 30 3200 2 1 4 0). Time Qed.

Lemma nonhalt77249: ~halts (TM_from_str "1RB0LA_1LC1RD_0RD1RC_0RE1RF_1LE0LA_---1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 4 0). Time Qed.

Lemma nonhalt77250: ~halts (TM_from_str "1RB0LA_0RC1RD_0RD1RF_1RE1LA_1LF1RB_---1LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 30 3200 2 1 4 0). Time Qed.

Lemma nonhalt77251: ~halts (TM_from_str "1RB1LE_1LC1RD_---1LA_0RF1RA_1RD0LE_0RA1RC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 30 3200 2 1 4 0). Time Qed.

Lemma nonhalt77252: ~halts (TM_from_str "1RB0RE_0LC1RA_0LD1LC_1LA1LF_---1RD_1LB0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 4 0). Time Qed.

Lemma nonhalt77253: ~halts (TM_from_str "1RB1LD_1LC0LF_0LA0LD_1RE1LB_1RA---_0LD0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 2 0). Time Qed.

Lemma nonhalt77254: ~halts (TM_from_str "1RB---_1RC1LE_1LD0LF_0LB0LE_1RA1LC_0LE0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 2 0). Time Qed.

Lemma nonhalt77255: ~halts (TM_from_str "1RB0RF_0RC0RD_1LA1RD_1LE1RA_1LC---_0RD0LC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 2 0). Time Qed.

Lemma nonhalt77256: ~halts (TM_from_str "1RB1LD_1RC---_1RD1LA_1LE0LF_0LC0LA_0LA0RC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 2 0). Time Qed.

Lemma nonhalt77257: ~halts (TM_from_str "1RB---_0RC0RB_1RD0LF_0RE0RA_1RF0LE_1LC1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 60 3200 2 1 3 0). Time Qed.

Lemma nonhalt77258: ~halts (TM_from_str "1RB0RF_0RC1RA_1RD0LE_1LE0LD_0RB0LD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 42 3200 2 1 3 0). Time Qed.

Lemma nonhalt77259: ~halts (TM_from_str "1RB0RF_0RC1RA_1RD0RC_1LE0LD_0RB0LD_0RE---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 42 3200 2 1 3 0). Time Qed.

Lemma nonhalt77260: ~halts (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_0LF---_0RD1LC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 3 0). Time Qed.

Lemma nonhalt77261: ~halts (TM_from_str "1RB1LC_1RC0RB_1LD0RE_0LE0LC_1RB0LF_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 3 0). Time Qed.

Lemma nonhalt77262: ~halts (TM_from_str "1RB0RF_0RC1RA_1RD0RA_1LE0LD_0RB0LD_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 60 3200 2 1 2 0). Time Qed.

Lemma nonhalt77263: ~halts (TM_from_str "1RB0RF_1LC0RC_0RD0LD_1LE1RB_1RA0LB_1RD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77264: ~halts (TM_from_str "1RB0LD_1RC0RF_1LA1RD_1LE0RE_0RC0LC_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77265: ~halts (TM_from_str "1RB0LF_1LC0RE_0RD0LD_1LA1RF_1RD---_1LC0RC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77266: ~halts (TM_from_str "1RB---_0RC1LE_1RD0LF_0LB0LD_1RF0RE_1RA1LC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77267: ~halts (TM_from_str "1RB0RA_1RC1LE_1RD---_0RE1LA_1RF0LB_0LD0LF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77268: ~halts (TM_from_str "1RB0LB_0LC0RC_1RD1LA_1LE0RA_---0LF_1LC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77269: ~halts (TM_from_str "1RB0RB_1RC---_1LD1RE_1RA0LE_1LF0RF_0RC0LC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77270: ~halts (TM_from_str "1RB0LD_1LC0RF_1LA1RD_1LE0RE_0RC0LC_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77271: ~halts (TM_from_str "1RB0LF_1RC0LC_0LD0RD_1RE1LB_1LA0RB_1LD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77272: ~halts (TM_from_str "1RB0LF_0RC0RE_0RD0LD_1LA1RF_1RD---_1LC0RC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77273: ~halts (TM_from_str "1RB0LC_0LA0RF_1LD0RD_0RE0LE_1LA1RC_1RE---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77274: ~halts (TM_from_str "1RB0LD_0LC0RF_1LA1RD_1LE0RE_0RC0LC_1RC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77275: ~halts (TM_from_str "1RB0RA_1LC0RE_1RD0LB_1LA0LD_1RC1RF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 36 3200 2 1 6 0). Time Qed.

Lemma nonhalt77276: ~halts (TM_from_str "1RB0RC_1LC0RA_1RA0LD_0LE1LF_0LB0LD_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 6 0). Time Qed.

Lemma nonhalt77277: ~halts (TM_from_str "1RB0LC_1LC0RD_1LA0LB_0RF1RE_0LA---_0RA0RD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 6 0). Time Qed.

Lemma nonhalt77278: ~halts (TM_from_str "1RB0LC_1RC0RD_1LA0LC_1RE1LD_0RA0RF_0RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 56 3200 2 1 6 0). Time Qed.

Lemma nonhalt77279: ~halts (TM_from_str "1RB0LC_1LC0RA_1LA1LD_1RE0LB_---1RF_1RE0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 35 3200 2 1 6 0). Time Qed.

Lemma nonhalt77280: ~halts (TM_from_str "1RB0RA_1LC0RE_1LD0LB_0LE0LA_1RA0LF_0LC---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 28 3200 2 1 6 0). Time Qed.

Lemma nonhalt77281: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD---_1LB1RD_1LE0RF_0RB0LC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 32 3200 2 1 6 0). Time Qed.

Lemma nonhalt77282: ~halts (TM_from_str "1RB1RE_1LC0RA_0LF0LD_1LE---_0LB0LE_1LA0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 48 3200 2 1 3 0). Time Qed.

Lemma nonhalt77283: ~halts (TM_from_str "1RB0LA_1LC1LF_1RD0LB_0RA0RE_1RF---_0RC0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 48 3200 2 1 3 0). Time Qed.

Lemma nonhalt77284: ~halts (TM_from_str "1RB0LD_0RC0RE_1RD0LC_1LA1LF_1RF---_0RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 48 3200 2 1 3 0). Time Qed.

Lemma nonhalt77285: ~halts (TM_from_str "1RB1LF_1LC0LD_1RD0LB_1LF1RE_0RA---_1RF0RC") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 48 3200 2 1 6 0). Time Qed.

Lemma nonhalt77286: ~halts (TM_from_str "1RB1LE_1LB0LC_1LA0RD_1RC0RA_0LF---_1LD1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 48 3200 2 1 6 0). Time Qed.

Lemma nonhalt77287: ~halts (TM_from_str "1RB0LC_1RC0RE_1LD1LA_0RF0LE_1RA1LE_---1RD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 60 3200 2 1 8 0). Time Qed.

Lemma nonhalt77288: ~halts (TM_from_str "1RB0LC_1LC1LF_1RD0LB_0RF0RE_0RC---_1RA0RF") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 60 3200 2 1 8 0). Time Qed.

Lemma nonhalt77289: ~halts (TM_from_str "1RB0RE_0LC0RA_1LF1RD_1LE---_1RA0LB_1LA0LD") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 56 3200 2 1 8 0). Time Qed.

Lemma nonhalt77290: ~halts (TM_from_str "1RB0RD_1RC1RD_1RD1RF_0LE1RA_1LC1LE_---0LA") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 30 3200 2 1 8 0). Time Qed.

Lemma nonhalt77291: ~halts (TM_from_str "1RB1RE_1LC0RF_0RA0LD_0LE1LC_1RC1LE_0RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 12 0). Time Qed.

Lemma nonhalt77292: ~halts (TM_from_str "1RB1LA_0RC0LE_1RD1RA_1LB0RF_0LA1LB_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 12 0). Time Qed.

Lemma nonhalt77293: ~halts (TM_from_str "1RB0LF_0LC0RE_1LA1LD_1LB1RD_0RD1RB_0LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 18 3200 2 1 12 0). Time Qed.

Lemma nonhalt77294: ~halts (TM_from_str "1RB1RE_1LC1RB_1LD0LC_0RA1LA_0RD0RF_0RD---") c0.
Proof. solve_cert (RWL_mod 1001 3000000 3000000 32 3200 2 1 8 0). Time Qed.

