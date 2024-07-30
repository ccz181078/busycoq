
From BusyCoq Require Import Individual62.
From BusyCoq Require Import SBCv1.
Require Import ZArith.
Require Import String.

Definition tm0 := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RF_0LA0RE").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_SBCv1 tm0(Build_SBC_cert_v1 E D[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD0LA_0RC---").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_SBCv1 tm1(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD1LD_0LE0RF_1RF0LF_0RA0LA").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_SBCv1 tm2(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB0LC_0RC0RB_0RD1LE_1LB1RA_0LF---_0LA1RD").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_SBCv1 tm3(Build_SBC_cert_v1 F D[0;0;0;0;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;1;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LF_0RA0LF").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_SBCv1 tm4(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB0RF_0LA---").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_SBCv1 tm5(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1RE_0RE0LA_1LB1RF_0RB1RA").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_SBCv1 tm6(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0LB").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_SBCv1 tm7(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1LB1RE_0LC0LB_1RD1LB_0RA---_0RF0LC_1RA0RD").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_SBCv1 tm8(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1LB0RB_0RC0LE_0LF0RD_1RA---_1RC0LE_1RD1LE").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_SBCv1 tm9(Build_SBC_cert_v1 E A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RA_0LA0RE_0RB0RF_0LE---").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_SBCv1 tm10(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1RB0RF_0RC1LD_1LD1RE_0LE0RA_1RB0LB_0RC---").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_SBCv1 tm11(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1RB0LE_0RC0RF_1LD1RA_0LA---_0RC0LF_0RC0RD").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_SBCv1 tm12(Build_SBC_cert_v1 A C[0;1;1;0] [1;1;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RF_0RA0LA_0RB1RF_1LB---").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_SBCv1 tm13(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1LB0RF_1RC1LE_0LA0RD_1RA---_0RF1RA_0RC0LF").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_SBCv1 tm14(Build_SBC_cert_v1 E A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [1] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1LB1RC_0LC---_1RD0LD_0RA0LE_0RA0RF_0RE---").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_SBCv1 tm15(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD0RF_0LC---").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_SBCv1 tm16(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1LB1RD_0LC1RB_1RB0LD_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_SBCv1 tm17(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1LB0RD_0LC0LD_0RD---_1RE1LF_1RA0RE_0RF0LA").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_SBCv1 tm18(Build_SBC_cert_v1 B A[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1LB1RE_0LC1RD_1RA0LD_0RA0LB_0RF---_1RC0RD").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_SBCv1 tm19(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0;0;0] [1;1;0;1;0] [0;0;0] [1;0;0] [1;0] [1;0] 3 1).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LD_0RA0RE_0LA---_---0RD").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_SBCv1 tm20(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1RB0LD_0RC1LA_1LA1RD_0RE0LB_0LA0RF_0RC---").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_SBCv1 tm21(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB0LD_0LE---").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_SBCv1 tm22(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1LB1LD_1RC0LA_1RD1RB_1LB0RE_0RB1RF_0LB---").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_SBCv1 tm23(Build_SBC_cert_v1 B D[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RD_0LA0RB").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_SBCv1 tm24(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1LF").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_SBCv1 tm25(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1RB1RC_0LA0RC_0RD1RE_1LE1RF_0LF---_0RB0LC").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_SBCv1 tm26(Build_SBC_cert_v1 F D[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1RB0LA_1LC0RE_1LA0RD_1RE0LC_1RC1LF_---0RB").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_SBCv1 tm27(Build_SBC_cert_v1 A C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1RB1LE_0RC1RF_0LD0LC_1LA---_0LF1LA_0RA0RB").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_SBCv1 tm28(Build_SBC_cert_v1 A B[0;1] [1;1] [1;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;0;1] [0;0] [1;0] [1] [1] 3 0).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1RB0LE_0RC1LD_1LD1RA_0LA0RF_0RC1RD_---0RE").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_SBCv1 tm29(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1RB_0LC0RD").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_SBCv1 tm30(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm31 := Eval compute in (TM_from_str "1RB0RF_1LC0RE_1RB0LD_1LC0LB_1RA0LD_0RB---").

Theorem nonhalt31: ~halts tm31 c0.
Proof.
  solve_SBCv1 tm31(Build_SBC_cert_v1 C B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm32 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA---_0RF1RD_0LA0RB").

Theorem nonhalt32: ~halts tm32 c0.
Proof.
  solve_SBCv1 tm32(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm33 := Eval compute in (TM_from_str "1RB1LE_0RC0LC_1LD1RF_0LA---_0LA0RB_0RE1RD").

Theorem nonhalt33: ~halts tm33 c0.
Proof.
  solve_SBCv1 tm33(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm34 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA---_0RF1RD_0LA0RB").

Theorem nonhalt34: ~halts tm34 c0.
Proof.
  solve_SBCv1 tm34(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm35 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB0LC_0LC---").

Theorem nonhalt35: ~halts tm35 c0.
Proof.
  solve_SBCv1 tm35(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm36 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD0LD_0RA0RE_0LA0RF_0RA---").

Theorem nonhalt36: ~halts tm36 c0.
Proof.
  solve_SBCv1 tm36(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm37 := Eval compute in (TM_from_str "1LB1RD_0LC1RC_1RB0LD_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt37: ~halts tm37 c0.
Proof.
  solve_SBCv1 tm37(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm38 := Eval compute in (TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB0LA").

Theorem nonhalt38: ~halts tm38 c0.
Proof.
  solve_SBCv1 tm38(Build_SBC_cert_v1 A E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm39 := Eval compute in (TM_from_str "1RB0RA_1LC0RD_1RA0LD_1RA1LE_0RE0LF_1LC---").

Theorem nonhalt39: ~halts tm39 c0.
Proof.
  solve_SBCv1 tm39(Build_SBC_cert_v1 C B[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm40 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD1RD_0LE0RF_1RF0LF_0RA1LB").

Theorem nonhalt40: ~halts tm40 c0.
Proof.
  solve_SBCv1 tm40(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm41 := Eval compute in (TM_from_str "1RB---_0LC0RE_1RE1RD_1LB1RF_0RD0LD_0RB1RA").

Theorem nonhalt41: ~halts tm41 c0.
Proof.
  solve_SBCv1 tm41(Build_SBC_cert_v1 B D[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm42 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LB_0RF1RF_0LC0RD").

Theorem nonhalt42: ~halts tm42 c0.
Proof.
  solve_SBCv1 tm42(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm43 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LA_0RF---_1RC0RD").

Theorem nonhalt43: ~halts tm43 c0.
Proof.
  solve_SBCv1 tm43(Build_SBC_cert_v1 C D[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm44 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD0RF_0LD---").

Theorem nonhalt44: ~halts tm44 c0.
Proof.
  solve_SBCv1 tm44(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm45 := Eval compute in (TM_from_str "1RB0LB_0RC0RE_1LD1RA_0LA0RF_0LC---_0RC0RF").

Theorem nonhalt45: ~halts tm45 c0.
Proof.
  solve_SBCv1 tm45(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm46 := Eval compute in (TM_from_str "1LB0LE_1RC---_0RC0LD_1LA0RE_1RF1LC_1RD0RF").

Theorem nonhalt46: ~halts tm46 c0.
Proof.
  solve_SBCv1 tm46(Build_SBC_cert_v1 A D[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm47 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RB_0LC---").

Theorem nonhalt47: ~halts tm47 c0.
Proof.
  solve_SBCv1 tm47(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm48 := Eval compute in (TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RC0LE_1LD0LE_0RC---").

Theorem nonhalt48: ~halts tm48 c0.
Proof.
  solve_SBCv1 tm48(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm49 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD1RD_0RC---").

Theorem nonhalt49: ~halts tm49 c0.
Proof.
  solve_SBCv1 tm49(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm50 := Eval compute in (TM_from_str "1RB1RC_0RC0LD_1LD1RA_0LA0RE_0RF0LC_0RC---").

Theorem nonhalt50: ~halts tm50 c0.
Proof.
  solve_SBCv1 tm50(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm51 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_0RB0LC_0RA---").

Theorem nonhalt51: ~halts tm51 c0.
Proof.
  solve_SBCv1 tm51(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm52 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LE_0RD0LA").

Theorem nonhalt52: ~halts tm52 c0.
Proof.
  solve_SBCv1 tm52(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm53 := Eval compute in (TM_from_str "1LB1RE_1RC0LC_0RA1LD_0LB0RC_0RD1RF_0LB---").

Theorem nonhalt53: ~halts tm53 c0.
Proof.
  solve_SBCv1 tm53(Build_SBC_cert_v1 B A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm54 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LF_0RB0LD_0RA---").

Theorem nonhalt54: ~halts tm54 c0.
Proof.
  solve_SBCv1 tm54(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm55 := Eval compute in (TM_from_str "1LB0RF_1RC1LE_1LE0RD_1RA---_0RF1RA_0RC0LA").

Theorem nonhalt55: ~halts tm55 c0.
Proof.
  solve_SBCv1 tm55(Build_SBC_cert_v1 E A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [1] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm56 := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LB_1RD1RB_0RC1RA").

Theorem nonhalt56: ~halts tm56 c0.
Proof.
  solve_SBCv1 tm56(Build_SBC_cert_v1 C B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm57 := Eval compute in (TM_from_str "1RB---_0LC0RD_1RD0LD_0RE0LD_1LB1RF_0RB1RA").

Theorem nonhalt57: ~halts tm57 c0.
Proof.
  solve_SBCv1 tm57(Build_SBC_cert_v1 C E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm58 := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RE_1RE0LA").

Theorem nonhalt58: ~halts tm58 c0.
Proof.
  solve_SBCv1 tm58(Build_SBC_cert_v1 E D[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm59 := Eval compute in (TM_from_str "1RB---_0LC0RD_1RD0LD_0RE1RB_1LB1RF_0RB1RA").

Theorem nonhalt59: ~halts tm59 c0.
Proof.
  solve_SBCv1 tm59(Build_SBC_cert_v1 C E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm60 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RF_0RA0LF_0RB1RF_1LB---").

Theorem nonhalt60: ~halts tm60 c0.
Proof.
  solve_SBCv1 tm60(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm61 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD1RA_0RA0LF_0RD0LA_---0RE").

Theorem nonhalt61: ~halts tm61 c0.
Proof.
  solve_SBCv1 tm61(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm62 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LF_0RF1RB_0LC0RD").

Theorem nonhalt62: ~halts tm62 c0.
Proof.
  solve_SBCv1 tm62(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm63 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RB_0RA0LD").

Theorem nonhalt63: ~halts tm63 c0.
Proof.
  solve_SBCv1 tm63(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm64 := Eval compute in (TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LA1LC_0RA0LC").

Theorem nonhalt64: ~halts tm64 c0.
Proof.
  solve_SBCv1 tm64(Build_SBC_cert_v1 D C[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm65 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RD_0RA---").

Theorem nonhalt65: ~halts tm65 c0.
Proof.
  solve_SBCv1 tm65(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm66 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LC_0RA0LD").

Theorem nonhalt66: ~halts tm66 c0.
Proof.
  solve_SBCv1 tm66(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm67 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF1RF_0LA0RB").

Theorem nonhalt67: ~halts tm67 c0.
Proof.
  solve_SBCv1 tm67(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm68 := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RC_0LA1RE_---0RF_1RA0RB").

Theorem nonhalt68: ~halts tm68 c0.
Proof.
  solve_SBCv1 tm68(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm69 := Eval compute in (TM_from_str "1LB0LA_1RC0LA_1LB0RD_1RE0LA_1RC0RF_0RC---").

Theorem nonhalt69: ~halts tm69 c0.
Proof.
  solve_SBCv1 tm69(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm70 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1RC---").

Theorem nonhalt70: ~halts tm70 c0.
Proof.
  solve_SBCv1 tm70(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm71 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_1LD0RA").

Theorem nonhalt71: ~halts tm71 c0.
Proof.
  solve_SBCv1 tm71(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm72 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RA_0LA0RE_---0RF_0RC---").

Theorem nonhalt72: ~halts tm72 c0.
Proof.
  solve_SBCv1 tm72(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm73 := Eval compute in (TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RA").

Theorem nonhalt73: ~halts tm73 c0.
Proof.
  solve_SBCv1 tm73(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm74 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD1RD").

Theorem nonhalt74: ~halts tm74 c0.
Proof.
  solve_SBCv1 tm74(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm75 := Eval compute in (TM_from_str "1LB1RC_0LC---_1RD0LE_0RA0LF_0RA1RB_0RE0RF").

Theorem nonhalt75: ~halts tm75 c0.
Proof.
  solve_SBCv1 tm75(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm76 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RF_0RA0LD_0RB1RF_0LD---").

Theorem nonhalt76: ~halts tm76 c0.
Proof.
  solve_SBCv1 tm76(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm77 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD0LD_0RA1LB_---0RF_0RA---").

Theorem nonhalt77: ~halts tm77 c0.
Proof.
  solve_SBCv1 tm77(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm78 := Eval compute in (TM_from_str "1RB0RE_0LC---_1LF1RD_1RE0LE_0RC0RB_0LD0RA").

Theorem nonhalt78: ~halts tm78 c0.
Proof.
  solve_SBCv1 tm78(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm79 := Eval compute in (TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LA1LC_0RF0LC_1RB---").

Theorem nonhalt79: ~halts tm79 c0.
Proof.
  solve_SBCv1 tm79(Build_SBC_cert_v1 A C[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm80 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RD_0RE---").

Theorem nonhalt80: ~halts tm80 c0.
Proof.
  solve_SBCv1 tm80(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm81 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF0LB_0LA0RB").

Theorem nonhalt81: ~halts tm81 c0.
Proof.
  solve_SBCv1 tm81(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm82 := Eval compute in (TM_from_str "1RB1LD_0RC0LE_1LD1RA_0LA1RF_---0RF_0RB0LA").

Theorem nonhalt82: ~halts tm82 c0.
Proof.
  solve_SBCv1 tm82(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm83 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD0LE").

Theorem nonhalt83: ~halts tm83 c0.
Proof.
  solve_SBCv1 tm83(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm84 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LE_0RA0LB_0RA1RB_0RE---").

Theorem nonhalt84: ~halts tm84 c0.
Proof.
  solve_SBCv1 tm84(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm85 := Eval compute in (TM_from_str "1LB0RC_0LC0RE_1RD0LF_1RE---_0RA0RD_1LB1RB").

Theorem nonhalt85: ~halts tm85 c0.
Proof.
  solve_SBCv1 tm85(Build_SBC_cert_v1 B A[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm86 := Eval compute in (TM_from_str "1RB0LB_0RC1LE_1LD1RA_0LA0RF_0RA0RD_0RC---").

Theorem nonhalt86: ~halts tm86 c0.
Proof.
  solve_SBCv1 tm86(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm87 := Eval compute in (TM_from_str "1RB0LB_0RC0LC_1LD1RE_0LA1LE_0RF---_1RA0RB").

Theorem nonhalt87: ~halts tm87 c0.
Proof.
  solve_SBCv1 tm87(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm88 := Eval compute in (TM_from_str "1RB---_0RC0RA_1LD0RE_0LE0RB_1RA0LF_1LD0LC").

Theorem nonhalt88: ~halts tm88 c0.
Proof.
  solve_SBCv1 tm88(Build_SBC_cert_v1 D C[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 7 4).
Qed.


Definition tm89 := Eval compute in (TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE0LC_1RB0RF_0RB---").

Theorem nonhalt89: ~halts tm89 c0.
Proof.
  solve_SBCv1 tm89(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm90 := Eval compute in (TM_from_str "1LB0LA_1RC0LA_1RD0RC_1LB0RE_1RF---_1RB1LC").

Theorem nonhalt90: ~halts tm90 c0.
Proof.
  solve_SBCv1 tm90(Build_SBC_cert_v1 A C[0;0;0;1] [0;1;0;1] [0;1;0;1] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;1;0;1] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm91 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD0LB_0RC---").

Theorem nonhalt91: ~halts tm91 c0.
Proof.
  solve_SBCv1 tm91(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm92 := Eval compute in (TM_from_str "1RB---_1LC1RF_0LE0RD_0RB0LB_1RD1LC_0RC1RA").

Theorem nonhalt92: ~halts tm92 c0.
Proof.
  solve_SBCv1 tm92(Build_SBC_cert_v1 C B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm93 := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1RE_0RE0LE_1LB1RF_0RB1RA").

Theorem nonhalt93: ~halts tm93 c0.
Proof.
  solve_SBCv1 tm93(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm94 := Eval compute in (TM_from_str "1LB0RE_1LC1RD_0LD0RA_1RE0LE_0RB0RF_0LB---").

Theorem nonhalt94: ~halts tm94 c0.
Proof.
  solve_SBCv1 tm94(Build_SBC_cert_v1 D B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm95 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_0RB1RB_0RA---").

Theorem nonhalt95: ~halts tm95 c0.
Proof.
  solve_SBCv1 tm95(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm96 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RF_0RF1RB_0LC0RD").

Theorem nonhalt96: ~halts tm96 c0.
Proof.
  solve_SBCv1 tm96(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm97 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_0LC---").

Theorem nonhalt97: ~halts tm97 c0.
Proof.
  solve_SBCv1 tm97(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm98 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF0LA_0LA0RB").

Theorem nonhalt98: ~halts tm98 c0.
Proof.
  solve_SBCv1 tm98(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm99 := Eval compute in (TM_from_str "1LB0RF_1RC1LE_0LA0RD_1RA---_0RF1RA_0RC0LA").

Theorem nonhalt99: ~halts tm99 c0.
Proof.
  solve_SBCv1 tm99(Build_SBC_cert_v1 E A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [1] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm100 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB0LD_0RA---").

Theorem nonhalt100: ~halts tm100 c0.
Proof.
  solve_SBCv1 tm100(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm101 := Eval compute in (TM_from_str "1LB---_1RC1LF_0RE1RD_0RB0RC_0LA0LE_0LD1LB").

Theorem nonhalt101: ~halts tm101 c0.
Proof.
  solve_SBCv1 tm101(Build_SBC_cert_v1 B C[0;1] [1;1] [1;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;0;1] [0;0] [1;0] [1] [1] 3 1).
Qed.


Definition tm102 := Eval compute in (TM_from_str "1RB0LB_0RC0LC_1LD1RE_0LE---_0RF1LF_0LA0RB").

Theorem nonhalt102: ~halts tm102 c0.
Proof.
  solve_SBCv1 tm102(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm103 := Eval compute in (TM_from_str "1RB0LC_0LA1RA_1RD1LB_0RE---_0RF0RD_1LB1RC").

Theorem nonhalt103: ~halts tm103 c0.
Proof.
  solve_SBCv1 tm103(Build_SBC_cert_v1 B F[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm104 := Eval compute in (TM_from_str "1LB---_1RC0LC_0RE1RD_0LB0RC_1LD1RF_0RD0RA").

Theorem nonhalt104: ~halts tm104 c0.
Proof.
  solve_SBCv1 tm104(Build_SBC_cert_v1 B E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm105 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1LB").

Theorem nonhalt105: ~halts tm105 c0.
Proof.
  solve_SBCv1 tm105(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm106 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB1RB_0LC---").

Theorem nonhalt106: ~halts tm106 c0.
Proof.
  solve_SBCv1 tm106(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm107 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LE_0RD0LE").

Theorem nonhalt107: ~halts tm107 c0.
Proof.
  solve_SBCv1 tm107(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm108 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB0RF_0LA---").

Theorem nonhalt108: ~halts tm108 c0.
Proof.
  solve_SBCv1 tm108(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm109 := Eval compute in (TM_from_str "1LB0RB_0RC0RF_1LE1RD_1RB0LB_0LD0RA_0LC---").

Theorem nonhalt109: ~halts tm109 c0.
Proof.
  solve_SBCv1 tm109(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm110 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LD_0RA0RE_0LF---_1LB0RD").

Theorem nonhalt110: ~halts tm110 c0.
Proof.
  solve_SBCv1 tm110(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm111 := Eval compute in (TM_from_str "1LB1RC_0LC1RE_1RD1LB_0RA1LE_---0RF_0LB0RD").

Theorem nonhalt111: ~halts tm111 c0.
Proof.
  solve_SBCv1 tm111(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm112 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt112: ~halts tm112 c0.
Proof.
  solve_SBCv1 tm112(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm113 := Eval compute in (TM_from_str "1LB1RC_0LC0RD_1RD1RE_0RA0LE_1LB0RF_0RD---").

Theorem nonhalt113: ~halts tm113 c0.
Proof.
  solve_SBCv1 tm113(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm114 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt114: ~halts tm114 c0.
Proof.
  solve_SBCv1 tm114(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm115 := Eval compute in (TM_from_str "1RB1RC_0RC0LE_1LD1RF_0LA0RB_1LD---_0RD1RE").

Theorem nonhalt115: ~halts tm115 c0.
Proof.
  solve_SBCv1 tm115(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm116 := Eval compute in (TM_from_str "1RB0RB_0RC---_1LD1RE_0LE0RA_1RF0LF_0RC1LD").

Theorem nonhalt116: ~halts tm116 c0.
Proof.
  solve_SBCv1 tm116(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm117 := Eval compute in (TM_from_str "1LB1RA_0LC1RE_1RD0LD_0RA0LB_---0RF_1RC0RD").

Theorem nonhalt117: ~halts tm117 c0.
Proof.
  solve_SBCv1 tm117(Build_SBC_cert_v1 C D[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm118 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt118: ~halts tm118 c0.
Proof.
  solve_SBCv1 tm118(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm119 := Eval compute in (TM_from_str "1RB1LD_0RC0LD_1LD1RA_0LA0RE_0RF0LC_0RC---").

Theorem nonhalt119: ~halts tm119 c0.
Proof.
  solve_SBCv1 tm119(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm120 := Eval compute in (TM_from_str "1RB1LD_0RC0LB_1LD1RE_0LA0LF_0RF---_1RA0RB").

Theorem nonhalt120: ~halts tm120 c0.
Proof.
  solve_SBCv1 tm120(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm121 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD0LB_0RC---").

Theorem nonhalt121: ~halts tm121 c0.
Proof.
  solve_SBCv1 tm121(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm122 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD1RD_0LE---").

Theorem nonhalt122: ~halts tm122 c0.
Proof.
  solve_SBCv1 tm122(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm123 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LB_0LA---").

Theorem nonhalt123: ~halts tm123 c0.
Proof.
  solve_SBCv1 tm123(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm124 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LA_1LC---").

Theorem nonhalt124: ~halts tm124 c0.
Proof.
  solve_SBCv1 tm124(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm125 := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD0LA_1RA0RF_1LB0LA_0RA---").

Theorem nonhalt125: ~halts tm125 c0.
Proof.
  solve_SBCv1 tm125(Build_SBC_cert_v1 B A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm126 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0RF_0RA0LA_0RB0RF_0LA---").

Theorem nonhalt126: ~halts tm126 c0.
Proof.
  solve_SBCv1 tm126(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm127 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0RF_0RB0LC_0LA---").

Theorem nonhalt127: ~halts tm127 c0.
Proof.
  solve_SBCv1 tm127(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm128 := Eval compute in (TM_from_str "1RB0RD_1LC1RE_0LE0RA_0RB0RF_1RD0LD_0LB---").

Theorem nonhalt128: ~halts tm128 c0.
Proof.
  solve_SBCv1 tm128(Build_SBC_cert_v1 E B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm129 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD0LD_0RA1LB_0RA1RF_0LB---").

Theorem nonhalt129: ~halts tm129 c0.
Proof.
  solve_SBCv1 tm129(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm130 := Eval compute in (TM_from_str "1LB1RE_0RC0RF_0RA1LD_0LE0RB_1RC0LC_0LB---").

Theorem nonhalt130: ~halts tm130 c0.
Proof.
  solve_SBCv1 tm130(Build_SBC_cert_v1 E A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm131 := Eval compute in (TM_from_str "1LB1RD_0LC1RB_0LD0LD_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt131: ~halts tm131 c0.
Proof.
  solve_SBCv1 tm131(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm132 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB0LD_0LC---").

Theorem nonhalt132: ~halts tm132 c0.
Proof.
  solve_SBCv1 tm132(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm133 := Eval compute in (TM_from_str "1RB---_1LC0RE_1RF1LD_0RE1RB_0RF0LB_0LB0RA").

Theorem nonhalt133: ~halts tm133 c0.
Proof.
  solve_SBCv1 tm133(Build_SBC_cert_v1 D B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [1] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm134 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1RD---").

Theorem nonhalt134: ~halts tm134 c0.
Proof.
  solve_SBCv1 tm134(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm135 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0RE").

Theorem nonhalt135: ~halts tm135 c0.
Proof.
  solve_SBCv1 tm135(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 1).
Qed.


Definition tm136 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RA_0LA0RE_0RC1RF_0LD---").

Theorem nonhalt136: ~halts tm136 c0.
Proof.
  solve_SBCv1 tm136(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm137 := Eval compute in (TM_from_str "1LB1RE_1RC0LC_0RA1LD_0LB0RC_0RD0RF_0LD---").

Theorem nonhalt137: ~halts tm137 c0.
Proof.
  solve_SBCv1 tm137(Build_SBC_cert_v1 B A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm138 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD0LA_0RC---").

Theorem nonhalt138: ~halts tm138 c0.
Proof.
  solve_SBCv1 tm138(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm139 := Eval compute in (TM_from_str "1RB---_1LC0RD_0LF0LD_1RE0LB_0RB0RA_0RD1LF").

Theorem nonhalt139: ~halts tm139 c0.
Proof.
  solve_SBCv1 tm139(Build_SBC_cert_v1 C B[1;0;1;0] [0;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm140 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB1RB_0RA---").

Theorem nonhalt140: ~halts tm140 c0.
Proof.
  solve_SBCv1 tm140(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm141 := Eval compute in (TM_from_str "1RB0LB_0RC1LE_1LD1RA_0LA0RF_0LA0RD_0RC---").

Theorem nonhalt141: ~halts tm141 c0.
Proof.
  solve_SBCv1 tm141(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm142 := Eval compute in (TM_from_str "1RB0LE_0RC0RD_1LD1RA_0LA1RF_0RC1LD_---0RA").

Theorem nonhalt142: ~halts tm142 c0.
Proof.
  solve_SBCv1 tm142(Build_SBC_cert_v1 A C[1;1;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm143 := Eval compute in (TM_from_str "1RB1RC_0RC0LF_1LD1RA_0LA0RE_0RB0LC_---0RE").

Theorem nonhalt143: ~halts tm143 c0.
Proof.
  solve_SBCv1 tm143(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm144 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LF_0RB1RB_0LD---").

Theorem nonhalt144: ~halts tm144 c0.
Proof.
  solve_SBCv1 tm144(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm145 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RD_0LA---").

Theorem nonhalt145: ~halts tm145 c0.
Proof.
  solve_SBCv1 tm145(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm146 := Eval compute in (TM_from_str "1LB0LC_1RC0LA_1LB0RD_1RE0LA_1RC0RF_0RC---").

Theorem nonhalt146: ~halts tm146 c0.
Proof.
  solve_SBCv1 tm146(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm147 := Eval compute in (TM_from_str "1RB1LD_0RC0LE_1LD1RA_0LA0RF_---0RF_0RB0LC").

Theorem nonhalt147: ~halts tm147 c0.
Proof.
  solve_SBCv1 tm147(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm148 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RB_0RC---").

Theorem nonhalt148: ~halts tm148 c0.
Proof.
  solve_SBCv1 tm148(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm149 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1RD_0RD0LA").

Theorem nonhalt149: ~halts tm149 c0.
Proof.
  solve_SBCv1 tm149(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm150 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LB_0RF1RB_0LC0RD").

Theorem nonhalt150: ~halts tm150 c0.
Proof.
  solve_SBCv1 tm150(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm151 := Eval compute in (TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LA1LC_0RA1RF_0LA---").

Theorem nonhalt151: ~halts tm151 c0.
Proof.
  solve_SBCv1 tm151(Build_SBC_cert_v1 A C[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm152 := Eval compute in (TM_from_str "1RB---_0RC1RD_1LD1RE_0LE---_0RF0LB_0LA0RB").

Theorem nonhalt152: ~halts tm152 c0.
Proof.
  solve_SBCv1 tm152(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm153 := Eval compute in (TM_from_str "1RB---_1LC0RD_1RE0LD_1RE1LF_1RB0RA_0RF0LB").

Theorem nonhalt153: ~halts tm153 c0.
Proof.
  solve_SBCv1 tm153(Build_SBC_cert_v1 C B[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm154 := Eval compute in (TM_from_str "1LB1RC_0LC1LF_1RD0LD_0RA0RE_0LA0RD_---1RD").

Theorem nonhalt154: ~halts tm154 c0.
Proof.
  solve_SBCv1 tm154(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm155 := Eval compute in (TM_from_str "1LB1RF_0RC0RB_0RA1LD_0LE---_0LF1RA_1RB0LC").

Theorem nonhalt155: ~halts tm155 c0.
Proof.
  solve_SBCv1 tm155(Build_SBC_cert_v1 E A[0;0;0;0;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;1;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm156 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RF_0LC---").

Theorem nonhalt156: ~halts tm156 c0.
Proof.
  solve_SBCv1 tm156(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm157 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB1RB_0LE---").

Theorem nonhalt157: ~halts tm157 c0.
Proof.
  solve_SBCv1 tm157(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm158 := Eval compute in (TM_from_str "1LB0LA_0LC1RE_1RC1LD_---1LE_0RA0RF_0RA1RF").

Theorem nonhalt158: ~halts tm158 c0.
Proof.
  solve_SBCv1 tm158(Build_SBC_cert_v1 D A[1;1;0;1] [1;0;0;1] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0;1] [1;0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm159 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0RF_1LE1RB_0LB0RA_0LD---").

Theorem nonhalt159: ~halts tm159 c0.
Proof.
  solve_SBCv1 tm159(Build_SBC_cert_v1 B D[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm160 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD1RD_0LE0RF_1RF0LF_0RA1RB").

Theorem nonhalt160: ~halts tm160 c0.
Proof.
  solve_SBCv1 tm160(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm161 := Eval compute in (TM_from_str "1RB0RE_0RC0LD_1LD1RA_0LA0RF_0LC---_0RB0LC").

Theorem nonhalt161: ~halts tm161 c0.
Proof.
  solve_SBCv1 tm161(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm162 := Eval compute in (TM_from_str "1LB0RC_1RC0LC_0RE0RD_0LE---_1LF1RB_0LB0RA").

Theorem nonhalt162: ~halts tm162 c0.
Proof.
  solve_SBCv1 tm162(Build_SBC_cert_v1 B E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm163 := Eval compute in (TM_from_str "1RB0LD_1RC0RB_1LA0RE_1LA0LD_1RF---_1RA1LB").

Theorem nonhalt163: ~halts tm163 c0.
Proof.
  solve_SBCv1 tm163(Build_SBC_cert_v1 D B[0;0;0;1] [0;1;0;1] [0;1;0;1] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;1;0;1] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm164 := Eval compute in (TM_from_str "1LB0LA_1RC0LA_1LB0RD_1RE0LC_1RC0RF_0RC---").

Theorem nonhalt164: ~halts tm164 c0.
Proof.
  solve_SBCv1 tm164(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm165 := Eval compute in (TM_from_str "1RB1LE_0RC---_1LD1RF_0LA0RB_0LA1LB_0RD0LA").

Theorem nonhalt165: ~halts tm165 c0.
Proof.
  solve_SBCv1 tm165(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm166 := Eval compute in (TM_from_str "1RB0LF_1RC---_0RD0RB_1LE0RA_0LA0RC_1LE0LD").

Theorem nonhalt166: ~halts tm166 c0.
Proof.
  solve_SBCv1 tm166(Build_SBC_cert_v1 E D[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm167 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0LD").

Theorem nonhalt167: ~halts tm167 c0.
Proof.
  solve_SBCv1 tm167(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm168 := Eval compute in (TM_from_str "1RB0LB_0RC1RE_1LD1RA_0LA0RF_0LD---_0LC0RB").

Theorem nonhalt168: ~halts tm168 c0.
Proof.
  solve_SBCv1 tm168(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm169 := Eval compute in (TM_from_str "1RB0RB_0RC1LD_1LD1RE_0LE---_0RF0LB_0LA1RF").

Theorem nonhalt169: ~halts tm169 c0.
Proof.
  solve_SBCv1 tm169(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm170 := Eval compute in (TM_from_str "1RB1LD_0RC1LE_1LD1RA_0LA1RE_---0RF_0LD0RB").

Theorem nonhalt170: ~halts tm170 c0.
Proof.
  solve_SBCv1 tm170(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm171 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LE---_0RF1RF_0LA0RB").

Theorem nonhalt171: ~halts tm171 c0.
Proof.
  solve_SBCv1 tm171(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm172 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD0RF_0LD---").

Theorem nonhalt172: ~halts tm172 c0.
Proof.
  solve_SBCv1 tm172(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm173 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0RE_0RA0LB_0LA---_0RD0LA").

Theorem nonhalt173: ~halts tm173 c0.
Proof.
  solve_SBCv1 tm173(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm174 := Eval compute in (TM_from_str "1LB1LD_1RC0LA_1RD1RB_1LB0RE_0RF0LA_1RC---").

Theorem nonhalt174: ~halts tm174 c0.
Proof.
  solve_SBCv1 tm174(Build_SBC_cert_v1 B D[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm175 := Eval compute in (TM_from_str "1LB0LA_1RC0LA_1RD0RC_1LA0RE_1RF---_1RB1LC").

Theorem nonhalt175: ~halts tm175 c0.
Proof.
  solve_SBCv1 tm175(Build_SBC_cert_v1 A C[0;0;0;1] [0;1;0;1] [0;1;0;1] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;1;0;1] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm176 := Eval compute in (TM_from_str "1RB0LB_0RC1LE_1LD1RA_0RB0RF_0LA0RD_0LD---").

Theorem nonhalt176: ~halts tm176 c0.
Proof.
  solve_SBCv1 tm176(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm177 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt177: ~halts tm177 c0.
Proof.
  solve_SBCv1 tm177(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm178 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD1RD").

Theorem nonhalt178: ~halts tm178 c0.
Proof.
  solve_SBCv1 tm178(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm179 := Eval compute in (TM_from_str "1RB0RE_0RC0LC_1LD1RF_0LA0RB_0LC---_0RD0RE").

Theorem nonhalt179: ~halts tm179 c0.
Proof.
  solve_SBCv1 tm179(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm180 := Eval compute in (TM_from_str "1LB1RC_0LC---_1RD0LE_0RA0RF_0RA0LF_0RA0RB").

Theorem nonhalt180: ~halts tm180 c0.
Proof.
  solve_SBCv1 tm180(Build_SBC_cert_v1 C A[0;1;1;0] [1;1;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm181 := Eval compute in (TM_from_str "1LB1RC_0LC0RD_1RD0LE_0RA1LF_0RA1RB_---0RB").

Theorem nonhalt181: ~halts tm181 c0.
Proof.
  solve_SBCv1 tm181(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm182 := Eval compute in (TM_from_str "1RB0LB_0RC0RE_1LD1RA_0LA0RE_0LC0RF_0RC---").

Theorem nonhalt182: ~halts tm182 c0.
Proof.
  solve_SBCv1 tm182(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm183 := Eval compute in (TM_from_str "1RB1LD_1RC0LC_1LD1RE_---0LE_0RF1LF_0LA0RB").

Theorem nonhalt183: ~halts tm183 c0.
Proof.
  solve_SBCv1 tm183(Build_SBC_cert_v1 D C[1;0;0;1] [1;1;0;1] [1;0;1;0] [1;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm184 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt184: ~halts tm184 c0.
Proof.
  solve_SBCv1 tm184(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm185 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD0LA").

Theorem nonhalt185: ~halts tm185 c0.
Proof.
  solve_SBCv1 tm185(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm186 := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RA").

Theorem nonhalt186: ~halts tm186 c0.
Proof.
  solve_SBCv1 tm186(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm187 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1RD_0RD1RD").

Theorem nonhalt187: ~halts tm187 c0.
Proof.
  solve_SBCv1 tm187(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm188 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_0LD---").

Theorem nonhalt188: ~halts tm188 c0.
Proof.
  solve_SBCv1 tm188(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm189 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_1RD1RB_---0RD").

Theorem nonhalt189: ~halts tm189 c0.
Proof.
  solve_SBCv1 tm189(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm190 := Eval compute in (TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD0LB").

Theorem nonhalt190: ~halts tm190 c0.
Proof.
  solve_SBCv1 tm190(Build_SBC_cert_v1 C B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm191 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0RF_0RB0LD_0LA---").

Theorem nonhalt191: ~halts tm191 c0.
Proof.
  solve_SBCv1 tm191(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm192 := Eval compute in (TM_from_str "1RB0RC_1RC1LE_0RD0LC_1LE1RF_0LB0LA_0RA---").

Theorem nonhalt192: ~halts tm192 c0.
Proof.
  solve_SBCv1 tm192(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm193 := Eval compute in (TM_from_str "1LB0RD_0LC0RA_0RD1LC_1RE0LA_0RA1RF_1RA---").

Theorem nonhalt193: ~halts tm193 c0.
Proof.
  solve_SBCv1 tm193(Build_SBC_cert_v1 B A[1;1;1;0] [0;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm194 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1LD---").

Theorem nonhalt194: ~halts tm194 c0.
Proof.
  solve_SBCv1 tm194(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm195 := Eval compute in (TM_from_str "1LB---_0LC0RF_1RD1RA_0RE0LB_1LB1RC_0RD0LA").

Theorem nonhalt195: ~halts tm195 c0.
Proof.
  solve_SBCv1 tm195(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm196 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB0LC_0RA---").

Theorem nonhalt196: ~halts tm196 c0.
Proof.
  solve_SBCv1 tm196(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm197 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB1RB_0RA---").

Theorem nonhalt197: ~halts tm197 c0.
Proof.
  solve_SBCv1 tm197(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm198 := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RF_0LA0LE").

Theorem nonhalt198: ~halts tm198 c0.
Proof.
  solve_SBCv1 tm198(Build_SBC_cert_v1 E D[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm199 := Eval compute in (TM_from_str "1RB1LF_1LC0RE_1RD0LC_1LB0RA_1RA0LB_---0RD").

Theorem nonhalt199: ~halts tm199 c0.
Proof.
  solve_SBCv1 tm199(Build_SBC_cert_v1 C B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm200 := Eval compute in (TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LF0RF_0RB0LA").

Theorem nonhalt200: ~halts tm200 c0.
Proof.
  solve_SBCv1 tm200(Build_SBC_cert_v1 A E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm201 := Eval compute in (TM_from_str "1RB1RE_0RC1RE_1LD1RF_0LA0RB_0LF---_0RD0LB").

Theorem nonhalt201: ~halts tm201 c0.
Proof.
  solve_SBCv1 tm201(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm202 := Eval compute in (TM_from_str "1LB0RE_1RC0LD_1RA1RB_1LF1LA_0RB0LA_1RC---").

Theorem nonhalt202: ~halts tm202 c0.
Proof.
  solve_SBCv1 tm202(Build_SBC_cert_v1 B A[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm203 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RE_0LE1RA_0RF1LD_0LA0RB").

Theorem nonhalt203: ~halts tm203 c0.
Proof.
  solve_SBCv1 tm203(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm204 := Eval compute in (TM_from_str "1RB1RE_0RC0LE_1LD1RA_0LA0RB_1LD0RF_0RB---").

Theorem nonhalt204: ~halts tm204 c0.
Proof.
  solve_SBCv1 tm204(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm205 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA0LB_1LA0RF_1RC0RD").

Theorem nonhalt205: ~halts tm205 c0.
Proof.
  solve_SBCv1 tm205(Build_SBC_cert_v1 C D[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm206 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF1RD_0LA0RB").

Theorem nonhalt206: ~halts tm206 c0.
Proof.
  solve_SBCv1 tm206(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm207 := Eval compute in (TM_from_str "1LB0RE_1RC0LC_0RF1LD_0LB0RA_0RF---_1LD1RB").

Theorem nonhalt207: ~halts tm207 c0.
Proof.
  solve_SBCv1 tm207(Build_SBC_cert_v1 B F[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm208 := Eval compute in (TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LC1LB_0RF0LD_1RA---").

Theorem nonhalt208: ~halts tm208 c0.
Proof.
  solve_SBCv1 tm208(Build_SBC_cert_v1 C B[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm209 := Eval compute in (TM_from_str "1RB0RA_1LC0RE_1LD0LC_1RA0LC_1RF---_1RD1LA").

Theorem nonhalt209: ~halts tm209 c0.
Proof.
  solve_SBCv1 tm209(Build_SBC_cert_v1 C A[0;0;0;1] [0;1;0;1] [0;1;0;1] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;1;0;1] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm210 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB0RF_0LB---").

Theorem nonhalt210: ~halts tm210 c0.
Proof.
  solve_SBCv1 tm210(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm211 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RD_0RC---").

Theorem nonhalt211: ~halts tm211 c0.
Proof.
  solve_SBCv1 tm211(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm212 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD1RF_0LB---").

Theorem nonhalt212: ~halts tm212 c0.
Proof.
  solve_SBCv1 tm212(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm213 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD0LF_0LE0RF_1RF---_0RA1RB").

Theorem nonhalt213: ~halts tm213 c0.
Proof.
  solve_SBCv1 tm213(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm214 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1RD_0RD0LE").

Theorem nonhalt214: ~halts tm214 c0.
Proof.
  solve_SBCv1 tm214(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm215 := Eval compute in (TM_from_str "1RB0LD_1LC1RE_0LA1RD_0RB0LC_0RF---_1RA0RD").

Theorem nonhalt215: ~halts tm215 c0.
Proof.
  solve_SBCv1 tm215(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0;0;0] [1;1;0;1;0] [0;0;0] [1;0;0] [1;0] [1;0] 3 0).
Qed.


Definition tm216 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_1LB---").

Theorem nonhalt216: ~halts tm216 c0.
Proof.
  solve_SBCv1 tm216(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm217 := Eval compute in (TM_from_str "1LB0RD_0LC0RA_1RD0LD_0RE0RF_1LB1RC_0LE---").

Theorem nonhalt217: ~halts tm217 c0.
Proof.
  solve_SBCv1 tm217(Build_SBC_cert_v1 C E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm218 := Eval compute in (TM_from_str "1LB1RE_0LC1RE_1RD1LB_0RA---_0RF0LC_0LC0RD").

Theorem nonhalt218: ~halts tm218 c0.
Proof.
  solve_SBCv1 tm218(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm219 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LC_0RA1RB").

Theorem nonhalt219: ~halts tm219 c0.
Proof.
  solve_SBCv1 tm219(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm220 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD0RF_0LC---").

Theorem nonhalt220: ~halts tm220 c0.
Proof.
  solve_SBCv1 tm220(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm221 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0RB").

Theorem nonhalt221: ~halts tm221 c0.
Proof.
  solve_SBCv1 tm221(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 5).
Qed.


Definition tm222 := Eval compute in (TM_from_str "1RB1RE_0RC0LD_1LD1RA_0LA0RF_1LD---_0RB0LC").

Theorem nonhalt222: ~halts tm222 c0.
Proof.
  solve_SBCv1 tm222(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm223 := Eval compute in (TM_from_str "1LB0RE_1LC0LE_1RD---_0RD0LA_1RF1LD_1RA0RF").

Theorem nonhalt223: ~halts tm223 c0.
Proof.
  solve_SBCv1 tm223(Build_SBC_cert_v1 B A[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm224 := Eval compute in (TM_from_str "1LB0RE_1RC0LD_1RA1RB_1LF1LA_0RF0LA_1RC---").

Theorem nonhalt224: ~halts tm224 c0.
Proof.
  solve_SBCv1 tm224(Build_SBC_cert_v1 B A[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm225 := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1LD1RA_0LA---_0RC0RF_0RE---").

Theorem nonhalt225: ~halts tm225 c0.
Proof.
  solve_SBCv1 tm225(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm226 := Eval compute in (TM_from_str "1RB0RF_0LC0RA_1RD0LD_0RE1LB_1LB1RC_0RE---").

Theorem nonhalt226: ~halts tm226 c0.
Proof.
  solve_SBCv1 tm226(Build_SBC_cert_v1 C E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm227 := Eval compute in (TM_from_str "1LB1RD_0LC1RC_0LD0LB_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt227: ~halts tm227 c0.
Proof.
  solve_SBCv1 tm227(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm228 := Eval compute in (TM_from_str "1RB0LB_0RC0RE_1LD1RA_0LA1LF_0LC0RB_---1RB").

Theorem nonhalt228: ~halts tm228 c0.
Proof.
  solve_SBCv1 tm228(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm229 := Eval compute in (TM_from_str "1RB1RD_0RC1LD_1LD1RA_0LE0RF_1RB0LB_---0RB").

Theorem nonhalt229: ~halts tm229 c0.
Proof.
  solve_SBCv1 tm229(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm230 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LF_0RB0LC_0RA---").

Theorem nonhalt230: ~halts tm230 c0.
Proof.
  solve_SBCv1 tm230(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm231 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD0LF_1LE0RF_1RE0RA_0RA1RB").

Theorem nonhalt231: ~halts tm231 c0.
Proof.
  solve_SBCv1 tm231(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm232 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD0LA_0RC---").

Theorem nonhalt232: ~halts tm232 c0.
Proof.
  solve_SBCv1 tm232(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm233 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD1RD_0RC---").

Theorem nonhalt233: ~halts tm233 c0.
Proof.
  solve_SBCv1 tm233(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm234 := Eval compute in (TM_from_str "1LB1RD_0LC1RC_0LD0LD_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt234: ~halts tm234 c0.
Proof.
  solve_SBCv1 tm234(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm235 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1RF_0LC0RD").

Theorem nonhalt235: ~halts tm235 c0.
Proof.
  solve_SBCv1 tm235(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm236 := Eval compute in (TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB0LE").

Theorem nonhalt236: ~halts tm236 c0.
Proof.
  solve_SBCv1 tm236(Build_SBC_cert_v1 A E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm237 := Eval compute in (TM_from_str "1RB0RD_1LC1RE_0LE0RA_0RB---_1RF0LF_0RB1LC").

Theorem nonhalt237: ~halts tm237 c0.
Proof.
  solve_SBCv1 tm237(Build_SBC_cert_v1 E B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm238 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RB_0RA1LB").

Theorem nonhalt238: ~halts tm238 c0.
Proof.
  solve_SBCv1 tm238(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm239 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1RC---").

Theorem nonhalt239: ~halts tm239 c0.
Proof.
  solve_SBCv1 tm239(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm240 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD0LA").

Theorem nonhalt240: ~halts tm240 c0.
Proof.
  solve_SBCv1 tm240(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm241 := Eval compute in (TM_from_str "1LB0RC_0LC0RE_1RD0LF_1RE---_0RA0RD_1LB0LA").

Theorem nonhalt241: ~halts tm241 c0.
Proof.
  solve_SBCv1 tm241(Build_SBC_cert_v1 B A[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm242 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LC_0RA0LF").

Theorem nonhalt242: ~halts tm242 c0.
Proof.
  solve_SBCv1 tm242(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm243 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RB_0RE---").

Theorem nonhalt243: ~halts tm243 c0.
Proof.
  solve_SBCv1 tm243(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm244 := Eval compute in (TM_from_str "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RD_0LB---").

Theorem nonhalt244: ~halts tm244 c0.
Proof.
  solve_SBCv1 tm244(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm245 := Eval compute in (TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LF1LC_0RA0LC_1RB---").

Theorem nonhalt245: ~halts tm245 c0.
Proof.
  solve_SBCv1 tm245(Build_SBC_cert_v1 A C[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm246 := Eval compute in (TM_from_str "1RB0RD_0LC0RA_1RD0LD_0RE0RF_1LB1RC_0LE---").

Theorem nonhalt246: ~halts tm246 c0.
Proof.
  solve_SBCv1 tm246(Build_SBC_cert_v1 C E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm247 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LF_0RA1RB").

Theorem nonhalt247: ~halts tm247 c0.
Proof.
  solve_SBCv1 tm247(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm248 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RB_0RA0LF").

Theorem nonhalt248: ~halts tm248 c0.
Proof.
  solve_SBCv1 tm248(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm249 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0RE_0RA1LB_0LF---_0LD0RD").

Theorem nonhalt249: ~halts tm249 c0.
Proof.
  solve_SBCv1 tm249(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm250 := Eval compute in (TM_from_str "1LB1RD_1RC0LD_0RA1LB_0RE0LC_0LB0RF_0RA---").

Theorem nonhalt250: ~halts tm250 c0.
Proof.
  solve_SBCv1 tm250(Build_SBC_cert_v1 D A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm251 := Eval compute in (TM_from_str "1RB1RE_0RC0LE_1LD1RF_0LA0RB_1LD---_0RD1RE").

Theorem nonhalt251: ~halts tm251 c0.
Proof.
  solve_SBCv1 tm251(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm252 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0RA").

Theorem nonhalt252: ~halts tm252 c0.
Proof.
  solve_SBCv1 tm252(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm253 := Eval compute in (TM_from_str "1RB0LD_1RC0RB_1LA0RD_1RB1LE_0RE0LF_1LA---").

Theorem nonhalt253: ~halts tm253 c0.
Proof.
  solve_SBCv1 tm253(Build_SBC_cert_v1 A C[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm254 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0RF_0RA0LD_0RB0RF_1LC---").

Theorem nonhalt254: ~halts tm254 c0.
Proof.
  solve_SBCv1 tm254(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm255 := Eval compute in (TM_from_str "1LB0RF_1RB0RC_1LD1RE_0LE---_0RA0LF_0RC1RD").

Theorem nonhalt255: ~halts tm255 c0.
Proof.
  solve_SBCv1 tm255(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm256 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LE---_0RF1RF_0LA0RB").

Theorem nonhalt256: ~halts tm256 c0.
Proof.
  solve_SBCv1 tm256(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm257 := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RE_0LA0LA").

Theorem nonhalt257: ~halts tm257 c0.
Proof.
  solve_SBCv1 tm257(Build_SBC_cert_v1 E D[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm258 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0RC").

Theorem nonhalt258: ~halts tm258 c0.
Proof.
  solve_SBCv1 tm258(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 1).
Qed.


Definition tm259 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB0RF_1LC---").

Theorem nonhalt259: ~halts tm259 c0.
Proof.
  solve_SBCv1 tm259(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm260 := Eval compute in (TM_from_str "1RB1LE_0RC0LC_1LD1RF_0LA---_0LA0RB_0RE1RE").

Theorem nonhalt260: ~halts tm260 c0.
Proof.
  solve_SBCv1 tm260(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm261 := Eval compute in (TM_from_str "1LB0RB_0RC---_1LF1RD_1RE0LE_0RC1LF_0LD0RA").

Theorem nonhalt261: ~halts tm261 c0.
Proof.
  solve_SBCv1 tm261(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm262 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LF_0RA1LB").

Theorem nonhalt262: ~halts tm262 c0.
Proof.
  solve_SBCv1 tm262(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm263 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1RC").

Theorem nonhalt263: ~halts tm263 c0.
Proof.
  solve_SBCv1 tm263(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 1).
Qed.


Definition tm264 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LD_0RA1LE_0LC0RB_0RA---").

Theorem nonhalt264: ~halts tm264 c0.
Proof.
  solve_SBCv1 tm264(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm265 := Eval compute in (TM_from_str "1LB0RE_1RC0LD_1RA1RB_1LB1LA_0RF0LA_1RC---").

Theorem nonhalt265: ~halts tm265 c0.
Proof.
  solve_SBCv1 tm265(Build_SBC_cert_v1 B A[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm266 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_0LC---").

Theorem nonhalt266: ~halts tm266 c0.
Proof.
  solve_SBCv1 tm266(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm267 := Eval compute in (TM_from_str "1RB0LD_1RC1RA_1LA0RE_0LF1LC_0RA0LC_0RC---").

Theorem nonhalt267: ~halts tm267 c0.
Proof.
  solve_SBCv1 tm267(Build_SBC_cert_v1 A C[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm268 := Eval compute in (TM_from_str "1RB0LE_0RC0LD_1LD1RA_0LA0RF_0RC1RD_0RE---").

Theorem nonhalt268: ~halts tm268 c0.
Proof.
  solve_SBCv1 tm268(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm269 := Eval compute in (TM_from_str "1RB0LC_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---").

Theorem nonhalt269: ~halts tm269 c0.
Proof.
  solve_SBCv1 tm269(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm270 := Eval compute in (TM_from_str "1RB---_1LC0RE_1RF1LD_0RE1RB_0RF0LE_0LB0RA").

Theorem nonhalt270: ~halts tm270 c0.
Proof.
  solve_SBCv1 tm270(Build_SBC_cert_v1 D B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [1] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm271 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0LF").

Theorem nonhalt271: ~halts tm271 c0.
Proof.
  solve_SBCv1 tm271(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 1).
Qed.


Definition tm272 := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RF_0LA0LA").

Theorem nonhalt272: ~halts tm272 c0.
Proof.
  solve_SBCv1 tm272(Build_SBC_cert_v1 E D[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm273 := Eval compute in (TM_from_str "1RB0LE_0RC1LF_1LD1RA_0LA0RB_0RC0LE_---0RD").

Theorem nonhalt273: ~halts tm273 c0.
Proof.
  solve_SBCv1 tm273(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm274 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB1RF_0LC---").

Theorem nonhalt274: ~halts tm274 c0.
Proof.
  solve_SBCv1 tm274(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm275 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt275: ~halts tm275 c0.
Proof.
  solve_SBCv1 tm275(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm276 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LE_0RD1RD").

Theorem nonhalt276: ~halts tm276 c0.
Proof.
  solve_SBCv1 tm276(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm277 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0LC").

Theorem nonhalt277: ~halts tm277 c0.
Proof.
  solve_SBCv1 tm277(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm278 := Eval compute in (TM_from_str "1LB0RF_0LC0RA_1RD0LD_0RE1LB_1LB1RC_0RE---").

Theorem nonhalt278: ~halts tm278 c0.
Proof.
  solve_SBCv1 tm278(Build_SBC_cert_v1 C E[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm279 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0RF_0RB1RB_0LA---").

Theorem nonhalt279: ~halts tm279 c0.
Proof.
  solve_SBCv1 tm279(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm280 := Eval compute in (TM_from_str "1RB0LE_0RC1LF_1LD1RA_0LA0RB_0RC1LD_---0RD").

Theorem nonhalt280: ~halts tm280 c0.
Proof.
  solve_SBCv1 tm280(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm281 := Eval compute in (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0LD_0RF0LA_1RC0RB").

Theorem nonhalt281: ~halts tm281 c0.
Proof.
  solve_SBCv1 tm281(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm282 := Eval compute in (TM_from_str "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RF_1RD---").

Theorem nonhalt282: ~halts tm282 c0.
Proof.
  solve_SBCv1 tm282(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm283 := Eval compute in (TM_from_str "1RB0LD_1RC0RF_1LA0RD_1RB1LE_0RE0LC_1RC---").

Theorem nonhalt283: ~halts tm283 c0.
Proof.
  solve_SBCv1 tm283(Build_SBC_cert_v1 A C[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm284 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LD_0RA1RE_0LB---_0LA0RD").

Theorem nonhalt284: ~halts tm284 c0.
Proof.
  solve_SBCv1 tm284(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm285 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1RD---").

Theorem nonhalt285: ~halts tm285 c0.
Proof.
  solve_SBCv1 tm285(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm286 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LB_0RB0RF_0LB---").

Theorem nonhalt286: ~halts tm286 c0.
Proof.
  solve_SBCv1 tm286(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm287 := Eval compute in (TM_from_str "1RB1LE_0RC---_1LD1RF_0LA0RB_0LA1RF_0RD0LA").

Theorem nonhalt287: ~halts tm287 c0.
Proof.
  solve_SBCv1 tm287(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm288 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_0RD1RA_0LE0RF_1RF0LA_0RA---").

Theorem nonhalt288: ~halts tm288 c0.
Proof.
  solve_SBCv1 tm288(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm289 := Eval compute in (TM_from_str "1LB1RC_0LC0RD_1RD0LE_0RA1LF_0RA0LE_---0RB").

Theorem nonhalt289: ~halts tm289 c0.
Proof.
  solve_SBCv1 tm289(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm290 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB0LC_0RA---").

Theorem nonhalt290: ~halts tm290 c0.
Proof.
  solve_SBCv1 tm290(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm291 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA---_0RF1RD_0LA0RB").

Theorem nonhalt291: ~halts tm291 c0.
Proof.
  solve_SBCv1 tm291(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm292 := Eval compute in (TM_from_str "1RB0LF_1RC---_0RD0RB_1LE0RA_0LA0RC_1LE0LF").

Theorem nonhalt292: ~halts tm292 c0.
Proof.
  solve_SBCv1 tm292(Build_SBC_cert_v1 E D[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm293 := Eval compute in (TM_from_str "1RB0LE_0RC1LF_1LD1RA_0LA0RB_0RC1RD_---0RD").

Theorem nonhalt293: ~halts tm293 c0.
Proof.
  solve_SBCv1 tm293(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm294 := Eval compute in (TM_from_str "1LB1RE_0LC0LF_1RD1LB_0RA0LD_0RF---_1RC0RD").

Theorem nonhalt294: ~halts tm294 c0.
Proof.
  solve_SBCv1 tm294(Build_SBC_cert_v1 C D[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm295 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LF_0RA---_0RB0LC_0LC1LD").

Theorem nonhalt295: ~halts tm295 c0.
Proof.
  solve_SBCv1 tm295(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm296 := Eval compute in (TM_from_str "1LB1RC_0LC1RF_1RD0LE_0RA0RB_0RA1LB_---0RC").

Theorem nonhalt296: ~halts tm296 c0.
Proof.
  solve_SBCv1 tm296(Build_SBC_cert_v1 C A[1;1;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm297 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LF_0RA---_0RB0LC_0LC1RE").

Theorem nonhalt297: ~halts tm297 c0.
Proof.
  solve_SBCv1 tm297(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm298 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD1LF_0RA0LA_0RF1RB_0LC0RD").

Theorem nonhalt298: ~halts tm298 c0.
Proof.
  solve_SBCv1 tm298(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm299 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD0RF_0LD---").

Theorem nonhalt299: ~halts tm299 c0.
Proof.
  solve_SBCv1 tm299(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm300 := Eval compute in (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA1LB_0RF0LA_0LA0RB").

Theorem nonhalt300: ~halts tm300 c0.
Proof.
  solve_SBCv1 tm300(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm301 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA0LB_0RF---_1RC0RD").

Theorem nonhalt301: ~halts tm301 c0.
Proof.
  solve_SBCv1 tm301(Build_SBC_cert_v1 C D[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm302 := Eval compute in (TM_from_str "1LB1RD_0LC1RC_0LD0RB_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt302: ~halts tm302 c0.
Proof.
  solve_SBCv1 tm302(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm303 := Eval compute in (TM_from_str "1LB1RC_0LC0RD_1RD0LE_0RA1LF_0RA0LD_---0RB").

Theorem nonhalt303: ~halts tm303 c0.
Proof.
  solve_SBCv1 tm303(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm304 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD1LF_0RA0LA_0RF1RF_0LC0RD").

Theorem nonhalt304: ~halts tm304 c0.
Proof.
  solve_SBCv1 tm304(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm305 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB1RF_0LD---").

Theorem nonhalt305: ~halts tm305 c0.
Proof.
  solve_SBCv1 tm305(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm306 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB1RF_0LC---").

Theorem nonhalt306: ~halts tm306 c0.
Proof.
  solve_SBCv1 tm306(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm307 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA0LD_0RF1RB_0LC0RD").

Theorem nonhalt307: ~halts tm307 c0.
Proof.
  solve_SBCv1 tm307(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm308 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1RE").

Theorem nonhalt308: ~halts tm308 c0.
Proof.
  solve_SBCv1 tm308(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm309 := Eval compute in (TM_from_str "1LB1RE_1RC1RD_0RA1LD_---0LE_0RF1LB_0LB0RC").

Theorem nonhalt309: ~halts tm309 c0.
Proof.
  solve_SBCv1 tm309(Build_SBC_cert_v1 E A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm310 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RF_0RD0LA_0RC---").

Theorem nonhalt310: ~halts tm310 c0.
Proof.
  solve_SBCv1 tm310(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm311 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_1RD---").

Theorem nonhalt311: ~halts tm311 c0.
Proof.
  solve_SBCv1 tm311(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm312 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD0LF_0LE1RD_1RF0RF_0RA1LB").

Theorem nonhalt312: ~halts tm312 c0.
Proof.
  solve_SBCv1 tm312(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm313 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD0RF_0LD---").

Theorem nonhalt313: ~halts tm313 c0.
Proof.
  solve_SBCv1 tm313(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm314 := Eval compute in (TM_from_str "1RB1RD_0RC1LD_1LA1RE_---0LE_0RF1LA_0LA0RB").

Theorem nonhalt314: ~halts tm314 c0.
Proof.
  solve_SBCv1 tm314(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm315 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD0LB_0RC---").

Theorem nonhalt315: ~halts tm315 c0.
Proof.
  solve_SBCv1 tm315(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm316 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB0LD_0RA---").

Theorem nonhalt316: ~halts tm316 c0.
Proof.
  solve_SBCv1 tm316(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm317 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD1RF_1RD---").

Theorem nonhalt317: ~halts tm317 c0.
Proof.
  solve_SBCv1 tm317(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm318 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1LA").

Theorem nonhalt318: ~halts tm318 c0.
Proof.
  solve_SBCv1 tm318(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm319 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF0LD_0LC0RD").

Theorem nonhalt319: ~halts tm319 c0.
Proof.
  solve_SBCv1 tm319(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm320 := Eval compute in (TM_from_str "1LB1RC_0LC0RD_1RD0LE_0RA1LF_0RA1LB_---0RB").

Theorem nonhalt320: ~halts tm320 c0.
Proof.
  solve_SBCv1 tm320(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm321 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_0LC---").

Theorem nonhalt321: ~halts tm321 c0.
Proof.
  solve_SBCv1 tm321(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm322 := Eval compute in (TM_from_str "1LB1RC_0LC1RE_0RD1LB_0LE0RF_1RF0LC_0RA---").

Theorem nonhalt322: ~halts tm322 c0.
Proof.
  solve_SBCv1 tm322(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm323 := Eval compute in (TM_from_str "1LB0RF_0RC1LE_1LE1RD_1RB0LB_0LD0RA_0RC---").

Theorem nonhalt323: ~halts tm323 c0.
Proof.
  solve_SBCv1 tm323(Build_SBC_cert_v1 D C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm324 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_0LD---").

Theorem nonhalt324: ~halts tm324 c0.
Proof.
  solve_SBCv1 tm324(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm325 := Eval compute in (TM_from_str "1RB0LB_1LC1RD_---0LD_0RE1LE_0LF0RA_1RA1LC").

Theorem nonhalt325: ~halts tm325 c0.
Proof.
  solve_SBCv1 tm325(Build_SBC_cert_v1 C B[1;0;0;1] [1;1;0;1] [1;0;1;0] [1;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm326 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB0RF_0LB---").

Theorem nonhalt326: ~halts tm326 c0.
Proof.
  solve_SBCv1 tm326(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm327 := Eval compute in (TM_from_str "1LB1RC_0LC1RE_1RD1LB_0RA0LF_0RD0LC_---0RE").

Theorem nonhalt327: ~halts tm327 c0.
Proof.
  solve_SBCv1 tm327(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm328 := Eval compute in (TM_from_str "1LB1RF_0RC---_1RE1LD_0LC0RE_0RA0LA_0RD1RD").

Theorem nonhalt328: ~halts tm328 c0.
Proof.
  solve_SBCv1 tm328(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm329 := Eval compute in (TM_from_str "1RB0LC_0RC---_1LD1RE_0LE0RA_0RF1RC_0LA0RB").

Theorem nonhalt329: ~halts tm329 c0.
Proof.
  solve_SBCv1 tm329(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm330 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RB_0RA1RB").

Theorem nonhalt330: ~halts tm330 c0.
Proof.
  solve_SBCv1 tm330(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm331 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD1LD_0LE0RF_1RF1LB_0RA0LA").

Theorem nonhalt331: ~halts tm331 c0.
Proof.
  solve_SBCv1 tm331(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm332 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_0LB---").

Theorem nonhalt332: ~halts tm332 c0.
Proof.
  solve_SBCv1 tm332(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm333 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0RF").

Theorem nonhalt333: ~halts tm333 c0.
Proof.
  solve_SBCv1 tm333(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm334 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD1RF_1LD---").

Theorem nonhalt334: ~halts tm334 c0.
Proof.
  solve_SBCv1 tm334(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm335 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD1RD_0LA---").

Theorem nonhalt335: ~halts tm335 c0.
Proof.
  solve_SBCv1 tm335(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm336 := Eval compute in (TM_from_str "1RB1LC_1RC0LE_1RD0RC_1LE0RF_1LB0LE_1RA---").

Theorem nonhalt336: ~halts tm336 c0.
Proof.
  solve_SBCv1 tm336(Build_SBC_cert_v1 E C[0;0;0;1] [0;1;0;1] [0;1;0;1] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;1;0;1] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm337 := Eval compute in (TM_from_str "1LB0RE_1RC0LD_1RA1RB_0LF1LA_0RB0LA_0RA---").

Theorem nonhalt337: ~halts tm337 c0.
Proof.
  solve_SBCv1 tm337(Build_SBC_cert_v1 B A[1;1;1;1;0;0] [1;1;1;1;1;1] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [1;1;0;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm338 := Eval compute in (TM_from_str "1LB1RE_0LC1LD_1RD1LB_0RA---_0RF0LC_0LC0RD").

Theorem nonhalt338: ~halts tm338 c0.
Proof.
  solve_SBCv1 tm338(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm339 := Eval compute in (TM_from_str "1RB1RE_0RC0LB_1LD1RF_0LA0RB_0LB---_0RD1RE").

Theorem nonhalt339: ~halts tm339 c0.
Proof.
  solve_SBCv1 tm339(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm340 := Eval compute in (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA1RE_0RF0LA_0LA0RB").

Theorem nonhalt340: ~halts tm340 c0.
Proof.
  solve_SBCv1 tm340(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm341 := Eval compute in (TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD0LC").

Theorem nonhalt341: ~halts tm341 c0.
Proof.
  solve_SBCv1 tm341(Build_SBC_cert_v1 C B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [0] [1;0;0] [1;0;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm342 := Eval compute in (TM_from_str "1RB0LB_0RC1LE_1LD1RA_0RB0RF_0LA0RD_0RC---").

Theorem nonhalt342: ~halts tm342 c0.
Proof.
  solve_SBCv1 tm342(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm343 := Eval compute in (TM_from_str "1LB0LA_0LC0RE_1RD0LA_1RE---_0RF0RD_1LB0RC").

Theorem nonhalt343: ~halts tm343 c0.
Proof.
  solve_SBCv1 tm343(Build_SBC_cert_v1 B F[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm344 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LB_0LE---").

Theorem nonhalt344: ~halts tm344 c0.
Proof.
  solve_SBCv1 tm344(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm345 := Eval compute in (TM_from_str "1RB0LB_0RC0RE_1LD1RA_0LA0RF_0LC---_---0RB").

Theorem nonhalt345: ~halts tm345 c0.
Proof.
  solve_SBCv1 tm345(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm346 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_0RD1LB_0LE0RF_1RF0LA_0RA---").

Theorem nonhalt346: ~halts tm346 c0.
Proof.
  solve_SBCv1 tm346(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm347 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1LB_0RB0LD_0RA---").

Theorem nonhalt347: ~halts tm347 c0.
Proof.
  solve_SBCv1 tm347(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm348 := Eval compute in (TM_from_str "1LB1RD_0LC1RB_0LD0RB_1RE1LB_0RF---_0RA0RE").

Theorem nonhalt348: ~halts tm348 c0.
Proof.
  solve_SBCv1 tm348(Build_SBC_cert_v1 B A[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm349 := Eval compute in (TM_from_str "1RB0LF_1RC---_0RD0RB_1LE0RA_0LA0RC_1LE1RE").

Theorem nonhalt349: ~halts tm349 c0.
Proof.
  solve_SBCv1 tm349(Build_SBC_cert_v1 E D[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 3 1).
Qed.


Definition tm350 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD1RA_0RA0LB_0RF0LA_0RA---").

Theorem nonhalt350: ~halts tm350 c0.
Proof.
  solve_SBCv1 tm350(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm351 := Eval compute in (TM_from_str "1RB0LC_0RC1RF_1LD0RA_0LE0RC_0RA1LE_1RC---").

Theorem nonhalt351: ~halts tm351 c0.
Proof.
  solve_SBCv1 tm351(Build_SBC_cert_v1 D C[1;1;1;0] [0;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm352 := Eval compute in (TM_from_str "1LB---_0LC0RF_1RD1RA_0RE0LB_1LB1RC_0RD0LE").

Theorem nonhalt352: ~halts tm352 c0.
Proof.
  solve_SBCv1 tm352(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm353 := Eval compute in (TM_from_str "1RB---_1LC0RE_1RF1LD_0RE1RB_0RF0LB_1LD0RA").

Theorem nonhalt353: ~halts tm353 c0.
Proof.
  solve_SBCv1 tm353(Build_SBC_cert_v1 D B[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [1] [1] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm354 := Eval compute in (TM_from_str "1RB1LE_1RC0RB_1LD0RA_0LF0LA_0RE0LC_0RA---").

Theorem nonhalt354: ~halts tm354 c0.
Proof.
  solve_SBCv1 tm354(Build_SBC_cert_v1 D C[1;0;1;0] [1;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm355 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD1RD_0RC---").

Theorem nonhalt355: ~halts tm355 c0.
Proof.
  solve_SBCv1 tm355(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm356 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RB_0RA0LD").

Theorem nonhalt356: ~halts tm356 c0.
Proof.
  solve_SBCv1 tm356(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm357 := Eval compute in (TM_from_str "1RB0LB_0RC0LC_1LD1RE_0LA0RB_0RF---_1RA0RB").

Theorem nonhalt357: ~halts tm357 c0.
Proof.
  solve_SBCv1 tm357(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm358 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB0RF_0LB---").

Theorem nonhalt358: ~halts tm358 c0.
Proof.
  solve_SBCv1 tm358(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm359 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1RF").

Theorem nonhalt359: ~halts tm359 c0.
Proof.
  solve_SBCv1 tm359(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm360 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LE_0RA1LB_0RA1RB_---0RE").

Theorem nonhalt360: ~halts tm360 c0.
Proof.
  solve_SBCv1 tm360(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm361 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RF_0RD1RD_0RC---").

Theorem nonhalt361: ~halts tm361 c0.
Proof.
  solve_SBCv1 tm361(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm362 := Eval compute in (TM_from_str "1LB0RF_1LC1RD_0LD0RA_1RE0LE_0RB1LC_0RB---").

Theorem nonhalt362: ~halts tm362 c0.
Proof.
  solve_SBCv1 tm362(Build_SBC_cert_v1 D B[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm363 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt363: ~halts tm363 c0.
Proof.
  solve_SBCv1 tm363(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm364 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD1LB_0RA0LF_0RD0LA_---0RE").

Theorem nonhalt364: ~halts tm364 c0.
Proof.
  solve_SBCv1 tm364(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm365 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD0LF_0LE0RF_1RD1RF_0RA1RB").

Theorem nonhalt365: ~halts tm365 c0.
Proof.
  solve_SBCv1 tm365(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm366 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RE_0RC0LB_0RD1RD").

Theorem nonhalt366: ~halts tm366 c0.
Proof.
  solve_SBCv1 tm366(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm367 := Eval compute in (TM_from_str "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RF_1LD---").

Theorem nonhalt367: ~halts tm367 c0.
Proof.
  solve_SBCv1 tm367(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm368 := Eval compute in (TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LE_1LB1RF_0RB1RA").

Theorem nonhalt368: ~halts tm368 c0.
Proof.
  solve_SBCv1 tm368(Build_SBC_cert_v1 B E[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm369 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_0LD---").

Theorem nonhalt369: ~halts tm369 c0.
Proof.
  solve_SBCv1 tm369(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm370 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD1RF_0LA---").

Theorem nonhalt370: ~halts tm370 c0.
Proof.
  solve_SBCv1 tm370(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm371 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_1LA---").

Theorem nonhalt371: ~halts tm371 c0.
Proof.
  solve_SBCv1 tm371(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm372 := Eval compute in (TM_from_str "1RB0LC_0RC0RF_1LD0RA_0LE0LA_0RA1LE_1RC---").

Theorem nonhalt372: ~halts tm372 c0.
Proof.
  solve_SBCv1 tm372(Build_SBC_cert_v1 D C[1;0;1;0] [0;1;1;0] [1;0;1;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm373 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RF_0RA1RF_0RB0LD_0LE---").

Theorem nonhalt373: ~halts tm373 c0.
Proof.
  solve_SBCv1 tm373(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm374 := Eval compute in (TM_from_str "1RB1RE_0RC0LD_1LD1RA_0LA0RF_1LD---_0RB0LE").

Theorem nonhalt374: ~halts tm374 c0.
Proof.
  solve_SBCv1 tm374(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm375 := Eval compute in (TM_from_str "1LB1RE_0RC0RF_0RA1LD_0LE0RB_1RC0LC_0RA---").

Theorem nonhalt375: ~halts tm375 c0.
Proof.
  solve_SBCv1 tm375(Build_SBC_cert_v1 E A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm376 := Eval compute in (TM_from_str "1RB1LE_0RC---_0RD0RB_1LE1RA_0LF1RE_0LA0RE").

Theorem nonhalt376: ~halts tm376 c0.
Proof.
  solve_SBCv1 tm376(Build_SBC_cert_v1 E D[0;0;0;0;1;1] [0;0;1;0;1;1] [1;0;0;1;0;0] [0;0;1;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;0;1;1] [0] [1] [1;0;0] [1;0;0] 3 0).
Qed.


Definition tm377 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LD_0RA0RE_0LA---_0RA0RF").

Theorem nonhalt377: ~halts tm377 c0.
Proof.
  solve_SBCv1 tm377(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm378 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LF_0RB1RB_0RA---").

Theorem nonhalt378: ~halts tm378 c0.
Proof.
  solve_SBCv1 tm378(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm379 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB0LC_1LA---").

Theorem nonhalt379: ~halts tm379 c0.
Proof.
  solve_SBCv1 tm379(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm380 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF0LC_0LC0RD").

Theorem nonhalt380: ~halts tm380 c0.
Proof.
  solve_SBCv1 tm380(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm381 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LB_0RB1RF_0LC---").

Theorem nonhalt381: ~halts tm381 c0.
Proof.
  solve_SBCv1 tm381(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm382 := Eval compute in (TM_from_str "1RB---_0RC0RA_1LD0RE_0LE0RB_1RA0LF_1LD0LF").

Theorem nonhalt382: ~halts tm382 c0.
Proof.
  solve_SBCv1 tm382(Build_SBC_cert_v1 D C[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 7 4).
Qed.


Definition tm383 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD1LB_0RA0LB_0RF0LA_0RA---").

Theorem nonhalt383: ~halts tm383 c0.
Proof.
  solve_SBCv1 tm383(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm384 := Eval compute in (TM_from_str "1RB0LE_0RC0LF_1LD1RA_0LA---_0RC1RD_0RE0RF").

Theorem nonhalt384: ~halts tm384 c0.
Proof.
  solve_SBCv1 tm384(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm385 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA1LC").

Theorem nonhalt385: ~halts tm385 c0.
Proof.
  solve_SBCv1 tm385(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm386 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RF_0LA0RB").

Theorem nonhalt386: ~halts tm386 c0.
Proof.
  solve_SBCv1 tm386(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm387 := Eval compute in (TM_from_str "1RB1LE_0RC0LC_1LD1RF_0RA---_0LA0RB_0RE1RE").

Theorem nonhalt387: ~halts tm387 c0.
Proof.
  solve_SBCv1 tm387(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm388 := Eval compute in (TM_from_str "1RB1LC_1RC0LE_1RD0RC_1LB0RF_1LB0LE_1RA---").

Theorem nonhalt388: ~halts tm388 c0.
Proof.
  solve_SBCv1 tm388(Build_SBC_cert_v1 E C[0;0;0;1] [0;1;0;1] [0;1;0;1] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;1;0;1] [0;0;0] [0;1;0] [0;1] [0;1] 7 4).
Qed.


Definition tm389 := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF---_1RA0RB").

Theorem nonhalt389: ~halts tm389 c0.
Proof.
  solve_SBCv1 tm389(Build_SBC_cert_v1 A B[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 0).
Qed.


Definition tm390 := Eval compute in (TM_from_str "1RB0LB_0RC0RE_1LD1RA_0LA0RF_0LF---_1LD0RB").

Theorem nonhalt390: ~halts tm390 c0.
Proof.
  solve_SBCv1 tm390(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm391 := Eval compute in (TM_from_str "1LB1RC_0LC0RF_1RD0LD_0RA1LE_0RC0RB_0RA---").

Theorem nonhalt391: ~halts tm391 c0.
Proof.
  solve_SBCv1 tm391(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm392 := Eval compute in (TM_from_str "1RB0RB_0RC0RF_1LD1RE_0LE0RA_1RB0LB_0LC---").

Theorem nonhalt392: ~halts tm392 c0.
Proof.
  solve_SBCv1 tm392(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm393 := Eval compute in (TM_from_str "1RB0LC_0RC---_1LD1RE_0LE0RA_0RF1LD_0LA0RB").

Theorem nonhalt393: ~halts tm393 c0.
Proof.
  solve_SBCv1 tm393(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm394 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD0LE").

Theorem nonhalt394: ~halts tm394 c0.
Proof.
  solve_SBCv1 tm394(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm395 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RF_0RD0LB_0RC---").

Theorem nonhalt395: ~halts tm395 c0.
Proof.
  solve_SBCv1 tm395(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm396 := Eval compute in (TM_from_str "1RB1RE_0RC0LC_1LD1RF_0LA0RB_1LD---_0RD1RE").

Theorem nonhalt396: ~halts tm396 c0.
Proof.
  solve_SBCv1 tm396(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm397 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD0RF_1LA---").

Theorem nonhalt397: ~halts tm397 c0.
Proof.
  solve_SBCv1 tm397(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm398 := Eval compute in (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD0LB_0LC---").

Theorem nonhalt398: ~halts tm398 c0.
Proof.
  solve_SBCv1 tm398(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm399 := Eval compute in (TM_from_str "1RB0LE_0RC1LF_1LD1RA_0LA0RB_0RC0LB_---0RD").

Theorem nonhalt399: ~halts tm399 c0.
Proof.
  solve_SBCv1 tm399(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm400 := Eval compute in (TM_from_str "1LB1RE_0LC1LE_1RD0LD_0RA0LA_0RF---_1RC0RD").

Theorem nonhalt400: ~halts tm400 c0.
Proof.
  solve_SBCv1 tm400(Build_SBC_cert_v1 C D[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 3 1).
Qed.


Definition tm401 := Eval compute in (TM_from_str "1RB0RE_0RC1LD_1LD1RA_0LA0RF_0LF---_0LB0RB").

Theorem nonhalt401: ~halts tm401 c0.
Proof.
  solve_SBCv1 tm401(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm402 := Eval compute in (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0RD").

Theorem nonhalt402: ~halts tm402 c0.
Proof.
  solve_SBCv1 tm402(Build_SBC_cert_v1 B C[0;0;1;0] [1;0;1;0] [0;1;0;1] [1;0;0;0;0;0;0;0;0;0;0;0] [] [] [0;1;0;0;0] [1;1;0;1;0] [0;0;0] [0;1;0] [0;1] [0;1] 7 1).
Qed.


Definition tm403 := Eval compute in (TM_from_str "1LB1RC_0LC0RE_1RD0LD_0RA1LB_0RD0RF_0LE---").

Theorem nonhalt403: ~halts tm403 c0.
Proof.
  solve_SBCv1 tm403(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm404 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LE---_0RF1LF_0LA0RB").

Theorem nonhalt404: ~halts tm404 c0.
Proof.
  solve_SBCv1 tm404(Build_SBC_cert_v1 D C[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm405 := Eval compute in (TM_from_str "1RB---_0RC0RA_1LD0RE_0LE0RB_1RA0LF_1LD1RD").

Theorem nonhalt405: ~halts tm405 c0.
Proof.
  solve_SBCv1 tm405(Build_SBC_cert_v1 D C[0;1;0;1;1;0] [0;1;0;0;1;0] [1;0;0;1;0;0] [0;0;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0;0] [0;1;1;0] [0] [1] [1;0;0] [1;0;0] 7 4).
Qed.


Definition tm406 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LF_0RA0LD").

Theorem nonhalt406: ~halts tm406 c0.
Proof.
  solve_SBCv1 tm406(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm407 := Eval compute in (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD0LA_0LC---").

Theorem nonhalt407: ~halts tm407 c0.
Proof.
  solve_SBCv1 tm407(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm408 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB0LC_0RA1LB").

Theorem nonhalt408: ~halts tm408 c0.
Proof.
  solve_SBCv1 tm408(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm409 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB0RF_0LB---").

Theorem nonhalt409: ~halts tm409 c0.
Proof.
  solve_SBCv1 tm409(Build_SBC_cert_v1 B A[0;0;0;1] [0;1;0;1] [1;0;1;0] [0;1;0;0;0;0;0;0;0;0;0;0] [] [] [1;0;0] [0;1;1] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm410 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LF_0RB1RB_0RA---").

Theorem nonhalt410: ~halts tm410 c0.
Proof.
  solve_SBCv1 tm410(Build_SBC_cert_v1 C A[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 1).
Qed.


Definition tm411 := Eval compute in (TM_from_str "1RB0LB_0RC0RF_1LD1RE_0LA0RB_0RD1RD_0LC---").

Theorem nonhalt411: ~halts tm411 c0.
Proof.
  solve_SBCv1 tm411(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm412 := Eval compute in (TM_from_str "1RB0RE_0RC0LB_1LD1RF_0LA0RB_1LA---_0RD0RE").

Theorem nonhalt412: ~halts tm412 c0.
Proof.
  solve_SBCv1 tm412(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm413 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LA_0LA---").

Theorem nonhalt413: ~halts tm413 c0.
Proof.
  solve_SBCv1 tm413(Build_SBC_cert_v1 A C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


Definition tm414 := Eval compute in (TM_from_str "1RB0RF_1RC0LC_0RD1LE_1LE1RB_0LB0RA_0RD---").

Theorem nonhalt414: ~halts tm414 c0.
Proof.
  solve_SBCv1 tm414(Build_SBC_cert_v1 B D[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 7 3).
Qed.


Definition tm415 := Eval compute in (TM_from_str "1LB0RF_0LC---_1LD1RE_0LE0RA_1RF0LF_0RC0RB").

Theorem nonhalt415: ~halts tm415 c0.
Proof.
  solve_SBCv1 tm415(Build_SBC_cert_v1 E C[0;0;1;0] [1;0;1;0] [1;0;1;0] [1;0;0;0;0;0;0;0;0;0;0;0] [0] [0] [1;0;0] [1;1;0] [0] [1] [1;0] [1;0] 3 0).
Qed.


