
From BusyCoq Require Import Individual62.
From BusyCoq Require Import BECv1.
Require Import ZArith.
Require Import String.


Definition tm0 := Eval compute in (TM_from_str "1RB0RF_0LC0RB_1RA1LD_0LC0LE_1LA0LF_---1LE").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_BECv1 tm0(Build_BEC_cert_v1 E B A B [0] [1] [1] [0] [1] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;0;1] [1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_0LE0RD_1RC0RD_0LA1LE_1LA---").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_BECv1 tm1(Build_BEC_cert_v1 F D B D [0] [1] [1] [0] [1] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;0;1] [1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD1RC_1LE0LE_0LF1LE_1LA---").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_BECv1 tm2(Build_BEC_cert_v1 E C A B [0] [1] [1] [] [] [1] [1] [0] [] [] [0;0] [1;0] [1;0;1;1;1] [1;1;0;0] 2 1 2).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1LB---_1LC0LA_1RD1LA_1RE0RD_0LE1LF_0LB0RF").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_BECv1 tm3(Build_BEC_cert_v1 A F A D [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [0;1] [0;0] [0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1] 2 0 1).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1LB0RA_1RC0LD_---1RA_0LF1LE_1RF0LC_1LB1LF").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_BECv1 tm4(Build_BEC_cert_v1 F A F A [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [] [] [] [] [1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB0RA_1LC0LF_1LE1LD_0LE---_0RB1LE_1RA1LF").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_BECv1 tm5(Build_BEC_cert_v1 E B F A [0] [1] [1] [] [] [1;1] [1;1] [0] [1;1] [1;0] [0] [1;1;0] [1;1;0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1RB1LE_0LC1RD_1LA1LC_1RB0RD_0LF0LE_1LB---").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_BECv1 tm6(Build_BEC_cert_v1 E B C D [0;0] [1;1] [1;1] [] [] [1;1;1;0] [1;0;0;1] [0;0] [] [] [1;0;0;0;0;0] [1;1;1;1;1;0] [1;1;1;1;1;0;1;1;1;0;1;1;1;0] [1;0;0;1;1;0;0;0;0;0] 1 0 0).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB1LF_0LC0RB_1RD1LE_1RB1LD_---0LF_1LC0LA").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_BECv1 tm7(Build_BEC_cert_v1 F B D B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1LB0RD_1LC1RE_0LD1LF_0RE0LC_1RA0RA_0LB---").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_BECv1 tm8(Build_BEC_cert_v1 D A B D [0;0;0] [0;1;0] [0;1;1] [] [] [1;0;1;1;1] [1;0;0;0;0] [0;0] [0] [0] [1;0;0] [0;1;1;1] [0;1;1;1;1;0;1;1;1;1;0;1;1;1] [1;0;0;0;0;1;0;0] 1 0 0).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1LE1LD_0LB0RF_1LF---_1RA1LF").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_BECv1 tm9(Build_BEC_cert_v1 B A F A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0;0] [1;1;1] [1;1;1;0;1;1;0;1;1] [0;1;0;0;0;0] 1 0 0).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1LE1LD_0LB0RE_1RF1LE_---0RA").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_BECv1 tm10(Build_BEC_cert_v1 B A E A [0] [1] [1] [0] [1] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1] [1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1RB1LA_0RC1LF_1LD0RB_1LE---_0LF1LB_0LA1RC").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_BECv1 tm11(Build_BEC_cert_v1 A B A B [0;0] [0;1] [0;1] [0;0] [1;1] [1;1] [1;1] [0;0] [1;1] [0;0] [1;1;1;1] [1;1;1;1] [0;1;0;0;1;1;1;1;1;1] [1;1;1;1;1;1;1;1] 2 0 1).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1LB0LF_1RC1LF_0LD0RC_0RB1LE_0LA---_1LA---").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_BECv1 tm12(Build_BEC_cert_v1 A C A C [0;0;0] [0;1;0] [1;1;1] [] [] [0;1] [1;0] [0] [1] [0] [1;0;1;0] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [1;0;1;0;1;0;1;0] 2 1 2).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1LB0LE_1RC1LB_0LE0RD_1RC0RD_1LA1LF_0LA---").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_BECv1 tm13(Build_BEC_cert_v1 E D B D [0] [1] [1] [0] [1] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;0;1] [1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1RB0RA_1LC0LF_0LF1LD_0LE---_0RB1LE_1RA1LF").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_BECv1 tm14(Build_BEC_cert_v1 E B F A [0] [1] [1] [] [] [1;1] [1;1] [0] [1;1] [1;0] [0] [1;1;0] [1;1;0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1LB0RA_1RC0LD_---1RA_0LF1LE_1LF0LC_1LB1LF").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_BECv1 tm15(Build_BEC_cert_v1 F A F A [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [] [] [] [] [1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1LB0LF_1RC1LF_0LE0RD_1RC0RD_0LA1LE_1LA---").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_BECv1 tm16(Build_BEC_cert_v1 F D F D [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1RB0RA_1LC0LF_1RE1LD_0LB---_1RA1LE_0LB0RE").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_BECv1 tm17(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1LB0LF_1RC1LE_1RD1LC_0LB0RD_1RA0LA_---1LA").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_BECv1 tm18(Build_BEC_cert_v1 A D C D [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1RB0RA_1LC0LF_1RE1LD_0LE---_0RB1LE_1RA1LF").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_BECv1 tm19(Build_BEC_cert_v1 E B F A [0] [1] [1] [] [] [1;1] [1;1] [0] [1;1] [1;0] [0] [1;1;0] [1;1;0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1LB0RA_1LC0LE_1RD0LF_1LA0RE_0RD1RA_0LC---").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_BECv1 tm20(Build_BEC_cert_v1 F A E A [0;0;0] [1;0;1] [1;1;1] [0] [0] [0;1;1;1;1;1;1] [0;0;0;0;1;0;1] [0;0;0;0] [0;0] [0;0] [0;0] [1;1;1] [1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1] [0;0;0;0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1LB0RA_0LC1LB_1RD1LE_1RA0LA_---1LF_1RB0LD").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_BECv1 tm21(Build_BEC_cert_v1 B A B A [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1LB1LE_1RC1LD_0RC0RD_1RE1LB_1LA0LF_---0LB").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_BECv1 tm22(Build_BEC_cert_v1 D D B C [0;0] [1;0] [0;0] [] [] [1;1;1;1] [1;1;1;1] [0;0] [1] [0] [1] [1;1] [1;1;1;1;1;1;1;1;1;1] [1;1;1;1;1] 1 0 0).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD1LE_0LA1LC_1RB1RD_0LE---").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_BECv1 tm23(Build_BEC_cert_v1 F B E B [0] [1] [1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1LB---_1LC0LF_1RD0LC_0RD0RE_1LA1LC_1RE1LF").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_BECv1 tm24(Build_BEC_cert_v1 F E C D [0] [1] [0] [] [] [1;1] [1;1] [0] [1] [0] [1;1;0] [0;1;1;1] [0;1;1;1;1;1;1;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1LB0LF_1RC1RD_0LD0RC_0RB1LE_0LA1LB_1LA---").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_BECv1 tm25(Build_BEC_cert_v1 A C B C [0] [1] [1] [0] [1] [0;1] [1;0] [0] [1] [0] [1;0;0] [1;0;1] [1;0;1;0;1;0;1] [1;0;1;0;0] 1 0 0).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1LB0RA_0LC1LB_1RD1LD_1RA1LE_1RB0LF_---0LA").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_BECv1 tm26(Build_BEC_cert_v1 B A B A [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_0LD0RC_0RB1LE_0LA---_1LA---").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_BECv1 tm27(Build_BEC_cert_v1 A C B C [0] [1] [1] [] [] [0;1] [1;0] [0] [1] [0] [1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [1;0;1;0;0] 1 0 0).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1RD0RC_0LD1LE_0LA1RC_1LA---").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_BECv1 tm28(Build_BEC_cert_v1 F C B C [0] [1] [1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_1LD1LB_1RE---_1RA1LE_0LC0RE").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_BECv1 tm29(Build_BEC_cert_v1 C A E A [0] [1] [1] [] [] [0;1] [1;0] [0] [] [] [0;0] [1;1] [1;1;0;1;0;1] [1;0;0;0] 1 0 0).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1RB1LF_1LC0RB_0RC1RD_0LD1LE_0LF1LA_0LA---").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_BECv1 tm30(Build_BEC_cert_v1 F B F B [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;1] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm31 := Eval compute in (TM_from_str "1RB1RB_0LC1LE_0RD0LB_1RA0RD_1LF0RD_1LB---").

Theorem nonhalt31: ~halts tm31 c0.
Proof.
  solve_BECv1 tm31(Build_BEC_cert_v1 F D F D [0;0;0] [0;1;0] [1;1;1] [0] [1] [0;0;1;1;1] [0;0;1;0;0] [0;0] [1;1] [0;0] [] [1] [1;0;0;1;1;1;0;0;1;1;1] [0;0;1;0;0] 1 0 0).
Qed.


Definition tm32 := Eval compute in (TM_from_str "1LB0LF_1RC1LE_1RD1LC_0LB0RD_0RC0LA_---1LA").

Theorem nonhalt32: ~halts tm32 c0.
Proof.
  solve_BECv1 tm32(Build_BEC_cert_v1 A D C D [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm33 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1RE1LD_0LB0RF_1RA1LE_1RA---").

Theorem nonhalt33: ~halts tm33 c0.
Proof.
  solve_BECv1 tm33(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm34 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1LE1LD_0LB0RF_1RF---_1RA1LF").

Theorem nonhalt34: ~halts tm34 c0.
Proof.
  solve_BECv1 tm34(Build_BEC_cert_v1 B A F A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0;0] [1;1;1] [1;1;1;0;1;1;0;1;1] [0;1;0;0;0;0] 1 0 0).
Qed.


Definition tm35 := Eval compute in (TM_from_str "1LB0LE_1LC---_1LD0LD_1RA1LD_1RF1LE_0RA0RF").

Theorem nonhalt35: ~halts tm35 c0.
Proof.
  solve_BECv1 tm35(Build_BEC_cert_v1 D A E F [0] [1] [1] [] [] [1;1] [1;1] [0] [1] [0] [0] [1;0] [1;0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm36 := Eval compute in (TM_from_str "1RB1RD_1RC1LB_0LA0RC_1LE0LD_1LB0LF_---1LD").

Theorem nonhalt36: ~halts tm36 c0.
Proof.
  solve_BECv1 tm36(Build_BEC_cert_v1 D C B C [0] [1] [1] [] [] [1;0;1] [0;1;1] [0;0] [] [] [0;0] [1;1] [1;1;1;0;1;1;0;1] [0;1;1;0;0] 1 0 0).
Qed.


Definition tm37 := Eval compute in (TM_from_str "1LB1LE_1RC0LB_0LA1RD_0LA0RA_0RD1LF_1LA---").

Theorem nonhalt37: ~halts tm37 c0.
Proof.
  solve_BECv1 tm37(Build_BEC_cert_v1 A A A A [0;0;0] [1;1;0] [1;1;1] [0] [1] [0;1;1;1;1] [0;1;1;0;0] [0;0] [1;1;1] [0;0;0] [] [1;1] [1;1;0;1;1;1;1;0;1;1;1;1] [0;1;1;0;0] 1 0 0).
Qed.


Definition tm38 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1RD0RC_0LE0RC_0LA1LE_1LA---").

Theorem nonhalt38: ~halts tm38 c0.
Proof.
  solve_BECv1 tm38(Build_BEC_cert_v1 F C B C [0] [1] [1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm39 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1RE1LD_0LB0RF_1RA1LE_0RE---").

Theorem nonhalt39: ~halts tm39 c0.
Proof.
  solve_BECv1 tm39(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm40 := Eval compute in (TM_from_str "1LB0LD_1RC1LB_1RD0RC_0RE0LF_1LF---_0LA0RB").

Theorem nonhalt40: ~halts tm40 c0.
Proof.
  solve_BECv1 tm40(Build_BEC_cert_v1 A C B C [0] [1] [1] [] [] [0;1] [1;0] [0;0;0] [] [] [0] [1] [1;0;1;0;1;0;1] [1;0;1;0;0] 2 1 2).
Qed.


Definition tm41 := Eval compute in (TM_from_str "1LB1LE_1RC0LB_0LC1RD_0LA0RA_0RD1LF_1LA---").

Theorem nonhalt41: ~halts tm41 c0.
Proof.
  solve_BECv1 tm41(Build_BEC_cert_v1 A A A A [0;0;0] [1;1;0] [1;1;1] [0] [1] [0;1;1;1;1] [0;1;1;0;0] [0;0] [1;1;1] [0;0;0] [] [1;1] [1;1;0;1;1;1;1;0;1;1;1;1] [0;1;1;0;0] 1 0 0).
Qed.


Definition tm42 := Eval compute in (TM_from_str "1LB0RA_0LC1LB_1RD1LE_1RA0LA_---1LF_1LB0LD").

Theorem nonhalt42: ~halts tm42 c0.
Proof.
  solve_BECv1 tm42(Build_BEC_cert_v1 B A B A [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm43 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_0LD0RC_0RB1LE_1RD0LA_1LA---").

Theorem nonhalt43: ~halts tm43 c0.
Proof.
  solve_BECv1 tm43(Build_BEC_cert_v1 A C B C [0] [1] [1] [] [] [0;1] [1;0] [0] [1] [0] [1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [1;0;1;0;0] 1 0 0).
Qed.


Definition tm44 := Eval compute in (TM_from_str "1LB0RA_0LC1LB_1RD1LE_1RA0LA_---1LF_0RF0LD").

Theorem nonhalt44: ~halts tm44 c0.
Proof.
  solve_BECv1 tm44(Build_BEC_cert_v1 B A B A [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm45 := Eval compute in (TM_from_str "1RB1LA_1RC0RB_0LD1LA_0LE1LC_1RB1LF_0LE---").

Theorem nonhalt45: ~halts tm45 c0.
Proof.
  solve_BECv1 tm45(Build_BEC_cert_v1 F B A B [0] [1] [1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm46 := Eval compute in (TM_from_str "1LB0LE_1LC---_1RD0LD_0RF0LA_0RC0LC_1LB0RF").

Theorem nonhalt46: ~halts tm46 c0.
Proof.
  solve_BECv1 tm46(Build_BEC_cert_v1 C F C F [0;0] [1;0] [1;1] [0] [1] [1;1;0;1] [0;1;0;0] [0;0] [1;1] [0;0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;0;0] 1 0 0).
Qed.


Definition tm47 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD1LE_0LA1LC_1RB1RD_0LA---").

Theorem nonhalt47: ~halts tm47 c0.
Proof.
  solve_BECv1 tm47(Build_BEC_cert_v1 F B E B [0] [1] [1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm48 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_0LD0RC_1RB1LE_---0LA_1LD1LA").

Theorem nonhalt48: ~halts tm48 c0.
Proof.
  solve_BECv1 tm48(Build_BEC_cert_v1 A C B C [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm49 := Eval compute in (TM_from_str "1RB0LF_1RC1LB_0LD0RC_1RB1RE_1LA0LE_---1LE").

Theorem nonhalt49: ~halts tm49 c0.
Proof.
  solve_BECv1 tm49(Build_BEC_cert_v1 E C B C [0] [1] [1] [] [] [1;0;1] [0;1;1] [0;0] [] [] [0;0] [1;1] [1;1;1;0;1;1;0;1] [0;1;1;0;0] 1 0 0).
Qed.


Definition tm50 := Eval compute in (TM_from_str "1LB0RA_0LC0LF_1LD0RA_1RE1LB_---0RC_0RA0LD").

Theorem nonhalt50: ~halts tm50 c0.
Proof.
  solve_BECv1 tm50(Build_BEC_cert_v1 C A C A [0;0] [1;1] [1;1] [0;0] [0;1] [1;1;0;1] [0;1;1;0] [0;0] [0;1] [0;0] [] [] [1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm51 := Eval compute in (TM_from_str "1RB1RD_1RC1LB_0LA0RC_1LE0LD_1LA0LF_---1LD").

Theorem nonhalt51: ~halts tm51 c0.
Proof.
  solve_BECv1 tm51(Build_BEC_cert_v1 D C B C [0] [1] [1] [] [] [1;0;1] [0;1;1] [0;0] [] [] [0;0;0] [1;1;1] [1;1;1;1;0;1;1;0;1] [0;1;1;0;0;0] 1 0 0).
Qed.


Definition tm52 := Eval compute in (TM_from_str "1RB1LA_1RC0RB_0LD1LA_0LE1LC_0LF1LD_1RA---").

Theorem nonhalt52: ~halts tm52 c0.
Proof.
  solve_BECv1 tm52(Build_BEC_cert_v1 D B A B [0] [1] [1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;0;0] [1;1;1;1;0;1] [1;1;1;1;0;1;0;1;0;1] [0;1;0;1;0;0;0] 1 0 0).
Qed.


Definition tm53 := Eval compute in (TM_from_str "1LB0LF_0LC1LB_1RD1LD_1RE1LA_1LB0RE_---0LE").

Theorem nonhalt53: ~halts tm53 c0.
Proof.
  solve_BECv1 tm53(Build_BEC_cert_v1 B E B E [0;0] [1;1] [1;1] [] [] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm54 := Eval compute in (TM_from_str "1RB0RA_1RC0RA_0LD1LE_0RA0LC_1LF0RB_1LC---").

Theorem nonhalt54: ~halts tm54 c0.
Proof.
  solve_BECv1 tm54(Build_BEC_cert_v1 F A F A [0;0;0] [0;1;0] [1;1;1] [] [] [0;0;1;1;1] [0;0;1;0;0] [0;0] [1;1] [0;0] [] [1;1] [1;1;0;0;1;1;1;0;0;1;1;1] [0;0;1;0;0] 1 0 0).
Qed.


Definition tm55 := Eval compute in (TM_from_str "1LB---_0LC0LF_1RD1LC_0RE0RD_1LA0LC_1RE1LF").

Theorem nonhalt55: ~halts tm55 c0.
Proof.
  solve_BECv1 tm55(Build_BEC_cert_v1 F E C D [0] [1] [1] [] [] [1;1] [1;1] [0] [1] [0] [1;1;0] [1;0;1;1] [1;0;1;1;1;1;1;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm56 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1RE1LD_0LB0RE_1RF1LE_---0RA").

Theorem nonhalt56: ~halts tm56 c0.
Proof.
  solve_BECv1 tm56(Build_BEC_cert_v1 B A E A [0] [1] [1] [0] [1] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1] [1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm57 := Eval compute in (TM_from_str "1LB0LE_1LC---_1LD1LA_0RE1LE_0LA1RF_0RE0RF").

Theorem nonhalt57: ~halts tm57 c0.
Proof.
  solve_BECv1 tm57(Build_BEC_cert_v1 A F B F [0;0;0] [0;1;0] [1;1;1] [] [] [0;1;1;1;1] [0;0;0;1;0] [0;0] [] [] [0] [1] [1;0;1;1;1;1;0;1;1;1;1] [0;0;0;1;0;0] 1 0 0).
Qed.


Definition tm58 := Eval compute in (TM_from_str "1RB1LA_0LC0RB_1RA1LD_0LC0LE_1LA0LF_---1LE").

Theorem nonhalt58: ~halts tm58 c0.
Proof.
  solve_BECv1 tm58(Build_BEC_cert_v1 E B A B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm59 := Eval compute in (TM_from_str "1LB0RA_0LC0RE_1RD1LE_1RA0LA_---1LF_1LB0LD").

Theorem nonhalt59: ~halts tm59 c0.
Proof.
  solve_BECv1 tm59(Build_BEC_cert_v1 B A B A [0;0] [1;1] [1;1] [0] [1] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [] [1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm60 := Eval compute in (TM_from_str "1RB1RD_1RC0RB_0LD1LA_0LE1LC_0RF1LF_0LA---").

Theorem nonhalt60: ~halts tm60 c0.
Proof.
  solve_BECv1 tm60(Build_BEC_cert_v1 F B A B [0] [1] [1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm61 := Eval compute in (TM_from_str "1LB0LF_1RC1RD_0LD0RC_0RB1LE_0LA1LF_1LA---").

Theorem nonhalt61: ~halts tm61 c0.
Proof.
  solve_BECv1 tm61(Build_BEC_cert_v1 A C A C [0;0;0] [0;1;0] [1;1;1] [] [] [0;1] [1;0] [0] [1] [0] [1;0;1;0] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [1;0;1;0;1;0;1;0] 2 1 2).
Qed.


Definition tm62 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD1RC_1RE0LE_0LF1LE_1LA---").

Theorem nonhalt62: ~halts tm62 c0.
Proof.
  solve_BECv1 tm62(Build_BEC_cert_v1 E C A B [0] [1] [1] [] [] [1] [1] [0] [] [] [0;0] [1;0] [1;0;1;1;1] [1;1;0;0] 2 1 2).
Qed.


Definition tm63 := Eval compute in (TM_from_str "1LB1LE_1LC---_1LD0LD_1RA1LD_1RF0LE_0RF0RA").

Theorem nonhalt63: ~halts tm63 c0.
Proof.
  solve_BECv1 tm63(Build_BEC_cert_v1 D A E F [0] [1] [0] [] [] [1;1] [1;1] [0] [1] [0] [0] [0;1] [0;1;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm64 := Eval compute in (TM_from_str "1RB1RD_1RC0RB_0LD1LA_0LE1LC_0LF1LD_1RA---").

Theorem nonhalt64: ~halts tm64 c0.
Proof.
  solve_BECv1 tm64(Build_BEC_cert_v1 D B A B [0] [1] [1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [0;1;0;1;0;0;0] 1 0 0).
Qed.


Definition tm65 := Eval compute in (TM_from_str "1LB1LE_1RC0LB_1LE1RD_0LA0RA_0RD1LF_1LA---").

Theorem nonhalt65: ~halts tm65 c0.
Proof.
  solve_BECv1 tm65(Build_BEC_cert_v1 B A F A [0;0;0] [0;1;1] [1;1;1] [0] [1] [0;1;1;1;1] [0;0;0;1;1] [0;0] [0] [0] [0] [1] [1;0;1;1;1;1;0;1;1;1;1] [0;0;0;1;1;0] 1 0 0).
Qed.


Definition tm66 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_0LC1LD_0LA1RE_1RC0RE_1LA---").

Theorem nonhalt66: ~halts tm66 c0.
Proof.
  solve_BECv1 tm66(Build_BEC_cert_v1 F E B E [0] [1] [1] [0] [1] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;0;1] [1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm67 := Eval compute in (TM_from_str "1LB0RA_0LC0LF_1LD0RA_1RE1LB_---1RF_0RA0LD").

Theorem nonhalt67: ~halts tm67 c0.
Proof.
  solve_BECv1 tm67(Build_BEC_cert_v1 C A C A [0;0] [1;1] [1;1] [0] [0] [1;1;0;1] [0;1;1;0] [0;0] [0;1] [0;0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm68 := Eval compute in (TM_from_str "1RB0RD_0LC1LE_0RD0LB_1RA1LA_1LF0RA_1LB---").

Theorem nonhalt68: ~halts tm68 c0.
Proof.
  solve_BECv1 tm68(Build_BEC_cert_v1 F D F D [0;0;0] [0;1;0] [1;1;1] [0] [1] [0;0;1;1;1] [0;0;1;0;0] [0;0] [1;1] [0;0] [] [1] [1;0;0;1;1;1;0;0;1;1;1] [0;0;1;0;0] 1 0 0).
Qed.


Definition tm69 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LF1LE_1RB1LA_0LA---").

Theorem nonhalt69: ~halts tm69 c0.
Proof.
  solve_BECv1 tm69(Build_BEC_cert_v1 F B F B [0;0;0] [0;0;1] [1;1;1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 2 3).
Qed.


Definition tm70 := Eval compute in (TM_from_str "1LB0LF_1RC0RF_0LD0RC_1RB1LE_---0LA_0RD1LA").

Theorem nonhalt70: ~halts tm70 c0.
Proof.
  solve_BECv1 tm70(Build_BEC_cert_v1 A C B C [0] [1] [1] [0] [1] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;0;1] [1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm71 := Eval compute in (TM_from_str "1LB0LC_1LC1RA_1RD1LA_0LE0RD_1RC1LF_---0LA").

Theorem nonhalt71: ~halts tm71 c0.
Proof.
  solve_BECv1 tm71(Build_BEC_cert_v1 A D A D [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;1;1] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [1;1;1;1;1;1;0;1] 2 1 2).
Qed.


Definition tm72 := Eval compute in (TM_from_str "1RB1LA_1RC0RB_0LD0LB_0LE1LD_1RA0LF_---1LE").

Theorem nonhalt72: ~halts tm72 c0.
Proof.
  solve_BECv1 tm72(Build_BEC_cert_v1 E C A B [0] [1] [1] [] [] [0;1] [1;1] [0] [1;0;1] [1;0;0] [1;1;0] [1;1;0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm73 := Eval compute in (TM_from_str "1LB0LE_1LC---_1RD0LD_1RA1LD_1RF1LE_0RA0RF").

Theorem nonhalt73: ~halts tm73 c0.
Proof.
  solve_BECv1 tm73(Build_BEC_cert_v1 D A E F [0] [1] [1] [] [] [1;1] [1;1] [0] [1] [0] [0] [1;0] [1;0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm74 := Eval compute in (TM_from_str "1RB0RA_1RC1LE_0LD1LB_0RA0LC_1LF1RA_1LC---").

Theorem nonhalt74: ~halts tm74 c0.
Proof.
  solve_BECv1 tm74(Build_BEC_cert_v1 E A E A [0;0;0;0] [0;0;1;0] [1;1;1;1] [] [] [0;0;1;1;1;1] [0;0;0;1;0;0] [0;0] [1;1] [0;0] [] [1;1] [1;1;0;0;1;1;1;1;0;0;1;1;1;1] [0;0;0;1;0;0] 1 0 0).
Qed.


Definition tm75 := Eval compute in (TM_from_str "1LB0LF_1RC1LF_0LC1LD_0LA1RE_1RC0RE_1LA---").

Theorem nonhalt75: ~halts tm75 c0.
Proof.
  solve_BECv1 tm75(Build_BEC_cert_v1 F E F E [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm76 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD0LA_1LE1LF_---0LF_1RC1LF").

Theorem nonhalt76: ~halts tm76 c0.
Proof.
  solve_BECv1 tm76(Build_BEC_cert_v1 F C A B [0] [1] [1] [] [] [1;1] [1;1] [0] [1] [0] [1;0] [1;0;1] [1;0;1;1;1;1;1] [1;1;1;0] 1 0 0).
Qed.


Definition tm77 := Eval compute in (TM_from_str "1RB0LE_0RC1LA_1RD1LF_0LB0RD_1LC0LF_1LE---").

Theorem nonhalt77: ~halts tm77 c0.
Proof.
  solve_BECv1 tm77(Build_BEC_cert_v1 E D E D [0;0;0] [0;1;0] [1;1;1] [] [] [0;1] [1;0] [0] [1] [0] [1;0;1;0] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [1;0;1;0;1;0;1;0] 2 1 2).
Qed.


Definition tm78 := Eval compute in (TM_from_str "1LB1RA_1LC1LF_1LD0LE_1RE0LD_0RE0RA_---0LC").

Theorem nonhalt78: ~halts tm78 c0.
Proof.
  solve_BECv1 tm78(Build_BEC_cert_v1 C A D E [0] [1] [0] [] [] [1;1] [1;1] [0] [] [] [0] [1] [1;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm79 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_1LE1LD_0LC0LB_1RA1LE_---0RE").

Theorem nonhalt79: ~halts tm79 c0.
Proof.
  solve_BECv1 tm79(Build_BEC_cert_v1 C A E A [0] [1] [1] [] [] [0;1] [1;0] [0] [] [] [0] [1] [1;0;1;0;1] [1;0;0] 1 0 0).
Qed.


Definition tm80 := Eval compute in (TM_from_str "1RB0RA_1RC0RA_0LD1LE_0RA0LC_1LF0RA_1LC---").

Theorem nonhalt80: ~halts tm80 c0.
Proof.
  solve_BECv1 tm80(Build_BEC_cert_v1 F A F A [0;0;0] [0;1;0] [1;1;1] [] [] [0;0;1;1;1] [0;0;1;0;0] [0;0] [1;1] [0;0] [] [1;1] [1;1;0;0;1;1;1;0;0;1;1;1] [0;0;1;0;0] 1 0 0).
Qed.


Definition tm81 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LE1RB_1LA0LF_1LE---").

Theorem nonhalt81: ~halts tm81 c0.
Proof.
  solve_BECv1 tm81(Build_BEC_cert_v1 F B F B [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm82 := Eval compute in (TM_from_str "1LB0LE_0LC0RB_1RD1LA_1RB0RF_1LD0LF_---1LE").

Theorem nonhalt82: ~halts tm82 c0.
Proof.
  solve_BECv1 tm82(Build_BEC_cert_v1 E B D B [0] [1] [1] [0] [1] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;0;1] [1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm83 := Eval compute in (TM_from_str "1LB0LF_1RC1LF_1RD0RC_0LE0RC_0LA1LE_1LA---").

Theorem nonhalt83: ~halts tm83 c0.
Proof.
  solve_BECv1 tm83(Build_BEC_cert_v1 F C F C [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm84 := Eval compute in (TM_from_str "1RB0LA_0LC1RC_0LD0RD_1LA1LE_0RC1LF_1LD---").

Theorem nonhalt84: ~halts tm84 c0.
Proof.
  solve_BECv1 tm84(Build_BEC_cert_v1 F D F D [0;0;0] [0;1;1] [1;1;1] [0] [1] [0;1;1;1;1] [0;0;1;1;0] [0;0] [1;1] [0;0] [] [1] [1;0;1;1;1;1;0;1;1;1;1] [0;0;1;1;0] 1 0 0).
Qed.


Definition tm85 := Eval compute in (TM_from_str "1LB0LE_0LC0RB_1RD1LA_1RB1LD_1LC0LF_---1LE").

Theorem nonhalt85: ~halts tm85 c0.
Proof.
  solve_BECv1 tm85(Build_BEC_cert_v1 E B D B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm86 := Eval compute in (TM_from_str "1LB1LE_1RC0LB_1RD1RD_0LA0RA_0RD1LF_1LA---").

Theorem nonhalt86: ~halts tm86 c0.
Proof.
  solve_BECv1 tm86(Build_BEC_cert_v1 F A F A [0;0;0] [0;1;1] [1;1;1] [0] [1] [0;1;1;1;1] [0;0;1;1;0] [0;0] [1;1] [0;0] [] [1] [1;0;1;1;1;1;0;1;1;1;1] [0;0;1;1;0] 1 0 0).
Qed.


Definition tm87 := Eval compute in (TM_from_str "1RB0RA_1LC0LF_1LE1LD_0LB---_1RA1LE_0LB0RE").

Theorem nonhalt87: ~halts tm87 c0.
Proof.
  solve_BECv1 tm87(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm88 := Eval compute in (TM_from_str "1LB0LF_0LC0RD_1RD1LD_1RE1LA_1LB0RE_---0LE").

Theorem nonhalt88: ~halts tm88 c0.
Proof.
  solve_BECv1 tm88(Build_BEC_cert_v1 B E B E [0;0] [1;1] [1;1] [0] [1] [1;1;0;1] [0;1;1;0] [0;0] [1] [0] [] [] [1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm89 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1RD0RC_0LD1LE_0LA0RE_1LA---").

Theorem nonhalt89: ~halts tm89 c0.
Proof.
  solve_BECv1 tm89(Build_BEC_cert_v1 F E B C [0] [1] [1] [] [] [0;1] [0;1] [0] [0;1] [0;0] [0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;0] 1 0 0).
Qed.


Definition tm90 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1RD0RC_0LD1LE_0LA0RB_1LA---").

Theorem nonhalt90: ~halts tm90 c0.
Proof.
  solve_BECv1 tm90(Build_BEC_cert_v1 F C B C [0] [1] [1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm91 := Eval compute in (TM_from_str "1LB0RA_1LC---_1RD0LF_0RE0LE_1RF0LD_0RA0LA").

Theorem nonhalt91: ~halts tm91 c0.
Proof.
  solve_BECv1 tm91(Build_BEC_cert_v1 C A C A [0;0] [1;0] [1;1] [0] [1] [1;1;0;1] [0;1;0;0] [0;0] [1;1] [0;0] [] [1] [1;1;1;0;1;1;1;0;1] [0;1;0;0] 1 0 0).
Qed.


Definition tm92 := Eval compute in (TM_from_str "1LB1RA_1RC1LF_0LD1LC_1RE1LD_0RA0RE_---0LC").

Theorem nonhalt92: ~halts tm92 c0.
Proof.
  solve_BECv1 tm92(Build_BEC_cert_v1 C A D E [0] [1] [1] [] [] [1;1] [1;1] [0] [] [] [0] [0] [0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm93 := Eval compute in (TM_from_str "1RB0LA_1RC---_1LD0RF_0LA1LE_1LA1LC_0LC1RE").

Theorem nonhalt93: ~halts tm93 c0.
Proof.
  solve_BECv1 tm93(Build_BEC_cert_v1 A E C E [0;0;0] [0;1;1] [1;1;1] [1] [1] [0;1;1;1;1] [0;0;0;1;1] [0;0] [0;0] [1;0] [0] [1;1] [1;1;0;1;1;1;1;0;1;1;1;1] [0;0;0;1;1;0] 1 0 0).
Qed.


Definition tm94 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1LD1LB_1RA1LF_0LC0RD_1LC---").

Theorem nonhalt94: ~halts tm94 c0.
Proof.
  solve_BECv1 tm94(Build_BEC_cert_v1 C A C A [0;0;0] [0;1;0] [1;1;1] [] [] [0;1] [1;0] [0] [] [] [1;0] [0;1] [0;1;0;1;0;1;0;1] [1;0;1;0;1;0] 2 2 3).
Qed.


Definition tm95 := Eval compute in (TM_from_str "1LB1LE_1LC---_1RD0LD_1RA1LD_1RF0LE_0RF0RA").

Theorem nonhalt95: ~halts tm95 c0.
Proof.
  solve_BECv1 tm95(Build_BEC_cert_v1 D A E F [0] [1] [0] [] [] [1;1] [1;1] [0] [1] [0] [0] [0;1] [0;1;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm96 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD0LA_1LE1RF_---0LF_1RC1LF").

Theorem nonhalt96: ~halts tm96 c0.
Proof.
  solve_BECv1 tm96(Build_BEC_cert_v1 F C A B [0] [1] [1] [] [] [1;1] [1;1] [0] [1] [0] [1;0] [1;0;1] [1;0;1;1;1;1;1] [1;1;1;0] 1 0 0).
Qed.


Definition tm97 := Eval compute in (TM_from_str "1RB1LA_0LC0RB_1RA1LD_1LB0LE_1RA0LF_---1LE").

Theorem nonhalt97: ~halts tm97 c0.
Proof.
  solve_BECv1 tm97(Build_BEC_cert_v1 E B A B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;1;1;0] [1;1;0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [1;1;1;1;1;1;0] 1 0 0).
Qed.


Definition tm98 := Eval compute in (TM_from_str "1RB1LA_1RC0RB_0LC1LD_0LE1RA_0LF---_1RB1LE").

Theorem nonhalt98: ~halts tm98 c0.
Proof.
  solve_BECv1 tm98(Build_BEC_cert_v1 E B A B [0] [1] [1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm99 := Eval compute in (TM_from_str "1RB1RC_1RC0RB_0LC1LD_0LE1LA_0LF---_1RB1LE").

Theorem nonhalt99: ~halts tm99 c0.
Proof.
  solve_BECv1 tm99(Build_BEC_cert_v1 E B A B [0] [1] [1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm100 := Eval compute in (TM_from_str "1LB0LE_0LC0RB_1RD1LA_1RB1LD_1LD0LF_---1LE").

Theorem nonhalt100: ~halts tm100 c0.
Proof.
  solve_BECv1 tm100(Build_BEC_cert_v1 E B D B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm101 := Eval compute in (TM_from_str "1RB---_0LC0LD_1LE1LD_0LB0RE_1RF1LE_0RA0RF").

Theorem nonhalt101: ~halts tm101 c0.
Proof.
  solve_BECv1 tm101(Build_BEC_cert_v1 C F E F [0] [1] [1] [] [] [0;0;1] [1;0;0] [0;0] [] [] [0] [1] [1;0;0;1;0;0;1] [1;0;0;0] 1 0 0).
Qed.


Definition tm102 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1LE1LD_0LB0RF_1RA1LE_0RE---").

Theorem nonhalt102: ~halts tm102 c0.
Proof.
  solve_BECv1 tm102(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm103 := Eval compute in (TM_from_str "1RB1LD_1RC1LB_0LA0RC_1RC0LE_1LA0LF_---1LE").

Theorem nonhalt103: ~halts tm103 c0.
Proof.
  solve_BECv1 tm103(Build_BEC_cert_v1 E C B C [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm104 := Eval compute in (TM_from_str "1LB1RA_1LC1LF_0LD1LC_1RE1LD_0RA0RE_---0LC").

Theorem nonhalt104: ~halts tm104 c0.
Proof.
  solve_BECv1 tm104(Build_BEC_cert_v1 C A D E [0] [1] [1] [] [] [1;1] [1;1] [0] [] [] [0] [0] [0;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm105 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD0LA_1LE1LF_---0LF_1RC1LD").

Theorem nonhalt105: ~halts tm105 c0.
Proof.
  solve_BECv1 tm105(Build_BEC_cert_v1 D C A B [0] [1] [1] [] [] [1;1] [1;1] [0] [1] [0] [1;0] [1;0;1] [1;0;1;1;1;1;1] [1;1;1;0] 1 0 0).
Qed.


Definition tm106 := Eval compute in (TM_from_str "1LB0LF_1RC0RE_0LD0RC_0RB1LE_0LA1LA_1LA---").

Theorem nonhalt106: ~halts tm106 c0.
Proof.
  solve_BECv1 tm106(Build_BEC_cert_v1 A C B C [0] [1] [1] [0] [1] [0;1] [1;0] [0] [1] [0] [1;0;0] [1;0;1] [1;0;1;0;1;0;1] [1;0;1;0;0] 1 0 0).
Qed.


Definition tm107 := Eval compute in (TM_from_str "1RB1LF_1LC0RD_0LF1LA_1RE0RD_0LE1LC_0LA---").

Theorem nonhalt107: ~halts tm107 c0.
Proof.
  solve_BECv1 tm107(Build_BEC_cert_v1 F D F D [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;1] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm108 := Eval compute in (TM_from_str "1RB0RA_1LC0LF_1LE0LD_1LB---_1RA1LE_0LB0RC").

Theorem nonhalt108: ~halts tm108 c0.
Proof.
  solve_BECv1 tm108(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [1;0;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;1;0;1;1;0;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm109 := Eval compute in (TM_from_str "1LB0LF_1RC1LE_1RD1LC_0LB0RD_0RD0LA_---1LA").

Theorem nonhalt109: ~halts tm109 c0.
Proof.
  solve_BECv1 tm109(Build_BEC_cert_v1 A D C D [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm110 := Eval compute in (TM_from_str "1LB1LF_0LC0RB_1RD1LE_1RB0RA_---0LF_1LD0LA").

Theorem nonhalt110: ~halts tm110 c0.
Proof.
  solve_BECv1 tm110(Build_BEC_cert_v1 F B D B [0] [1] [1] [0] [1] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;0;1] [1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm111 := Eval compute in (TM_from_str "1RB0RA_1LC0LD_1LE1LD_0LB0RF_1RA1LE_1RA---").

Theorem nonhalt111: ~halts tm111 c0.
Proof.
  solve_BECv1 tm111(Build_BEC_cert_v1 B A E A [0] [1] [1] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [1;1] [1;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm112 := Eval compute in (TM_from_str "1LB1LF_0LC0RB_1RD1LE_1RB1LD_---0LF_1LD0LA").

Theorem nonhalt112: ~halts tm112 c0.
Proof.
  solve_BECv1 tm112(Build_BEC_cert_v1 F B D B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [1;1;1;1;0] 1 0 0).
Qed.


Definition tm113 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_1LD1LB_1LE---_1RA1LE_0LC0RE").

Theorem nonhalt113: ~halts tm113 c0.
Proof.
  solve_BECv1 tm113(Build_BEC_cert_v1 C A E A [0] [1] [1] [] [] [0;1] [1;0] [0] [] [] [0;0] [1;1] [1;1;0;1;0;1] [1;0;0;0] 1 0 0).
Qed.


Definition tm114 := Eval compute in (TM_from_str "1RB1LD_0RC0RB_1LC0LD_1LA1LE_0LF0RE_0LD---").

Theorem nonhalt114: ~halts tm114 c0.
Proof.
  solve_BECv1 tm114(Build_BEC_cert_v1 A C A B [0;0] [1;0] [1;1] [] [] [1;1;1] [1;1;1] [0] [1;0] [0;0] [1;1;1] [1;0;1;1;1] [1;0;1;1;1;1;1;1;1;1;1] [1;1;1;1;1;1] 1 0 0).
Qed.


Definition tm115 := Eval compute in (TM_from_str "1RB---_1LC0LD_0LE1LD_0LB0RE_1RF0LE_0RF0RA").

Theorem nonhalt115: ~halts tm115 c0.
Proof.
  solve_BECv1 tm115(Build_BEC_cert_v1 B A E F [0] [1] [0] [] [] [0;1;1] [0;1;0] [0;0] [] [] [0;0] [0;1] [0;1;0;1;1;0;1;1] [0;1;0;0;0] 1 0 0).
Qed.


Definition tm116 := Eval compute in (TM_from_str "1RB1LA_1RC0RB_0LC1LD_0LE1LA_0LF---_1RB1LE").

Theorem nonhalt116: ~halts tm116 c0.
Proof.
  solve_BECv1 tm116(Build_BEC_cert_v1 E B A B [0] [1] [1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm117 := Eval compute in (TM_from_str "1LB0RA_0LC0LF_1LD0RA_1RE1LB_---0RC_1RB0LD").

Theorem nonhalt117: ~halts tm117 c0.
Proof.
  solve_BECv1 tm117(Build_BEC_cert_v1 C A C A [0;0] [1;1] [1;1] [0;0] [0;1] [1;1;0;1] [0;1;1;0] [0;0] [0;1] [0;0] [] [] [1;1;0;1;1;1;0;1] [0;1;1;0] 1 0 0).
Qed.


Definition tm118 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA0RF_---1LE_1LA0LE_0LA0RF").

Theorem nonhalt118: ~halts tm118 c0.
Proof.
  solve_BECv1 tm118(Build_BEC_cert_v1 E F B F [0] [1] [1] [0] [1] [1;0;1] [0;1;1] [0;0] [] [] [0;0] [1] [1;1;0;1;1;0;1] [0;1;1;0;0] 1 0 0).
Qed.


Definition tm119 := Eval compute in (TM_from_str "1RB1LD_0RC0RB_1LC0LD_1LA1LE_0LF0RE_1LB---").

Theorem nonhalt119: ~halts tm119 c0.
Proof.
  solve_BECv1 tm119(Build_BEC_cert_v1 A C A B [0;0] [1;0] [1;1] [] [] [1;1;1] [1;1;1] [0] [1;0] [0;0] [1;1;1] [1;0;1;1;1] [1;0;1;1;1;1;1;1;1;1;1] [1;1;1;1;1;1] 1 0 0).
Qed.


Definition tm120 := Eval compute in (TM_from_str "1RB1LF_1LC0RD_0LF1LA_0RE0RD_0LB0LA_0LA---").

Theorem nonhalt120: ~halts tm120 c0.
Proof.
  solve_BECv1 tm120(Build_BEC_cert_v1 F D F D [0;0;0] [0;0;1] [1;1;1] [] [] [0;1] [0;1] [0] [1] [0] [0;1;0;1] [1;0;1;0;1] [1;1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 1 2).
Qed.


Definition tm121 := Eval compute in (TM_from_str "1RB1LA_0LC0RB_1RA1LD_0LB0LE_1RA0LF_---1LE").

Theorem nonhalt121: ~halts tm121 c0.
Proof.
  solve_BECv1 tm121(Build_BEC_cert_v1 E B A B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;1;1;0] [1;1;0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [1;1;1;1;1;1;0] 1 0 0).
Qed.


Definition tm122 := Eval compute in (TM_from_str "1LB1LF_1RC1LE_1RD1LC_0LB0RD_---0LF_1RC0LA").

Theorem nonhalt122: ~halts tm122 c0.
Proof.
  solve_BECv1 tm122(Build_BEC_cert_v1 F D C D [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;1;1;0] [1;1;0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [1;1;1;1;1;1;0] 1 0 0).
Qed.


Definition tm123 := Eval compute in (TM_from_str "1LB1RA_1RC1LF_1LD1LC_1RE0LD_0RE0RA_---0LC").

Theorem nonhalt123: ~halts tm123 c0.
Proof.
  solve_BECv1 tm123(Build_BEC_cert_v1 C A D E [0] [1] [0] [] [] [1;1] [1;1] [0] [] [] [0] [1] [1;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm124 := Eval compute in (TM_from_str "1LB0LE_1RC1LB_1RD0RC_0LE0RC_1LA1LF_0LA---").

Theorem nonhalt124: ~halts tm124 c0.
Proof.
  solve_BECv1 tm124(Build_BEC_cert_v1 E C B C [0] [1] [1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm125 := Eval compute in (TM_from_str "1LB---_1RC1LA_0RC1RD_1LD1LE_0LA1RF_1RC0LF").

Theorem nonhalt125: ~halts tm125 c0.
Proof.
  solve_BECv1 tm125(Build_BEC_cert_v1 A D F C [0] [1] [0] [] [] [1;1] [0;1] [0] [1;1] [1;0] [0;1;0;0] [0;0;0;1;1;1] [0;0;0;1;1;1;1;1;1;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm126 := Eval compute in (TM_from_str "1RB0RA_1RC0RE_0LD1LE_0RA0LC_1LF0RA_1LC---").

Theorem nonhalt126: ~halts tm126 c0.
Proof.
  solve_BECv1 tm126(Build_BEC_cert_v1 F A F A [0;0;0] [0;1;0] [1;1;1] [0] [1] [0;0;1;1;1] [0;0;1;0;0] [0;0] [1;1] [0;0] [] [1] [1;0;0;1;1;1;0;0;1;1;1] [0;0;1;0;0] 1 0 0).
Qed.


Definition tm127 := Eval compute in (TM_from_str "1LB1RA_1LC1LF_1LD1LC_1RE0LD_0RE0RA_---0LC").

Theorem nonhalt127: ~halts tm127 c0.
Proof.
  solve_BECv1 tm127(Build_BEC_cert_v1 C A D E [0] [1] [0] [] [] [1;1] [1;1] [0] [] [] [0] [1] [1;1;1;1;1] [1;1;0] 1 0 0).
Qed.


Definition tm128 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LC1LD_0LF1LE_0RE1LA_0LA---").

Theorem nonhalt128: ~halts tm128 c0.
Proof.
  solve_BECv1 tm128(Build_BEC_cert_v1 F B F B [0;0;0] [0;0;1] [1;1;1] [0] [1] [0;1] [0;1] [0] [1] [0] [0;1;0;1] [0;1;0;1] [1;1;1;0;0;1;0;1;0;1] [0;1;0;1;0;1;0;1] 2 2 3).
Qed.


Definition tm129 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_0RD0RC_0LE1LB_1LD0LF_1LA---").

Theorem nonhalt129: ~halts tm129 c0.
Proof.
  solve_BECv1 tm129(Build_BEC_cert_v1 F C B C [0] [1] [1] [] [] [0;1] [0;1] [0] [] [] [0;1;0;0] [1;1;0;1] [1;1;0;1;0;1;0;1] [0;1;0;1;0;0] 1 0 0).
Qed.


Definition tm130 := Eval compute in (TM_from_str "1RB1LF_1RC1LE_1RD1LC_0LB0RD_---0LF_1LB0LA").

Theorem nonhalt130: ~halts tm130 c0.
Proof.
  solve_BECv1 tm130(Build_BEC_cert_v1 F D C D [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.


Definition tm131 := Eval compute in (TM_from_str "1RB1LA_0LC0RB_1RA1LD_0LC0LE_1LC0LF_---1LE").

Theorem nonhalt131: ~halts tm131 c0.
Proof.
  solve_BECv1 tm131(Build_BEC_cert_v1 E B A B [0] [1] [1] [] [] [0;1] [1;1] [0] [1] [0] [1;1;0;0] [1;1;1;0;1] [1;1;1;0;1;0;1;0;1] [1;1;1;1;0;0] 1 0 0).
Qed.
