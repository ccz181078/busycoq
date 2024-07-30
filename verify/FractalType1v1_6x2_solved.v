
From BusyCoq Require Import Individual62.
From BusyCoq Require Import FractalType1v1.
Require Import ZArith.
Require Import String.


Definition tm0 := Eval compute in (TM_from_str "1LB0LF_0LC1RE_0LD---_1RA0RD_0RA0RE_1LF0LB").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_FractalType1v1 tm0(Build_FractalType1_cert_v1 F E [0;1;0] [0] [0] [1] [1] [0] 2 1 5 3 1 0 0 7).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1LB0LF_0LC0RC_1LD---_1RE0RB_0RA0RE_1LF0LB").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_FractalType1v1 tm1(Build_FractalType1_cert_v1 F E [0;1;0] [0] [0] [1] [1] [0] 2 1 5 3 1 0 0 7).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB0RA_0LC0LD_1RA1LD_0LE1LE_1RC1LF_---1LD").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_FractalType1v1 tm2(Build_FractalType1_cert_v1 E A [0;1;1] [0] [0] [1] [1] [0] 2 1 3 1 2 0 3 10).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1RD1LB_1RA---_1RD1LF_1LF1LC").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_FractalType1v1 tm3(Build_FractalType1_cert_v1 F A [0;1;1] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1RB0RA_1LB0LC_0LD1LD_1RE1LF_1RA1LC_---1LC").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_FractalType1v1 tm4(Build_FractalType1_cert_v1 D A [0;1;1] [0] [0] [1] [1] [0] 2 1 9 7 6 0 1 22).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_1RE1LD").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_FractalType1v1 tm5(Build_FractalType1_cert_v1 D A [1;1] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0RE1LD_1LB---_1RE1LF_1LC1RA").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_FractalType1v1 tm6(Build_FractalType1_cert_v1 C A [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB1RC_0RA0LA_0RD0RC_1RE0LF_0LB---_1LF1LA").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_FractalType1v1 tm7(Build_FractalType1_cert_v1 F C [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0RE1LD_1LB---_1RF1LF_1LC0RA").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_FractalType1v1 tm8(Build_FractalType1_cert_v1 C A [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB1LE_0RC1LA_1RD1LF_1RE0RD_0LB0LC_1LB---").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_FractalType1v1 tm9(Build_FractalType1_cert_v1 B D [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB0LF_0LC1RE_0RB0LD_1LC---_0RA0RE_1LF1LD").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_FractalType1v1 tm10(Build_FractalType1_cert_v1 F E [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1LB---_0RC1LE_1LA1RD_0RE0RD_0LA0LF_1LF1LC").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_FractalType1v1 tm11(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 5 3 4 0 3 16).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1RB0RA_0RC0RB_1LD0LE_0LA---_1LE1LF_0LD0LA").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_FractalType1v1 tm12(Build_FractalType1_cert_v1 E B [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_---0LD_1RE1LC_1RA1LF_0RF1LD").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_FractalType1v1 tm13(Build_FractalType1_cert_v1 D A [1;1] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1RB---_1RC0RB_0LD0LE_1RA1LC_0RC1LF_1LF1LD").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_FractalType1v1 tm14(Build_FractalType1_cert_v1 F B [0;1;1] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD0LA_0RA1LE_1LC0RB_1LD---").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_FractalType1v1 tm15(Build_FractalType1_cert_v1 D B [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1RB1LE_1RC1LF_1RD0RC_0LE0LB_---0LA_1LA1LA").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_FractalType1v1 tm16(Build_FractalType1_cert_v1 A C [1;1] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1LB1RD_1LC---_0RA1LE_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_FractalType1v1 tm17(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 9 7 7 0 2 25).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB---_1LD1LF_1RF1LE").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_FractalType1v1 tm18(Build_FractalType1_cert_v1 F A [1;0;0] [0] [0] [1] [1] [0] 2 1 3 1 2 0 3 10).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1RB1LB_1RC1LE_0RD0RC_0LE0LF_0LA---_1LF1LB").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_FractalType1v1 tm19(Build_FractalType1_cert_v1 F C [0;1;1] [0] [0] [1] [] [] 2 1 7 5 4 0 1 16).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB---_1LB1LF_1LF1LD").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_FractalType1v1 tm20(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1RB0LB_0RC1LA_1RD1LF_1RE0RD_0LA0LC_1LB---").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_FractalType1v1 tm21(Build_FractalType1_cert_v1 B D [1;0] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB---_1RA1LF_1LF1LD").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_FractalType1v1 tm22(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1RB0RA_0LB0LC_1RD1LE_1RA1LC_0RD1LF_0LE---").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_FractalType1v1 tm23(Build_FractalType1_cert_v1 E A [1;0] [0] [0] [1] [1] [0] 1 1 4 3 2 0 0 5).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1RB1LE_1RC1LF_1RD0RC_0LE0LB_---0LA_1LA0RB").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_FractalType1v1 tm24(Build_FractalType1_cert_v1 A C [1;1] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1LB---_1LC1RD_0RB1LE_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_FractalType1v1 tm25(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 9 7 7 0 2 25).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1RB0RA_1LC0LE_0RD0LB_1LB1RA_---1LF_1LF1LD").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_FractalType1v1 tm26(Build_FractalType1_cert_v1 F A [1;0;0] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD0LA_0LE0RC_0RA1LD_1LE---").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_FractalType1v1 tm27(Build_FractalType1_cert_v1 E B [1;0] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_1LF1LD_1RE0LE_---1RA_0RF1LC").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_FractalType1v1 tm28(Build_FractalType1_cert_v1 F A [1;1] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1RB0RA_0LC0LD_1RA1LD_1LE1LF_0LF---_1RC1LC").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_FractalType1v1 tm29(Build_FractalType1_cert_v1 F A [0;0;1;1] [0] [0] [1] [1] [0] 3 1 8 5 6 0 4 33).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1RB0RA_0RC0LF_0LD1RA_0LE---_1LE1LF_1LB0RD").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_FractalType1v1 tm30(Build_FractalType1_cert_v1 E A [1;0] [0] [0] [1] [] [] 1 1 4 3 2 0 0 5).
Qed.


Definition tm31 := Eval compute in (TM_from_str "1LB0RF_0LC---_1RC0RD_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt31: ~halts tm31 c0.
Proof.
  solve_FractalType1v1 tm31(Build_FractalType1_cert_v1 F D [0;1;1] [0] [0] [1] [1] [0] 2 1 11 9 7 0 0 25).
Qed.


Definition tm32 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0RE1RD_1LB---_1RA1LF_1LF1LD").

Theorem nonhalt32: ~halts tm32 c0.
Proof.
  solve_FractalType1v1 tm32(Build_FractalType1_cert_v1 F A [1;0;0] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm33 := Eval compute in (TM_from_str "1LB---_0LC0LD_0RD1LB_1RE1LF_1RB0RE_1LF1LA").

Theorem nonhalt33: ~halts tm33 c0.
Proof.
  solve_FractalType1v1 tm33(Build_FractalType1_cert_v1 F E [0;1;0] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm34 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD0LA_0RA1LE_1LC1LC_1LD---").

Theorem nonhalt34: ~halts tm34 c0.
Proof.
  solve_FractalType1v1 tm34(Build_FractalType1_cert_v1 D B [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm35 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0LD0LD_0RE1LC_1RA1LF_1LD---").

Theorem nonhalt35: ~halts tm35 c0.
Proof.
  solve_FractalType1v1 tm35(Build_FractalType1_cert_v1 D A [1;0] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm36 := Eval compute in (TM_from_str "1RB0RA_0RC0RB_1LD0LE_0LA---_1LE1LF_0LD1LA").

Theorem nonhalt36: ~halts tm36 c0.
Proof.
  solve_FractalType1v1 tm36(Build_FractalType1_cert_v1 E B [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm37 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_1LF1LD_1RE0LE_---1RA_1LF1LC").

Theorem nonhalt37: ~halts tm37 c0.
Proof.
  solve_FractalType1v1 tm37(Build_FractalType1_cert_v1 F A [1;1] [0] [0] [1] [1] [0] 1 1 2 1 1 0 1 3).
Qed.


Definition tm38 := Eval compute in (TM_from_str "1LB---_0LC1LA_1RC0RD_0RE0RD_0LA0LF_1LF1LB").

Theorem nonhalt38: ~halts tm38 c0.
Proof.
  solve_FractalType1v1 tm38(Build_FractalType1_cert_v1 F D [0;0;1;1] [0] [0] [1] [] [] 3 1 9 6 5 0 2 29).
Qed.


Definition tm39 := Eval compute in (TM_from_str "1LB0LE_0LC---_1RD0RC_0RA0RD_1LE1RF_0LB1LF").

Theorem nonhalt39: ~halts tm39 c0.
Proof.
  solve_FractalType1v1 tm39(Build_FractalType1_cert_v1 E D [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm40 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD0LA_0RA1LE_1LC0RD_1LD---").

Theorem nonhalt40: ~halts tm40 c0.
Proof.
  solve_FractalType1v1 tm40(Build_FractalType1_cert_v1 D B [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm41 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_1RD1RA_0LB---_1LB1LF_1LF1LE").

Theorem nonhalt41: ~halts tm41 c0.
Proof.
  solve_FractalType1v1 tm41(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm42 := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD---_1RE0RD_0RF0RE_1LC0LB").

Theorem nonhalt42: ~halts tm42 c0.
Proof.
  solve_FractalType1v1 tm42(Build_FractalType1_cert_v1 B E [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm43 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB---_1LD1LF_1LF1LD").

Theorem nonhalt43: ~halts tm43 c0.
Proof.
  solve_FractalType1v1 tm43(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [] [] 1 1 3 2 2 0 1 5).
Qed.


Definition tm44 := Eval compute in (TM_from_str "1RB0RA_0RC0RB_1LD0LE_0LA---_1LE1LF_0LD0RE").

Theorem nonhalt44: ~halts tm44 c0.
Proof.
  solve_FractalType1v1 tm44(Build_FractalType1_cert_v1 E B [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm45 := Eval compute in (TM_from_str "1LB0LE_0LC---_1RD1RC_0RA0RD_1LE1LF_0LB1LF").

Theorem nonhalt45: ~halts tm45 c0.
Proof.
  solve_FractalType1v1 tm45(Build_FractalType1_cert_v1 E D [0;0;1;1] [0] [0] [1] [] [] 3 1 7 4 3 0 2 21).
Qed.


Definition tm46 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB---_0RC1LF_1LF1LD").

Theorem nonhalt46: ~halts tm46 c0.
Proof.
  solve_FractalType1v1 tm46(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm47 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_0LD1RA_1LB---_1LD1LF_1LF1LE").

Theorem nonhalt47: ~halts tm47 c0.
Proof.
  solve_FractalType1v1 tm47(Build_FractalType1_cert_v1 F A [0;1;0] [0] [0] [1] [] [] 2 1 3 1 2 0 3 10).
Qed.


Definition tm48 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1RC1LD_0LB0RA_---1LF_1LF1LC").

Theorem nonhalt48: ~halts tm48 c0.
Proof.
  solve_FractalType1v1 tm48(Build_FractalType1_cert_v1 F A [0;0;1;1] [0] [0] [1] [] [] 3 1 4 1 1 0 3 13).
Qed.


Definition tm49 := Eval compute in (TM_from_str "1LB1LA_0LC---_1RC0RD_0RE0RD_0LA0LF_1LF1RA").

Theorem nonhalt49: ~halts tm49 c0.
Proof.
  solve_FractalType1v1 tm49(Build_FractalType1_cert_v1 F D [0;0;1;1] [0] [0] [1] [] [] 3 1 14 11 9 0 1 45).
Qed.


Definition tm50 := Eval compute in (TM_from_str "1LB---_0RC0LA_1LA1RD_0RE0RD_0LA0LF_1LF1LC").

Theorem nonhalt50: ~halts tm50 c0.
Proof.
  solve_FractalType1v1 tm50(Build_FractalType1_cert_v1 F D [1;0;0] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm51 := Eval compute in (TM_from_str "1LB0LE_0LC---_1RD1RC_0RA0RD_1LE1RF_0LB1LF").

Theorem nonhalt51: ~halts tm51 c0.
Proof.
  solve_FractalType1v1 tm51(Build_FractalType1_cert_v1 E D [0;0;1;1] [0] [0] [1] [] [] 3 1 7 4 3 0 2 21).
Qed.


Definition tm52 := Eval compute in (TM_from_str "1LB1RD_1LC---_0RA0LA_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt52: ~halts tm52 c0.
Proof.
  solve_FractalType1v1 tm52(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 6 4 4 0 2 16).
Qed.


Definition tm53 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_1RD1LB_1RA---_1RE1LF_1LF1LC").

Theorem nonhalt53: ~halts tm53 c0.
Proof.
  solve_FractalType1v1 tm53(Build_FractalType1_cert_v1 F A [0;1;1] [0] [0] [1] [] [] 2 1 5 3 3 0 2 13).
Qed.


Definition tm54 := Eval compute in (TM_from_str "1LB---_0RC0LD_1LA1RD_0RE0RD_0LA0LF_1LF1LC").

Theorem nonhalt54: ~halts tm54 c0.
Proof.
  solve_FractalType1v1 tm54(Build_FractalType1_cert_v1 F D [1;0;0] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


Definition tm55 := Eval compute in (TM_from_str "1LB1LA_0LC---_1RC0RD_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt55: ~halts tm55 c0.
Proof.
  solve_FractalType1v1 tm55(Build_FractalType1_cert_v1 F D [0;0;1;1] [0] [0] [1] [] [] 3 1 14 11 9 0 1 45).
Qed.


Definition tm56 := Eval compute in (TM_from_str "1LB---_0RC1RE_1LA1RD_0RE0RD_0LA0LF_1LF1LC").

Theorem nonhalt56: ~halts tm56 c0.
Proof.
  solve_FractalType1v1 tm56(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 7 5 4 0 1 16).
Qed.


Definition tm57 := Eval compute in (TM_from_str "1RB0RA_0LC0LD_---1LD_0LE1LE_1RF1LC_1RA1LD").

Theorem nonhalt57: ~halts tm57 c0.
Proof.
  solve_FractalType1v1 tm57(Build_FractalType1_cert_v1 E A [0;1;1] [0] [0] [1] [1] [0] 2 1 3 1 2 0 3 10).
Qed.


Definition tm58 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_0LD0LA_0RA1LE_1LC1LA_1LD---").

Theorem nonhalt58: ~halts tm58 c0.
Proof.
  solve_FractalType1v1 tm58(Build_FractalType1_cert_v1 D B [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm59 := Eval compute in (TM_from_str "1RB0RA_0RC0LD_0LD1RA_1LB1LE_1LE1LF_1LB---").

Theorem nonhalt59: ~halts tm59 c0.
Proof.
  solve_FractalType1v1 tm59(Build_FractalType1_cert_v1 E A [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm60 := Eval compute in (TM_from_str "1LB0RA_0RC1LD_1RA1RD_0LB0LE_---1LF_1LF0LC").

Theorem nonhalt60: ~halts tm60 c0.
Proof.
  solve_FractalType1v1 tm60(Build_FractalType1_cert_v1 F A [1;0;0] [0] [0] [1] [1] [0] 2 1 3 1 1 0 2 7).
Qed.


Definition tm61 := Eval compute in (TM_from_str "1LB1LB_0LC---_1RC0RD_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt61: ~halts tm61 c0.
Proof.
  solve_FractalType1v1 tm61(Build_FractalType1_cert_v1 F D [0;1;1] [0] [0] [1] [1] [0] 2 1 11 9 7 0 0 25).
Qed.


Definition tm62 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0RE1LD_1LB---_1RA1LF_1LC---").

Theorem nonhalt62: ~halts tm62 c0.
Proof.
  solve_FractalType1v1 tm62(Build_FractalType1_cert_v1 C A [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm63 := Eval compute in (TM_from_str "1RB0RA_0RC0LD_0LD1RA_1LB0RE_0LF---_1LF1LD").

Theorem nonhalt63: ~halts tm63 c0.
Proof.
  solve_FractalType1v1 tm63(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [] [] 1 1 2 1 1 0 1 3).
Qed.


Definition tm64 := Eval compute in (TM_from_str "1RB0RA_0RC0RB_1LD0LE_0LA---_1LE1LF_0LD0RB").

Theorem nonhalt64: ~halts tm64 c0.
Proof.
  solve_FractalType1v1 tm64(Build_FractalType1_cert_v1 E B [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm65 := Eval compute in (TM_from_str "1LB1RD_1LC---_0RA1RE_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt65: ~halts tm65 c0.
Proof.
  solve_FractalType1v1 tm65(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 4 2 2 0 2 10).
Qed.


Definition tm66 := Eval compute in (TM_from_str "1LB1RD_1LC---_0RA0LB_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt66: ~halts tm66 c0.
Proof.
  solve_FractalType1v1 tm66(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 5 3 3 0 2 13).
Qed.


Definition tm67 := Eval compute in (TM_from_str "1LB0LE_0LC---_1RD0RC_0RA0RD_1LE1LF_0LB---").

Theorem nonhalt67: ~halts tm67 c0.
Proof.
  solve_FractalType1v1 tm67(Build_FractalType1_cert_v1 E D [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm68 := Eval compute in (TM_from_str "1LB---_0RC0LC_1LA1RD_0RE0RD_0LA0LF_1LF1LC").

Theorem nonhalt68: ~halts tm68 c0.
Proof.
  solve_FractalType1v1 tm68(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 3 1 2 0 3 10).
Qed.


Definition tm69 := Eval compute in (TM_from_str "1RB0RA_1LC0LE_0RD0LD_1LB1RA_---1LF_1LF1LD").

Theorem nonhalt69: ~halts tm69 c0.
Proof.
  solve_FractalType1v1 tm69(Build_FractalType1_cert_v1 F A [0;1;0] [0] [0] [1] [] [] 2 1 3 1 2 0 3 10).
Qed.


Definition tm70 := Eval compute in (TM_from_str "1RB0RA_0RC0LE_1RD1RA_0LB---_1LB1LF_1RF1LE").

Theorem nonhalt70: ~halts tm70 c0.
Proof.
  solve_FractalType1v1 tm70(Build_FractalType1_cert_v1 F A [1;0] [0] [0] [1] [1] [0] 1 1 5 4 3 0 0 7).
Qed.


Definition tm71 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0LD1LB_1RD1LA_---1LF_1LF1LC").

Theorem nonhalt71: ~halts tm71 c0.
Proof.
  solve_FractalType1v1 tm71(Build_FractalType1_cert_v1 F A [0;0;1;1] [0] [0] [1] [] [] 3 1 4 1 1 0 3 13).
Qed.


Definition tm72 := Eval compute in (TM_from_str "1RB0RA_0RC0RB_1LD0LE_0LA---_1LE1LF_0LD0LD").

Theorem nonhalt72: ~halts tm72 c0.
Proof.
  solve_FractalType1v1 tm72(Build_FractalType1_cert_v1 E B [0;1;0] [0] [0] [1] [] [] 2 1 5 3 1 0 0 7).
Qed.


Definition tm73 := Eval compute in (TM_from_str "1LB1RD_1LC---_0RA0LD_0RE0RD_0LA0LF_1LF1LA").

Theorem nonhalt73: ~halts tm73 c0.
Proof.
  solve_FractalType1v1 tm73(Build_FractalType1_cert_v1 F D [0;1;0] [0] [0] [1] [] [] 2 1 6 4 4 0 2 16).
Qed.


Definition tm74 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0RE1LD_1LB---_1RA1LF_1LF1LD").

Theorem nonhalt74: ~halts tm74 c0.
Proof.
  solve_FractalType1v1 tm74(Build_FractalType1_cert_v1 F A [0;1;0] [0] [0] [1] [] [] 2 1 7 5 4 0 1 16).
Qed.


Definition tm75 := Eval compute in (TM_from_str "1RB0RA_0LC0LE_0RE1LD_1LB1LC_1RA1LF_1RC---").

Theorem nonhalt75: ~halts tm75 c0.
Proof.
  solve_FractalType1v1 tm75(Build_FractalType1_cert_v1 C A [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm76 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_0RE1LD_1LB---_1RA1LF_1RE1LC").

Theorem nonhalt76: ~halts tm76 c0.
Proof.
  solve_FractalType1v1 tm76(Build_FractalType1_cert_v1 C A [0;1;0] [0] [0] [1] [1] [0] 2 1 6 4 4 0 2 16).
Qed.


Definition tm77 := Eval compute in (TM_from_str "1LB---_0LC1LA_1RC0RD_0RE0RD_0LA0LF_1LF0RB").

Theorem nonhalt77: ~halts tm77 c0.
Proof.
  solve_FractalType1v1 tm77(Build_FractalType1_cert_v1 F D [0;0;1;1] [0] [0] [1] [] [] 3 1 9 6 5 0 2 29).
Qed.


Definition tm78 := Eval compute in (TM_from_str "1RB0RA_0RC0LD_0LD1RA_1LB1LE_1LE1LF_1LD---").

Theorem nonhalt78: ~halts tm78 c0.
Proof.
  solve_FractalType1v1 tm78(Build_FractalType1_cert_v1 E A [1;0;0] [0] [0] [1] [] [] 2 1 3 1 1 0 2 7).
Qed.


