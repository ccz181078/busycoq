
From BusyCoq Require Import Individual62.
From BusyCoq Require Import SOCv1.
Require Import ZArith.
Require Import String.

Open Scope list.

Definition tm0 := Eval compute in (TM_from_str "1RB---_1LC0LB_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_SOCv1 tm0 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_0LB1LB_1RA0RC").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_SOCv1 tm1 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB0LF_1RC0RE_1RD---_1RE1LE_1LF1RB_0LB0LA").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_SOCv1 tm2 (Build_SOC_cert_v1 B E [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 2047 545).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB0RB_1LC1RF_0LF0LD_1LE0LC_1RA---_1RE0RB").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_SOCv1 tm3 (Build_SOC_cert_v1 F B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1LB1RE_1RC---_1RD1LC_1LF1RE_1RB0RA_1LC0LF").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_SOCv1 tm4 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RD1LA_1RF0RB_1RA---").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_SOCv1 tm5 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_0RB---").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_SOCv1 tm6 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 72).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD1LE_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_SOCv1 tm7 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_0RA1LC").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_SOCv1 tm8 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB0RB_1LC1RE_0LE0LD_0LB0LC_1RF0RB_1RA---").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_SOCv1 tm9 (Build_SOC_cert_v1 E B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1RA_1RF0RB_1RA---").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_SOCv1 tm10 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_1LE0LD_1RC0LF_1RA0RC").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_SOCv1 tm11 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1RB---").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_SOCv1 tm12 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_0RE0RA_1LF---_1RF1RC").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_SOCv1 tm13 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA0LD").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_SOCv1 tm14 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_0RF0LD_1RA0RC").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_SOCv1 tm15 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1LB1RD_1RC1RE_1RA1LC_1RB0RA_---1LF_0LD0LF").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_SOCv1 tm16 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LA0LF_1RE0LE").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_SOCv1 tm17 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RC---_1LC0LF").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_SOCv1 tm18 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1LD1RE_---1RF_1RA0RA").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_SOCv1 tm19 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1LB1RD_1LC0LF_1RA1LC_1RE0RA_1RC---_---0LB").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_SOCv1 tm20 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1RB0RF_1RC1LB_1LD1RE_1LA0LD_1RA0RC_---1LA").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_SOCv1 tm21 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_0RC0LD_1RA0RC").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_SOCv1 tm22 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 3).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1LA1RA_1RF0RB_1RA---").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_SOCv1 tm23 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_0LF0RC_1RA1RF").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_SOCv1 tm24 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1RB1RF_1RC1LB_1LD1RE_1LB0LD_0LA0RC_1RA---").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_SOCv1 tm25 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LA0LF_1LB0LE").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_SOCv1 tm26 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 3).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1LB1LB_1RC1LB_1LF1RD_1RE0RC_1RB---_1LA0LF").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_SOCv1 tm27 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA0LC").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_SOCv1 tm28 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LF0LE_1LB0RF").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_SOCv1 tm29 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LA0LF_0RD0LE").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_SOCv1 tm30 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm31 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_0LE1RF_1RC---").

Theorem nonhalt31: ~halts tm31 c0.
Proof.
  solve_SOCv1 tm31 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm32 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_0LE0RA_1RC1RF_1RE---").

Theorem nonhalt32: ~halts tm32 c0.
Proof.
  solve_SOCv1 tm32 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm33 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0LF_---0LE").

Theorem nonhalt33: ~halts tm33 c0.
Proof.
  solve_SOCv1 tm33 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm34 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LA0LF_1RE0LE").

Theorem nonhalt34: ~halts tm34 c0.
Proof.
  solve_SOCv1 tm34 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm35 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0LD0LC_1LE0RD_1RA---_1RE0RB").

Theorem nonhalt35: ~halts tm35 c0.
Proof.
  solve_SOCv1 tm35 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm36 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA0LF_1LA1RF").

Theorem nonhalt36: ~halts tm36 c0.
Proof.
  solve_SOCv1 tm36 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm37 := Eval compute in (TM_from_str "1RB1RF_1RC1LB_1LD1RE_1LB0LD_1RA0LA_0RC---").

Theorem nonhalt37: ~halts tm37 c0.
Proof.
  solve_SOCv1 tm37 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm38 := Eval compute in (TM_from_str "1LB0LA_1LC1LC_1RD1LC_1LA1RE_1RF0RD_1RC---").

Theorem nonhalt38: ~halts tm38 c0.
Proof.
  solve_SOCv1 tm38 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm39 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LF1LB_1RA0RC").

Theorem nonhalt39: ~halts tm39 c0.
Proof.
  solve_SOCv1 tm39 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm40 := Eval compute in (TM_from_str "1LB0LB_0LC0LA_1RD0RF_1RE---_1RF1LF_1LB1RC").

Theorem nonhalt40: ~halts tm40 c0.
Proof.
  solve_SOCv1 tm40 (Build_SOC_cert_v1 C F [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm41 := Eval compute in (TM_from_str "1LB1RE_1RC---_1RD1LC_1LF1RE_1RB0RA_0LE0LF").

Theorem nonhalt41: ~halts tm41 c0.
Proof.
  solve_SOCv1 tm41 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm42 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RF_1LA1RE").

Theorem nonhalt42: ~halts tm42 c0.
Proof.
  solve_SOCv1 tm42 (Build_SOC_cert_v1 B F [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm43 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1LE---").

Theorem nonhalt43: ~halts tm43 c0.
Proof.
  solve_SOCv1 tm43 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm44 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_1LD1LA_---1RA").

Theorem nonhalt44: ~halts tm44 c0.
Proof.
  solve_SOCv1 tm44 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm45 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RD1LC_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt45: ~halts tm45 c0.
Proof.
  solve_SOCv1 tm45 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm46 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_1RA0LD_0RA---").

Theorem nonhalt46: ~halts tm46 c0.
Proof.
  solve_SOCv1 tm46 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm47 := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1LF").

Theorem nonhalt47: ~halts tm47 c0.
Proof.
  solve_SOCv1 tm47 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm48 := Eval compute in (TM_from_str "1RB0LE_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").

Theorem nonhalt48: ~halts tm48 c0.
Proof.
  solve_SOCv1 tm48 (Build_SOC_cert_v1 D B [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm49 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF0LE_0RA1RE_1RC---").

Theorem nonhalt49: ~halts tm49 c0.
Proof.
  solve_SOCv1 tm49 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm50 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LD0LC_1LA1RD_1RF0RB_1RA---").

Theorem nonhalt50: ~halts tm50 c0.
Proof.
  solve_SOCv1 tm50 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm51 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1RD0LD_1RA0RC").

Theorem nonhalt51: ~halts tm51 c0.
Proof.
  solve_SOCv1 tm51 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 3).
Qed.


Definition tm52 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0RE---_1LF1LE_1RF1RA").

Theorem nonhalt52: ~halts tm52 c0.
Proof.
  solve_SOCv1 tm52 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm53 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1LB---").

Theorem nonhalt53: ~halts tm53 c0.
Proof.
  solve_SOCv1 tm53 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 2047 545).
Qed.


Definition tm54 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_0LF1LA_1RA1RF").

Theorem nonhalt54: ~halts tm54 c0.
Proof.
  solve_SOCv1 tm54 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm55 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RF0RA_1RE0RA_1RC---").

Theorem nonhalt55: ~halts tm55 c0.
Proof.
  solve_SOCv1 tm55 (Build_SOC_cert_v1 E A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm56 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0LF_0RC1RF").

Theorem nonhalt56: ~halts tm56 c0.
Proof.
  solve_SOCv1 tm56 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm57 := Eval compute in (TM_from_str "1RB0LB_1LC0LA_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt57: ~halts tm57 c0.
Proof.
  solve_SOCv1 tm57 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm58 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1RA1LE_1RE---").

Theorem nonhalt58: ~halts tm58 c0.
Proof.
  solve_SOCv1 tm58 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm59 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RD1RD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt59: ~halts tm59 c0.
Proof.
  solve_SOCv1 tm59 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm60 := Eval compute in (TM_from_str "1LB---_0LC0LB_1RD0RF_1RE---_1RF0RF_1LB1RC").

Theorem nonhalt60: ~halts tm60 c0.
Proof.
  solve_SOCv1 tm60 (Build_SOC_cert_v1 C F [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm61 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").

Theorem nonhalt61: ~halts tm61 c0.
Proof.
  solve_SOCv1 tm61 (Build_SOC_cert_v1 D B [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm62 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0LE_1RA1RF_0RB---").

Theorem nonhalt62: ~halts tm62 c0.
Proof.
  solve_SOCv1 tm62 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm63 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RE_1LB0LD_1RA0RC_1RF0RC").

Theorem nonhalt63: ~halts tm63 c0.
Proof.
  solve_SOCv1 tm63 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm64 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_1LA---").

Theorem nonhalt64: ~halts tm64 c0.
Proof.
  solve_SOCv1 tm64 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm65 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA0LD_0LB0LC_1RF0RB_1RA---").

Theorem nonhalt65: ~halts tm65 c0.
Proof.
  solve_SOCv1 tm65 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm66 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LA0LF_1LB0LE").

Theorem nonhalt66: ~halts tm66 c0.
Proof.
  solve_SOCv1 tm66 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 3).
Qed.


Definition tm67 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_0LD0LE").

Theorem nonhalt67: ~halts tm67 c0.
Proof.
  solve_SOCv1 tm67 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm68 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LE0LD_0LB0LC_1RF0RB_1RA---").

Theorem nonhalt68: ~halts tm68 c0.
Proof.
  solve_SOCv1 tm68 (Build_SOC_cert_v1 E B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm69 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA0LF_0RA1RF").

Theorem nonhalt69: ~halts tm69 c0.
Proof.
  solve_SOCv1 tm69 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm70 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_0LC0LD_1RA0RC").

Theorem nonhalt70: ~halts tm70 c0.
Proof.
  solve_SOCv1 tm70 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 4).
Qed.


Definition tm71 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LA0LF_0LD0LE").

Theorem nonhalt71: ~halts tm71 c0.
Proof.
  solve_SOCv1 tm71 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 3).
Qed.


Definition tm72 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RB1RB_1RA0RC").

Theorem nonhalt72: ~halts tm72 c0.
Proof.
  solve_SOCv1 tm72 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm73 := Eval compute in (TM_from_str "1RB0LB_0LC0LA_1RE0RD_1LB1RC_1RF---_1RD0RD").

Theorem nonhalt73: ~halts tm73 c0.
Proof.
  solve_SOCv1 tm73 (Build_SOC_cert_v1 C D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm74 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0LA_1LE1RA_0LF0LE_1RF0RD").

Theorem nonhalt74: ~halts tm74 c0.
Proof.
  solve_SOCv1 tm74 (Build_SOC_cert_v1 F D [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 72).
Qed.


Definition tm75 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1RA0LD_1RE---").

Theorem nonhalt75: ~halts tm75 c0.
Proof.
  solve_SOCv1 tm75 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm76 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1RD0LD_1RA0RC").

Theorem nonhalt76: ~halts tm76 c0.
Proof.
  solve_SOCv1 tm76 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 3).
Qed.


Definition tm77 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_1RA0LA").

Theorem nonhalt77: ~halts tm77 c0.
Proof.
  solve_SOCv1 tm77 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm78 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_0LD1LA_1RA---").

Theorem nonhalt78: ~halts tm78 c0.
Proof.
  solve_SOCv1 tm78 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm79 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LA0LF_0RD0LE").

Theorem nonhalt79: ~halts tm79 c0.
Proof.
  solve_SOCv1 tm79 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm80 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RB1LB_1RA0RC").

Theorem nonhalt80: ~halts tm80 c0.
Proof.
  solve_SOCv1 tm80 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm81 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA1LF_1RC0RE").

Theorem nonhalt81: ~halts tm81 c0.
Proof.
  solve_SOCv1 tm81 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm82 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_0RD---").

Theorem nonhalt82: ~halts tm82 c0.
Proof.
  solve_SOCv1 tm82 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 127 8).
Qed.


Definition tm83 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RF0RA_0RB1RB_1RC---").

Theorem nonhalt83: ~halts tm83 c0.
Proof.
  solve_SOCv1 tm83 (Build_SOC_cert_v1 E A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm84 := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA0LD").

Theorem nonhalt84: ~halts tm84 c0.
Proof.
  solve_SOCv1 tm84 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm85 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RC1LD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt85: ~halts tm85 c0.
Proof.
  solve_SOCv1 tm85 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm86 := Eval compute in (TM_from_str "1LB1RF_0LC0LB_1LD0RC_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt86: ~halts tm86 c0.
Proof.
  solve_SOCv1 tm86 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm87 := Eval compute in (TM_from_str "1LB---_1RC---_1RD1LC_1LF1RE_1RB0RD_1LC0LF").

Theorem nonhalt87: ~halts tm87 c0.
Proof.
  solve_SOCv1 tm87 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm88 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD1LF_1RE0RA_1RF---_1RA1LF").

Theorem nonhalt88: ~halts tm88 c0.
Proof.
  solve_SOCv1 tm88 (Build_SOC_cert_v1 F A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm89 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_0RE0LE").

Theorem nonhalt89: ~halts tm89 c0.
Proof.
  solve_SOCv1 tm89 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm90 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_1LB---").

Theorem nonhalt90: ~halts tm90 c0.
Proof.
  solve_SOCv1 tm90 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm91 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_1LE0LD_1RC1LE_1RA0RC").

Theorem nonhalt91: ~halts tm91 c0.
Proof.
  solve_SOCv1 tm91 (Build_SOC_cert_v1 E C [1;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm92 := Eval compute in (TM_from_str "1LB---_1RC0RD_1RE1RA_1LF1RB_1RD1LD_0LB0LF").

Theorem nonhalt92: ~halts tm92 c0.
Proof.
  solve_SOCv1 tm92 (Build_SOC_cert_v1 B D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 3).
Qed.


Definition tm93 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0LF_---1LE").

Theorem nonhalt93: ~halts tm93 c0.
Proof.
  solve_SOCv1 tm93 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm94 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0LE---_1RF1RE_1RA1LA").

Theorem nonhalt94: ~halts tm94 c0.
Proof.
  solve_SOCv1 tm94 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm95 := Eval compute in (TM_from_str "1RB0RB_1LC1RF_0LF0LD_1RE0LC_1RA---_1RE0RB").

Theorem nonhalt95: ~halts tm95 c0.
Proof.
  solve_SOCv1 tm95 (Build_SOC_cert_v1 F B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm96 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0LD1RF_1RE0RA_1RF---_1RA1LF").

Theorem nonhalt96: ~halts tm96 c0.
Proof.
  solve_SOCv1 tm96 (Build_SOC_cert_v1 F A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm97 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_0LC0LA").

Theorem nonhalt97: ~halts tm97 c0.
Proof.
  solve_SOCv1 tm97 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 63 20).
Qed.


Definition tm98 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_0LE0LA").

Theorem nonhalt98: ~halts tm98 c0.
Proof.
  solve_SOCv1 tm98 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm99 := Eval compute in (TM_from_str "1RB0LF_1RC0RE_1RD---_1RE0RE_1LF1RB_0LB0LA").

Theorem nonhalt99: ~halts tm99 c0.
Proof.
  solve_SOCv1 tm99 (Build_SOC_cert_v1 B E [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 2047 545).
Qed.


Definition tm100 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1RD---").

Theorem nonhalt100: ~halts tm100 c0.
Proof.
  solve_SOCv1 tm100 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm101 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_0LD0RA_1RA---").

Theorem nonhalt101: ~halts tm101 c0.
Proof.
  solve_SOCv1 tm101 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm102 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_1LA0LD_0RE0LC_1RA---_1RE0RB").

Theorem nonhalt102: ~halts tm102 c0.
Proof.
  solve_SOCv1 tm102 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm103 := Eval compute in (TM_from_str "1LB0LB_0LC0LA_1RD0RF_1RE---_1RF0RF_1LB1RC").

Theorem nonhalt103: ~halts tm103 c0.
Proof.
  solve_SOCv1 tm103 (Build_SOC_cert_v1 C F [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm104 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_0RC0LD_1RA0RC").

Theorem nonhalt104: ~halts tm104 c0.
Proof.
  solve_SOCv1 tm104 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 7 3).
Qed.


Definition tm105 := Eval compute in (TM_from_str "1LB0LF_1RC---_1RD1LC_1LF1RE_1RB0RD_1LC0LA").

Theorem nonhalt105: ~halts tm105 c0.
Proof.
  solve_SOCv1 tm105 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm106 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0LE---_1RF1RE_1RA0RA").

Theorem nonhalt106: ~halts tm106 c0.
Proof.
  solve_SOCv1 tm106 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm107 := Eval compute in (TM_from_str "1LB0LA_1LC1RC_1RD1LC_1LA1RE_1RF0RD_1RC---").

Theorem nonhalt107: ~halts tm107 c0.
Proof.
  solve_SOCv1 tm107 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm108 := Eval compute in (TM_from_str "1RB1RD_1RC1LB_1LA1RF_---1LE_1LB0LE_1RA0RC").

Theorem nonhalt108: ~halts tm108 c0.
Proof.
  solve_SOCv1 tm108 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm109 := Eval compute in (TM_from_str "1LB1RE_1RC0LB_0LD1LD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt109: ~halts tm109 c0.
Proof.
  solve_SOCv1 tm109 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm110 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LB0LE_---0LD_1RA0RC").

Theorem nonhalt110: ~halts tm110 c0.
Proof.
  solve_SOCv1 tm110 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm111 := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA0RA").

Theorem nonhalt111: ~halts tm111 c0.
Proof.
  solve_SOCv1 tm111 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm112 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA0RF_1RD0RB_---1LD").

Theorem nonhalt112: ~halts tm112 c0.
Proof.
  solve_SOCv1 tm112 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm113 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_1RA1LD_---0RA").

Theorem nonhalt113: ~halts tm113 c0.
Proof.
  solve_SOCv1 tm113 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm114 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LF0LE_1RF0RD").

Theorem nonhalt114: ~halts tm114 c0.
Proof.
  solve_SOCv1 tm114 (Build_SOC_cert_v1 F D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm115 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_0RB0LE").

Theorem nonhalt115: ~halts tm115 c0.
Proof.
  solve_SOCv1 tm115 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm116 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_0RD0RA_1LE---_1RE1RF_1RA0RA").

Theorem nonhalt116: ~halts tm116 c0.
Proof.
  solve_SOCv1 tm116 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm117 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LA1RB_1RA0RC").

Theorem nonhalt117: ~halts tm117 c0.
Proof.
  solve_SOCv1 tm117 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm118 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_0RA1RC").

Theorem nonhalt118: ~halts tm118 c0.
Proof.
  solve_SOCv1 tm118 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm119 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA1LA_---0LB").

Theorem nonhalt119: ~halts tm119 c0.
Proof.
  solve_SOCv1 tm119 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm120 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1RF_1RD0RB_---1LA").

Theorem nonhalt120: ~halts tm120 c0.
Proof.
  solve_SOCv1 tm120 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm121 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RF0RC_0LF1RA").

Theorem nonhalt121: ~halts tm121 c0.
Proof.
  solve_SOCv1 tm121 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm122 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_1LA0LD_1LE0LC_1RA---_1RE0RB").

Theorem nonhalt122: ~halts tm122 c0.
Proof.
  solve_SOCv1 tm122 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm123 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_1LD---").

Theorem nonhalt123: ~halts tm123 c0.
Proof.
  solve_SOCv1 tm123 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm124 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_0LC---").

Theorem nonhalt124: ~halts tm124 c0.
Proof.
  solve_SOCv1 tm124 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm125 := Eval compute in (TM_from_str "1LB0LA_1RC1LC_1RD1LC_1LA1RE_1RF0RD_1RC---").

Theorem nonhalt125: ~halts tm125 c0.
Proof.
  solve_SOCv1 tm125 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm126 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LD_1RE0RA_1RF---_1RA1LA").

Theorem nonhalt126: ~halts tm126 c0.
Proof.
  solve_SOCv1 tm126 (Build_SOC_cert_v1 D A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm127 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_0RD0RA_1LE---_1RE1RF_1RA1LA").

Theorem nonhalt127: ~halts tm127 c0.
Proof.
  solve_SOCv1 tm127 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm128 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_1RE0LE").

Theorem nonhalt128: ~halts tm128 c0.
Proof.
  solve_SOCv1 tm128 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm129 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_1RA1LD_---1LA").

Theorem nonhalt129: ~halts tm129 c0.
Proof.
  solve_SOCv1 tm129 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm130 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LD_1RE0RA_1RF---_1RA0RA").

Theorem nonhalt130: ~halts tm130 c0.
Proof.
  solve_SOCv1 tm130 (Build_SOC_cert_v1 D A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm131 := Eval compute in (TM_from_str "1LB1RD_1RC0LE_1RA1LC_1RB0RA_---0LF_1LC0LE").

Theorem nonhalt131: ~halts tm131 c0.
Proof.
  solve_SOCv1 tm131 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm132 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA0LD_0LC0LC_1RF0RB_1RA---").

Theorem nonhalt132: ~halts tm132 c0.
Proof.
  solve_SOCv1 tm132 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm133 := Eval compute in (TM_from_str "1LB0RA_1RC---_1RD1LC_1LF1RE_1RB0RD_0LA0LF").

Theorem nonhalt133: ~halts tm133 c0.
Proof.
  solve_SOCv1 tm133 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm134 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LF0LE_1RF0RD").

Theorem nonhalt134: ~halts tm134 c0.
Proof.
  solve_SOCv1 tm134 (Build_SOC_cert_v1 F D [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 72).
Qed.


Definition tm135 := Eval compute in (TM_from_str "1LB0LA_1RC1RF_1RD1LC_1LA1RE_1RB0RD_---1LC").

Theorem nonhalt135: ~halts tm135 c0.
Proof.
  solve_SOCv1 tm135 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm136 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1LC---").

Theorem nonhalt136: ~halts tm136 c0.
Proof.
  solve_SOCv1 tm136 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm137 := Eval compute in (TM_from_str "1RB0RB_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").

Theorem nonhalt137: ~halts tm137 c0.
Proof.
  solve_SOCv1 tm137 (Build_SOC_cert_v1 D B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm138 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RE1LB_1RA0RC").

Theorem nonhalt138: ~halts tm138 c0.
Proof.
  solve_SOCv1 tm138 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm139 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LB1RB_1RA0RC").

Theorem nonhalt139: ~halts tm139 c0.
Proof.
  solve_SOCv1 tm139 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm140 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_0LB0LE").

Theorem nonhalt140: ~halts tm140 c0.
Proof.
  solve_SOCv1 tm140 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 6).
Qed.


Definition tm141 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0RB1RB_1RA0RC").

Theorem nonhalt141: ~halts tm141 c0.
Proof.
  solve_SOCv1 tm141 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm142 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LF0LE_1RF0RD").

Theorem nonhalt142: ~halts tm142 c0.
Proof.
  solve_SOCv1 tm142 (Build_SOC_cert_v1 F D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm143 := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1LA").

Theorem nonhalt143: ~halts tm143 c0.
Proof.
  solve_SOCv1 tm143 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm144 := Eval compute in (TM_from_str "1LB1RF_1LC0LB_0LD1LE_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt144: ~halts tm144 c0.
Proof.
  solve_SOCv1 tm144 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm145 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0LD1RE_1RF---_1RA1LA").

Theorem nonhalt145: ~halts tm145 c0.
Proof.
  solve_SOCv1 tm145 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm146 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1LA1LA_1RF0RB_1RA---").

Theorem nonhalt146: ~halts tm146 c0.
Proof.
  solve_SOCv1 tm146 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm147 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1LC0LD_1RA0RC").

Theorem nonhalt147: ~halts tm147 c0.
Proof.
  solve_SOCv1 tm147 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 5).
Qed.


Definition tm148 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RE1LA_1RF0RB_1RA---").

Theorem nonhalt148: ~halts tm148 c0.
Proof.
  solve_SOCv1 tm148 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm149 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RF_0LE0LD_1RE0RC_1RA0RC").

Theorem nonhalt149: ~halts tm149 c0.
Proof.
  solve_SOCv1 tm149 (Build_SOC_cert_v1 E C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm150 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1LF_---1LE").

Theorem nonhalt150: ~halts tm150 c0.
Proof.
  solve_SOCv1 tm150 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm151 := Eval compute in (TM_from_str "1RB1RF_1RC1LB_1LD1RE_1LB0LD_1RA1LA_---0RC").

Theorem nonhalt151: ~halts tm151 c0.
Proof.
  solve_SOCv1 tm151 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm152 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RE_1LB0LD_1RA0RC_0RD1RD").

Theorem nonhalt152: ~halts tm152 c0.
Proof.
  solve_SOCv1 tm152 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm153 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_0RA---").

Theorem nonhalt153: ~halts tm153 c0.
Proof.
  solve_SOCv1 tm153 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm154 := Eval compute in (TM_from_str "1LB0RD_1RC1RF_1RD1LC_1LE1RA_1LC0LE_---1RB").

Theorem nonhalt154: ~halts tm154 c0.
Proof.
  solve_SOCv1 tm154 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm155 := Eval compute in (TM_from_str "1LB1RD_1RC0LE_1RA1LC_1RB0RA_---0LF_0LD0LE").

Theorem nonhalt155: ~halts tm155 c0.
Proof.
  solve_SOCv1 tm155 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm156 := Eval compute in (TM_from_str "1RB1RA_1RC1LB_1LD1RE_1LB0LD_1RF0RC_0LA---").

Theorem nonhalt156: ~halts tm156 c0.
Proof.
  solve_SOCv1 tm156 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm157 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_1RB0LA").

Theorem nonhalt157: ~halts tm157 c0.
Proof.
  solve_SOCv1 tm157 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 127 8).
Qed.


Definition tm158 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RC1RD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt158: ~halts tm158 c0.
Proof.
  solve_SOCv1 tm158 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm159 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RC1RB_1RA0RC").

Theorem nonhalt159: ~halts tm159 c0.
Proof.
  solve_SOCv1 tm159 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm160 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0RE1LB_1RA0RC").

Theorem nonhalt160: ~halts tm160 c0.
Proof.
  solve_SOCv1 tm160 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm161 := Eval compute in (TM_from_str "1RB0RB_1LC1RE_0LE0LD_0RC0LC_1RF0RB_1RA---").

Theorem nonhalt161: ~halts tm161 c0.
Proof.
  solve_SOCv1 tm161 (Build_SOC_cert_v1 E B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm162 := Eval compute in (TM_from_str "1RB1RC_1LA0LB_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt162: ~halts tm162 c0.
Proof.
  solve_SOCv1 tm162 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm163 := Eval compute in (TM_from_str "1LB1RB_1RC1LB_1LF1RD_1RE0RC_1RB---_1LA0LF").

Theorem nonhalt163: ~halts tm163 c0.
Proof.
  solve_SOCv1 tm163 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm164 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA0RA_0LE0LF").

Theorem nonhalt164: ~halts tm164 c0.
Proof.
  solve_SOCv1 tm164 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm165 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_0LE0RA_1RF1RE_1RC---").

Theorem nonhalt165: ~halts tm165 c0.
Proof.
  solve_SOCv1 tm165 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm166 := Eval compute in (TM_from_str "1LB0RD_1RC1RB_1RD1LC_1LE1RA_1LC0LF_---0LE").

Theorem nonhalt166: ~halts tm166 c0.
Proof.
  solve_SOCv1 tm166 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm167 := Eval compute in (TM_from_str "1RB1RF_1RC1LB_1LD1RE_1LA0LD_1RA0RC_---1LB").

Theorem nonhalt167: ~halts tm167 c0.
Proof.
  solve_SOCv1 tm167 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm168 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_0RE---").

Theorem nonhalt168: ~halts tm168 c0.
Proof.
  solve_SOCv1 tm168 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 6).
Qed.


Definition tm169 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_1LE0LD_1RC1LE_1RA0RC").

Theorem nonhalt169: ~halts tm169 c0.
Proof.
  solve_SOCv1 tm169 (Build_SOC_cert_v1 E C [1;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm170 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA0LD_1RA0LC_1RF0RB_1RA---").

Theorem nonhalt170: ~halts tm170 c0.
Proof.
  solve_SOCv1 tm170 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 63 24).
Qed.


Definition tm171 := Eval compute in (TM_from_str "1LB0LA_1RC0RF_1RD1LC_1LA1RE_1RB0RD_---1LB").

Theorem nonhalt171: ~halts tm171 c0.
Proof.
  solve_SOCv1 tm171 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm172 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LE0LD_1RE0RC_1RA0RC").

Theorem nonhalt172: ~halts tm172 c0.
Proof.
  solve_SOCv1 tm172 (Build_SOC_cert_v1 E C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm173 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0RB1LE_1RA0RC").

Theorem nonhalt173: ~halts tm173 c0.
Proof.
  solve_SOCv1 tm173 (Build_SOC_cert_v1 E C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm174 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LA1RB_1RA0RC").

Theorem nonhalt174: ~halts tm174 c0.
Proof.
  solve_SOCv1 tm174 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm175 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_0RF0LD_1RA0RC").

Theorem nonhalt175: ~halts tm175 c0.
Proof.
  solve_SOCv1 tm175 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm176 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_1LE0LA").

Theorem nonhalt176: ~halts tm176 c0.
Proof.
  solve_SOCv1 tm176 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm177 := Eval compute in (TM_from_str "1RB0LB_0LC0LA_1RE0RD_1LB1RC_1RF---_1RD1LD").

Theorem nonhalt177: ~halts tm177 c0.
Proof.
  solve_SOCv1 tm177 (Build_SOC_cert_v1 C D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm178 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA0LD_0RC0LC_1RF0RB_1RA---").

Theorem nonhalt178: ~halts tm178 c0.
Proof.
  solve_SOCv1 tm178 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm179 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA0RA").

Theorem nonhalt179: ~halts tm179 c0.
Proof.
  solve_SOCv1 tm179 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm180 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE1LE_1RC1RF_---0RA").

Theorem nonhalt180: ~halts tm180 c0.
Proof.
  solve_SOCv1 tm180 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm181 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_1LD0RA_---1RA").

Theorem nonhalt181: ~halts tm181 c0.
Proof.
  solve_SOCv1 tm181 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm182 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1LA_1RF0RB_1RA---").

Theorem nonhalt182: ~halts tm182 c0.
Proof.
  solve_SOCv1 tm182 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm183 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1RF0LD_1RA0RC").

Theorem nonhalt183: ~halts tm183 c0.
Proof.
  solve_SOCv1 tm183 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm184 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_0RE---").

Theorem nonhalt184: ~halts tm184 c0.
Proof.
  solve_SOCv1 tm184 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 2047 545).
Qed.


Definition tm185 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LA0LF_0LD0LE").

Theorem nonhalt185: ~halts tm185 c0.
Proof.
  solve_SOCv1 tm185 (Build_SOC_cert_v1 A D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 3).
Qed.


Definition tm186 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1RC---").

Theorem nonhalt186: ~halts tm186 c0.
Proof.
  solve_SOCv1 tm186 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 72).
Qed.


Definition tm187 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LF1RB_1RA0RC").

Theorem nonhalt187: ~halts tm187 c0.
Proof.
  solve_SOCv1 tm187 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm188 := Eval compute in (TM_from_str "1LB1RF_0LC0LB_0RD0RA_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt188: ~halts tm188 c0.
Proof.
  solve_SOCv1 tm188 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm189 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0RB1LB_1RA0RC").

Theorem nonhalt189: ~halts tm189 c0.
Proof.
  solve_SOCv1 tm189 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm190 := Eval compute in (TM_from_str "1LB---_0LC0LB_1RD0RF_1RE---_1RF1LF_1LB1RC").

Theorem nonhalt190: ~halts tm190 c0.
Proof.
  solve_SOCv1 tm190 (Build_SOC_cert_v1 C F [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm191 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0RC0LD_1RE0RA_1RF---_1RA1LA").

Theorem nonhalt191: ~halts tm191 c0.
Proof.
  solve_SOCv1 tm191 (Build_SOC_cert_v1 D A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm192 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_0RC---").

Theorem nonhalt192: ~halts tm192 c0.
Proof.
  solve_SOCv1 tm192 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 63 20).
Qed.


Definition tm193 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_1LA0LA").

Theorem nonhalt193: ~halts tm193 c0.
Proof.
  solve_SOCv1 tm193 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm194 := Eval compute in (TM_from_str "1LB1RE_1RC0LB_0LC1LD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt194: ~halts tm194 c0.
Proof.
  solve_SOCv1 tm194 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm195 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE1RF_1RA0LD_1LA---").

Theorem nonhalt195: ~halts tm195 c0.
Proof.
  solve_SOCv1 tm195 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm196 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_0LC0LD_1RA0RC").

Theorem nonhalt196: ~halts tm196 c0.
Proof.
  solve_SOCv1 tm196 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 4).
Qed.


Definition tm197 := Eval compute in (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").

Theorem nonhalt197: ~halts tm197 c0.
Proof.
  solve_SOCv1 tm197 (Build_SOC_cert_v1 D B [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm198 := Eval compute in (TM_from_str "1LB1RF_1LC0LB_0LD1RE_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt198: ~halts tm198 c0.
Proof.
  solve_SOCv1 tm198 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm199 := Eval compute in (TM_from_str "1RB---_1RC1LE_1LD1RF_1LE0LD_0RE1LB_1RA0RC").

Theorem nonhalt199: ~halts tm199 c0.
Proof.
  solve_SOCv1 tm199 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm200 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1LC0LD_1RA0RC").

Theorem nonhalt200: ~halts tm200 c0.
Proof.
  solve_SOCv1 tm200 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 5).
Qed.


Definition tm201 := Eval compute in (TM_from_str "1RB1RA_1RC1LB_1LD1RF_1LB0LE_---0LD_1LA0RC").

Theorem nonhalt201: ~halts tm201 c0.
Proof.
  solve_SOCv1 tm201 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm202 := Eval compute in (TM_from_str "1RB1LB_1LC1RF_0LF0LD_1RE0LC_1RA---_1RE0RB").

Theorem nonhalt202: ~halts tm202 c0.
Proof.
  solve_SOCv1 tm202 (Build_SOC_cert_v1 F B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm203 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RE_1LB0LD_1RA0RC_0RD0RC").

Theorem nonhalt203: ~halts tm203 c0.
Proof.
  solve_SOCv1 tm203 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm204 := Eval compute in (TM_from_str "1RB1LD_1LC1RE_0LD0LC_1RE0RA_1RF0LD_1RA---").

Theorem nonhalt204: ~halts tm204 c0.
Proof.
  solve_SOCv1 tm204 (Build_SOC_cert_v1 D B [0;0;1] [1;0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm205 := Eval compute in (TM_from_str "1RB1RF_1RC1LB_1LD1RE_1LB0LD_1LA0RC_---1RA").

Theorem nonhalt205: ~halts tm205 c0.
Proof.
  solve_SOCv1 tm205 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm206 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LB1LB_1RA0RC").

Theorem nonhalt206: ~halts tm206 c0.
Proof.
  solve_SOCv1 tm206 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm207 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_1RC---").

Theorem nonhalt207: ~halts tm207 c0.
Proof.
  solve_SOCv1 tm207 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm208 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LE0LD_1RE0RC_1RA0RC").

Theorem nonhalt208: ~halts tm208 c0.
Proof.
  solve_SOCv1 tm208 (Build_SOC_cert_v1 E C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm209 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_0RD0LE").

Theorem nonhalt209: ~halts tm209 c0.
Proof.
  solve_SOCv1 tm209 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm210 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").

Theorem nonhalt210: ~halts tm210 c0.
Proof.
  solve_SOCv1 tm210 (Build_SOC_cert_v1 D B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm211 := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD1RE_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt211: ~halts tm211 c0.
Proof.
  solve_SOCv1 tm211 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm212 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RA1LC").

Theorem nonhalt212: ~halts tm212 c0.
Proof.
  solve_SOCv1 tm212 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm213 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD1LF_1RE---_1RA0RA_0RE1RE").

Theorem nonhalt213: ~halts tm213 c0.
Proof.
  solve_SOCv1 tm213 (Build_SOC_cert_v1 F A [1;0] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm214 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA1RF_---0LE_1LB0LD_1RA0RC").

Theorem nonhalt214: ~halts tm214 c0.
Proof.
  solve_SOCv1 tm214 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm215 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0LD1LF_1RE0RA_1RF---_1RA1LF").

Theorem nonhalt215: ~halts tm215 c0.
Proof.
  solve_SOCv1 tm215 (Build_SOC_cert_v1 F A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm216 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LE0LD_1RE0RC_1RA0RC").

Theorem nonhalt216: ~halts tm216 c0.
Proof.
  solve_SOCv1 tm216 (Build_SOC_cert_v1 E C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm217 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RF0RA_0RB0RA_1RC---").

Theorem nonhalt217: ~halts tm217 c0.
Proof.
  solve_SOCv1 tm217 (Build_SOC_cert_v1 E A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm218 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RE1RA_1RF0RB_1RA---").

Theorem nonhalt218: ~halts tm218 c0.
Proof.
  solve_SOCv1 tm218 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm219 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_0RB---").

Theorem nonhalt219: ~halts tm219 c0.
Proof.
  solve_SOCv1 tm219 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm220 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RF_1LE0LD_1RC1RB_1RA0RC").

Theorem nonhalt220: ~halts tm220 c0.
Proof.
  solve_SOCv1 tm220 (Build_SOC_cert_v1 E C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm221 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1LD1RE_---1RF_1RA1LA").

Theorem nonhalt221: ~halts tm221 c0.
Proof.
  solve_SOCv1 tm221 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm222 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RE_1LB0LD_1RA0RC_0RA0RC").

Theorem nonhalt222: ~halts tm222 c0.
Proof.
  solve_SOCv1 tm222 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm223 := Eval compute in (TM_from_str "1RB---_0LC0LB_1RE0RD_1LB1RC_1RF---_1RD1LD").

Theorem nonhalt223: ~halts tm223 c0.
Proof.
  solve_SOCv1 tm223 (Build_SOC_cert_v1 C D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm224 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0LE_1RC1RF_0RA---").

Theorem nonhalt224: ~halts tm224 c0.
Proof.
  solve_SOCv1 tm224 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm225 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1RF0LD_1RA0RC").

Theorem nonhalt225: ~halts tm225 c0.
Proof.
  solve_SOCv1 tm225 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm226 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LE0LD_0RC0LC_1RF0RB_1RA---").

Theorem nonhalt226: ~halts tm226 c0.
Proof.
  solve_SOCv1 tm226 (Build_SOC_cert_v1 E B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm227 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_0RE0LA").

Theorem nonhalt227: ~halts tm227 c0.
Proof.
  solve_SOCv1 tm227 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 6).
Qed.


Definition tm228 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LA1LB_1RA0RC").

Theorem nonhalt228: ~halts tm228 c0.
Proof.
  solve_SOCv1 tm228 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm229 := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RC---_0LD0LF").

Theorem nonhalt229: ~halts tm229 c0.
Proof.
  solve_SOCv1 tm229 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm230 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_0RC0LA").

Theorem nonhalt230: ~halts tm230 c0.
Proof.
  solve_SOCv1 tm230 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm231 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0LF_1LE1RA_0LF0LE_1RF0RD").

Theorem nonhalt231: ~halts tm231 c0.
Proof.
  solve_SOCv1 tm231 (Build_SOC_cert_v1 F D [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 72).
Qed.


Definition tm232 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1LB0LD_1RA0RC").

Theorem nonhalt232: ~halts tm232 c0.
Proof.
  solve_SOCv1 tm232 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 2047 546).
Qed.


Definition tm233 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RC1LD_1RA1LC_1RF0RA_1RD---").

Theorem nonhalt233: ~halts tm233 c0.
Proof.
  solve_SOCv1 tm233 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm234 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_1LA0LD_0LE0LC_1RA---_1RE0RB").

Theorem nonhalt234: ~halts tm234 c0.
Proof.
  solve_SOCv1 tm234 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm235 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0RC0LD_1RE0RA_1RF---_1RA0RA").

Theorem nonhalt235: ~halts tm235 c0.
Proof.
  solve_SOCv1 tm235 (Build_SOC_cert_v1 D A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm236 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA1RE_1LB0LD_1RF0RC_1RB---").

Theorem nonhalt236: ~halts tm236 c0.
Proof.
  solve_SOCv1 tm236 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm237 := Eval compute in (TM_from_str "1RB0LD_1LC1RE_0LD0LC_1RE0RA_1RF0LD_1RA---").

Theorem nonhalt237: ~halts tm237 c0.
Proof.
  solve_SOCv1 tm237 (Build_SOC_cert_v1 D B [0;0;1] [1;0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm238 := Eval compute in (TM_from_str "1RB---_1RC1LF_1LD1RE_1LB0LD_1RA0RC_0RF1LB").

Theorem nonhalt238: ~halts tm238 c0.
Proof.
  solve_SOCv1 tm238 (Build_SOC_cert_v1 F C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm239 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0RC1RB_1RA0RC").

Theorem nonhalt239: ~halts tm239 c0.
Proof.
  solve_SOCv1 tm239 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm240 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1LA0LD_1RA0RC").

Theorem nonhalt240: ~halts tm240 c0.
Proof.
  solve_SOCv1 tm240 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm241 := Eval compute in (TM_from_str "1LB---_1RC0RA_1RD1LC_1LF1RE_1RB0RD_0LB0LF").

Theorem nonhalt241: ~halts tm241 c0.
Proof.
  solve_SOCv1 tm241 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm242 := Eval compute in (TM_from_str "1LB---_1RC0RD_1RE1RA_1LF1RB_1RD0RD_0LB0LF").

Theorem nonhalt242: ~halts tm242 c0.
Proof.
  solve_SOCv1 tm242 (Build_SOC_cert_v1 B D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 15 3).
Qed.


Definition tm243 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_0LA---").

Theorem nonhalt243: ~halts tm243 c0.
Proof.
  solve_SOCv1 tm243 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm244 := Eval compute in (TM_from_str "1RB1LB_1LC1RF_0LF0LD_1LE0LC_1RA---_1RE0RB").

Theorem nonhalt244: ~halts tm244 c0.
Proof.
  solve_SOCv1 tm244 (Build_SOC_cert_v1 F B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm245 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RA1RC").

Theorem nonhalt245: ~halts tm245 c0.
Proof.
  solve_SOCv1 tm245 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm246 := Eval compute in (TM_from_str "1LB0LA_1RC1RC_1RD1LC_1LA1RE_1RF0RD_1RC---").

Theorem nonhalt246: ~halts tm246 c0.
Proof.
  solve_SOCv1 tm246 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm247 := Eval compute in (TM_from_str "1RB---_1RC0LF_1LD1RF_1LE0LD_1RC1LE_1RA0RC").

Theorem nonhalt247: ~halts tm247 c0.
Proof.
  solve_SOCv1 tm247 (Build_SOC_cert_v1 E C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm248 := Eval compute in (TM_from_str "1LB---_1LC0LB_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt248: ~halts tm248 c0.
Proof.
  solve_SOCv1 tm248 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm249 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA1RF_0LD---").

Theorem nonhalt249: ~halts tm249 c0.
Proof.
  solve_SOCv1 tm249 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm250 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_1LE0LD_1RC0LF_1RA0RC").

Theorem nonhalt250: ~halts tm250 c0.
Proof.
  solve_SOCv1 tm250 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm251 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_0LF0RA_1RA1RF").

Theorem nonhalt251: ~halts tm251 c0.
Proof.
  solve_SOCv1 tm251 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm252 := Eval compute in (TM_from_str "1LB0LB_1LC0LA_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt252: ~halts tm252 c0.
Proof.
  solve_SOCv1 tm252 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm253 := Eval compute in (TM_from_str "1RB1RC_0LC0LB_1RE0RD_1LB1RC_1RF---_1RD1LA").

Theorem nonhalt253: ~halts tm253 c0.
Proof.
  solve_SOCv1 tm253 (Build_SOC_cert_v1 C D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm254 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0LD1RE_1RF---_1RA0RA").

Theorem nonhalt254: ~halts tm254 c0.
Proof.
  solve_SOCv1 tm254 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm255 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LD0LC_1RE0RA_1RF0LD_1RA---").

Theorem nonhalt255: ~halts tm255 c0.
Proof.
  solve_SOCv1 tm255 (Build_SOC_cert_v1 D B [0;0;1] [1;0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm256 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1RE---").

Theorem nonhalt256: ~halts tm256 c0.
Proof.
  solve_SOCv1 tm256 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm257 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RD1LD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt257: ~halts tm257 c0.
Proof.
  solve_SOCv1 tm257 (Build_SOC_cert_v1 D A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm258 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_0LE1LB_1RA0RC").

Theorem nonhalt258: ~halts tm258 c0.
Proof.
  solve_SOCv1 tm258 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm259 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LA1LB_1RA0RC").

Theorem nonhalt259: ~halts tm259 c0.
Proof.
  solve_SOCv1 tm259 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm260 := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RA0RF_1RA---").

Theorem nonhalt260: ~halts tm260 c0.
Proof.
  solve_SOCv1 tm260 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 2).
Qed.


Definition tm261 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LE_1RF0RA_0RF0RA_1RC---").

Theorem nonhalt261: ~halts tm261 c0.
Proof.
  solve_SOCv1 tm261 (Build_SOC_cert_v1 E A [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm262 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1LE1RF_---1RC").

Theorem nonhalt262: ~halts tm262 c0.
Proof.
  solve_SOCv1 tm262 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm263 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA0LD_1LC0LC_1RF0RB_1RA---").

Theorem nonhalt263: ~halts tm263 c0.
Proof.
  solve_SOCv1 tm263 (Build_SOC_cert_v1 A B [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm264 := Eval compute in (TM_from_str "1RB1LC_1LA0LB_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt264: ~halts tm264 c0.
Proof.
  solve_SOCv1 tm264 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm265 := Eval compute in (TM_from_str "1RB---_1RC0LE_1LD1RF_0LE0LD_1RE0RC_1RA0RC").

Theorem nonhalt265: ~halts tm265 c0.
Proof.
  solve_SOCv1 tm265 (Build_SOC_cert_v1 E C [0;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 255 73).
Qed.


Definition tm266 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA0RA_---0LB").

Theorem nonhalt266: ~halts tm266 c0.
Proof.
  solve_SOCv1 tm266 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm267 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1LA0LD_1RA0RC").

Theorem nonhalt267: ~halts tm267 c0.
Proof.
  solve_SOCv1 tm267 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 255 74).
Qed.


Definition tm268 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LE_1RF0RA_0RE1LC_1RC---").

Theorem nonhalt268: ~halts tm268 c0.
Proof.
  solve_SOCv1 tm268 (Build_SOC_cert_v1 E A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm269 := Eval compute in (TM_from_str "1LB1RD_1LC0LF_1RA1LC_1RE0RA_1RC---_0LD0LF").

Theorem nonhalt269: ~halts tm269 c0.
Proof.
  solve_SOCv1 tm269 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm270 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD1RF_1RE0RA_1RF---_1RA1LF").

Theorem nonhalt270: ~halts tm270 c0.
Proof.
  solve_SOCv1 tm270 (Build_SOC_cert_v1 F A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm271 := Eval compute in (TM_from_str "1LB1RD_1RC1RE_1RA1LC_1RB0RA_---1LF_1LC0LF").

Theorem nonhalt271: ~halts tm271 c0.
Proof.
  solve_SOCv1 tm271 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm272 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LD1RE_1LB0LA_1RF0RC_1RB---").

Theorem nonhalt272: ~halts tm272 c0.
Proof.
  solve_SOCv1 tm272 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 10).
Qed.


Definition tm273 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA1LA").

Theorem nonhalt273: ~halts tm273 c0.
Proof.
  solve_SOCv1 tm273 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm274 := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA1LF_---1RC").

Theorem nonhalt274: ~halts tm274 c0.
Proof.
  solve_SOCv1 tm274 (Build_SOC_cert_v1 C A [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm275 := Eval compute in (TM_from_str "1LB---_1RC0RD_1RE1RA_1LF1RB_1RD1LE_1LE0LF").

Theorem nonhalt275: ~halts tm275 c0.
Proof.
  solve_SOCv1 tm275 (Build_SOC_cert_v1 E D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm276 := Eval compute in (TM_from_str "1RB---_0LC0LB_1RE0RD_1LB1RC_1RF---_1RD0RD").

Theorem nonhalt276: ~halts tm276 c0.
Proof.
  solve_SOCv1 tm276 (Build_SOC_cert_v1 C D [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 12).
Qed.


Definition tm277 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0RC1LB_1RA0RC").

Theorem nonhalt277: ~halts tm277 c0.
Proof.
  solve_SOCv1 tm277 (Build_SOC_cert_v1 B C [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm278 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1LB0LD_1RA0RC").

Theorem nonhalt278: ~halts tm278 c0.
Proof.
  solve_SOCv1 tm278 (Build_SOC_cert_v1 F C [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 2047 546).
Qed.


Definition tm279 := Eval compute in (TM_from_str "1LB0LA_1RB1LC_1RD1LC_1LA1RE_1RF0RD_1RC---").

Theorem nonhalt279: ~halts tm279 c0.
Proof.
  solve_SOCv1 tm279 (Build_SOC_cert_v1 C D [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm280 := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_0LF---_1RC1RF").

Theorem nonhalt280: ~halts tm280 c0.
Proof.
  solve_SOCv1 tm280 (Build_SOC_cert_v1 C A [1;1] [0;1] 0%nat [0]%nat [0;0]%nat [1]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm281 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LE0LD_1LC0LC_1RF0RB_1RA---").

Theorem nonhalt281: ~halts tm281 c0.
Proof.
  solve_SOCv1 tm281 (Build_SOC_cert_v1 E B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


Definition tm282 := Eval compute in (TM_from_str "1RB0RB_1LC1RE_0LE0LD_1LC0LC_1RF0RB_1RA---").

Theorem nonhalt282: ~halts tm282 c0.
Proof.
  solve_SOCv1 tm282 (Build_SOC_cert_v1 E B [0;1] [0;1] 0%nat [1]%nat [1;1]%nat [0]%nat []%nat [1;1]%nat [0]%nat 31 11).
Qed.


