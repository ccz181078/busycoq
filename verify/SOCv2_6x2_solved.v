
From BusyCoq Require Import Individual62.
From BusyCoq Require Import SOCv2.
Require Import ZArith.
Require Import String.

Open Scope list.

Definition tm0 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LD_1LE0LC_1RA---_1RE0RB").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_SOCv2 tm0 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RC---_0RA0LF").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_SOCv2 tm1 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1LC0LE_1RA0RC").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_SOCv2 tm2 (Build_SOC_cert_v2 B F [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 7 1).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LB0LE_0RC0LE_1RA0RC").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_SOCv2 tm3 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1RF0LE_1LF1LC").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_SOCv2 tm4 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_0LE1LA_1RF0RB_1RA---").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_SOCv2 tm5 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD1LD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_SOCv2 tm6 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA0RA_1LA0LF").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_SOCv2 tm7 (Build_SOC_cert_v2 C C [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 3 1).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA1LD_1RA1RF_1RD0RB_---0LC").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_SOCv2 tm8 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LA0LF_0RD0LF").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_SOCv2 tm9 (Build_SOC_cert_v2 A A [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 7 1).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RA1LD_1RA1RF_1RD0RB_---0LC").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_SOCv2 tm10 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1RB0LA_1LC0LA_1RD1LC_1LB1RE_1RF0RD_1RC---").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_SOCv2 tm11 (Build_SOC_cert_v2 C E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_1RA1RD_---1LE_0RB0LE_1RC0RB").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_SOCv2 tm12 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1LB1LC_0RA0LB_1RD---_1RE1LD_1LB1RF_1RC0RE").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_SOCv2 tm13 (Build_SOC_cert_v2 D F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA1RF_---0LE_0RC0LD_1RA0RC").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_SOCv2 tm14 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RC1LD_1RA1RF_1RD0RB_---0LC").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_SOCv2 tm15 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1LB1RF_0RC0LB_1LD1LD_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_SOCv2 tm16 (Build_SOC_cert_v2 E F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_1LC0LF").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_SOCv2 tm17 (Build_SOC_cert_v2 B D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 31 1).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA0RA_1RB0LF").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_SOCv2 tm18 (Build_SOC_cert_v2 C C [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 3 1).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1LB1RE_0RB1LC_1RD1RF_1RA1LD_1RC0RA_---0LB").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_SOCv2 tm19 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD1RF_1RE---_1RA1LE_1RD0RC").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_SOCv2 tm20 (Build_SOC_cert_v2 E F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1LB0LA_1LC1RE_1RD1RF_1RB1LD_1RC0RB_---1LA").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_SOCv2 tm21 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1LB0LA_1LC1RF_1RD---_1RE1LD_1LA1RF_1RC0RB").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_SOCv2 tm22 (Build_SOC_cert_v2 D F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1RB0LA_1LB1LC_1RD1LC_1LA1RE_1RF0RD_1RC---").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_SOCv2 tm23 (Build_SOC_cert_v2 C E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_1LE1LB_1RA0RC").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_SOCv2 tm24 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA1LA_1RB0LF").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_SOCv2 tm25 (Build_SOC_cert_v2 C C [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 3 1).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LA0LD_1RC0LD_1RF0RB_1RA---").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_SOCv2 tm26 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1LB1RD_1RC0LE_1RA1LC_1RB0RA_---0LF_0RA0LE").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_SOCv2 tm27 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1RD0LE_1RA0RC").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_SOCv2 tm28 (Build_SOC_cert_v2 F F [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 127 24).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1LB0LF_1LC1RE_1RD0LF_1RB1LD_1RC0RB_---0LA").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_SOCv2 tm29 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RA0LD_0RB0LD_1RF0RB_1RA---").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_SOCv2 tm30 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm31 := Eval compute in (TM_from_str "1LB1RE_1RC---_1RD1LC_1LF1RE_1RB0RA_0RA0LF").

Theorem nonhalt31: ~halts tm31 c0.
Proof.
  solve_SOCv2 tm31 (Build_SOC_cert_v2 C E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm32 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LC1LE_1RA---_1RE0RB").

Theorem nonhalt32: ~halts tm32 c0.
Proof.
  solve_SOCv2 tm32 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm33 := Eval compute in (TM_from_str "1LB0LA_1LC1RD_0LD0LA_1RE0RB_1RF---_1RB1LF").

Theorem nonhalt33: ~halts tm33 c0.
Proof.
  solve_SOCv2 tm33 (Build_SOC_cert_v2 F D [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 3 1).
Qed.


Definition tm34 := Eval compute in (TM_from_str "1LB1RD_1LC0LF_1RA1LC_1RE0RA_1RC---_1LA0LF").

Theorem nonhalt34: ~halts tm34 c0.
Proof.
  solve_SOCv2 tm34 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm35 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LD1LA_1RF0RB_1RA---").

Theorem nonhalt35: ~halts tm35 c0.
Proof.
  solve_SOCv2 tm35 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm36 := Eval compute in (TM_from_str "1LB0LA_1LC1RD_0LD0LA_1RE0RB_1RF---_1RB1LB").

Theorem nonhalt36: ~halts tm36 c0.
Proof.
  solve_SOCv2 tm36 (Build_SOC_cert_v2 D D [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm37 := Eval compute in (TM_from_str "1LB0LA_1RC1RF_1RD1LC_1LA1RE_1RB0RD_---0RA").

Theorem nonhalt37: ~halts tm37 c0.
Proof.
  solve_SOCv2 tm37 (Build_SOC_cert_v2 C E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm38 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA1LA_1LA0LF").

Theorem nonhalt38: ~halts tm38 c0.
Proof.
  solve_SOCv2 tm38 (Build_SOC_cert_v2 C C [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 3 1).
Qed.


Definition tm39 := Eval compute in (TM_from_str "1RB0RF_1RC---_1RD1LC_1LE1RA_0RF0LE_1LB1RA").

Theorem nonhalt39: ~halts tm39 c0.
Proof.
  solve_SOCv2 tm39 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm40 := Eval compute in (TM_from_str "1LB0LF_1RC1LB_1LA1RD_1RE0RC_1RB---_0RC0LF").

Theorem nonhalt40: ~halts tm40 c0.
Proof.
  solve_SOCv2 tm40 (Build_SOC_cert_v2 B D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm41 := Eval compute in (TM_from_str "1LB1RE_1RC0LB_0LE1LD_1RA1LD_1RF0RA_1RD---").

Theorem nonhalt41: ~halts tm41 c0.
Proof.
  solve_SOCv2 tm41 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm42 := Eval compute in (TM_from_str "1LB1RD_1RC1LE_1RA1LC_1RE0RA_1RC1RF_---0LB").

Theorem nonhalt42: ~halts tm42 c0.
Proof.
  solve_SOCv2 tm42 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm43 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_0LA0LF_1RE0LF").

Theorem nonhalt43: ~halts tm43 c0.
Proof.
  solve_SOCv2 tm43 (Build_SOC_cert_v2 A A [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 7 1).
Qed.


Definition tm44 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1RC0LF_0RD0LF").

Theorem nonhalt44: ~halts tm44 c0.
Proof.
  solve_SOCv2 tm44 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm45 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE0LC_1RA---_1RE0RB").

Theorem nonhalt45: ~halts tm45 c0.
Proof.
  solve_SOCv2 tm45 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm46 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LD1LA_1RA0RC").

Theorem nonhalt46: ~halts tm46 c0.
Proof.
  solve_SOCv2 tm46 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm47 := Eval compute in (TM_from_str "1LB0LF_1RC---_1RD1LC_1LF1RE_1RB0RD_0RA0LF").

Theorem nonhalt47: ~halts tm47 c0.
Proof.
  solve_SOCv2 tm47 (Build_SOC_cert_v2 C E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm48 := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RF_0RD1LA_---0LD_1RA0RC").

Theorem nonhalt48: ~halts tm48 c0.
Proof.
  solve_SOCv2 tm48 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm49 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_1LB1LB_1RA0RC").

Theorem nonhalt49: ~halts tm49 c0.
Proof.
  solve_SOCv2 tm49 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm50 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0RF0LE_1LB1LB").

Theorem nonhalt50: ~halts tm50 c0.
Proof.
  solve_SOCv2 tm50 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm51 := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD1RF_1RA1LD_1RC0RA_---0RB").

Theorem nonhalt51: ~halts tm51 c0.
Proof.
  solve_SOCv2 tm51 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm52 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_1RC0LD_1RF0RB_1RA---").

Theorem nonhalt52: ~halts tm52 c0.
Proof.
  solve_SOCv2 tm52 (Build_SOC_cert_v2 A E [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 3 1).
Qed.


Definition tm53 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA1LA_0RA0LF").

Theorem nonhalt53: ~halts tm53 c0.
Proof.
  solve_SOCv2 tm53 (Build_SOC_cert_v2 C C [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 3 1).
Qed.


Definition tm54 := Eval compute in (TM_from_str "1LB1RE_1RC---_1RD1LC_1LF1RE_1RB0RA_1LD0LF").

Theorem nonhalt54: ~halts tm54 c0.
Proof.
  solve_SOCv2 tm54 (Build_SOC_cert_v2 C E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm55 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1RD0LE_1RA0RC").

Theorem nonhalt55: ~halts tm55 c0.
Proof.
  solve_SOCv2 tm55 (Build_SOC_cert_v2 F F [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 127 24).
Qed.


Definition tm56 := Eval compute in (TM_from_str "1RB1RD_1RC1LB_1LA1RF_---1LE_0RC0LE_1RA0RC").

Theorem nonhalt56: ~halts tm56 c0.
Proof.
  solve_SOCv2 tm56 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm57 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA1RF_---0LE_1LC0LD_1RA0RC").

Theorem nonhalt57: ~halts tm57 c0.
Proof.
  solve_SOCv2 tm57 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm58 := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA0RA_0RA0LF").

Theorem nonhalt58: ~halts tm58 c0.
Proof.
  solve_SOCv2 tm58 (Build_SOC_cert_v2 C C [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 3 1).
Qed.


Definition tm59 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_1LB0LD_1RF0RB_1RA---").

Theorem nonhalt59: ~halts tm59 c0.
Proof.
  solve_SOCv2 tm59 (Build_SOC_cert_v2 A E [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 127 27).
Qed.


Definition tm60 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LA0LF_1RE0LF").

Theorem nonhalt60: ~halts tm60 c0.
Proof.
  solve_SOCv2 tm60 (Build_SOC_cert_v2 A A [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 7 1).
Qed.


Definition tm61 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RF_1RA---_1RE0RD").

Theorem nonhalt61: ~halts tm61 c0.
Proof.
  solve_SOCv2 tm61 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm62 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_0RD0LF").

Theorem nonhalt62: ~halts tm62 c0.
Proof.
  solve_SOCv2 tm62 (Build_SOC_cert_v2 C A [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 7 3).
Qed.


Definition tm63 := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RF_1RB1LA_---0LD_1RA0RC").

Theorem nonhalt63: ~halts tm63 c0.
Proof.
  solve_SOCv2 tm63 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm64 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LB0LE_1RD0LE_1RA0RC").

Theorem nonhalt64: ~halts tm64 c0.
Proof.
  solve_SOCv2 tm64 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm65 := Eval compute in (TM_from_str "1LB0LA_1LC1RE_1LD0LA_1RB1LD_1RF0RB_1RD---").

Theorem nonhalt65: ~halts tm65 c0.
Proof.
  solve_SOCv2 tm65 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm66 := Eval compute in (TM_from_str "1LB0LA_1LC1RE_1RD0LA_1RB1LD_1RF0RB_1RD---").

Theorem nonhalt66: ~halts tm66 c0.
Proof.
  solve_SOCv2 tm66 (Build_SOC_cert_v2 D E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm67 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_0RC0LE_1RA0RC").

Theorem nonhalt67: ~halts tm67 c0.
Proof.
  solve_SOCv2 tm67 (Build_SOC_cert_v2 F F [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 127 24).
Qed.


Definition tm68 := Eval compute in (TM_from_str "1RB0RD_1RC1RF_1RD1LC_1LE1RA_1LC1LB_---0LE").

Theorem nonhalt68: ~halts tm68 c0.
Proof.
  solve_SOCv2 tm68 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm69 := Eval compute in (TM_from_str "1LB1RD_1RC1RE_1RA1LC_1RB0RA_---1LF_1LA0LF").

Theorem nonhalt69: ~halts tm69 c0.
Proof.
  solve_SOCv2 tm69 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm70 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RB0LE_0RC0LE_1RA0RC").

Theorem nonhalt70: ~halts tm70 c0.
Proof.
  solve_SOCv2 tm70 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm71 := Eval compute in (TM_from_str "1RB0RD_1RC1RF_1RD1LC_1LE1RA_1RC1LB_---0LE").

Theorem nonhalt71: ~halts tm71 c0.
Proof.
  solve_SOCv2 tm71 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm72 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_0RC0LE_1RA0RC").

Theorem nonhalt72: ~halts tm72 c0.
Proof.
  solve_SOCv2 tm72 (Build_SOC_cert_v2 F F [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 127 24).
Qed.


Definition tm73 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LA0LD_1RA0RC").

Theorem nonhalt73: ~halts tm73 c0.
Proof.
  solve_SOCv2 tm73 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm74 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1RF_1RD0RB_---0RC").

Theorem nonhalt74: ~halts tm74 c0.
Proof.
  solve_SOCv2 tm74 (Build_SOC_cert_v2 A E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm75 := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_0LF0LE_1LC0LE_1RA0RC").

Theorem nonhalt75: ~halts tm75 c0.
Proof.
  solve_SOCv2 tm75 (Build_SOC_cert_v2 F F [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm76 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1RF0LE_1LC1LC").

Theorem nonhalt76: ~halts tm76 c0.
Proof.
  solve_SOCv2 tm76 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm77 := Eval compute in (TM_from_str "1RB0RB_1LC1RE_0LE0LD_0RB0LD_1RF0RB_1RA---").

Theorem nonhalt77: ~halts tm77 c0.
Proof.
  solve_SOCv2 tm77 (Build_SOC_cert_v2 E E [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm78 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LA1RF_1RA0RE").

Theorem nonhalt78: ~halts tm78 c0.
Proof.
  solve_SOCv2 tm78 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm79 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LB0LE_1LC0LE_1RA0RC").

Theorem nonhalt79: ~halts tm79 c0.
Proof.
  solve_SOCv2 tm79 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm80 := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA1RE_1LC0LD_1RF0RC_1RB---").

Theorem nonhalt80: ~halts tm80 c0.
Proof.
  solve_SOCv2 tm80 (Build_SOC_cert_v2 B E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm81 := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RF_1LB1LA_---0LD_1RA0RC").

Theorem nonhalt81: ~halts tm81 c0.
Proof.
  solve_SOCv2 tm81 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm82 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1LE_1RA---_1RE0RB").

Theorem nonhalt82: ~halts tm82 c0.
Proof.
  solve_SOCv2 tm82 (Build_SOC_cert_v2 A F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm83 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_0RD0LF").

Theorem nonhalt83: ~halts tm83 c0.
Proof.
  solve_SOCv2 tm83 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm84 := Eval compute in (TM_from_str "1LB1RD_1LC0LF_1RA1LC_1RE0RA_1RC---_0RA0LF").

Theorem nonhalt84: ~halts tm84 c0.
Proof.
  solve_SOCv2 tm84 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm85 := Eval compute in (TM_from_str "1LB1LB_1RC1LB_1LF1RD_1RE0RC_1RB---_1RA0LF").

Theorem nonhalt85: ~halts tm85 c0.
Proof.
  solve_SOCv2 tm85 (Build_SOC_cert_v2 B D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 15 1).
Qed.


Definition tm86 := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RC---_1LA0LF").

Theorem nonhalt86: ~halts tm86 c0.
Proof.
  solve_SOCv2 tm86 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm87 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_0RB0LD_1RF0RB_1RA---").

Theorem nonhalt87: ~halts tm87 c0.
Proof.
  solve_SOCv2 tm87 (Build_SOC_cert_v2 A E [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 3 1).
Qed.


Definition tm88 := Eval compute in (TM_from_str "1RB0RD_1RC1RF_1RD1LC_1LE1RA_0RE1LB_---0LE").

Theorem nonhalt88: ~halts tm88 c0.
Proof.
  solve_SOCv2 tm88 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm89 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0RF0LE_1LB0LE").

Theorem nonhalt89: ~halts tm89 c0.
Proof.
  solve_SOCv2 tm89 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm90 := Eval compute in (TM_from_str "1LB1RD_1LC1LE_1RA1LC_1RE0RA_1RC1RF_---0LB").

Theorem nonhalt90: ~halts tm90 c0.
Proof.
  solve_SOCv2 tm90 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm91 := Eval compute in (TM_from_str "1RB1RD_1RC1LB_1LA1RF_---1LE_1LC0LE_1RA0RC").

Theorem nonhalt91: ~halts tm91 c0.
Proof.
  solve_SOCv2 tm91 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm92 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_1RE0LF").

Theorem nonhalt92: ~halts tm92 c0.
Proof.
  solve_SOCv2 tm92 (Build_SOC_cert_v2 C A [1;1;1;1;1] [1;0;1;0;1] 1%nat []%nat [0;0]%nat [1;0]%nat 7 3).
Qed.


Definition tm93 := Eval compute in (TM_from_str "1RB0RD_1RC1RE_1RD1LC_1LB1RA_---1LF_0RD0LF").

Theorem nonhalt93: ~halts tm93 c0.
Proof.
  solve_SOCv2 tm93 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm94 := Eval compute in (TM_from_str "1LB1RF_0RC0LC_---1LD_1RE1RB_1RA1LE_1RD0RA").

Theorem nonhalt94: ~halts tm94 c0.
Proof.
  solve_SOCv2 tm94 (Build_SOC_cert_v2 E F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm95 := Eval compute in (TM_from_str "1RB1RF_1RC1LB_1LD1RE_1LA0LD_1RA0RC_---0RD").

Theorem nonhalt95: ~halts tm95 c0.
Proof.
  solve_SOCv2 tm95 (Build_SOC_cert_v2 B E [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm96 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LE0LD_1RC0LD_1RF0RB_1RA---").

Theorem nonhalt96: ~halts tm96 c0.
Proof.
  solve_SOCv2 tm96 (Build_SOC_cert_v2 E E [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm97 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LA1LA_1RA0RC").

Theorem nonhalt97: ~halts tm97 c0.
Proof.
  solve_SOCv2 tm97 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm98 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_0LA0LF_0RD0LF").

Theorem nonhalt98: ~halts tm98 c0.
Proof.
  solve_SOCv2 tm98 (Build_SOC_cert_v2 A A [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 7 1).
Qed.


Definition tm99 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1RF0LE_0LA1LC").

Theorem nonhalt99: ~halts tm99 c0.
Proof.
  solve_SOCv2 tm99 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm100 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_0LF1LB_1RA0RC").

Theorem nonhalt100: ~halts tm100 c0.
Proof.
  solve_SOCv2 tm100 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm101 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0RF0LE_1LE1LB").

Theorem nonhalt101: ~halts tm101 c0.
Proof.
  solve_SOCv2 tm101 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm102 := Eval compute in (TM_from_str "1RB0RB_1LC1RE_0LE0LD_1RC0LD_1RF0RB_1RA---").

Theorem nonhalt102: ~halts tm102 c0.
Proof.
  solve_SOCv2 tm102 (Build_SOC_cert_v2 E E [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm103 := Eval compute in (TM_from_str "1LB1RD_1RC0LE_1RA1LC_1RB0RA_---0LF_1LA0LE").

Theorem nonhalt103: ~halts tm103 c0.
Proof.
  solve_SOCv2 tm103 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm104 := Eval compute in (TM_from_str "1LB1RD_1RC1RE_1RA1LC_1RB0RA_---1LF_0RA0LF").

Theorem nonhalt104: ~halts tm104 c0.
Proof.
  solve_SOCv2 tm104 (Build_SOC_cert_v2 C D [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm105 := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LA1RF_1RA0RE").

Theorem nonhalt105: ~halts tm105 c0.
Proof.
  solve_SOCv2 tm105 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm106 := Eval compute in (TM_from_str "1RB1RD_1RC1LB_1LD1RF_0RE0LE_---1LA_1RA0RC").

Theorem nonhalt106: ~halts tm106 c0.
Proof.
  solve_SOCv2 tm106 (Build_SOC_cert_v2 B F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 127 23).
Qed.


Definition tm107 := Eval compute in (TM_from_str "1LB1RF_0RC0LC_1LD0LB_1RE---_1RA1LE_1RD0RA").

Theorem nonhalt107: ~halts tm107 c0.
Proof.
  solve_SOCv2 tm107 (Build_SOC_cert_v2 E F [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 3 1).
Qed.


Definition tm108 := Eval compute in (TM_from_str "1RB0RD_1RC1RE_1RD1LC_1LE1RA_0RF0LF_---1LB").

Theorem nonhalt108: ~halts tm108 c0.
Proof.
  solve_SOCv2 tm108 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


Definition tm109 := Eval compute in (TM_from_str "1LB0LA_1LC1RD_0LD0LA_1RE0RB_1RF---_1RB0RB").

Theorem nonhalt109: ~halts tm109 c0.
Proof.
  solve_SOCv2 tm109 (Build_SOC_cert_v2 D D [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm110 := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_0LF0LE_1LC0LE_1RA0RC").

Theorem nonhalt110: ~halts tm110 c0.
Proof.
  solve_SOCv2 tm110 (Build_SOC_cert_v2 F F [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 7 2).
Qed.


Definition tm111 := Eval compute in (TM_from_str "1RB1LB_1LC1RE_0LE0LD_0RB0LD_1RF0RB_1RA---").

Theorem nonhalt111: ~halts tm111 c0.
Proof.
  solve_SOCv2 tm111 (Build_SOC_cert_v2 E E [0;1;1] [1;0;1] 1%nat [1]%nat [1;1]%nat [0]%nat 15 2).
Qed.


Definition tm112 := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LC0LF_1RE0LF").

Theorem nonhalt112: ~halts tm112 c0.
Proof.
  solve_SOCv2 tm112 (Build_SOC_cert_v2 C A [1;1;1] [1;0;1] 1%nat [0]%nat [0;0]%nat [1]%nat 7 1).
Qed.


