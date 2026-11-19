
From BusyCoq Require Import Individual62.
From BusyCoq Require Import SBCv2.
Require Import ZArith.
Require Import String.

Definition tm0 := Eval compute in (TM_from_str "1RB1RF_0RC0RA_1RD0LE_0LC1RA_1LC1LE_---0RB").

Theorem nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 E B [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm1 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RD_0RA0LF").

Theorem nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1LB1RA_1RC0LC_0LA0RD_1RE---_1LE0RF_0RB1LD").

Theorem nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 A C [0;0;1;0;0] [1;0;0;1;1] [0;1;0;0;1;1] [0;1;0;0;1;0] [0;1]
    (fun n => [1;0;1;0;0]^^n *> [1] *> const 0)
    (fun n m => [1;0;1;0;0]^^m *> [1;0] *> [1;0;1;0;0]^^n *> [1] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1LB1LD_1RC0LC_1LA0RD_0RB0RE_1RD0RF_0RC---").

Theorem nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 C D [0;1;1;0;1] [0;0;0;0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB1RA_1RD---").

Theorem nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 B A [1;0;1;0;1;0;1;1;0;1;0] [1;0;1;0;1;1;0;0;1;1;0] [0;1;1;0] [1;0;1;0] []
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 2).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0RF_0LE0LC").

Theorem nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 F C [1;0] [0;1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;1;0;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0;0]^^m *> [0] *> [0;1;0;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1LF_0RF0RB_0LC0RD").

Theorem nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 F E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1RB1LE_0LC0RD_1RD0RB_1RE1RF_1LA0LE_---0RC").

Theorem nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 E F [1;1;1;1;1] [1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [1;0;1]^^n *> [1] *> const 0)
    (fun n m => [1;0;1]^^m *> [1] *> [1;0;1]^^n *> [1] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1RB0LC_1LA1RD_1LA1RB_1RE1RF_0RA0RD_---0LE").

Theorem nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RD_0RA0LD").

Theorem nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1RE_0RE0LA_1LB1RF_0RB1RD").

Theorem nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 B F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LE---").

Theorem nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1 B C [0;0;1;0;1;0;0] [0;1;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [1] *> [1;0;0]^^n *> [] *> const 0)
    1 2 0 1 1 3).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD1RB").

Theorem nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1 B F [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm13 := Eval compute in (TM_from_str "1RB0RF_1LC0RE_1RD0LC_1LB0RE_1RA0LB_0RB---").

Theorem nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1 C F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1RB0LB_1LC0RD_1LA0LB_0RA0RE_1RD0RF_0RB---").

Theorem nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1 B D [0;1;1;0;1] [0;0;0;0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1RB0LC_1LA1RD_1LA1RC_1RE0RF_0RA0RD_---1RE").

Theorem nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1LD_0RD1RB").

Theorem nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1 D F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LF_0RB0RA").

Theorem nonhalt17: ~halts tm17 c0.
Proof.
  solve_cert (cert1 D C [1;0;1;0;1;0;1;1;0;1;0] [1;0;1;0;1;1;0;0;1;1;0] [0;1;1;0] [1;0;1;0] []
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm18 := Eval compute in (TM_from_str "1LB1RC_1RA0LE_1RD1RF_0RB0RC_1LB1LE_---0RD").

Theorem nonhalt18: ~halts tm18 c0.
Proof.
  solve_cert (cert1 E C [] [] [0;0;1] [1;1;1] [1;1]
    (fun n => [0;1]^^n *> [] *> const 0)
    (fun n m => [0;1]^^m *> [0] *> [0;1]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm19 := Eval compute in (TM_from_str "1RB1RC_0LC0LC_1RE1LD_0LB1RD_0RF---_0RA0RE").

Theorem nonhalt19: ~halts tm19 c0.
Proof.
  solve_cert (cert1 D F [1;0] [0;1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;1;0;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0;0]^^m *> [0] *> [0;1;0;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm20 := Eval compute in (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LA_0LE1RE").

Theorem nonhalt20: ~halts tm20 c0.
Proof.
  solve_cert (cert1 F B [1] [1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;0;1;0]^^m *> [0] *> [0;0;1;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm21 := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD1RB_1RA0RF_1LB0LE_0RA---").

Theorem nonhalt21: ~halts tm21 c0.
Proof.
  solve_cert (cert1 E C [] [] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm22 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RD_0RA1RB").

Theorem nonhalt22: ~halts tm22 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1RB0LA_0LC---_0LD1LC_1RD1RE_0RA0RF_1RE0RD").

Theorem nonhalt23: ~halts tm23 c0.
Proof.
  solve_cert (cert1 C E [1] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    1 1 0 0 1 3).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1LB1RE_0LC0RC_1RD0LE_0RA0LD_1RF0LD_0RB---").

Theorem nonhalt24: ~halts tm24 c0.
Proof.
  solve_cert (cert1 D A [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1RB---_1RC0RE_0LD1RF_1LE1RD_0LF0LD_0RB0RA").

Theorem nonhalt25: ~halts tm25 c0.
Proof.
  solve_cert (cert1 E C [1;0;1;0;1;0;1;1;0;1;0] [1;0;1;0;1;1;0;0;1;1;0] [0;1;1;0] [1;0;1;0] []
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm26 := Eval compute in (TM_from_str "1LB1RA_1RC0LC_0LA0RD_1RE---_0RF0RF_0RB0LD").

Theorem nonhalt26: ~halts tm26 c0.
Proof.
  solve_cert (cert1 A C [0;0;1;0;0] [1;0;0;1;1] [0;1;0;0;1;1] [0;1;0;0;1;0] [0;1]
    (fun n => [1;0;1;0;0]^^n *> [1] *> const 0)
    (fun n m => [1;0;1;0;0]^^m *> [1;0] *> [1;0;1;0;0]^^n *> [1] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm27 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB1RD_0RA---").

Theorem nonhalt27: ~halts tm27 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm28 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD1RF_0RC---").

Theorem nonhalt28: ~halts tm28 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm29 := Eval compute in (TM_from_str "1RB0LC_0LA1RD_1LA1RC_1RE0RF_0RA0RD_---1RE").

Theorem nonhalt29: ~halts tm29 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    1 1 0 0 1 3).
Qed.


Definition tm30 := Eval compute in (TM_from_str "1RB1LE_0RC0LC_1LD1RF_0RA---_0LA0RB_0RE1RB").

Theorem nonhalt30: ~halts tm30 c0.
Proof.
  solve_cert (cert1 D F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm31 := Eval compute in (TM_from_str "1RB0RB_0LC1RD_0RA1LD_0LE0RE_1LB1RF_0RA---").

Theorem nonhalt31: ~halts tm31 c0.
Proof.
  solve_cert (cert1 B D [1;0;1;0;1;1] [1;0;0;1;1;0] [0;1;1;0] [0;1;0;0] []
    (fun n => [0;1;1;0;1;1]^^n *> [] *> const 0)
    (fun n m => [0;1;1;0;1;1]^^m *> [0;1;1;1] *> [0;1;1;0;1;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm32 := Eval compute in (TM_from_str "1RB1RC_0LA0RF_1RD0LE_1LC0RA_1LC0LD_0RD---").

Theorem nonhalt32: ~halts tm32 c0.
Proof.
  solve_cert (cert1 D A [] [] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 1).
Qed.


Definition tm33 := Eval compute in (TM_from_str "1RB0LC_1LA1RD_1LA1RC_1RE1RF_0RA0RD_---0LE").

Theorem nonhalt33: ~halts tm33 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm34 := Eval compute in (TM_from_str "1LB---_0LC1RE_1LD0RB_1RB1LB_0RB1RF_0RC0RA").

Theorem nonhalt34: ~halts tm34 c0.
Proof.
  solve_cert (cert1 B C [1;1;0;1;1;0] [0;1;1;0;0;1] [1;0;1;0;0;1] [1;0;1;1;0;1] [1;0;1;1]
    (fun n => [1;1;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;1;0]^^m *> [1] *> [1;1;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm35 := Eval compute in (TM_from_str "1LB0RE_0LC0LE_1LD---_1RA0RF_1RD0LA_0RA1LB").

Theorem nonhalt35: ~halts tm35 c0.
Proof.
  solve_cert (cert1 C F [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm36 := Eval compute in (TM_from_str "1RB0RC_1LA0RF_0RB1LD_0LE---_1LA0LE_1RA1RD").

Theorem nonhalt36: ~halts tm36 c0.
Proof.
  solve_cert (cert1 E C [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm37 := Eval compute in (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LF_0LE1RE").

Theorem nonhalt37: ~halts tm37 c0.
Proof.
  solve_cert (cert1 F B [1] [1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;0;1;0]^^m *> [0] *> [0;0;1;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm38 := Eval compute in (TM_from_str "1LB1RE_0LC0RC_1RD0LE_0RA1LB_1RF0LD_0RB---").

Theorem nonhalt38: ~halts tm38 c0.
Proof.
  solve_cert (cert1 D A [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm39 := Eval compute in (TM_from_str "1LB1RC_1RC0LA_1LB1RD_1RE0RF_0RB0RD_---1RE").

Theorem nonhalt39: ~halts tm39 c0.
Proof.
  solve_cert (cert1 A E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm40 := Eval compute in (TM_from_str "1RB0RF_0LC0RE_0RA1RD_1LE0LB_1RA0LD_0LE---").

Theorem nonhalt40: ~halts tm40 c0.
Proof.
  solve_cert (cert1 C B [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm41 := Eval compute in (TM_from_str "1RB1RF_0LC0RE_0RA1RD_1LE0LB_1RA0LD_1RB---").

Theorem nonhalt41: ~halts tm41 c0.
Proof.
  solve_cert (cert1 C B [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm42 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LD_0RB1RF_1RA---").

Theorem nonhalt42: ~halts tm42 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm43 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LF_0RB1RF_0RA---").

Theorem nonhalt43: ~halts tm43 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm44 := Eval compute in (TM_from_str "1RB---_0LC0RE_0RA1RD_1LE0LB_1RF0LD_1RB1RA").

Theorem nonhalt44: ~halts tm44 c0.
Proof.
  solve_cert (cert1 C B [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm45 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_0LE---").

Theorem nonhalt45: ~halts tm45 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm46 := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1LC0RD_1RE0LA_1RA0RF_0RA---").

Theorem nonhalt46: ~halts tm46 c0.
Proof.
  solve_cert (cert1 B F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm47 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB0RF_0LE---").

Theorem nonhalt47: ~halts tm47 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm48 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0RC---").

Theorem nonhalt48: ~halts tm48 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm49 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB1RF_0LD---").

Theorem nonhalt49: ~halts tm49 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm50 := Eval compute in (TM_from_str "1RB1RC_0RC---_1LD1RF_0LA0RE_0RC0LC_0RD1RB").

Theorem nonhalt50: ~halts tm50 c0.
Proof.
  solve_cert (cert1 D F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm51 := Eval compute in (TM_from_str "1RB0LC_0LA1RD_1LA1RC_1RE1RF_0RA0RD_---0LE").

Theorem nonhalt51: ~halts tm51 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    1 1 0 0 1 3).
Qed.


Definition tm52 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LB_0RD1RE").

Theorem nonhalt52: ~halts tm52 c0.
Proof.
  solve_cert (cert1 B F [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm53 := Eval compute in (TM_from_str "1RB0RD_0RC1LD_1LD1RA_0LE0RF_1RB0LB_---0RB").

Theorem nonhalt53: ~halts tm53 c0.
Proof.
  solve_cert (cert1 D A [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm54 := Eval compute in (TM_from_str "1RB1RE_0LB1LC_1LD0LF_1RA0RB_0RD0RA_0LB---").

Theorem nonhalt54: ~halts tm54 c0.
Proof.
  solve_cert (cert1 D A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0;0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm55 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF0RD_0LA0RB").

Theorem nonhalt55: ~halts tm55 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm56 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD1RF_1RC---").

Theorem nonhalt56: ~halts tm56 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm57 := Eval compute in (TM_from_str "1LB---_0LC1RE_0RD1LF_1RB1LA_0RF0RC_0LA0RB").

Theorem nonhalt57: ~halts tm57 c0.
Proof.
  solve_cert (cert1 B E [1;0;1;0;1;1] [1;0;0;1;1;0] [0;1;1;0] [0;1;0;0] []
    (fun n => [0;1;1;0;1;1]^^n *> [0;1;1] *> const 0)
    (fun n m => [0;1;1;0;1;1]^^m *> [0;1;1;1] *> [0;1;1;0;1;1]^^n *> [0;1;1] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm58 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD1RF_0RC---").

Theorem nonhalt58: ~halts tm58 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm59 := Eval compute in (TM_from_str "1RB0RF_1LC0RE_1RD0LC_1LD0RE_1RA0LB_0RB---").

Theorem nonhalt59: ~halts tm59 c0.
Proof.
  solve_cert (cert1 C F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm60 := Eval compute in (TM_from_str "1LB0RE_0LC---_1LD0LA_1RA0LC_1RF0LA_0RA0RF").

Theorem nonhalt60: ~halts tm60 c0.
Proof.
  solve_cert (cert1 C F [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm61 := Eval compute in (TM_from_str "1RB1RE_0LB1LC_1LD0LF_1RA0RB_0RD0RA_0RB---").

Theorem nonhalt61: ~halts tm61 c0.
Proof.
  solve_cert (cert1 D A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0;0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm62 := Eval compute in (TM_from_str "1LB1RA_1RC0LA_1LB1RD_1RE0RF_0RB0RD_---1RE").

Theorem nonhalt62: ~halts tm62 c0.
Proof.
  solve_cert (cert1 A E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm63 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB0RF_0LE---").

Theorem nonhalt63: ~halts tm63 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm64 := Eval compute in (TM_from_str "1RB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RD").

Theorem nonhalt64: ~halts tm64 c0.
Proof.
  solve_cert (cert1 B F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm65 := Eval compute in (TM_from_str "1LB---_0LC1LB_1RC1RD_0RE0RF_1RA0LA_1RD0RC").

Theorem nonhalt65: ~halts tm65 c0.
Proof.
  solve_cert (cert1 B D [1] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm66 := Eval compute in (TM_from_str "1LB1RA_1RC0LA_1LB1RD_1RE1RF_0RB0RD_---0LE").

Theorem nonhalt66: ~halts tm66 c0.
Proof.
  solve_cert (cert1 A E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm67 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD1RB_0RC---").

Theorem nonhalt67: ~halts tm67 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm68 := Eval compute in (TM_from_str "1RB0RC_1LC1RE_0LE1LD_0RD0LB_0RA0RF_1RA---").

Theorem nonhalt68: ~halts tm68 c0.
Proof.
  solve_cert (cert1 C B [1;0;1;0;1;0;1;1;0;1;0] [1;0;1;0;1;1;0;0;1;1;0] [0;1;1;0] [1;0;1;0] []
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm69 := Eval compute in (TM_from_str "1RB0LC_1LA1RD_1LA1RB_1RE0RF_0RA0RD_---1RE").

Theorem nonhalt69: ~halts tm69 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm70 := Eval compute in (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LA_0LE0LC").

Theorem nonhalt70: ~halts tm70 c0.
Proof.
  solve_cert (cert1 F B [1] [1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;0;1;0]^^m *> [0] *> [0;0;1;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm71 := Eval compute in (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0RF_0RD1RB_0RC0LC").

Theorem nonhalt71: ~halts tm71 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm72 := Eval compute in (TM_from_str "1RB0LE_0RC0RB_1RD0RB_0RE0RA_1LD0LF_1LA---").

Theorem nonhalt72: ~halts tm72 c0.
Proof.
  solve_cert (cert1 D B [1] [1] [0;1;0;0;0;1] [0;1;0;0;1;1] [0;1;0;0;1]
    (fun n => [0;0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;0;1;0]^^m *> [0] *> [0;0;1;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm73 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LE_0RA---_0RB1LF_0LE1RC").

Theorem nonhalt73: ~halts tm73 c0.
Proof.
  solve_cert (cert1 F D [1;0;1] [0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm74 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RB_0RA---").

Theorem nonhalt74: ~halts tm74 c0.
Proof.
  solve_cert (cert1 F E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm75 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LF_0RB1RD_0RA---").

Theorem nonhalt75: ~halts tm75 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm76 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RF_0RA1LB").

Theorem nonhalt76: ~halts tm76 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm77 := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1LB_0RE0LA_1LB1RF_0RB1RD").

Theorem nonhalt77: ~halts tm77 c0.
Proof.
  solve_cert (cert1 B F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm78 := Eval compute in (TM_from_str "1LB1RA_1RC0LA_0LA1RD_1RE1RF_0RB0RD_---0LE").

Theorem nonhalt78: ~halts tm78 c0.
Proof.
  solve_cert (cert1 A E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm79 := Eval compute in (TM_from_str "1RB0LC_0RC0RB_1LD0RA_0LE---_1LF0LC_1RC0LE").

Theorem nonhalt79: ~halts tm79 c0.
Proof.
  solve_cert (cert1 E B [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm80 := Eval compute in (TM_from_str "1RB0LC_1RC1RF_1LD0RA_1RC0LE_0RA1LE_0RC---").

Theorem nonhalt80: ~halts tm80 c0.
Proof.
  solve_cert (cert1 E C [0;1;0;0] [1;1;0;0] [1;1;0;0] [1;1;0;1] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm81 := Eval compute in (TM_from_str "1RB0LE_0RC---_0LD0RD_1RE0LA_0RF0LE_1LC1RA").

Theorem nonhalt81: ~halts tm81 c0.
Proof.
  solve_cert (cert1 E F [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm82 := Eval compute in (TM_from_str "1RB---_1LC0LD_1RD0LB_0LA0RE_1RF1LA_0RD0RF").

Theorem nonhalt82: ~halts tm82 c0.
Proof.
  solve_cert (cert1 B E [0;1;0;1] [0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm83 := Eval compute in (TM_from_str "1LB1RE_1RC0LC_0RA1LD_0LB0RC_0RD1RF_0RA---").

Theorem nonhalt83: ~halts tm83 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm84 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD1RF_0RC---").

Theorem nonhalt84: ~halts tm84 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm85 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RB_0LA0RB").

Theorem nonhalt85: ~halts tm85 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm86 := Eval compute in (TM_from_str "1RB---_1LC0LD_1RD0LB_0LA0RE_1RF1RA_0RD0RF").

Theorem nonhalt86: ~halts tm86 c0.
Proof.
  solve_cert (cert1 B E [0;1;0;1] [0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm87 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA0LF_0RB0RF_0LE---").

Theorem nonhalt87: ~halts tm87 c0.
Proof.
  solve_cert (cert1 D A [0;0;1;0;1;0;0] [0;1;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [1] *> [1;0;0]^^n *> [] *> const 0)
    1 2 0 1 1 3).
Qed.


Definition tm88 := Eval compute in (TM_from_str "1RB0LE_1RC1RF_0LD0RA_0RB1RE_1LA0LC_1RC---").

Theorem nonhalt88: ~halts tm88 c0.
Proof.
  solve_cert (cert1 D C [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm89 := Eval compute in (TM_from_str "1LB1RA_1RC0LA_0LA1RD_1RE0RF_0RB0RD_---1RE").

Theorem nonhalt89: ~halts tm89 c0.
Proof.
  solve_cert (cert1 A E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm90 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RF_0RA0LF").

Theorem nonhalt90: ~halts tm90 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm91 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RD_0RA1RB").

Theorem nonhalt91: ~halts tm91 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm92 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_0RA---").

Theorem nonhalt92: ~halts tm92 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm93 := Eval compute in (TM_from_str "1RB1RC_0LC0RD_1RE1LD_0LB1RD_0RF---_0RA0RE").

Theorem nonhalt93: ~halts tm93 c0.
Proof.
  solve_cert (cert1 D F [1;0] [0;1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;1;0;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0;0]^^m *> [0] *> [0;1;0;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm94 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RF_0RD1RB_0RC---").

Theorem nonhalt94: ~halts tm94 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm95 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD0RF_0LA---").

Theorem nonhalt95: ~halts tm95 c0.
Proof.
  solve_cert (cert1 F E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm96 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD1LF_0RA0LA_0RF1RD_0LC0RD").

Theorem nonhalt96: ~halts tm96 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm97 := Eval compute in (TM_from_str "1RB1LA_0LC1RE_---1LD_1RA0LC_1RF0RF_1RD1RE").

Theorem nonhalt97: ~halts tm97 c0.
Proof.
  solve_cert (cert1 A F [1;1] [0;1] [0;1] [1;1] [1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm98 := Eval compute in (TM_from_str "1RB0LC_1LA---_1RD1LA_1LE1RF_1RD1LE_1RA0RD").

Theorem nonhalt98: ~halts tm98 c0.
Proof.
  solve_cert (cert1 E F [1;1;1] [1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm99 := Eval compute in (TM_from_str "1LB1RC_1RA0LE_1RD1RF_0RB0RC_1LB1RA_---0LD").

Theorem nonhalt99: ~halts tm99 c0.
Proof.
  solve_cert (cert1 E D [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm100 := Eval compute in (TM_from_str "1RB0LE_1RC0RF_0LD0RA_0RB1RE_1LA0LC_0LA---").

Theorem nonhalt100: ~halts tm100 c0.
Proof.
  solve_cert (cert1 D C [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm101 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD1RF_0RC---").

Theorem nonhalt101: ~halts tm101 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm102 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LF_0RB1RD_0LD---").

Theorem nonhalt102: ~halts tm102 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm103 := Eval compute in (TM_from_str "1RB0LE_0RC1LD_1LD1RE_0LA0RF_1RF0LB_0RD---").

Theorem nonhalt103: ~halts tm103 c0.
Proof.
  solve_cert (cert1 B C [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm104 := Eval compute in (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RF_0RC---").

Theorem nonhalt104: ~halts tm104 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm105 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_0LA---").

Theorem nonhalt105: ~halts tm105 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm106 := Eval compute in (TM_from_str "1LB0LE_1RC0LA_1RE0RD_0LB---_0LF0RB_0RC1RA").

Theorem nonhalt106: ~halts tm106 c0.
Proof.
  solve_cert (cert1 F E [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm107 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1RA_0RA0LA_0RB1RF_0LD---").

Theorem nonhalt107: ~halts tm107 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm108 := Eval compute in (TM_from_str "1LB0RE_0LC---_1LD0LA_1RA0LC_1RF1RB_0RA0RF").

Theorem nonhalt108: ~halts tm108 c0.
Proof.
  solve_cert (cert1 C F [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm109 := Eval compute in (TM_from_str "1LB0LE_1RC0LA_1RE1RD_1RE---_0LF0RB_0RD1RA").

Theorem nonhalt109: ~halts tm109 c0.
Proof.
  solve_cert (cert1 F E [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm110 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB1RD_0LC---").

Theorem nonhalt110: ~halts tm110 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm111 := Eval compute in (TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE1RA_0LD0RF_0RB---").

Theorem nonhalt111: ~halts tm111 c0.
Proof.
  solve_cert (cert1 C D [] [] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm112 := Eval compute in (TM_from_str "1RB---_1LC0LD_1RD0LB_0LA0RE_1RF0LD_0RD0RF").

Theorem nonhalt112: ~halts tm112 c0.
Proof.
  solve_cert (cert1 B F [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm113 := Eval compute in (TM_from_str "1RB0LF_0LB1RC_1RD---_0LE0RA_0RC1RF_1LA0LD").

Theorem nonhalt113: ~halts tm113 c0.
Proof.
  solve_cert (cert1 E D [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm114 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB0RF_0LC---").

Theorem nonhalt114: ~halts tm114 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm115 := Eval compute in (TM_from_str "1RB0RF_1LC0RE_0RD0LC_0LB1LA_1RA0LC_0RB---").

Theorem nonhalt115: ~halts tm115 c0.
Proof.
  solve_cert (cert1 C F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm116 := Eval compute in (TM_from_str "1LB0RD_1LC1LD_1RA0LA_0RC0RE_1RD0RF_0RA---").

Theorem nonhalt116: ~halts tm116 c0.
Proof.
  solve_cert (cert1 A D [0;1;1;0;1] [0;0;0;0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [1;0;1;0]^^n *> [1] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [1] *> const 0)
    2 1 0 0 1 4).
Qed.


Definition tm117 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RB_0LE---").

Theorem nonhalt117: ~halts tm117 c0.
Proof.
  solve_cert (cert1 D D [0;0;1] [0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm118 := Eval compute in (TM_from_str "1LB0LC_1RC0RE_1LB0RD_1RB1RF_0RC1LF_0LA---").

Theorem nonhalt118: ~halts tm118 c0.
Proof.
  solve_cert (cert1 A E [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm119 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA0LD_0RF0RB_0LC0RD").

Theorem nonhalt119: ~halts tm119 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm120 := Eval compute in (TM_from_str "1LB1RC_0LC---_0RD1RD_0LE0RF_1RF1LD_0RA0LA").

Theorem nonhalt120: ~halts tm120 c0.
Proof.
  solve_cert (cert1 D F [1;0;1] [0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm121 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LB_0RB1RF_0RA---").

Theorem nonhalt121: ~halts tm121 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm122 := Eval compute in (TM_from_str "1LB1LF_1RC1RF_1RE0LD_---1LC_0RA1LE_1RB0RB").

Theorem nonhalt122: ~halts tm122 c0.
Proof.
  solve_cert (cert1 E B [1;1] [0;1] [0;1] [1;1] [1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm123 := Eval compute in (TM_from_str "1RB0LC_1LA0RD_0RD1LC_1RE0LB_1RB1RF_0RB---").

Theorem nonhalt123: ~halts tm123 c0.
Proof.
  solve_cert (cert1 C B [0;1;0;0] [1;1;0;0] [1;1;0;0] [1;1;0;1] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm124 := Eval compute in (TM_from_str "1RB1RC_0RC0LC_1LD1RE_0LA0RB_0RD0RF_0LA---").

Theorem nonhalt124: ~halts tm124 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm125 := Eval compute in (TM_from_str "1RB0LE_0RC---_0LD0RB_1RE0LA_0RF0LE_1LC1RA").

Theorem nonhalt125: ~halts tm125 c0.
Proof.
  solve_cert (cert1 E F [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm126 := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA0RE_0RF0RA_0LE1LB_0RC---").

Theorem nonhalt126: ~halts tm126 c0.
Proof.
  solve_cert (cert1 C A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0;0;0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm127 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RE_0RC1LD_0RD1RB").

Theorem nonhalt127: ~halts tm127 c0.
Proof.
  solve_cert (cert1 D F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm128 := Eval compute in (TM_from_str "1RB1RD_1RC0RF_1LD0RA_1RC0LE_1LD0LC_0RC---").

Theorem nonhalt128: ~halts tm128 c0.
Proof.
  solve_cert (cert1 C A [] [] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 1).
Qed.


Definition tm129 := Eval compute in (TM_from_str "1LB---_0LC0RD_1RD1RA_0RE0LA_1LB1RF_0RB1RD").

Theorem nonhalt129: ~halts tm129 c0.
Proof.
  solve_cert (cert1 B F [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm130 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD0RF_0LE---").

Theorem nonhalt130: ~halts tm130 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm131 := Eval compute in (TM_from_str "1RB1RF_1RC0LE_1RD1LC_0LE1RF_---1LB_1RA0RA").

Theorem nonhalt131: ~halts tm131 c0.
Proof.
  solve_cert (cert1 C A [1;1] [0;1] [0;1] [1;1] [1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm132 := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RB_0RD0RF_0LE---").

Theorem nonhalt132: ~halts tm132 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm133 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LF_0RA---_0RB1RF_0RA0LD").

Theorem nonhalt133: ~halts tm133 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm134 := Eval compute in (TM_from_str "1RB0LA_1LC0RD_1LA0RD_1RE0LC_1RC0RF_0RC---").

Theorem nonhalt134: ~halts tm134 c0.
Proof.
  solve_cert (cert1 A F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm135 := Eval compute in (TM_from_str "1RB0RF_1RC0LD_0LB---_0LE1LD_1RE1RA_1RA0RE").

Theorem nonhalt135: ~halts tm135 c0.
Proof.
  solve_cert (cert1 D A [1] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    1 1 0 0 1 3).
Qed.


Definition tm136 := Eval compute in (TM_from_str "1RB0LE_0RC0LB_1LD1RE_0LA0RF_1RF0LB_0RD---").

Theorem nonhalt136: ~halts tm136 c0.
Proof.
  solve_cert (cert1 B C [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm137 := Eval compute in (TM_from_str "1RB0RF_1LC0RE_0RD0LC_0LB1LA_1RA0LB_0RB---").

Theorem nonhalt137: ~halts tm137 c0.
Proof.
  solve_cert (cert1 C F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm138 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_0LA---").

Theorem nonhalt138: ~halts tm138 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm139 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LA1RE_0LA0RB_0RD0RF_1RC---").

Theorem nonhalt139: ~halts tm139 c0.
Proof.
  solve_cert (cert1 B C [0;0;1;0;1;0;0;1;0;0] [0;1;1;0;1;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [1;0;0;1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;1;0;0]^^m *> [1;0;1;1] *> [1;0;0;1;0;0]^^n *> [] *> const 0)
    1 2 1 0 1 2).
Qed.


Definition tm140 := Eval compute in (TM_from_str "1LB0RD_1LC0LA_1RA0LA_0RC0RE_1RD0RF_0RA---").

Theorem nonhalt140: ~halts tm140 c0.
Proof.
  solve_cert (cert1 A D [0;1;1;0;1] [0;0;0;0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [1;0;1;0]^^n *> [1] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [1] *> const 0)
    2 1 0 0 1 4).
Qed.


Definition tm141 := Eval compute in (TM_from_str "1LB0RE_0LC0LE_1LD---_1RA0RF_1RD0LA_0RA0LF").

Theorem nonhalt141: ~halts tm141 c0.
Proof.
  solve_cert (cert1 C F [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm142 := Eval compute in (TM_from_str "1RB1RE_0LB1LC_1LD0LB_1RA0RB_0RF0RA_0RD---").

Theorem nonhalt142: ~halts tm142 c0.
Proof.
  solve_cert (cert1 D A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0;0;0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm143 := Eval compute in (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0RF_0LE1RE").

Theorem nonhalt143: ~halts tm143 c0.
Proof.
  solve_cert (cert1 F C [1;0] [0;1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;1;0;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0;0]^^m *> [0] *> [0;1;0;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm144 := Eval compute in (TM_from_str "1RB1LF_0RC0LC_1LD1RE_0LE---_0RF1RF_0LA0RB").

Theorem nonhalt144: ~halts tm144 c0.
Proof.
  solve_cert (cert1 F B [1;0;1] [0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm145 := Eval compute in (TM_from_str "1LB0RF_1RC1LD_0LA0RD_0RE---_1RF0LC_0RC0RB").

Theorem nonhalt145: ~halts tm145 c0.
Proof.
  solve_cert (cert1 D B [1;1] [0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [0;0;0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;0;0;1]^^m *> [0;1] *> [0;0;0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm146 := Eval compute in (TM_from_str "1RB0LE_0RC---_0LD0RD_1RE0LA_0RF1LC_1LC1RA").

Theorem nonhalt146: ~halts tm146 c0.
Proof.
  solve_cert (cert1 E F [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm147 := Eval compute in (TM_from_str "1LB0LA_1RC0RE_1LB0RD_1RB1RF_0RC1LF_0LA---").

Theorem nonhalt147: ~halts tm147 c0.
Proof.
  solve_cert (cert1 A E [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm148 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD1LB_0RA0LA_0RB0RF_0LC---").

Theorem nonhalt148: ~halts tm148 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm149 := Eval compute in (TM_from_str "1RB1RF_0LC---_0LC1LD_1LE0LB_1RA0RC_0RE0RA").

Theorem nonhalt149: ~halts tm149 c0.
Proof.
  solve_cert (cert1 E A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0;0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm150 := Eval compute in (TM_from_str "1RB0RC_1LA0RF_0RB1LD_0LE---_1LA0LB_1RA1RD").

Theorem nonhalt150: ~halts tm150 c0.
Proof.
  solve_cert (cert1 E C [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm151 := Eval compute in (TM_from_str "1RB0LC_0LC1RD_1LA1RC_1RE0RF_0RA0RD_---1RE").

Theorem nonhalt151: ~halts tm151 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm152 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0RF_0LA---").

Theorem nonhalt152: ~halts tm152 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm153 := Eval compute in (TM_from_str "1RB0LC_0LC1RD_1LA1RC_1RE1RF_0RA0RD_---0LE").

Theorem nonhalt153: ~halts tm153 c0.
Proof.
  solve_cert (cert1 C E [0] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm154 := Eval compute in (TM_from_str "1RB1LD_0RC0LC_1LD1RE_0LA0RB_0RD1RF_0RC---").

Theorem nonhalt154: ~halts tm154 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm155 := Eval compute in (TM_from_str "1LB1RA_0LC0LA_0RD0RF_1RE0RB_1LB1RC_1RD---").

Theorem nonhalt155: ~halts tm155 c0.
Proof.
  solve_cert (cert1 B E [1;0;1;0;1;0;1;1;0;1;0] [1;0;1;0;1;1;0;0;1;1;0] [0;1;1;0] [1;0;1;0] []
    (fun n => [1;1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;1;0;1;0]^^m *> [1;1;0] *> [1;1;0;1;0]^^n *> [] *> const 0)
    1 1 1 0 1 2).
Qed.


Definition tm156 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RD_0RA0LF").

Theorem nonhalt156: ~halts tm156 c0.
Proof.
  solve_cert (cert1 F E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm157 := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1RD_0RD1RE").

Theorem nonhalt157: ~halts tm157 c0.
Proof.
  solve_cert (cert1 E F [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm158 := Eval compute in (TM_from_str "1RB1RF_0LC---_0LC1LD_1LE0LC_1RA0RC_0RE0RA").

Theorem nonhalt158: ~halts tm158 c0.
Proof.
  solve_cert (cert1 E A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0;0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm159 := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RB_0RD0RF_0LE---").

Theorem nonhalt159: ~halts tm159 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm160 := Eval compute in (TM_from_str "1RB1LD_0RC0RB_0LD0RA_1RE---_1LF0LC_1RC0LE").

Theorem nonhalt160: ~halts tm160 c0.
Proof.
  solve_cert (cert1 E A [0;1;0;1;0;0;1;0;1;0;1] [0;0;0;1;0;0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1;0;0;1]^^n *> [0;0;1] *> const 0)
    (fun n m => [0;0;1;0;0;1]^^m *> [0;0;1;1] *> [0;0;1;0;0;1]^^n *> [0;0;1] *> const 0)
    1 1 1 0 1 1).
Qed.


Definition tm161 := Eval compute in (TM_from_str "1RB0RF_0RC0RA_1RD0LD_1LE0RB_1LC0LD_0RD---").

Theorem nonhalt161: ~halts tm161 c0.
Proof.
  solve_cert (cert1 D B [0;1;1;0;1] [0;0;0;0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm162 := Eval compute in (TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD1RA").

Theorem nonhalt162: ~halts tm162 c0.
Proof.
  solve_cert (cert1 C F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm163 := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA---_0RF0RD_0LA0RB").

Theorem nonhalt163: ~halts tm163 c0.
Proof.
  solve_cert (cert1 B E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm164 := Eval compute in (TM_from_str "1LB0LE_1RC0LA_0LC1RD_1RE---_0LF0RB_0RD1RA").

Theorem nonhalt164: ~halts tm164 c0.
Proof.
  solve_cert (cert1 F E [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm165 := Eval compute in (TM_from_str "1LB0RE_0RC0LB_0LA1LD_1RA0RF_1RD0LB_0RA---").

Theorem nonhalt165: ~halts tm165 c0.
Proof.
  solve_cert (cert1 B F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm166 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1LF_0RB1RD_0LC---").

Theorem nonhalt166: ~halts tm166 c0.
Proof.
  solve_cert (cert1 F E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm167 := Eval compute in (TM_from_str "1RB---_0LC0RE_0RA1RD_1LE0LB_1RF0LD_0LF1RA").

Theorem nonhalt167: ~halts tm167 c0.
Proof.
  solve_cert (cert1 C B [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm168 := Eval compute in (TM_from_str "1RB0LB_1LC---_0LD1LC_1RD1RE_0RA0RF_1RE0RD").

Theorem nonhalt168: ~halts tm168 c0.
Proof.
  solve_cert (cert1 C E [1] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 6).
Qed.


Definition tm169 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF0RD_0LA0RB").

Theorem nonhalt169: ~halts tm169 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm170 := Eval compute in (TM_from_str "1RB0LE_0RC---_0LD0RB_1RE0LA_0RF1LC_1LC1RA").

Theorem nonhalt170: ~halts tm170 c0.
Proof.
  solve_cert (cert1 E F [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm171 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LE_0RA1LB_1RF0LD_0RB---").

Theorem nonhalt171: ~halts tm171 c0.
Proof.
  solve_cert (cert1 D A [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm172 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LF_0LE---_0RB1RF_0RA0LD").

Theorem nonhalt172: ~halts tm172 c0.
Proof.
  solve_cert (cert1 F A [0;0;1;0;1;0;0] [0;1;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [1] *> [1;0;0]^^n *> [] *> const 0)
    1 2 0 1 1 3).
Qed.


Definition tm173 := Eval compute in (TM_from_str "1RB1RD_0RC0RB_1LD0RA_0LE---_1LF0LC_1RC0LE").

Theorem nonhalt173: ~halts tm173 c0.
Proof.
  solve_cert (cert1 E B [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm174 := Eval compute in (TM_from_str "1LB0RE_0RC0LB_0LA1LD_1RA0RF_1RD0LA_0RA---").

Theorem nonhalt174: ~halts tm174 c0.
Proof.
  solve_cert (cert1 B F [0;1] [0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm175 := Eval compute in (TM_from_str "1RB0LE_0RC0LB_1LD1RE_0LA0RA_1RF0LB_0RD---").

Theorem nonhalt175: ~halts tm175 c0.
Proof.
  solve_cert (cert1 B C [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm176 := Eval compute in (TM_from_str "1RB0LE_0RC1LD_1LD1RE_0LA0RA_1RF0LB_0RD---").

Theorem nonhalt176: ~halts tm176 c0.
Proof.
  solve_cert (cert1 B C [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm177 := Eval compute in (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LF_0LE0LC").

Theorem nonhalt177: ~halts tm177 c0.
Proof.
  solve_cert (cert1 F B [1] [1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]
    (fun n => [0;0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;0;1;0]^^m *> [0] *> [0;0;1;0]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm178 := Eval compute in (TM_from_str "1RB0LE_1RC1RF_0LD0RA_0RF1RE_1LA0LC_1RC---").

Theorem nonhalt178: ~halts tm178 c0.
Proof.
  solve_cert (cert1 D C [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 3).
Qed.


Definition tm179 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA0RB_0RD0RF_0LA---").

Theorem nonhalt179: ~halts tm179 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm180 := Eval compute in (TM_from_str "1RB0RF_1RC0LD_1LB---_0LE1LD_1RE1RA_1RA0RE").

Theorem nonhalt180: ~halts tm180 c0.
Proof.
  solve_cert (cert1 D A [1] [1] [0;0;1] [1;1;1] [1;1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm181 := Eval compute in (TM_from_str "1LB0LE_1RC0LA_1RE1RD_1RE---_0LF0RB_0RC1RA").

Theorem nonhalt181: ~halts tm181 c0.
Proof.
  solve_cert (cert1 F E [0;0;0;1;0;0] [1;1;0;1;1;1] [0;1;1;1] [0;1;1;0] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm182 := Eval compute in (TM_from_str "1RB0LB_0LC0RD_1LA1RC_1RE---_0RF0RF_0RA1LD").

Theorem nonhalt182: ~halts tm182 c0.
Proof.
  solve_cert (cert1 C B [0;0;1;0;0] [1;0;0;1;1] [0;1;0;0;1;1] [0;1;0;0;1;0] [0;1]
    (fun n => [1;0;1;0;0]^^n *> [1] *> const 0)
    (fun n m => [1;0;1;0;0]^^m *> [1;0] *> [1;0;1;0;0]^^n *> [1] *> const 0)
    2 2 0 1 1 4).
Qed.


Definition tm183 := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD1LF_0RA0LA_0RF0RB_0LC0RD").

Theorem nonhalt183: ~halts tm183 c0.
Proof.
  solve_cert (cert1 B E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm184 := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA0RE_0RC0RA_1RF1LB_0LB---").

Theorem nonhalt184: ~halts tm184 c0.
Proof.
  solve_cert (cert1 C A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0;0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm185 := Eval compute in (TM_from_str "1RB1RF_0LC---_0LE1LD_1LE0LB_1RA0RC_0RE0RA").

Theorem nonhalt185: ~halts tm185 c0.
Proof.
  solve_cert (cert1 E F [1;1;1] [1;0;1] [0;1] [1;1] [1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [0;1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm186 := Eval compute in (TM_from_str "1RB0LC_1LA---_1RD0RE_1LC1RF_0LB1LD_1RA0RD").

Theorem nonhalt186: ~halts tm186 c0.
Proof.
  solve_cert (cert1 C F [1;1;1] [1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm187 := Eval compute in (TM_from_str "1RB0LC_0RC0RB_0LD0RA_1RE---_1LF0LC_1RC0LE").

Theorem nonhalt187: ~halts tm187 c0.
Proof.
  solve_cert (cert1 E B [0;1;0;1;0;1] [0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm188 := Eval compute in (TM_from_str "1RB1RB_0RC0LF_1LD0RA_0LE---_1RA0LC_1RE1LB").

Theorem nonhalt188: ~halts tm188 c0.
Proof.
  solve_cert (cert1 B A [1;0;1;0;0;0;1] [0;0;1;0;0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm189 := Eval compute in (TM_from_str "1RB0LB_1LC0RD_1LA1LD_0RA0RE_1RD0RF_0RB---").

Theorem nonhalt189: ~halts tm189 c0.
Proof.
  solve_cert (cert1 B D [0;1;1;0;1] [0;0;0;0;1] [0;0;0;0;0;1] [0;0;1;0;0;1] [0;0;1]
    (fun n => [1;0;1;0]^^n *> [] *> const 0)
    (fun n m => [1;0;1;0]^^m *> [0] *> [1;0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm190 := Eval compute in (TM_from_str "1RB0LB_0RC1LD_1LD1RE_0LA---_0RF1RB_0LA0RB").

Theorem nonhalt190: ~halts tm190 c0.
Proof.
  solve_cert (cert1 D E [1] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm191 := Eval compute in (TM_from_str "1RB1RF_1RC0LE_0RD1LC_1LA1LF_---1LB_1RA0RA").

Theorem nonhalt191: ~halts tm191 c0.
Proof.
  solve_cert (cert1 C A [1;1] [0;1] [0;1] [1;1] [1]
    (fun n => [1;0]^^n *> [] *> const 0)
    (fun n m => [1;0]^^m *> [0] *> [1;0]^^n *> [] *> const 0)
    2 2 0 0 1 4).
Qed.


Definition tm192 := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LE_0RA0LD_1RF0LD_0RB---").

Theorem nonhalt192: ~halts tm192 c0.
Proof.
  solve_cert (cert1 D A [0;0;0;1;0;0;0] [0;1;1;1;0;1;0] [0;1;1;0;1;0] [0;1;1;0;1;1] []
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 5).
Qed.


Definition tm193 := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RB_0RB1RF_0RA---").

Theorem nonhalt193: ~halts tm193 c0.
Proof.
  solve_cert (cert1 D E [0] [1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;0;1]^^n *> [] *> const 0)
    (fun n m => [0;0;1]^^m *> [1] *> [0;0;1]^^n *> [] *> const 0)
    1 1 0 1 1 2).
Qed.


Definition tm194 := Eval compute in (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0LA0RB_0RD1RD_0LE---").

Theorem nonhalt194: ~halts tm194 c0.
Proof.
  solve_cert (cert1 B B [0;0;1] [0;0;1] [0;0;0;1] [0;1;0;1] [0;1]
    (fun n => [0;1;0]^^n *> [] *> const 0)
    (fun n m => [0;1;0]^^m *> [0] *> [0;1;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm195 := Eval compute in (TM_from_str "1RB1RE_0LB1LC_1LD0LD_1RA0RB_0RF0RA_0RD---").

Theorem nonhalt195: ~halts tm195 c0.
Proof.
  solve_cert (cert1 D A [1;1;1;1] [0;1;0;1] [0;1] [1;1] [1]
    (fun n => [1;0;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0;0]^^m *> [0;0;0] *> [1;0;0;0]^^n *> [] *> const 0)
    2 2 0 0 1 5).
Qed.


Definition tm196 := Eval compute in (TM_from_str "1LB0RC_1RA0LE_1RD0LA_1RA1RF_0RC1LE_0RA---").

Theorem nonhalt196: ~halts tm196 c0.
Proof.
  solve_cert (cert1 E A [0;1;0;0] [1;1;0;0] [1;1;0;0] [1;1;0;1] []
    (fun n => [1;0;0]^^n *> [] *> const 0)
    (fun n m => [1;0;0]^^m *> [0] *> [1;0;0]^^n *> [] *> const 0)
    2 2 0 1 1 4).
Qed.


