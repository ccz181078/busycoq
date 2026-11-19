From BusyCoq Require Import Individual62.
Require Import String.
Require BusyCoq.CounterClass1.CounterClass1TM1Proof BusyCoq.CounterClass1.CounterClass1TM2Proof BusyCoq.CounterClass1.CounterClass1TM3Proof
  BusyCoq.CounterClass1.CounterClass1TM4Proof BusyCoq.CounterClass1.CounterClass1TM5Proof BusyCoq.CounterClass1.CounterClass1TM6Proof
  BusyCoq.CounterClass1.CounterClass1TM7Proof BusyCoq.CounterClass1.CounterClass1TM8Proof BusyCoq.CounterClass1.CounterClass1TM9Proof
  BusyCoq.CounterClass1.CounterClass1TM10Proof BusyCoq.CounterClass1.CounterClass1TM11Proof BusyCoq.CounterClass1.CounterClass1TM12Proof
  BusyCoq.CounterClass1.CounterClass1TM13Proof BusyCoq.CounterClass1.CounterClass1TM14Proof BusyCoq.CounterClass1.CounterClass1TM15Proof
  BusyCoq.CounterClass1.CounterClass1TM16Proof.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0RA---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM1Proof.nonhalt. Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC0LE_1LD1LC_0RA0LD_1RF1RA_1LB---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM2Proof.nonhalt. Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LA---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM3Proof.nonhalt. Qed.
End TM3.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RC---_1RA0LD").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM4Proof.nonhalt. Qed.
End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB---_0RC0LB_1RE0RD_1RA1RC_1RF0LD_1LB1LF").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM5Proof.nonhalt. Qed.
End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0RF---_1RA1RF").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM6Proof.nonhalt. Qed.
End TM6.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_1RB---_1RA1RF").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM7Proof.nonhalt. Qed.
End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0LC---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM8Proof.nonhalt. Qed.
End TM8.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RA0RE_1RF1RD_0LB---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM9Proof.nonhalt. Qed.
End TM9.

Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_1RA---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM10Proof.nonhalt. Qed.
End TM10.

Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1RC_0RC---_1RD0RA_1RE1RD_1LF1LE_0RC0LF").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM11Proof.nonhalt. Qed.
End TM11.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RA0LD_1RF1RA_0RA---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM12Proof.nonhalt. Qed.
End TM12.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0RC0LB_1RF0RD_1RE1RC_0LB---_1RA1RF").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM13Proof.nonhalt. Qed.
End TM13.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1LB_0RD0LC_1RA0RE_0RF1RD_0LD---").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM14Proof.nonhalt. Qed.
End TM14.

Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LB_0LD0LC_0RE0RF_0RF---_1RA1RD").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM15Proof.nonhalt. Qed.
End TM15.

Module TM16.
Definition tm := Eval compute in (TM_from_str "1LB1LA_0LC0LB_0RD0RE_0RE---_1RF1RC_1RA1RF").
Theorem nonhalt: ~halts tm c0.
Proof. exact BusyCoq.CounterClass1.CounterClass1TM16Proof.nonhalt. Qed.
End TM16.
