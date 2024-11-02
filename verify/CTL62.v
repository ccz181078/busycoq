Require Export String.
Require Export NArith.
From BusyCoq Require Export Individual62.
From BusyCoq Require Export CTL.

Module CTLDecider62 := CTLDecider BB62.
Export CTLDecider62.

Open Scope N.
Open Scope string.

Ltac solve_cert cert :=
  match goal with
  | |- ~halts (TM_from_str ?tm) c0 =>
    idtac tm;
    rewrite halts_halts';
    eapply (decide_nonhalt_spec _ cert);
    vm_cast_no_check (eq_refl true)
  end.

