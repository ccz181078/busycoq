Require Export String.
Require Export NArith.
From BusyCoq Require Export Individual33.
From BusyCoq Require Export CTL.

Module CTLDecider33 := CTLDecider BB33.
Export CTLDecider33.

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

Ltac Nsolve_cert cert :=
  match goal with
  | |- ~halts (TM_from_str ?tm) c0 =>
    idtac tm;
    rewrite halts_halts';
    eapply (decide_nonhalt_spec _ cert);
    native_cast_no_check (eq_refl true)
  end.


