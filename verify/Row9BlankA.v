(** Original815 row9 does not halt from the literal blank-A initial state.

    No changed-start theorem, other machine classification, or previously
    submitted pull request is a premise.  All finite certificate equations
    are checked in Row9CertificateCalls; Row9Certificate transports finite
    halting to the universally productive family in Row9Family. *)
From BusyCoq Require Import Individual62 Row9Machine Row9Bridge
  Row9Operators Row9Family Row9Certificate.
Require Import String.

Theorem nonhalt :
  ~ halts (TM_from_str "1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---") c0.
Proof.
  change (~ halts Row9Raw.tm c0).
  rewrite blank_halts_iff_K, row9_selected_path.
  exact selected_numeric_endpoint_nonhalting.
Qed.

Print Assumptions nonhalt.
