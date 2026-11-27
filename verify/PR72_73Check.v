From BusyCoq Require Import Individual62.
From Coq Require Import String.
From BusyCoq Require Import VisitLaw2 PR72_73Visit.

(* One finite calculation for both machines.  The soundness theorem and
   the physical visit laws can be built without running this check. *)
Lemma visit_campaign : check 161210 = true.
Proof. native_cast_no_check (eq_refl true). Time Qed.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA0RE_1RE---"%string).
Theorem halt : halts tm c0.
Proof.
  change (halts machine72 c0).
  exact (proj1 (both_halt_of_check _ visit_campaign)).
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LE_1RD0RF_1LB1RB_0LA1RB_1RE---"%string).
Theorem halt : halts tm c0.
Proof.
  change (halts machine73 c0).
  exact (proj2 (both_halt_of_check _ visit_campaign)).
Qed.
End TM2.

Print Assumptions TM1.halt.
Print Assumptions TM2.halt.
