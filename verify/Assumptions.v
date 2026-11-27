(** * Axiom audit for the deciders extracted from [Inductive_inf].

    [BBinf] instantiates [Ctx] with [Q := N] and [all_qs := []], then admits

      all_qs_spec  : forall a, In a all_qs
      all_syms_spec: forall a, In a all_syms

    (BBinf.v:56, BBinf.v:61). For an unbounded carrier these are not merely
    unproven, they are false: [In a []] is [False], so [all_qs_spec q0] is a
    proof of [False]. [Inductive_inf.v:5] applies the [Inductive] functor to
    exactly this module, so everything the extracted `decider` runs on is
    built in a context where [False] is derivable.

    TM.v:57 additionally does

      #[export] Hint Resolve all_qs_spec all_syms_spec : core.

    which places them in the default hint database. A stray [auto] or
    [trivial] anywhere in the functor body can therefore discharge a goal with
    [False] and leave no trace in the source.

    [Print Assumptions] is what detects that, and this file records the check
    for the lemmas the extracted binary's verdicts rest on. Every command below
    should print "Closed under the global context"; anything else means a
    verdict is no longer backed by a proof.

    Usage:  coqc -Q . BusyCoq Assumptions.v  *)

From Coq Require Import List NArith.
Require Import BusyCoq.Inductive_inf.

(* the simulator the two deciders below are built on *)
Print Assumptions Inductive_inf.hlin_layers_steps_spec.

(* "nonhalting" *)
Print Assumptions Inductive_inf.check_nonhalt_spec.
Print Assumptions Inductive_inf.decide_hlin_nonhalt_spec_1.

(* "halts at _ _" *)
Print Assumptions Inductive_inf.get_halts_at_spec.
Print Assumptions Inductive_inf.decide_hlin_halt_spec_1.
