(** Native blank halting equivalence of the two literal BB(6) tables. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
From BusyCoq.EqvRegularPairs.Pair3 Require Import Frozen3 Pair3.
From Coq Require Import String.
Open Scope string_scope.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA1RF_1LD1RF_1LE0LA_0RB---_0RA1RE").
Definition tm' := Eval compute in (TM_from_str "1RB0LC_1LA1RE_1LD1RE_1RE0LA_0RA1RF_0RB---").
Lemma source_binding : tm = frozen3.
Proof. reflexivity. Qed.
Lemma target_binding : tm' = original751.
Proof. reflexivity. Qed.
Theorem eqv : halts tm c0 <-> halts tm' c0.
Proof. rewrite source_binding,target_binding. exact original3_751_halting_equivalence. Qed.
Print Assumptions source_binding.
Print Assumptions target_binding.
Print Assumptions eqv.
