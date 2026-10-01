From BusyCoq Require Import Individual62 RegularInvariant62 EdgeTM617.
From BusyCoq.Eqv326408 Require Import Frozen408 Pair408.
From Coq Require Import String.
Open Scope string_scope.
Definition original326 := Eval compute in (TM_from_str "1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---").
Definition original408 := Eval compute in (TM_from_str "1RB0RE_0LC---_1RE1LD_0LE1LB_1LC0RF_1RA1LD").
Definition align (q : state6) : state6 := match q with
| A6 => A6 | B6 => D6 | C6 => E6 | D6 => C6 | E6 => F6 | F6 => B6 end.
Lemma exact_original408 : original408 = frozen408.
Proof. reflexivity. Qed.
Lemma exact_original326 : original326 = TM617.tm'.
Proof. reflexivity. Qed.
Theorem intermediate_alignment : halts TM617.tm c0 <-> halts alignedQ c0.
Proof.
 change (halts TM617.tm (A6,snd c0) <-> halts alignedQ (align A6,snd c0)).
 apply (Permute_halts_iff TM617.tm alignedQ align A6 (snd c0)). split.
 - intros q s; destruct q,s; cbn; congruence.
 - intros q s s' d q'; destruct q,s; cbn; intros H; inverts H; reflexivity.
Qed.
Theorem original326_408_blank_halting_equivalence : halts original326 c0 <-> halts original408 c0.
Proof.
 rewrite exact_original408,exact_original326.
 pose proof TM617.eqv as Hedge.
 pose proof intermediate_alignment as Halign.
 pose proof internal408_aligned_halting_equivalence as Hguarded.
 tauto.
Qed.
Print Assumptions exact_original408.
Print Assumptions exact_original326.
Print Assumptions intermediate_alignment.
Print Assumptions original326_408_blank_halting_equivalence.
