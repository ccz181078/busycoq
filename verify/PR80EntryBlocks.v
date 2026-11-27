(* 1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool Lists.Streams List Arith Lia ZifyNat ZifyN ZifyBool NArith ZArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

From BusyCoq Require Import PR80Core.

Section Cml.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

(* Run the certified symbolic machine to obtain the endpoint. Ltac only
   proposes a closed equality; Coq checks it before it is used by a bridge. *)
Local Notation "'computed_symbolic_certificate' bits start" :=
  (ltac:(
    let lhs := constr:(symRunBits bits start) in
    let rhs := eval vm_compute in lhs in
    exact (lhs = rhs))) (at level 10, bits at level 0, start at level 0).

(* #### Stage 7: `InvConvMLoop` → `ReachesInvM` (36 `rfl` lemmas) *)

Lemma rfl_cml_0_z1_r0 :
  computed_symbolic_certificate [7; 6; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_0_z1_r1 :
  computed_symbolic_certificate [7; 6; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_0_z2 :
  computed_symbolic_certificate [7; 6; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_0_z3 :
  computed_symbolic_certificate [7; 6; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_0_z4 :
  computed_symbolic_certificate [4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_0_z5 :
  computed_symbolic_certificate [4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_1_z1_r0 :
  computed_symbolic_certificate [7; 5; 4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_1_z1_r1 :
  computed_symbolic_certificate [7; 5; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_1_z2 :
  computed_symbolic_certificate [7; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_1_z3 :
  computed_symbolic_certificate [7; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_1_z4 :
  computed_symbolic_certificate [4; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_1_z5 :
  computed_symbolic_certificate [4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_2_z1_r0 :
  computed_symbolic_certificate [7; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_2_z1_r1 :
  computed_symbolic_certificate [7; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_2_z2 :
  computed_symbolic_certificate [7; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_2_z3 :
  computed_symbolic_certificate [6; 5; 4; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_2_z4 :
  computed_symbolic_certificate [4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_2_z5 :
  computed_symbolic_certificate [4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_3_z1_r0 :
  computed_symbolic_certificate [6; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_3_z1_r1 :
  computed_symbolic_certificate [8; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_3_z2 :
  computed_symbolic_certificate [5; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_3_z3 :
  computed_symbolic_certificate [8; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_3_z4 :
  computed_symbolic_certificate [4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_3_z5 :
  computed_symbolic_certificate [4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_4_z1_r0 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_4_z1_r1 :
  computed_symbolic_certificate [7; 6; 5; 4; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_4_z2 :
  computed_symbolic_certificate [7; 6; 5; 4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_4_z3 :
  computed_symbolic_certificate [7; 6; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_4_z4 :
  computed_symbolic_certificate [4; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_4_z5 :
  computed_symbolic_certificate [4; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_5_z1_r0 :
  computed_symbolic_certificate [6; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_5_z1_r1 :
  computed_symbolic_certificate [6; 4; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symZero); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_5_z2 :
  computed_symbolic_certificate [6; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symOne); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_5_z3 :
  computed_symbolic_certificate [6; 4; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 2%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_5_z4 :
  computed_symbolic_certificate [4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (symZero); sr_pair 2 0 (symConst 3%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cml_5_z5 :
  computed_symbolic_certificate [4; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (symZero); sr_pair 2 0 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma convMLoop_step_0 (pZ : nat)
  (ih : forall pZ', pZ' < pZ -> forall (j : nat) (hj : j < 6) (pA pM pC : nat),
    InvConvMLoop j pA pM pZ' pC -> ReachesInvM (convMLoopCfg j pA pM pZ' pC))
  (pA pM pC : nat) (hinv : InvConvMLoop 0 pA pM pZ pC) :
  ReachesInvM (convMLoopCfg 0 pA pM pZ pC).
Proof.
  destruct hinv as [hA [hM [hZ [h9M hC]]]].
  cbn [Nat.eqb] in h9M.
  destruct (pZ) as [| [| [| [| [| u1]]]]] eqn:hZeq.
  {
    fast_lia.
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_0_z1_r0) (eval_convMLoop (v5 u0 0 u2 u3 0) 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 28%N) (symConst 12%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2213%N) (u2 + 36) (4 * u0 + u3 + (#2214)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 36), (1), (4 * u0 + u3 + (#2214)), (4). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_0_z1_r1) (eval_convMLoop (v5 u0 0 u2 u3 0) 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 22%N) (symConst 9%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2227%N) (u2 + 36) (4 * u0 + u3 + (#2228)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 36), (1), (4 * u0 + u3 + (#2228)), (3). split; [solve_inv | exact hstep].
    }
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_0_z2) (eval_convMLoop (v5 u0 0 u2 u3 0) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 2 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 30%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 12%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2109%N) (u2 + 37) (u0 + (#51)) (u3 + (#2110)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 37), (u0 + (#51)), (u3 + (#2110)), (4). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_0_z3) (eval_convMLoop (v5 u0 0 u2 u3 0) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 3 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 22%N) (symConst 9%N) (mkSymN 1%N 0%N 0%N 1%N 0%N 2173%N) (u2 + 37) (u0 + u3 + (#2174)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 37), (1), (u0 + u3 + (#2174)), (3). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_0_z4) (eval_convMLoop (v5 u0 0 u2 u3 0) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (4) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 0) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (1) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (1) (ltac:(fast_lia)) 1 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (S (u1)))))) with (u1 + 5) in * by fast_lia.
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_cml_0_z5) (eval_convMLoop (v5 u0 u1 u2 u3 0) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (u1 + 5) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 0) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (u1 + 2) (ltac:(fast_lia)) 1 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma convMLoop_step_1 (pZ : nat)
  (ih : forall pZ', pZ' < pZ -> forall (j : nat) (hj : j < 6) (pA pM pC : nat),
    InvConvMLoop j pA pM pZ' pC -> ReachesInvM (convMLoopCfg j pA pM pZ' pC))
  (pA pM pC : nat) (hinv : InvConvMLoop 1 pA pM pZ pC) :
  ReachesInvM (convMLoopCfg 1 pA pM pZ pC).
Proof.
  destruct hinv as [hA [hM [hZ [h9M hC]]]].
  cbn [Nat.eqb] in h9M.
  destruct (pZ) as [| [| [| [| [| u1]]]]] eqn:hZeq.
  {
    fast_lia.
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_1_z1_r0) (eval_convMLoop (v5 u0 0 u2 u3 0) 1 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 37%N) (symConst 22%N) (symConst 9%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2216%N) (u2 + 38) (4 * u0 + u3 + (#2217)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 38), (1), (4 * u0 + u3 + (#2217)), (3). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_1_z1_r1) (eval_convMLoop (v5 u0 0 u2 u3 0) 1 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 37%N) (symConst 16%N) (symConst 6%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2230%N) (u2 + 38) (4 * u0 + u3 + (#2231)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 38), (1), (4 * u0 + u3 + (#2231)), (2). split; [solve_inv | exact hstep].
    }
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_1_z2) (eval_convMLoop (v5 u0 0 u2 u3 0) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 2 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 24%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 9%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2112%N) (u2 + 39) (u0 + (#51)) (u3 + (#2113)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 39), (u0 + (#51)), (u3 + (#2113)), (3). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_1_z3) (eval_convMLoop (v5 u0 0 u2 u3 0) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 3 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 16%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 1%N 0%N 2176%N) (u2 + 39) (u0 + u3 + (#2177)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 39), (1), (u0 + u3 + (#2177)), (2). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_1_z4) (eval_convMLoop (v5 u0 0 u2 u3 0) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (4) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 0) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (1) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (1) (ltac:(fast_lia)) 2 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (S (u1)))))) with (u1 + 5) in * by fast_lia.
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_cml_1_z5) (eval_convMLoop (v5 u0 u1 u2 u3 0) 1 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (u1 + 5) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 0) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (u1 + 2) (ltac:(fast_lia)) 2 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma convMLoop_step_2 (pZ : nat)
  (ih : forall pZ', pZ' < pZ -> forall (j : nat) (hj : j < 6) (pA pM pC : nat),
    InvConvMLoop j pA pM pZ' pC -> ReachesInvM (convMLoopCfg j pA pM pZ' pC))
  (pA pM pC : nat) (hinv : InvConvMLoop 2 pA pM pZ pC) :
  ReachesInvM (convMLoopCfg 2 pA pM pZ pC).
Proof.
  destruct hinv as [hA [hM [hZ [h9M hC]]]].
  cbn [Nat.eqb] in h9M.
  destruct (pZ) as [| [| [| [| [| u1]]]]] eqn:hZeq.
  {
    fast_lia.
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_2_z1_r0) (eval_convMLoop (v5 u0 0 u2 u3 0) 2 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 39%N) (symConst 16%N) (symConst 6%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2219%N) (u2 + 40) (4 * u0 + u3 + (#2220)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 40), (1), (4 * u0 + u3 + (#2220)), (2). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_2_z1_r1) (eval_convMLoop (v5 u0 0 u2 u3 0) 2 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 39%N) (symConst 10%N) (symConst 3%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2233%N) (u2 + 40) (4 * u0 + u3 + (#2234)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 40), (1), (4 * u0 + u3 + (#2234)), (1). split; [solve_inv | exact hstep].
    }
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_2_z2) (eval_convMLoop (v5 u0 0 u2 u3 0) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 2 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 18%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 6%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2115%N) (u2 + 41) (u0 + (#51)) (u3 + (#2116)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 41), (u0 + (#51)), (u3 + (#2116)), (2). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_2_z3) (eval_convMLoop (v5 u0 0 u2 u3 0) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 3 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 10%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 1%N 0%N 2179%N) (u2 + 41) (u0 + u3 + (#2180)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 41), (1), (u0 + u3 + (#2180)), (1). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_2_z4) (eval_convMLoop (v5 u0 0 u2 u3 0) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (4) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 0) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (1) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (1) (ltac:(fast_lia)) 5 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (S (u1)))))) with (u1 + 5) in * by fast_lia.
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_cml_2_z5) (eval_convMLoop (v5 u0 u1 u2 u3 0) 2 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (u1 + 5) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 0) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (u1 + 2) (ltac:(fast_lia)) 5 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma convMLoop_step_3 (pZ : nat)
  (ih : forall pZ', pZ' < pZ -> forall (j : nat) (hj : j < 6) (pA pM pC : nat),
    InvConvMLoop j pA pM pZ' pC -> ReachesInvM (convMLoopCfg j pA pM pZ' pC))
  (pA pM pC : nat) (hinv : InvConvMLoop 3 pA pM pZ pC) :
  ReachesInvM (convMLoopCfg 3 pA pM pZ pC).
Proof.
  destruct hinv as [hA [hM [hZ [h9M hC]]]].
  cbn [Nat.eqb] in h9M.
  destruct (pZ) as [| [| [| [| [| u1]]]]] eqn:hZeq.
  {
    fast_lia.
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_3_z1_r0) (eval_convMLoop (v5 u0 0 u2 u3 0) 3 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 43%N) (symConst 4%N) (symZero) (mkSymN 4%N 0%N 0%N 1%N 0%N 2225%N) (u2 + 44) (4 * u0 + u3 + (#2226)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 44), (1), (4 * u0 + u3 + (#2226)), (0). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_3_z1_r1) (eval_convMLoop (v5 u0 0 u2 u3 0) 3 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 32%N) (symConst 34%N) (symConst 15%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2221%N) (u2 + 33) (4 * u0 + u3 + (#2222)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 33), (1), (4 * u0 + u3 + (#2222)), (5). split; [solve_inv | exact hstep].
    }
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_3_z2) (eval_convMLoop (v5 u0 0 u2 u3 0) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 2 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 44%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2121%N) (u2 + 45) (u0 + (#51)) (u3 + (#2122)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 45), (u0 + (#51)), (u3 + (#2122)), (0). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_3_z3) (eval_convMLoop (v5 u0 0 u2 u3 0) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 3 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 33%N) (symConst 34%N) (symConst 15%N) (mkSymN 1%N 0%N 0%N 1%N 0%N 2167%N) (u2 + 34) (u0 + u3 + (#2168)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 34), (1), (u0 + u3 + (#2168)), (5). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_3_z4) (eval_convMLoop (v5 u0 0 u2 u3 0) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (4) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 0) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (1) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (1) (ltac:(fast_lia)) 4 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (S (u1)))))) with (u1 + 5) in * by fast_lia.
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_cml_3_z5) (eval_convMLoop (v5 u0 u1 u2 u3 0) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (u1 + 5) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 0) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (u1 + 2) (ltac:(fast_lia)) 4 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma convMLoop_step_4 (pZ : nat)
  (ih : forall pZ', pZ' < pZ -> forall (j : nat) (hj : j < 6) (pA pM pC : nat),
    InvConvMLoop j pA pM pZ' pC -> ReachesInvM (convMLoopCfg j pA pM pZ' pC))
  (pA pM pC : nat) (hinv : InvConvMLoop 4 pA pM pZ pC) :
  ReachesInvM (convMLoopCfg 4 pA pM pZ pC).
Proof.
  destruct hinv as [hA [hM [hZ [h9M hC]]]].
  cbn [Nat.eqb] in h9M.
  destruct (pZ) as [| [| [| [| [| u1]]]]] eqn:hZeq.
  {
    fast_lia.
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_4_z1_r0) (eval_convMLoop (v5 u0 0 u2 u3 0) 4 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 34%N) (symConst 15%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2210%N) (u2 + 35) (4 * u0 + u3 + (#2211)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 35), (1), (4 * u0 + u3 + (#2211)), (5). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_4_z1_r1) (eval_convMLoop (v5 u0 0 u2 u3 0) 4 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 28%N) (symConst 12%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2224%N) (u2 + 35) (4 * u0 + u3 + (#2225)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 35), (1), (4 * u0 + u3 + (#2225)), (4). split; [solve_inv | exact hstep].
    }
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_4_z2) (eval_convMLoop (v5 u0 0 u2 u3 0) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 2 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 36%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 15%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2106%N) (u2 + 36) (u0 + (#51)) (u3 + (#2107)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 36), (u0 + (#51)), (u3 + (#2107)), (5). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_4_z3) (eval_convMLoop (v5 u0 0 u2 u3 0) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 3 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 28%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 1%N 0%N 2170%N) (u2 + 36) (u0 + u3 + (#2171)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 36), (1), (u0 + u3 + (#2171)), (4). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_4_z4) (eval_convMLoop (v5 u0 0 u2 u3 0) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (4) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 0) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 47) (1) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (1) (ltac:(fast_lia)) 0 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 47) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (S (u1)))))) with (u1 + 5) in * by fast_lia.
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_cml_4_z5) (eval_convMLoop (v5 u0 u1 u2 u3 0) 4 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (u1 + 5) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 0) 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 46%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 47) (u1 + 2) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (u1 + 2) (ltac:(fast_lia)) 0 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 47) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma convMLoop_step_5 (pZ : nat)
  (ih : forall pZ', pZ' < pZ -> forall (j : nat) (hj : j < 6) (pA pM pC : nat),
    InvConvMLoop j pA pM pZ' pC -> ReachesInvM (convMLoopCfg j pA pM pZ' pC))
  (pA pM pC : nat) (hinv : InvConvMLoop 5 pA pM pZ pC) :
  ReachesInvM (convMLoopCfg 5 pA pM pZ pC).
Proof.
  destruct hinv as [hA [hM [hZ [h9M hC]]]].
  cbn [Nat.eqb] in h9M.
  destruct (pZ) as [| [| [| [| [| u1]]]]] eqn:hZeq.
  {
    fast_lia.
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_5_z1_r0) (eval_convMLoop (v5 u0 0 u2 u3 0) 5 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 41%N) (symConst 10%N) (symConst 3%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 2222%N) (u2 + 42) (4 * u0 + u3 + (#2223)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 42), (1), (4 * u0 + u3 + (#2223)), (1). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_5_z1_r1) (eval_convMLoop (v5 u0 0 u2 u3 0) 5 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 1 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 41%N) (symConst 4%N) (symZero) (mkSymN 4%N 0%N 0%N 1%N 0%N 2236%N) (u2 + 42) (4 * u0 + u3 + (#2237)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 42), (1), (4 * u0 + u3 + (#2237)), (0). split; [solve_inv | exact hstep].
    }
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_5_z2) (eval_convMLoop (v5 u0 0 u2 u3 0) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symOne) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 2 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z2 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 0%N 0%N 50%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2118%N) (u2 + 43) (u0 + (#51)) (u3 + (#2119)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 43), (u0 + (#51)), (u3 + (#2119)), (1). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_5_z3) (eval_convMLoop (v5 u0 0 u2 u3 0) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 2%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM 3 pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 4%N) (symZero) (mkSymN 1%N 0%N 0%N 1%N 0%N 2182%N) (u2 + 43) (u0 + u3 + (#2183)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    exists (u2 + 43), (1), (u0 + u3 + (#2183)), (0). split; [solve_inv | exact hstep].
  }
  {
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cml_5_z4) (eval_convMLoop (v5 u0 0 u2 u3 0) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symConst 3%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (4) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 0 u2 u3 0) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (symZero) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (1) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (1) (ltac:(fast_lia)) 3 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
  {
    replace (S (S (S (S (S (u1)))))) with (u1 + 5) in * by fast_lia.
    (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
    (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
    (set (u3 := pC - (#2120)) in * || pose (u3 := pC - (#2120))).
    pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 u1 u2 u3 0) rfl_cml_5_z5) (eval_convMLoop (v5 u0 u1 u2 u3 0) 5 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2119%N) pA pM (u1 + 5) pC (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_convMLoop (v5 u0 u1 u2 u3 0) 3 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 1%N 0%N 0%N 0%N 1%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 2124%N) (u0 + (#50)) (u2 + 46) (u1 + 2) (u3 + (#2125)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
    destruct (ih (u1 + 2) (ltac:(fast_lia)) 3 (ltac:(fast_lia)) (u0 + (#50)) (u2 + 46) (u3 + (#2125)) (ltac:(solve_inv))) as [m' [z' [c' [k' [hm' hrest]]]]].
    exists m', z', c', k'. split; [exact hm' | exact (ptrans hstep hrest)].
  }
Qed.


Lemma convMLoop_to_M (pZ : nat) :
  forall (i : nat) (hi : i < 6) (pA pM pC : nat),
    InvConvMLoop i pA pM pZ pC -> ReachesInvM (convMLoopCfg i pA pM pZ pC).
Proof.
  induction pZ as [pZ ih] using lt_wf_ind.
  intros i hi pA pM pC hinv.
  destruct i as [| [| [| [| [| [| _i]]]]]]; [| | | | | | fast_lia].
  - exact (convMLoop_step_0 pZ ih pA pM pC hinv).
  - exact (convMLoop_step_1 pZ ih pA pM pC hinv).
  - exact (convMLoop_step_2 pZ ih pA pM pC hinv).
  - exact (convMLoop_step_3 pZ ih pA pM pC hinv).
  - exact (convMLoop_step_4 pZ ih pA pM pC hinv).
  - exact (convMLoop_step_5 pZ ih pA pM pC hinv).
Qed.


(* #### Stage 6a: `InvConvSimple` → `ReachesInvM` (12 `rfl` lemmas) *)

Lemma rfl_cs_0_r0 :
  computed_symbolic_certificate [7; 6; 5] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_0_r1 :
  computed_symbolic_certificate [7; 6; 5; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_1_r0 :
  computed_symbolic_certificate [7; 5; 4; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_1_r1 :
  computed_symbolic_certificate [7; 6; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_2_r0 :
  computed_symbolic_certificate [7; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_2_r1 :
  computed_symbolic_certificate [7; 5; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_3_r0 :
  computed_symbolic_certificate [6; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_3_r1 :
  computed_symbolic_certificate [6; 4; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_4_r0 :
  computed_symbolic_certificate [8; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_4_r1 :
  computed_symbolic_certificate [5; 4] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_5_r0 :
  computed_symbolic_certificate [6; 5; 4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cs_5_r1 :
  computed_symbolic_certificate [6; 5; 4; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


Lemma convSimple_to_M (i : nat) (hi : i < 6) (pA pM R0 : nat)
  (hinv : InvConvSimple i pA pM R0) : ReachesInvM (convSimpleCfg i pA pM R0).
Proof.
  destruct hinv as [hA [hM [hR0 [h9M h2120]]]].
  destruct i as [| [| [| [| [| [| _i]]]]]]; [| | | | | | fast_lia].
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_0_r0) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 0 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 33%N) (symConst 28%N) (symConst 12%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 99%N) (u2 + 34) (4 * u0 + u3 + (#100)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 34), (1), (4 * u0 + u3 + (#100)), (4). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_0_r1) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 0 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 33%N) (symConst 34%N) (symConst 15%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 89%N) (u2 + 34) (4 * u0 + u3 + (#90)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 34), (1), (4 * u0 + u3 + (#90)), (5). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_1_r0) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 1 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 22%N) (symConst 9%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 102%N) (u2 + 36) (4 * u0 + u3 + (#103)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 36), (1), (4 * u0 + u3 + (#103)), (3). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_1_r1) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 1 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 28%N) (symConst 12%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 92%N) (u2 + 36) (4 * u0 + u3 + (#93)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 36), (1), (4 * u0 + u3 + (#93)), (4). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_2_r0) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 2 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 37%N) (symConst 16%N) (symConst 6%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 105%N) (u2 + 38) (4 * u0 + u3 + (#106)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 38), (1), (4 * u0 + u3 + (#106)), (2). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_2_r1) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 2 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 37%N) (symConst 22%N) (symConst 9%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 95%N) (u2 + 38) (4 * u0 + u3 + (#96)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 38), (1), (4 * u0 + u3 + (#96)), (3). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_3_r0) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 3 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 41%N) (symConst 4%N) (symZero) (mkSymN 4%N 0%N 0%N 1%N 0%N 111%N) (u2 + 42) (4 * u0 + u3 + (#112)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 42), (1), (4 * u0 + u3 + (#112)), (0). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_3_r1) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 3 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 41%N) (symConst 10%N) (symConst 3%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 101%N) (u2 + 42) (4 * u0 + u3 + (#102)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 42), (1), (4 * u0 + u3 + (#102)), (1). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_4_r0) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 4 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 32%N) (symConst 34%N) (symConst 15%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 96%N) (u2 + 33) (4 * u0 + u3 + (#97)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 33), (1), (4 * u0 + u3 + (#97)), (5). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_4_r1) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 4 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 43%N) (symConst 4%N) (symZero) (mkSymN 4%N 0%N 0%N 1%N 0%N 104%N) (u2 + 44) (4 * u0 + u3 + (#105)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 44), (1), (4 * u0 + u3 + (#105)), (0). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
    destruct hA_mod as [hrA | hrA].
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_5_r0) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 5 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 48%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 39%N) (symConst 10%N) (symConst 3%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 108%N) (u2 + 40) (4 * u0 + u3 + (#109)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 40), (1), (4 * u0 + u3 + (#109)), (1). split; [solve_inv | exact hstep].
    }
    {
      (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := R0 - 4) in * || pose (u3 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 0) rfl_cs_5_r1) (eval_convSimple_2 (v5 u0 0 u2 u3 0) 5 symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 1%N 0%N 3%N) pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 0) (mkSymN 0%N 0%N 1%N 0%N 0%N 39%N) (symConst 16%N) (symConst 6%N) (mkSymN 4%N 0%N 0%N 1%N 0%N 98%N) (u2 + 40) (4 * u0 + u3 + (#99)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 40), (1), (4 * u0 + u3 + (#99)), (2). split; [solve_inv | exact hstep].
    }
  }
Qed.


End Cml.

Section EntryRows.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

(* Run the certified symbolic machine to obtain the endpoint. Ltac only
   proposes a closed equality; Coq checks it before it is used by a bridge. *)
Local Notation "'computed_symbolic_certificate' bits start" :=
  (ltac:(
    let lhs := constr:(symRunBits bits start) in
    let rhs := eval vm_compute in lhs in
    exact (lhs = rhs))) (at level 10, bits at level 0, start at level 0).

(* #### Stage 6b: `InvConvEntryZ2` & `InvConvEntry` → `ReachesInvM` (66 `rfl` lemmas) *)

Lemma rfl_cez2_0_b0_a0 :
  computed_symbolic_certificate [7; 6; 5; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_0_b0_a1 :
  computed_symbolic_certificate [7; 6; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_0_b1 :
  computed_symbolic_certificate [7; 6; 5; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b0_z1 :
  computed_symbolic_certificate [7; 6; 5] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b0_z3 :
  computed_symbolic_certificate [7; 6; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b0_z4 :
  computed_symbolic_certificate [7; 6; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b0_z5 :
  computed_symbolic_certificate [4; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 3%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b0_z6 :
  computed_symbolic_certificate [4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b1_z1 :
  computed_symbolic_certificate [7; 6; 5; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b1_z3 :
  computed_symbolic_certificate [3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_0_b1_z4 :
  computed_symbolic_certificate [3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_1_b0_a0 :
  computed_symbolic_certificate [7; 5; 4; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_1_b0_a1 :
  computed_symbolic_certificate [7; 5; 4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_1_b1 :
  computed_symbolic_certificate [7; 5; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b0_z1 :
  computed_symbolic_certificate [7; 5; 4; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b0_z3 :
  computed_symbolic_certificate [7; 5; 4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b0_z4 :
  computed_symbolic_certificate [7; 5; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b0_z5 :
  computed_symbolic_certificate [4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 3%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b0_z6 :
  computed_symbolic_certificate [5] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b1_z1 :
  computed_symbolic_certificate [7; 6; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b1_z3 :
  computed_symbolic_certificate [3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_1_b1_z4 :
  computed_symbolic_certificate [3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_2_b0_a0 :
  computed_symbolic_certificate [7; 4; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_2_b0_a1 :
  computed_symbolic_certificate [7; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_2_b1 :
  computed_symbolic_certificate [7; 4; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b0_z1 :
  computed_symbolic_certificate [7; 4; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b0_z3 :
  computed_symbolic_certificate [7; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b0_z4 :
  computed_symbolic_certificate [7; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b0_z5 :
  computed_symbolic_certificate [4; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 3%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b0_z6 :
  computed_symbolic_certificate [4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b1_z1 :
  computed_symbolic_certificate [7; 5; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b1_z3 :
  computed_symbolic_certificate [3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_2_b1_z4 :
  computed_symbolic_certificate [3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_3_b0_a0 :
  computed_symbolic_certificate [6; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_3_b0_a1 :
  computed_symbolic_certificate [8; 5; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_3_b1 :
  computed_symbolic_certificate [6; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b0_z1 :
  computed_symbolic_certificate [6; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b0_z3 :
  computed_symbolic_certificate [6; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b0_z4 :
  computed_symbolic_certificate [8; 4; 3; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b0_z5 :
  computed_symbolic_certificate [5; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 3%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b0_z6 :
  computed_symbolic_certificate [5; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b1_z1 :
  computed_symbolic_certificate [6; 4; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b1_z3 :
  computed_symbolic_certificate [3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_3_b1_z4 :
  computed_symbolic_certificate [3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 3 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_4_b0_a0 :
  computed_symbolic_certificate [8; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_4_b0_a1 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_4_b1 :
  computed_symbolic_certificate [8; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b0_z1 :
  computed_symbolic_certificate [8; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b0_z3 :
  computed_symbolic_certificate [7; 6; 5; 4; 3; 2; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b0_z4 :
  computed_symbolic_certificate [7; 6; 5; 4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b0_z5 :
  computed_symbolic_certificate [4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 3%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b0_z6 :
  computed_symbolic_certificate [5] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b1_z1 :
  computed_symbolic_certificate [5; 4; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b1_z3 :
  computed_symbolic_certificate [3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_4_b1_z4 :
  computed_symbolic_certificate [3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 1 0 (symConst 2%N); sl_pair 2 0 (symZero); sl_pair 1 0 (symZero)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_5_b0_a0 :
  computed_symbolic_certificate [6; 5; 4; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_5_b0_a1 :
  computed_symbolic_certificate [6; 5; 3] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_cez2_5_b1 :
  computed_symbolic_certificate [6; 5; 4; 2] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symZero); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b0_z1 :
  computed_symbolic_certificate [6; 5; 4; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b0_z3 :
  computed_symbolic_certificate [6; 5; 3; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b0_z4 :
  computed_symbolic_certificate [6; 4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b0_z5 :
  computed_symbolic_certificate [4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (symConst 3%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b0_z6 :
  computed_symbolic_certificate [4; 3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 4%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b1_z1 :
  computed_symbolic_certificate [6; 5; 4; 3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b1_z3 :
  computed_symbolic_certificate [3; 2; 1] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (symOne); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.

Lemma rfl_ce_5_b1_z4 :
  computed_symbolic_certificate [3; 2; 1; 0] (mE, [sl_pair 0 0 (symZero); sl_pair 2 0 (symZero); sl_pair 2 0 (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N); sl_pair 1 1 (mkSymN 0%N 1%N 0%N 0%N 0%N 2%N); sl_mid (symZero); sl_pair 2 0 (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N); sl_mid (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N); sl_pair 1 1 (symZero); sl_pair 2 0 (symZero); sl_pair 1 0 (symOne)], [sr_pair 1 1 (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N); sr_pair 1 0 (symZero)]).
Proof. vm_compute. reflexivity. Qed.


End EntryRows.

Section EntryZ2.
Import PR80Core.TM1.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).
Local Notation "# x" := (N.to_nat x%N) (at level 10, format "# x").

Lemma convEntryZ2_to_M (i : nat) (hi : i < 6) (pB pA pM R0 : nat)
  (hinv : InvConvEntryZ2 i pB pA pM R0) : ReachesInvM (convEntryCfg i pB 2 pA pM R0).
Proof.
  destruct hinv as [hA [hB [hM [hR0 [h9M h2120]]]]].
  destruct i as [| [| [| [| [| [| _i]]]]]]; [| | | | | | fast_lia].
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
      destruct hA_mod as [hrA | hrA].
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_0_b0_a0) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 28%N) (symConst 12%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 137%N) (u2 + 36) (4 * u0 + 4 * u3 + u4 + (#138)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 36), (1), (4 * u0 + 4 * u3 + u4 + (#138)), (4). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_0_b0_a1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 35%N) (symConst 22%N) (symConst 9%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 151%N) (u2 + 36) (4 * u0 + 4 * u3 + u4 + (#152)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 36), (1), (4 * u0 + 4 * u3 + u4 + (#152)), (3). split; [solve_inv | exact hstep].
      }
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
      (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_0_b1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 0 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) symZero (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 28%N) (symConst 12%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 93%N) (u2 + 35) (u0 + 4 * u3 + u4 + (#94)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 35), (1), (u0 + 4 * u3 + u4 + (#94)), (4). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
      destruct hA_mod as [hrA | hrA].
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_1_b0_a0) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 37%N) (symConst 22%N) (symConst 9%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 140%N) (u2 + 38) (4 * u0 + 4 * u3 + u4 + (#141)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 38), (1), (4 * u0 + 4 * u3 + u4 + (#141)), (3). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_1_b0_a1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 37%N) (symConst 16%N) (symConst 6%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 154%N) (u2 + 38) (4 * u0 + 4 * u3 + u4 + (#155)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 38), (1), (4 * u0 + 4 * u3 + u4 + (#155)), (2). split; [solve_inv | exact hstep].
      }
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
      (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_1_b1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 1 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) symZero (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 36%N) (symConst 22%N) (symConst 9%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 96%N) (u2 + 37) (u0 + 4 * u3 + u4 + (#97)) 3 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 37), (1), (u0 + 4 * u3 + u4 + (#97)), (3). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
      destruct hA_mod as [hrA | hrA].
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_2_b0_a0) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 39%N) (symConst 16%N) (symConst 6%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 143%N) (u2 + 40) (4 * u0 + 4 * u3 + u4 + (#144)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 40), (1), (4 * u0 + 4 * u3 + u4 + (#144)), (2). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_2_b0_a1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 39%N) (symConst 10%N) (symConst 3%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 157%N) (u2 + 40) (4 * u0 + 4 * u3 + u4 + (#158)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 40), (1), (4 * u0 + 4 * u3 + u4 + (#158)), (1). split; [solve_inv | exact hstep].
      }
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
      (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_2_b1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 2 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) symZero (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 38%N) (symConst 16%N) (symConst 6%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 99%N) (u2 + 39) (u0 + 4 * u3 + u4 + (#100)) 2 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 39), (1), (u0 + 4 * u3 + u4 + (#100)), (2). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
      destruct hA_mod as [hrA | hrA].
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_3_b0_a0) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 43%N) (symConst 4%N) (symZero) (mkSymN 4%N 0%N 0%N 4%N 1%N 149%N) (u2 + 44) (4 * u0 + 4 * u3 + u4 + (#150)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 44), (1), (4 * u0 + 4 * u3 + u4 + (#150)), (0). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_3_b0_a1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 32%N) (symConst 34%N) (symConst 15%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 145%N) (u2 + 33) (4 * u0 + 4 * u3 + u4 + (#146)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 33), (1), (4 * u0 + 4 * u3 + u4 + (#146)), (5). split; [solve_inv | exact hstep].
      }
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
      (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_3_b1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 3 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) symZero (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 42%N) (symConst 4%N) (symZero) (mkSymN 1%N 0%N 0%N 4%N 1%N 105%N) (u2 + 43) (u0 + 4 * u3 + u4 + (#106)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 43), (1), (u0 + 4 * u3 + u4 + (#106)), (0). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
      destruct hA_mod as [hrA | hrA].
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_4_b0_a0) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 34%N) (symConst 15%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 134%N) (u2 + 35) (4 * u0 + 4 * u3 + u4 + (#135)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 35), (1), (4 * u0 + 4 * u3 + u4 + (#135)), (5). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_4_b0_a1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 34%N) (symConst 28%N) (symConst 12%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 148%N) (u2 + 35) (4 * u0 + 4 * u3 + u4 + (#149)) 4 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 35), (1), (4 * u0 + 4 * u3 + u4 + (#149)), (4). split; [solve_inv | exact hstep].
      }
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
      (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_4_b1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 4 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) symZero (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 33%N) (symConst 34%N) (symConst 15%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 90%N) (u2 + 34) (u0 + 4 * u3 + u4 + (#91)) 5 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 34), (1), (u0 + 4 * u3 + u4 + (#91)), (5). split; [solve_inv | exact hstep].
    }
  }
  {
    assert (hB_mod : pB mod 2 = 0 \/ pB mod 2 = 1 ) by fast_lia.
    destruct hB_mod as [hrB | hrB].
    {
      assert (hA_mod : pA mod 2 = 0 \/ pA mod 2 = 1 ) by fast_lia.
      destruct hA_mod as [hrA | hrA].
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_5_b0_a0) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 41%N) (symConst 10%N) (symConst 3%N) (mkSymN 4%N 0%N 0%N 4%N 1%N 146%N) (u2 + 42) (4 * u0 + 4 * u3 + u4 + (#147)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 42), (1), (4 * u0 + 4 * u3 + u4 + (#147)), (1). split; [solve_inv | exact hstep].
      }
      {
        (set (u0 := (pA - (#50)) / 2) in * || pose (u0 := (pA - (#50)) / 2)).
        (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
        (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
        (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
        pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_5_b0_a1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 18%N) symZero (mkSymN 2%N 0%N 0%N 0%N 0%N 50%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 41%N) (symConst 4%N) (symZero) (mkSymN 4%N 0%N 0%N 4%N 1%N 160%N) (u2 + 42) (4 * u0 + 4 * u3 + u4 + (#161)) 0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
        exists (u2 + 42), (1), (4 * u0 + 4 * u3 + u4 + (#161)), (0). split; [solve_inv | exact hstep].
      }
    }
    {
      (set (u0 := pA - (#50)) in * || pose (u0 := pA - (#50))).
      (set (u2 := pM - 46) in * || pose (u2 := pM - 46)).
      (set (u3 := (pB - 20) / 2) in * || pose (u3 := (pB - 20) / 2)).
      (set (u4 := R0 - 4) in * || pose (u4 := R0 - 4)).
      pose proof (reachesPlus_eq_both (symRunBits_sound_plus (v5 u0 0 u2 u3 u4) rfl_cez2_5_b1) (eval_convEntry_2_z2 (v5 u0 0 u2 u3 u4) 5 symZero (mkSymN 0%N 0%N 0%N 2%N 0%N 19%N) symZero (mkSymN 1%N 0%N 0%N 0%N 0%N 49%N) (mkSymN 0%N 0%N 1%N 0%N 0%N 45%N) (mkSymN 0%N 0%N 0%N 0%N 1%N 3%N) pB 2 pA pM R0 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq))) (eval_mCfg_z1 (v5 u0 0 u2 u3 u4) (mkSymN 0%N 0%N 1%N 0%N 0%N 40%N) (symConst 10%N) (symConst 3%N) (mkSymN 1%N 0%N 0%N 4%N 1%N 102%N) (u2 + 41) (u0 + 4 * u3 + u4 + (#103)) 1 (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)) (ltac:(solve_eval_eq)))) as hstep.
      exists (u2 + 41), (1), (u0 + 4 * u3 + u4 + (#103)), (1). split; [solve_inv | exact hstep].
    }
  }
Qed.


End EntryZ2.
