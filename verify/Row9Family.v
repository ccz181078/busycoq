From Coq Require Import List Arith Lia.
From BusyCoq Require Import Row9Eval Row9Algebra Row9Operators Row9Numerals.
Import ListNotations.

(** Productive nonhalting of the whole c=12 numeral family.

    One successful H advance creates two leading 2s.  Each root-level
    2 elimination does not increase a finite halting index.  Eliminating
    the two 2s brings us back to the original numeral, now at a strictly
    smaller index.  Ordinary induction on that index gives the result;
    no cycle of Boolean equivalences is used. *)

Lemma H_numeral_boundary m : 2 <= m ->
  H (7*m-12) (Some (numeral m)) = Q (Q (Some (numeral (m-2)))).
Proof.
  intro Hm. unfold H.
  rewrite power_F_numeral, numeral_boundary by exact Hm.
  apply G_nine.
Qed.

Theorem productive_numeric_family_index m : 2 <= m ->
  forall k, power (H (7*m-12)) k (Some (numeral m)) <> None.
Proof.
  intros Hm k. induction k as [|k IH].
  - discriminate.
  - intro E. rewrite power_succ_r, H_numeral_boundary in E by exact Hm.
    apply (Q_index_nonincrease_abstract F Q Z G F_none G_none Q_none Z_none F_Q F_Z G_Q) in E; [|lia].
    rewrite F_Q, F_numeral in E.
    apply (Q_index_nonincrease_abstract F Q Z G F_none G_none Q_none Z_none F_Q F_Z G_Q) in E; [|lia].
    rewrite F_numeral in E.
    replace (S (S (m-2))) with m in E by lia.
    exact (IH E).
Qed.

Theorem productive_numeric_family m : 2 <= m ->
  ~ K (7*m-12) (Some (numeral m)).
Proof.
  intros Hm [k E]. exact (productive_numeric_family_index m Hm k E).
Qed.

Corollary productive_numeric_family_steps m : 2 <= m ->
  forall k, exists W, power (H (7*m-12)) k (Some (numeral m)) = Some W.
Proof.
  intros Hm k.
  destruct (power (H (7*m-12)) k (Some (numeral m))) as [W|] eqn:E.
  - now exists W.
  - exfalso. exact (productive_numeric_family_index m Hm k E).
Qed.

Corollary productive_numeric_family_boundary m : 2 <= m ->
  ~ K (7*m-12) (Q (Q (Some (numeral (m-2))))).
Proof.
  intros Hm [k E]. apply (productive_numeric_family m Hm).
  exists (S k). now rewrite power_succ_r, H_numeral_boundary.
Qed.

Theorem selected_numeric_endpoint_nonhalting :
  ~ K 63492 (Some [2;2;5;1;1;5;1;5;1;13]).
Proof.
  pose proof (productive_numeric_family_boundary 9072 ltac:(vm_compute; lia)) as E.
  replace (7*9072-12) with 63492 in E by reflexivity.
  replace (9072-2) with 9070 in E by reflexivity.
  rewrite numeral_9070 in E. exact E.
Qed.
