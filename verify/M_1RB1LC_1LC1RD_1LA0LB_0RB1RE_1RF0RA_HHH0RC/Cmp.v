(** int comparisons as Z comparisons, and ints as nats. *)
From Coq Require Import ZArith Uint63.
Local Open Scope Z_scope.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).

Definition nat_of (x : int) : nat := Z.to_nat φ x.

Lemma eqb_Z x y : (x =? y)%uint63 = (φ x =? φ y).
Proof.
  destruct (x =? y)%uint63 eqn:E; symmetry.
  - apply Uint63.eqb_spec in E. subst. apply Z.eqb_refl.
  - apply Z.eqb_neq. intro H. apply to_Z_inj in H. subst. rewrite (proj2 (Uint63.eqb_spec y y) eq_refl) in E. discriminate.
Qed.
Lemma ltb_Z x y : (x <? y)%uint63 = (φ x <? φ y).
Proof. destruct (x <? y)%uint63 eqn:E; symmetry; [apply Z.ltb_lt, ltb_spec, E|apply Z.ltb_ge; rewrite <- Z.nlt_ge, <- ltb_spec, E; discriminate]. Qed.
Lemma leb_Z x y : (x <=? y)%uint63 = (φ x <=? φ y).
Proof. destruct (x <=? y)%uint63 eqn:E; symmetry; [apply Z.leb_le, leb_spec, E|apply Z.leb_gt; rewrite <- Z.nle_gt, <- leb_spec, E; discriminate]. Qed.
