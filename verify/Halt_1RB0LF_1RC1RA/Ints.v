(** Exact values of primitive-int expressions, by congruence: intermediate wraps do no harm if the final value is in range. *)
From Coq Require Import ZArith Lia Uint63.
Local Open Scope Z_scope.
Local Notation phi := Uint63.to_Z.
Notation P63 := 9223372036854775808%Z.
Notation TT := 1073741824%Z.     (* 2^30, slopes of region lines *)
Notation PP := 268435456%Z.      (* 2^28, fixed point of beta and W *)
Notation VO := 2305843009213693952%Z.  (* 2^61, offset of line values *)

Lemma wB63 : wB = P63.
Proof. reflexivity. Qed.
Lemma phi_bd63 (x : int) : 0 <= phi x < P63.
Proof. pose proof (to_Z_bounded x) as H. rewrite wB63 in H. exact H. Qed.

(** [cg x z]: the int [x] represents [z] modulo 2^63. *)
Definition cg (x : int) (z : Z) : Prop := phi x mod P63 = z mod P63.
Lemma cg_refl x : cg x (phi x).
Proof. reflexivity. Qed.
Lemma cg_add x y a b : cg x a -> cg y b -> cg (x + y)%uint63 (a + b).
Proof.
  unfold cg. intros H1 H2. rewrite add_spec, wB63, Z.mod_mod by lia.
  rewrite Z.add_mod by lia. rewrite H1, H2. rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma cg_sub x y a b : cg x a -> cg y b -> cg (x - y)%uint63 (a - b).
Proof.
  unfold cg. intros H1 H2. rewrite sub_spec, wB63, Z.mod_mod by lia.
  rewrite Zminus_mod. rewrite H1, H2. rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma cg_mul x y a b : cg x a -> cg y b -> cg (x * y)%uint63 (a * b).
Proof.
  unfold cg. intros H1 H2. rewrite mul_spec, wB63, Z.mod_mod by lia.
  rewrite Z.mul_mod by lia. rewrite H1, H2. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.
Lemma phi_of_cg x z : cg x z -> 0 <= z < P63 -> phi x = z.
Proof.
  unfold cg. intros H B. pose proof (phi_bd63 x) as Bx.
  rewrite Z.mod_small in H by lia. rewrite Z.mod_small in H by lia. exact H.
Qed.

(** [pv]: prove [phi e = z] for an arithmetic expression [e], leaving the range of [z] to lia. *)
Ltac cgs :=
  repeat first
    [ apply cg_add | apply cg_sub | apply cg_mul
    | match goal with
      | H : phi ?x = _ |- cg ?x _ => unfold cg; rewrite H; reflexivity
      end
    | apply cg_refl
    | (unfold cg; reflexivity) ].
Ltac bds := repeat match goal with |- context [phi ?x] => match goal with H : 0 <= phi x < P63 |- _ => fail 1 | _ => pose proof (phi_bd63 x) end end.
Ltac pv := apply phi_of_cg; [cgs | bds; lia].

Lemma phi_lsr x k : (0 <= phi k)%Z -> phi (x >> k)%uint63 = phi x / 2 ^ phi k.
Proof. intros _. apply lsr_spec. Qed.
Lemma phi_lsl x k v : phi x * 2 ^ phi k = v -> v < P63 -> phi (x << k)%uint63 = v.
Proof.
  intros <- H. rewrite lsl_spec, wB63. apply Z.mod_small.
  pose proof (phi_bd63 x). pose proof (Z.pow_nonneg 2 (phi k) ltac:(lia)). split; [nia|lia].
Qed.

Lemma ltb_true x y : (x <? y)%uint63 = true -> phi x < phi y.
Proof. apply ltb_spec. Qed.
Lemma ltb_false x y : (x <? y)%uint63 = false -> phi y <= phi x.
Proof.
  intros H. destruct (Z.le_gt_cases (phi y) (phi x)) as [X|X]; [exact X|].
  apply ltb_spec in X. congruence.
Qed.
Lemma leb_true x y : (x <=? y)%uint63 = true -> phi x <= phi y.
Proof. apply leb_spec. Qed.
Lemma leb_false x y : (x <=? y)%uint63 = false -> phi y < phi x.
Proof.
  intros H. destruct (Z.lt_ge_cases (phi y) (phi x)) as [X|X]; [exact X|].
  apply leb_spec in X. congruence.
Qed.
Lemma eqb_true x y : (x =? y)%uint63 = true -> phi x = phi y.
Proof. intros H. apply Uint63.eqb_spec in H. subst. reflexivity. Qed.

Lemma fl_lo (m : Z) : TT * (m / TT) <= m.
Proof. pose proof (Z.mul_div_le m TT ltac:(lia)). lia. Qed.
Lemma fl_hi (m : Z) : m < TT * (m / TT) + TT.
Proof. pose proof (Z.mul_succ_div_gt m TT ltac:(lia)). lia. Qed.
