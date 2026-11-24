(** Arithmetic modulo 2^63 for the block checker. *)
From Coq Require Import ZArith Lia Uint63.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).

Definition cg (x y : Z) : Prop := x mod wB = y mod wB.

Lemma wB_pos : 0 < wB. Proof. reflexivity. Qed.
Lemma cg_refl x : cg x x. Proof. reflexivity. Qed.
Lemma cg_sym x y : cg x y -> cg y x. Proof. unfold cg. auto. Qed.
Lemma cg_trans x y z : cg x y -> cg y z -> cg x z. Proof. unfold cg. congruence. Qed.
Lemma cg_add x x' y y' : cg x x' -> cg y y' -> cg (x + y) (x' + y').
Proof. unfold cg. intros. rewrite Z.add_mod, H, H0, <- Z.add_mod; [reflexivity|apply Z.neq_sym, Z.lt_neq, wB_pos..]. Qed.
Lemma cg_sub x x' y y' : cg x x' -> cg y y' -> cg (x - y) (x' - y').
Proof. unfold cg. intros. rewrite Zminus_mod, H, H0, <- Zminus_mod. reflexivity. Qed.
Lemma cg_mul x x' y y' : cg x x' -> cg y y' -> cg (x * y) (x' * y').
Proof. unfold cg. intros. rewrite Z.mul_mod, H, H0, <- Z.mul_mod; [reflexivity|apply Z.neq_sym, Z.lt_neq, wB_pos..]. Qed.
Lemma cg_mod x : cg (x mod wB) x.
Proof. unfold cg. apply Z.mod_mod. apply Z.neq_sym, Z.lt_neq, wB_pos. Qed.

Lemma cg_phi_add x y : cg φ (x + y) (φ x + φ y). Proof. rewrite add_spec. apply cg_mod. Qed.
Lemma cg_phi_sub x y : cg φ (x - y) (φ x - φ y). Proof. rewrite sub_spec. apply cg_mod. Qed.
Lemma cg_phi_mul x y : cg φ (x * y) (φ x * φ y). Proof. rewrite mul_spec. apply cg_mod. Qed.
Lemma cg_phi_lsl x y : cg φ (x << y) (φ x * 2 ^ φ y). Proof. rewrite lsl_spec. apply cg_mod. Qed.

(** A residue in [0, 2^62) congruent to a value in [-2^62, 2^62) is that value. *)
Lemma cg_eq x y : cg x y -> 0 <= x < 2 ^ 62 -> - 2 ^ 62 <= y < 2 ^ 62 -> x = y.
Proof. unfold cg. change wB with (2 ^ 63). intros. lia. Qed.
Lemma cg_phi x y : cg φ x y -> 0 <= y < wB -> φ x = y.
Proof. unfold cg. intros H B. rewrite Z.mod_small in H by apply to_Z_bounded. rewrite H. apply Z.mod_small. exact B. Qed.

(** exact operations *)
Lemma phi_add_small x y : φ x + φ y < wB -> φ (x + y) = φ x + φ y.
Proof. intros. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia. Qed.
Lemma phi_sub_small x y : φ y <= φ x -> φ (x - y) = φ x - φ y.
Proof. intros. rewrite sub_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia. Qed.
Lemma phi_mul_small x y : φ x * φ y < wB -> φ (x * y) = φ x * φ y.
Proof. intros. rewrite mul_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). nia. Qed.
Lemma land_1 x : φ (x land 1) = φ x mod 2.
Proof. rewrite land_spec'. change φ 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_3 x : φ (x land 3) = φ x mod 4.
Proof. rewrite land_spec'. change φ 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_63 x : φ (x land 63) = φ x mod 64.
Proof. rewrite land_spec'. change φ 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_4095 x : φ (x land 4095) = φ x mod 4096.
Proof. rewrite land_spec'. change φ 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
