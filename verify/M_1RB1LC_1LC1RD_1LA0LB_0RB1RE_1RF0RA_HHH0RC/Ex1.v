(** Soundness of one visit of Check.v: [ex1] is [op]. *)
From Coq Require Import ZArith Lia Uint63 Bool PeanoNat.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check Visits Block Arith Cmp.
Local Open Scope Z_scope.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).

Lemma even_to_nat x : 0 <= x -> Nat.even (Z.to_nat x) = Z.even x.
Proof. intros. rewrite <- Zeven_of_nat, Z2Nat.id by lia. reflexivity. Qed.

Lemma ev_mod x : Z.even x = (x mod 2 =? 0).
Proof.
  rewrite (Z.div_mod x 2) at 1 by lia. rewrite Z.add_comm, Z.even_add_mul_2.
  assert (x mod 2 = 0 \/ x mod 2 = 1) as [E|E] by lia; rewrite E; reflexivity.
Qed.

Ltac nsplit := match goal with
  | |- (if (?x =? ?y)%nat then _ else _) = _ /\ _ => destruct (Nat.eqb_spec x y); try (exfalso; lia)
  | |- (if (?x <=? ?y)%nat then _ else _) = _ /\ _ => destruct (Nat.leb_spec x y); try (exfalso; lia)
  end.
Ltac isplit := match goal with
  | Hx : (if (?x =? ?y)%uint63 then _ else _) = _ |- _ => rewrite (eqb_Z x y) in Hx; revert Hx; destruct (Z.eqb_spec φ x φ y); intro Hx; try (exfalso; lia)
  | Hx : (if (?x <=? ?y)%uint63 then _ else _) = _ |- _ => rewrite (leb_Z x y) in Hx; revert Hx; destruct (Z.leb_spec φ x φ y); intro Hx; try (exfalso; lia)
  | Hx : context [if (?x <? ?y)%uint63 then _ else _] |- _ => rewrite (ltb_Z x y) in Hx; revert Hx; destruct (Z.ltb_spec φ x φ y); intro Hx; try (exfalso; lia)
  end.

Lemma ex1_ok a b : φ a < 2 ^ 58 -> φ b < 2 ^ 58 -> φ b <> 3 ->
  op (nat_of a, nat_of b) = Some (nat_of (fst (ex1 a b)), nat_of (snd (ex1 a b))) /\
  φ (fst (ex1 a b)) + φ (snd (ex1 a b)) <= φ a + φ b + 7.
Proof.
  intros Ha Hb H3. pose proof (to_Z_bounded a) as Ba. pose proof (to_Z_bounded b) as Bb.
  assert (W : wB = 2 ^ 63) by reflexivity.
  assert (A1 : φ (a + 1) = φ a + 1) by (apply phi_add_small; change (φ 1) with 1; lia).
  assert (A2 : φ (a + 2) = φ a + 2) by (apply phi_add_small; change (φ 2) with 2; lia).
  assert (A3 : φ (a + 3) = φ a + 3) by (apply phi_add_small; change (φ 3) with 3; lia).
  assert (C : φ 2 = 2 /\ φ 3 = 3 /\ φ 0 = 0 /\ φ 1 = 1 /\ φ 4 = 4 /\ φ 7 = 7 /\ φ 9 = 9) by repeat split.
  destruct C as (C2 & C3 & C0 & C1 & C4 & C7 & C9).
  assert (M2a : φ (2 * a) = 2 * φ a) by (rewrite phi_mul_small; lia).
  assert (M2b : φ (2 * b) = 2 * φ b) by (rewrite phi_mul_small; lia).
  destruct (ex1 a b) as [x y] eqn:Hx. cbn [fst snd]. unfold ex1 in Hx.
  unfold op, nat_of. cbv beta iota zeta.
  destruct (Nat.eqb_spec (Z.to_nat φ b) 3); [exfalso; lia|].
  isplit.
  { nsplit. isplit; injection Hx as <- <-; (split; [f_equal; f_equal|]); try rewrite phi_sub_small; lia. }
  nsplit. isplit.
  { nsplit. injection Hx as <- <-.
    rewrite phi_add_small, phi_sub_small, phi_add_small, M2b, ?phi_sub_small by (rewrite ?phi_sub_small, ?M2b; lia).
    split; [f_equal; f_equal|]; lia. }
  nsplit. isplit.
  { nsplit. injection Hx as <- <-. rewrite phi_add_small, M2a by (rewrite ?M2a; lia). split; [f_equal; f_equal|]; lia. }
  nsplit. isplit.
  { nsplit. injection Hx as <- <-. rewrite phi_add_small, M2a by (rewrite ?M2a; lia). split; [f_equal; f_equal|]; lia. }
  nsplit. pose proof (is_even_spec a) as Ev. rewrite even_to_nat, ev_mod by lia. revert Hx.
  destruct (is_even a); intro Hx; destruct (Z.eqb_spec (φ a mod 2) 0); try (exfalso; lia).
  { injection Hx as <- <-. rewrite phi_add_small, M2a, !phi_sub_small by (rewrite ?M2a, ?phi_sub_small; lia).
    split; [f_equal; f_equal|]; lia. }
  isplit.
  { nsplit. injection Hx as <- <-. rewrite phi_add_small, M2a by (rewrite ?M2a; lia). split; [f_equal; f_equal|]; lia. }
  nsplit. injection Hx as <- <-. rewrite phi_add_small, M2a, phi_sub_small by (rewrite ?M2a; lia).
  split; [f_equal; f_equal|]; lia.
Qed.
