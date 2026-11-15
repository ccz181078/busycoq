(* 1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Arith PeanoNat Lia ZifyNat ZifyN PArith BinNat Nnat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := TM_from_str "1RB0RE_1LC0RA_1RE1LD_0LB0LF_1RA1RA_0LD---"%string.
Arguments tm _ : simpl never.

Local Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Local Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym_scope.
Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope nat_scope.

Local Notation "'0inf'" := (const S0).

(* ========================================================================== *)
(* Section 1: Reachability Combinators & Arithmetic Helpers                   *)
(* ========================================================================== *)

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma ps_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma p_to_s {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Lemma cons_zero_0inf : S0 >> 0inf = 0inf.
Proof. symmetry. apply const_unfold. Qed.

Lemma headLeft_cons_eq (q : Q) (a : sym) (l r : Stream sym) :
  ((a >> l) <{{q}} r) = (l {{q}}> (a >> r)).
Proof. reflexivity. Qed.

Lemma pow2_pos : forall k : nat, 0 < 2 ^ k.
Proof. induction k; simpl; lia. Qed.

Lemma pow4_pos : forall m : nat, 0 < 4 ^ m.
Proof. induction m; simpl; lia. Qed.

Lemma mod_decomp_mul (x c b : nat) (hc : 0 < c) (hb : 0 < b) :
  x mod (b * c) = c * ((x / c) mod b) + x mod c.
Proof.
  pose proof (Nat.div_mod x c ltac:(lia)) as hx.
  pose proof (Nat.mod_upper_bound x c ltac:(lia)) as hxc.
  pose proof (Nat.div_mod (x / c) b ltac:(lia)) as hq.
  pose proof (Nat.mod_upper_bound (x / c) b ltac:(lia)) as hqb.
  symmetry.
  apply (Nat.mod_unique x (b * c) ((x / c) / b)).
  - nia.
  - nia.
Qed.

Lemma mod_mul_mod_right (x c b : nat) (hc : 0 < c) (hb : 0 < b) :
  (x mod (b * c)) mod c = x mod c.
Proof.
  rewrite (mod_decomp_mul x c b hc hb).
  pose proof (Nat.mod_upper_bound x c ltac:(lia)).
  symmetry.
  apply (Nat.mod_unique _ c ((x / c) mod b)); lia.
Qed.

Lemma mod_mul_div_right (x c b : nat) (hc : 0 < c) (hb : 0 < b) :
  (x mod (b * c)) / c = (x / c) mod b.
Proof.
  rewrite (mod_decomp_mul x c b hc hb).
  pose proof (Nat.mod_upper_bound x c ltac:(lia)).
  symmetry.
  apply (Nat.div_unique _ c ((x / c) mod b) (x mod c)); lia.
Qed.

Lemma add_mul_div_left (a r b : nat) (hb : 0 < b) :
  (a * b + r) / b = a + r / b.
Proof.
  pose proof (Nat.div_mod r b ltac:(lia)) as hr.
  pose proof (Nat.mod_upper_bound r b ltac:(lia)) as hrb.
  symmetry.
  apply (Nat.div_unique (a * b + r) b (a + r / b) (r mod b)); nia.
Qed.

Lemma add_mul_mod_left (a r b : nat) (hb : 0 < b) :
  (a * b + r) mod b = r mod b.
Proof.
  pose proof (Nat.div_mod r b ltac:(lia)) as hr.
  pose proof (Nat.mod_upper_bound r b ltac:(lia)) as hrb.
  symmetry.
  apply (Nat.mod_unique (a * b + r) b (a + r / b)); nia.
Qed.

(* ========================================================================== *)
(* Section 2: Bit-Block Algebra & Core Micro/Sweep Lemmas                     *)
(* ========================================================================== *)

Fixpoint repBits (u : list sym) (n : nat) : list sym :=
  match n with
  | 0 => []
  | S n' => u ++ repBits u n'
  end.

Lemma repBits_add (u : list sym) : forall a b : nat,
  repBits u (a + b) = repBits u a ++ repBits u b.
Proof.
  induction a as [| a ih]; intros b; simpl.
  - reflexivity.
  - rewrite ih, app_assoc. reflexivity.
Qed.

Lemma repBits_succ_right (u : list sym) (n : nat) :
  repBits u (S n) = repBits u n ++ u.
Proof.
  replace (S n) with (n + 1) by lia.
  rewrite repBits_add. simpl. rewrite app_nil_r. reflexivity.
Qed.

Definition zBits (n : nat) : list sym := repBits [S0; S0] n.
Definition oBits (n : nat) : list sym := repBits [S1; S1] n.
Definition pBits (n : nat) : list sym := repBits [S0; S1] n.
Definition t10Bits (n : nat) : list sym := repBits [S1; S0] n.
Definition cBits (n : nat) : list sym := repBits [S1; S1; S0; S1; S1; S0] n.

Definition digitBits (d : nat) : list sym :=
  match d with
  | 0 => [S0; S1; S1; S0; S0; S1]
  | 1 => [S0; S0; S1; S0; S0; S1]
  | 2 => [S1; S1; S1; S0; S0; S1]
  | _ => [S1; S0; S1; S0; S0; S1]
  end.

Fixpoint dBlockBits (m val : nat) : list sym :=
  match m with
  | 0 => []
  | S m' => dBlockBits m' (val / 4) ++ digitBits (val mod 4)
  end.

Lemma dBlockBits_zero_val : forall m : nat,
  dBlockBits m 0 = repBits [S0; S1; S1; S0; S0; S1] m.
Proof.
  induction m as [| m ih].
  - reflexivity.
  - change (dBlockBits m (0 / 4) ++ digitBits (0 mod 4) = repBits [S0; S1; S1; S0; S0; S1] (S m)).
    replace (0 / 4) with 0 by reflexivity.
    replace (0 mod 4) with 0 by reflexivity.
    rewrite ih, repBits_succ_right. reflexivity.
Qed.

Lemma dBlockBits_mod : forall m val : nat,
  dBlockBits m (val mod 4 ^ m) = dBlockBits m val.
Proof.
  induction m as [| m ih]; intros val.
  - reflexivity.
  - cbn [dBlockBits].
    pose proof (pow4_pos m) as hp.
    assert (hpow : 4 ^ S m = 4 ^ m * 4) by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    rewrite hpow.
    rewrite (mod_mul_mod_right val 4 (4 ^ m) ltac:(lia) hp).
    rewrite (mod_mul_div_right val 4 (4 ^ m) ltac:(lia) hp).
    rewrite ih. reflexivity.
Qed.

Lemma dBlockBits_append : forall m2 m1 v1 v2 : nat,
  dBlockBits (m1 + m2) (v1 * 4 ^ m2 + v2 mod 4 ^ m2) =
    dBlockBits m1 v1 ++ dBlockBits m2 v2.
Proof.
  induction m2 as [| m2 ih]; intros m1 v1 v2.
  - replace (m1 + 0) with m1 by lia.
    replace (4 ^ 0) with 1 by reflexivity.
    replace (v2 mod 1) with 0 by (symmetry; apply Nat.mod_1_r).
    replace (v1 * 1 + 0) with v1 by lia.
    cbn [dBlockBits]. rewrite app_nil_r. reflexivity.
  - replace (m1 + S m2) with (S (m1 + m2)) by lia.
    cbn [dBlockBits].
    pose proof (pow4_pos m2) as hp.
    assert (hpow : 4 ^ S m2 = 4 ^ m2 * 4) by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    rewrite hpow.
    replace (v1 * (4 ^ m2 * 4)) with ((v1 * 4 ^ m2) * 4) by lia.
    rewrite (add_mul_mod_left (v1 * 4 ^ m2) (v2 mod (4 ^ m2 * 4)) 4 ltac:(lia)).
    rewrite (mod_mul_mod_right v2 4 (4 ^ m2) ltac:(lia) hp).
    rewrite (add_mul_div_left (v1 * 4 ^ m2) (v2 mod (4 ^ m2 * 4)) 4 ltac:(lia)).
    rewrite (mod_mul_div_right v2 4 (4 ^ m2) ltac:(lia) hp).
    rewrite ih, <- app_assoc. reflexivity.
Qed.

Lemma dBlockBits_cons_left (m val : nat) :
  dBlockBits (S m) val = digitBits ((val / 4 ^ m) mod 4) ++ dBlockBits m (val mod 4 ^ m).
Proof.
  pose proof (pow4_pos m) as hp.
  assert (hdecomp : val mod 4 ^ (1 + m) = ((val / 4 ^ m) mod 4) * 4 ^ m + val mod 4 ^ m).
  { assert (hpow : 4 ^ (1 + m) = 4 * 4 ^ m) by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    rewrite hpow.
    replace (4 * 4 ^ m) with (4 ^ m * 4) by lia.
    pose proof (Nat.div_mod val (4 ^ m) ltac:(lia)) as h1.
    pose proof (Nat.mod_upper_bound val (4 ^ m) ltac:(lia)) as h1b.
    pose proof (Nat.div_mod (val / 4 ^ m) 4 ltac:(lia)) as h2.
    pose proof (Nat.mod_upper_bound (val / 4 ^ m) 4 ltac:(lia)) as h2b.
    symmetry.
    apply (Nat.mod_unique val (4 ^ m * 4) ((val / 4 ^ m) / 4)); nia. }
  replace (S m) with (1 + m) by lia.
  rewrite <- (dBlockBits_mod (1 + m) val).
  rewrite hdecomp.
  rewrite (dBlockBits_append m 1 ((val / 4 ^ m) mod 4) val).
  cbn [dBlockBits].
  rewrite dBlockBits_mod.
  replace ((((val / 4 ^ m) mod 4) / 4)) with 0 by lia.
  replace ((((val / 4 ^ m) mod 4) mod 4)) with ((val / 4 ^ m) mod 4) by lia.
  reflexivity.
Qed.

Fixpoint zoBits (k val : nat) : list sym :=
  match k with
  | 0 => []
  | S k' => (if Nat.eqb (val mod 2) 0 then [S0; S0] else [S1; S1]) ++ zoBits k' (val / 2)
  end.

Lemma zoBits_zero_default : forall k : nat, zoBits k 0 *> 0inf = 0inf.
Proof.
  induction k as [| k ih].
  - reflexivity.
  - cbn [zoBits].
    replace (0 mod 2) with 0 by reflexivity.
    replace (0 / 2) with 0 by reflexivity.
    cbn [Nat.eqb app Str_app]. rewrite ih, !cons_zero_0inf. reflexivity.
Qed.

Lemma zoBits_add : forall k1 k2 val : nat,
  zoBits (k1 + k2) val = zoBits k1 val ++ zoBits k2 (val / 2 ^ k1).
Proof.
  induction k1 as [| k1 ih]; intros k2 val.
  - cbn [Nat.add zoBits app]. replace (2 ^ 0) with 1 by reflexivity. rewrite Nat.div_1_r. reflexivity.
  - cbn [Nat.add zoBits]. rewrite (ih k2 (val / 2)), <- app_assoc.
    f_equal. f_equal.
    pose proof (pow2_pos k1) as hp.
    rewrite Nat.Div0.div_div.
    replace (2 * 2 ^ k1) with (2 ^ S k1) by reflexivity.
    reflexivity.
Qed.

Lemma zoBits_pad_default (k1 k2 val : nat) (hval : val < 2 ^ k1) (hle : k1 <= k2) :
  zoBits k2 val *> 0inf = zoBits k1 val *> 0inf.
Proof.
  replace k2 with (k1 + (k2 - k1)) by lia.
  rewrite zoBits_add, Str_app_assoc.
  rewrite (Nat.div_small val (2 ^ k1) hval).
  rewrite zoBits_zero_default. reflexivity.
Qed.

Lemma zoBits_mod : forall k val : nat, zoBits k (val mod 2 ^ k) = zoBits k val.
Proof.
  induction k as [| k ih]; intros val.
  - reflexivity.
  - cbn [zoBits].
    pose proof (pow2_pos k) as hp.
    assert (hpow : 2 ^ S k = 2 ^ k * 2) by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    rewrite hpow.
    rewrite (mod_mul_mod_right val 2 (2 ^ k) ltac:(lia) hp).
    rewrite (mod_mul_div_right val 2 (2 ^ k) ltac:(lia) hp).
    rewrite ih. reflexivity.
Qed.

Lemma zoBits_zeros : forall n : nat, zoBits n 0 = zBits n.
Proof.
  induction n as [| n ih].
  - reflexivity.
  - cbn [zoBits zBits repBits].
    replace (0 mod 2) with 0 by reflexivity.
    replace (0 / 2) with 0 by reflexivity.
    simpl. rewrite ih. reflexivity.
Qed.

Lemma zoBits_ones : forall n : nat, zoBits n (2 ^ n - 1) = oBits n.
Proof.
  induction n as [| n ih].
  - reflexivity.
  - cbn [zoBits].
    pose proof (pow2_pos n) as hp.
    assert (hpow : 2 ^ S n = 2 * 2 ^ n) by reflexivity.
    assert (hmod : (2 ^ S n - 1) mod 2 = 1) by lia.
    assert (hdiv : (2 ^ S n - 1) / 2 = 2 ^ n - 1) by lia.
    rewrite hmod, hdiv. simpl. rewrite ih. reflexivity.
Qed.

Lemma zero_t10Bits_eq : forall n : nat,
  S0 :: t10Bits n = pBits n ++ [S0].
Proof.
  induction n as [| n ih].
  - reflexivity.
  - change (S0 :: S1 :: S0 :: t10Bits n = S0 :: S1 :: (pBits n ++ [S0])).
    rewrite ih. reflexivity.
Qed.

(* Fundamental TM570 Transition Micro-Lemmas *)

Lemma micro_A_c1 (l r : Stream sym) :
  l {{A}}> ([S1; S1; S0; S1; S1; S0] *> r) -->+ (rev [S0; S1; S1; S0; S0; S1] *> l) {{A}}> r.
Proof. start_progress. Qed.

Lemma micro_A_o1 (l r : Stream sym) :
  l {{A}}> ([S1; S1] *> r) -->+ (rev [S0; S1] *> l) {{A}}> r.
Proof. start_progress. Qed.

Lemma micro_A_t101 (l r : Stream sym) :
  l {{A}}> ([S1; S0] *> r) -->+ (rev [S0; S1] *> l) {{A}}> r.
Proof. start_progress. Qed.

Lemma micro_A_p1 (l r : Stream sym) :
  l {{A}}> ([S0; S1] *> r) -->+ (rev [S1; S0] *> l) {{A}}> r.
Proof. start_progress. Qed.

Lemma micro_A_0c1 (l r : Stream sym) :
  l {{A}}> (S0 >> ([S1; S1; S0; S1; S1; S0] *> r)) -->+
    (rev [S1; S0; S0; S1; S0; S1] *> l) {{A}}> (S0 >> r).
Proof. start_progress. Qed.

Lemma micro_B_c1 (l r : Stream sym) :
  l {{B}}> ([S1; S1; S0; S1; S1; S0] *> r) -->+ (rev [S0; S0; S1; S0; S1; S1] *> l) {{B}}> r.
Proof. start_progress. Qed.

Lemma micro_B_o1 (l r : Stream sym) :
  l {{B}}> ([S1; S1] *> r) -->+ (rev [S0; S0] *> l) {{E}}> r.
Proof. start_progress. Qed.

Lemma micro_B_t101 (l r : Stream sym) :
  l {{B}}> ([S1; S0] *> r) -->+ (rev [S0; S1] *> l) {{B}}> r.
Proof. start_progress. Qed.

Lemma micro_E_c1 (l r : Stream sym) :
  l {{E}}> ([S1; S1; S0; S1; S1; S0] *> r) -->+ (rev [S1; S0; S1; S0; S1; S1] *> l) {{B}}> r.
Proof. start_progress. Qed.

Lemma micro_E_o1 (l r : Stream sym) :
  l {{E}}> ([S1; S1] *> r) -->+ (rev [S1; S0] *> l) {{E}}> r.
Proof. start_progress. Qed.

Lemma micro_E_p1 (l r : Stream sym) :
  l {{E}}> ([S0; S1] *> r) -->+ (rev [S1; S0] *> l) {{E}}> r.
Proof. start_progress. Qed.

Lemma micro_A_00_bounce (l r : Stream sym) :
  l {{A}}> ([S0; S0] *> r) -->+ l <{{D}} ([S1; S1] *> r).
Proof. start_progress. Qed.

Lemma micro_P_pulse (l r : Stream sym) :
  (rev [S0; S1] *> l) <{{D}} r -->+ l <{{D}} ([S0; S0] *> r).
Proof. start_progress. Qed.

Lemma micro_D0_pulse (l r : Stream sym) :
  (rev (digitBits 0) *> l) <{{D}} r -->+ (rev (digitBits 1) *> l) {{A}}> r.
Proof. unfold digitBits; simpl rev. start_progress. Qed.

Lemma micro_D1_pulse (l r : Stream sym) :
  (rev (digitBits 1) *> l) <{{D}} r -->+ (rev (digitBits 2) *> l) {{A}}> r.
Proof. unfold digitBits; simpl rev. start_progress. Qed.

Lemma micro_D2_pulse (l r : Stream sym) :
  (rev (digitBits 2) *> l) <{{D}} r -->+ (rev (digitBits 3) *> l) {{A}}> r.
Proof. unfold digitBits; simpl rev. start_progress. Qed.

Lemma micro_D3_pulse (l r : Stream sym) :
  (rev (digitBits 3) *> l) <{{D}} r -->+ l <{{D}} ([S1; S1; S0; S1; S1; S0] *> r).
Proof. unfold digitBits; simpl rev. start_progress. Qed.

(* Multi-Copy Sweep Lemmas *)

Lemma sweep_rep_right {q : Q} {u v : list sym}
    (h1 : forall l r, l {{q}}> (u *> r) -->+ (rev v *> l) {{q}}> r) :
  forall n l r, l {{q}}> (repBits u n *> r) -->* (rev (repBits v n) *> l) {{q}}> r.
Proof.
  induction n as [| n ih]; intros l r.
  - simpl. apply evstep_refl.
  - simpl repBits. rewrite Str_app_assoc, rev_app_distr, Str_app_assoc.
    eapply etrans; [exact (p_to_s (h1 l _)) | exact (ih (rev v *> l) r)].
Qed.

Lemma sweep_rep_right_plus {q : Q} {u v : list sym}
    (h1 : forall l r, l {{q}}> (u *> r) -->+ (rev v *> l) {{q}}> r)
    {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{q}}> (repBits u n *> r) -->+ (rev (repBits v n) *> l) {{q}}> r.
Proof.
  destruct n as [| m]; [lia |].
  simpl repBits. rewrite Str_app_assoc, rev_app_distr, Str_app_assoc.
  eapply ps_trans; [exact (h1 l _) | exact (sweep_rep_right h1 m (rev v *> l) r)].
Qed.

Lemma sweep_A_c (n : nat) (l r : Stream sym) :
  l {{A}}> (cBits n *> r) -->* (rev (dBlockBits n 0) *> l) {{A}}> r.
Proof.
  rewrite dBlockBits_zero_val.
  exact (sweep_rep_right micro_A_c1 n l r).
Qed.

Lemma sweep_A_c_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{A}}> (cBits n *> r) -->+ (rev (dBlockBits n 0) *> l) {{A}}> r.
Proof.
  rewrite dBlockBits_zero_val.
  exact (sweep_rep_right_plus micro_A_c1 hn l r).
Qed.

Lemma sweep_A_o_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{A}}> (oBits n *> r) -->+ (rev (pBits n) *> l) {{A}}> r.
Proof. exact (sweep_rep_right_plus micro_A_o1 hn l r). Qed.

Lemma sweep_A_t10_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{A}}> (t10Bits n *> r) -->+ (rev (pBits n) *> l) {{A}}> r.
Proof. exact (sweep_rep_right_plus micro_A_t101 hn l r). Qed.

Lemma sweep_A_p_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{A}}> (pBits n *> r) -->+ (rev (t10Bits n) *> l) {{A}}> r.
Proof. exact (sweep_rep_right_plus micro_A_p1 hn l r). Qed.

Lemma sweep_B_t10_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{B}}> (t10Bits n *> r) -->+ (rev (pBits n) *> l) {{B}}> r.
Proof. exact (sweep_rep_right_plus micro_B_t101 hn l r). Qed.

Lemma sweep_E_o (n : nat) (l r : Stream sym) :
  l {{E}}> (oBits n *> r) -->* (rev (t10Bits n) *> l) {{E}}> r.
Proof. exact (sweep_rep_right micro_E_o1 n l r). Qed.

Lemma sweep_E_o_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{E}}> (oBits n *> r) -->+ (rev (t10Bits n) *> l) {{E}}> r.
Proof. exact (sweep_rep_right_plus micro_E_o1 hn l r). Qed.

Lemma sweep_E_p_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{E}}> (pBits n *> r) -->+ (rev (t10Bits n) *> l) {{E}}> r.
Proof. exact (sweep_rep_right_plus micro_E_p1 hn l r). Qed.

Lemma sweep_A_0c_aux : forall (n : nat) (l r : Stream sym),
  l {{A}}> (S0 >> (cBits n *> r)) -->*
    (rev (repBits [S1; S0; S0; S1; S0; S1] n) *> l) {{A}}> (S0 >> r).
Proof.
  induction n as [| n ih]; intros l r.
  - simpl. apply evstep_refl.
  - cbn [cBits repBits].
    rewrite Str_app_assoc, rev_app_distr, Str_app_assoc.
    eapply etrans; [exact (p_to_s (micro_A_0c1 l (cBits n *> r))) | exact (ih _ r)].
Qed.

Lemma rep100101_eq : forall m : nat,
  repBits [S1; S0; S0; S1; S0; S1] (S m) =
    [S1; S0; S0; S1] ++ dBlockBits m 0 ++ [S0; S1].
Proof.
  induction m as [| m ih].
  - reflexivity.
  - rewrite repBits_succ_right, ih, !dBlockBits_zero_val, repBits_succ_right.
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sweep_A_0c_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{A}}> (S0 >> (cBits n *> r)) -->+
    (rev ([S1; S0; S0; S1] ++ dBlockBits (n - 1) 0 ++ [S0; S1]) *> l) {{A}}> (S0 >> r).
Proof.
  destruct n as [| m]; [lia |].
  replace (S m - 1) with m by lia.
  rewrite <- (rep100101_eq m).
  cbn [cBits repBits].
  rewrite Str_app_assoc, rev_app_distr, Str_app_assoc.
  eapply ps_trans; [exact (micro_A_0c1 l (cBits m *> r)) | exact (sweep_A_0c_aux m _ r)].
Qed.

Lemma rep001011_eq : forall m : nat,
  repBits [S0; S0; S1; S0; S1; S1] (S m) =
    [S0; S0; S1] ++ dBlockBits m 0 ++ [S0; S1; S1].
Proof.
  induction m as [| m ih].
  - reflexivity.
  - rewrite repBits_succ_right, ih, !dBlockBits_zero_val, repBits_succ_right.
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sweep_B_c_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{B}}> (cBits n *> r) -->+
    (rev ([S0; S0; S1] ++ dBlockBits (n - 1) 0 ++ [S0; S1; S1]) *> l) {{B}}> r.
Proof.
  destruct n as [| m]; [lia |].
  replace (S m - 1) with m by lia.
  rewrite <- (rep001011_eq m).
  unfold cBits.
  exact (sweep_rep_right_plus (n := S m) micro_B_c1 ltac:(lia) l r).
Qed.

Lemma sweep_B_o_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{B}}> (oBits n *> r) -->+
    (rev ([S0; S0] ++ t10Bits (n - 1)) *> l) {{E}}> r.
Proof.
  destruct n as [| m]; [lia |].
  replace (S m - 1) with m by lia.
  cbn [oBits repBits].
  rewrite Str_app_assoc, rev_app_distr, Str_app_assoc.
  eapply ps_trans; [exact (micro_B_o1 l (oBits m *> r)) | exact (sweep_E_o m _ r)].
Qed.

Lemma sweep_E_c_plus {n : nat} (hn : 1 <= n) (l r : Stream sym) :
  l {{E}}> (cBits n *> r) -->+
    (rev ([S1; S0; S1] ++ dBlockBits (n - 1) 0 ++ [S0; S1; S1]) *> l) {{B}}> r.
Proof.
  destruct n as [| m]; [lia |].
  replace (S m - 1) with m by lia.
  cbn [cBits repBits].
  rewrite Str_app_assoc.
  pose proof (micro_E_c1 l (cBits m *> r)) as h1.
  destruct m as [| m'].
  - simpl in h1 |- *. exact h1.
  - pose proof (p_to_s (sweep_B_c_plus (n := S m') ltac:(lia)
      (rev [S1; S0; S1; S0; S1; S1] *> l) r)) as h2.
    replace (S m' - 1) with m' in h2 by lia.
    rewrite <- Str_app_assoc, <- rev_app_distr in h2.
    pose proof (ps_trans h1 h2) as hcomb.
    assert (hlist :
      [S1; S0; S1; S0; S1; S1] ++ ([S0; S0; S1] ++ dBlockBits m' 0 ++ [S0; S1; S1]) =
      [S1; S0; S1] ++ dBlockBits (S m') 0 ++ [S0; S1; S1]).
    { rewrite !dBlockBits_zero_val. simpl. reflexivity. }
    rewrite hlist in hcomb.
    exact hcomb.
Qed.

(* ========================================================================== *)
(* Section 3: Dyadic-Quartic Pulse Absorption & Carry Theory                  *)
(* ========================================================================== *)

Fixpoint Absorbs (amt : nat) (w w' : list sym) : Prop :=
  match amt with
  | 0 => w = w'
  | S amt' =>
    exists w1,
      (forall l r, (rev w *> l) <{{D}} r -->+ (rev w1 *> l) {{A}}> r) /\
      Absorbs amt' w1 w'
  end.

Lemma Absorbs_trans {n1 n2 : nat} {w w1 w2 : list sym} :
  Absorbs n1 w w1 -> Absorbs n2 w1 w2 -> Absorbs (n1 + n2) w w2.
Proof.
  revert w.
  induction n1 as [| n1 ih]; intros w h1 h2; simpl in *.
  - subst w1. exact h2.
  - destruct h1 as [wm [hstep hrest]].
    exists wm. split; [exact hstep | exact (ih wm hrest h2)].
Qed.

Lemma Absorbs_congr_left {amt : nat} {u w w' : list sym} :
  Absorbs amt w w' -> Absorbs amt (u ++ w) (u ++ w').
Proof.
  revert w.
  induction amt as [| amt ih]; intros w h; simpl in *.
  - subst w'. reflexivity.
  - destruct h as [w1 [hstep hrest]].
    exists (u ++ w1). split.
    + intros l r. rewrite !rev_app_distr, !Str_app_assoc. exact (hstep (rev u *> l) r).
    + exact (ih w1 hrest).
Qed.

Lemma dBlock_pulse_inc : forall (m val : nat), val + 1 < 4 ^ m ->
  forall l r,
    (rev (dBlockBits m val) *> l) <{{D}} r -->+
    (rev (dBlockBits m (val + 1)) *> l) {{A}}> r.
Proof.
  induction m as [| m ih]; intros val hlt l r.
  - simpl in hlt. lia.
  - cbn [dBlockBits].
    rewrite !rev_app_distr, !Str_app_assoc.
    pose proof (pow4_pos m) as hp.
    assert (hpow : 4 ^ S m = 4 * 4 ^ m) by reflexivity.
    assert (hd : val mod 4 = 0 \/ val mod 4 = 1 \/ val mod 4 = 2 \/ val mod 4 = 3) by lia.
    destruct hd as [h0 | [h1 | [h2 | h3]]].
    + assert (hdiv : (val + 1) / 4 = val / 4) by lia.
      assert (hmod : (val + 1) mod 4 = 1) by lia.
      rewrite h0, hdiv, hmod. exact (micro_D0_pulse _ r).
    + assert (hdiv : (val + 1) / 4 = val / 4) by lia.
      assert (hmod : (val + 1) mod 4 = 2) by lia.
      rewrite h1, hdiv, hmod. exact (micro_D1_pulse _ r).
    + assert (hdiv : (val + 1) / 4 = val / 4) by lia.
      assert (hmod : (val + 1) mod 4 = 3) by lia.
      rewrite h2, hdiv, hmod. exact (micro_D2_pulse _ r).
    + assert (hdiv : (val + 1) / 4 = val / 4 + 1) by lia.
      assert (hmod : (val + 1) mod 4 = 0) by lia.
      assert (hlt' : val / 4 + 1 < 4 ^ m) by lia.
      rewrite h3, hdiv, hmod.
      eapply ps_trans.
      * eapply ptrans; [exact (micro_D3_pulse _ r) | exact (ih (val / 4) hlt' l _)].
      * exact (p_to_s (micro_A_c1 _ r)).
Qed.

Lemma dBlock_pulse_carry : forall (m : nat) (l r : Stream sym),
  (rev (dBlockBits m (4 ^ m - 1)) *> l) <{{D}} r -->* l <{{D}} (cBits m *> r).
Proof.
  induction m as [| m ih]; intros l r.
  - simpl. apply evstep_refl.
  - cbn [dBlockBits].
    pose proof (pow4_pos m) as hp.
    assert (hpow : 4 ^ S m = 4 * 4 ^ m) by reflexivity.
    assert (hmod : (4 ^ S m - 1) mod 4 = 3) by lia.
    assert (hdiv : (4 ^ S m - 1) / 4 = 4 ^ m - 1) by lia.
    rewrite hmod, hdiv, rev_app_distr, Str_app_assoc.
    pose proof (p_to_s (micro_D3_pulse (rev (dBlockBits m (4 ^ m - 1)) *> l) r)) as s1.
    pose proof (ih l ([S1; S1; S0; S1; S1; S0] *> r)) as s2.
    unfold cBits in s2 |- *.
    rewrite <- Str_app_assoc, <- repBits_succ_right in s2.
    exact (etrans s1 s2).
Qed.

Lemma dBlock_pulse_carry_plus {m : nat} (hm : 1 <= m) (l r : Stream sym) :
  (rev (dBlockBits m (4 ^ m - 1)) *> l) <{{D}} r -->+ l <{{D}} (cBits m *> r).
Proof.
  destruct m as [| m']; [lia |].
  cbn [dBlockBits].
  pose proof (pow4_pos m') as hp.
  assert (hpow : 4 ^ S m' = 4 * 4 ^ m') by reflexivity.
  assert (hmod : (4 ^ S m' - 1) mod 4 = 3) by lia.
  assert (hdiv : (4 ^ S m' - 1) / 4 = 4 ^ m' - 1) by lia.
  rewrite hmod, hdiv, rev_app_distr, Str_app_assoc.
  pose proof (micro_D3_pulse (rev (dBlockBits m' (4 ^ m' - 1)) *> l) r) as s1.
  pose proof (dBlock_pulse_carry m' l ([S1; S1; S0; S1; S1; S0] *> r)) as s2.
  unfold cBits in s2 |- *.
  rewrite <- Str_app_assoc, <- repBits_succ_right in s2.
  exact (ps_trans s1 s2).
Qed.

Lemma Absorbs_db_lt (m : nat) : forall (amt val : nat), val + amt < 4 ^ m ->
  Absorbs amt (dBlockBits m val) (dBlockBits m (val + amt)).
Proof.
  induction amt as [| amt ih]; intros val hlt.
  - simpl. replace (val + 0) with val by lia. reflexivity.
  - simpl. exists (dBlockBits m (val + 1)).
    split.
    + exact (dBlock_pulse_inc m val ltac:(lia)).
    + replace (val + S amt) with ((val + 1) + amt) by lia.
      exact (ih (val + 1) ltac:(lia)).
Qed.

Lemma Absorbs_db_wrap (m : nat) {u u' : list sym}
    (hu : forall l r, (rev u *> l) <{{D}} r -->+ (rev u' *> l) {{A}}> r) :
  Absorbs (4 ^ m) (u ++ dBlockBits m 0) (u' ++ dBlockBits m 0).
Proof.
  pose proof (pow4_pos m) as hp.
  replace (4 ^ m) with ((4 ^ m - 1) + 1) by lia.
  eapply Absorbs_trans.
  - eapply Absorbs_congr_left.
    pose proof (Absorbs_db_lt m (4 ^ m - 1) 0 ltac:(lia)) as ha.
    simpl in ha. exact ha.
  - simpl. exists (u' ++ dBlockBits m 0). split; [| reflexivity].
    intros l r. rewrite !rev_app_distr, !Str_app_assoc.
    eapply ps_trans.
    + eapply sp_trans; [exact (dBlock_pulse_carry m (rev u *> l) r) | exact (hu l (cBits m *> r))].
    + exact (sweep_A_c m (rev u' *> l) r).
Qed.

Lemma Absorbs_db_zero_mul (m : nat) : forall (q : nat) {u u' : list sym},
  Absorbs q u u' ->
  Absorbs (q * 4 ^ m) (u ++ dBlockBits m 0) (u' ++ dBlockBits m 0).
Proof.
  induction q as [| q ih]; intros u u' hu; simpl in *.
  - subst u'. reflexivity.
  - destruct hu as [u1 [hstep hrest]].
    exact (Absorbs_trans (Absorbs_db_wrap m hstep) (ih u1 u' hrest)).
Qed.

Lemma Absorbs_db (m val amt : nat) {u u' : list sym}
    (hval : val < 4 ^ m)
    (hu : Absorbs ((val + amt) / 4 ^ m) u u') :
  Absorbs amt (u ++ dBlockBits m val) (u' ++ dBlockBits m ((val + amt) mod 4 ^ m)).
Proof.
  pose proof (pow4_pos m) as hp.
  destruct (Nat.lt_ge_cases (val + amt) (4 ^ m)) as [hlt | hge].
  - rewrite (Nat.div_small _ _ hlt) in hu. simpl in hu. subst u'.
    rewrite (Nat.mod_small _ _ hlt).
    exact (Absorbs_congr_left (Absorbs_db_lt m amt val hlt)).
  - pose proof (Nat.div_mod (val + amt) (4 ^ m) ltac:(lia)) as hdm.
    pose proof (Nat.mod_upper_bound (val + amt) (4 ^ m) ltac:(lia)) as hrem_lt.
    destruct ((val + amt) / 4 ^ m) as [| q'] eqn:hq; [nia |].
    simpl in hu. destruct hu as [u1 [hstep hrest]].
    assert (hamt_eq : amt = (4 ^ m - 1 - val) + 1 + q' * 4 ^ m + (val + amt) mod 4 ^ m) by nia.
    assert (h1 : Absorbs (4 ^ m - 1 - val) (u ++ dBlockBits m val) (u ++ dBlockBits m (4 ^ m - 1))).
    { apply Absorbs_congr_left.
      pose proof (Absorbs_db_lt m (4 ^ m - 1 - val) val ltac:(lia)) as ha.
      replace (val + (4 ^ m - 1 - val)) with (4 ^ m - 1) in ha by lia.
      exact ha. }
    assert (h2 : Absorbs 1 (u ++ dBlockBits m (4 ^ m - 1)) (u1 ++ dBlockBits m 0)).
    { simpl. exists (u1 ++ dBlockBits m 0). split; [| reflexivity].
      intros l r. rewrite !rev_app_distr, !Str_app_assoc.
      eapply ps_trans.
      - eapply sp_trans; [exact (dBlock_pulse_carry m (rev u *> l) r) | exact (hstep l (cBits m *> r))].
      - exact (sweep_A_c m (rev u1 *> l) r). }
    pose proof (Absorbs_db_zero_mul m q' hrest) as h3.
    assert (h4 : Absorbs ((val + amt) mod 4 ^ m) (u' ++ dBlockBits m 0)
      (u' ++ dBlockBits m ((val + amt) mod 4 ^ m))).
    { apply Absorbs_congr_left.
      pose proof (Absorbs_db_lt m ((val + amt) mod 4 ^ m) 0 ltac:(lia)) as ha.
      simpl in ha. exact ha. }
    pose proof (Absorbs_trans (Absorbs_trans (Absorbs_trans h1 h2) h3) h4) as hcomb.
    rewrite <- hamt_eq in hcomb.
    exact hcomb.
Qed.

Lemma Absorbs_p1 : forall (amt : nat) {u u' : list sym},
  Absorbs (2 * amt) u u' ->
  Absorbs amt (u ++ [S0; S1]) (u' ++ [S0; S1]).
Proof.
  induction amt as [| amt ih]; intros u u' hu.
  - simpl in *. subst u'. reflexivity.
  - replace (2 * S amt) with (S (S (2 * amt))) in hu by lia.
    destruct hu as [u1 [h1 [u2 [h2 hrest]]]].
    simpl. exists (u2 ++ [S0; S1]). split.
    + intros l r. rewrite !rev_app_distr, !Str_app_assoc.
      eapply ps_trans.
      * eapply ptrans; [| exact (h2 l ([S1; S1] *> r))].
        eapply ptrans; [| exact (micro_A_00_bounce (rev u1 *> l) r)].
        eapply ptrans; [exact (micro_P_pulse (rev u *> l) r) | exact (h1 l ([S0; S0] *> r))].
      * exact (p_to_s (micro_A_o1 (rev u2 *> l) r)).
    + exact (ih u2 u' hrest).
Qed.

Lemma Absorbs_p : forall (n amt : nat) {u u' : list sym},
  Absorbs (amt * 2 ^ n) u u' ->
  Absorbs amt (u ++ pBits n) (u' ++ pBits n).
Proof.
  induction n as [| n ih]; intros amt u u' hu.
  - replace (amt * 2 ^ 0) with amt in hu by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    unfold pBits; simpl. rewrite !app_nil_r. exact hu.
  - replace (amt * 2 ^ S n) with ((2 * amt) * 2 ^ n) in hu by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    pose proof (Absorbs_p1 amt (ih (2 * amt) u u' hu)) as hstep.
    unfold pBits in hstep |- *.
    rewrite repBits_succ_right, !app_assoc. exact hstep.
Qed.

(* Carry Semantics *)

Fixpoint Carries (strict : bool) (c : nat) (w car : list sym) : Prop :=
  match c with
  | 0 => False
  | 1 =>
    forall l r,
      if strict then
        (rev w *> l) <{{D}} r -->+ l <{{D}} (car *> r)
      else
        (rev w *> l) <{{D}} r -->* l <{{D}} (car *> r)
  | S (S c' as cm1) =>
    exists w1,
      (forall l r, (rev w *> l) <{{D}} r -->+ (rev w1 *> l) {{A}}> r) /\
      Carries strict cm1 w1 car
  end.

Lemma Carries_nil : Carries false 1 [] [].
Proof. intros l r. simpl. apply evstep_refl. Qed.

Lemma Carries_pos {strict : bool} {c : nat} {w car : list sym} :
  Carries strict c w car -> 1 <= c.
Proof. destruct c; [contradiction | lia]. Qed.

Lemma Carries_toStar_one {strict : bool} {w car : list sym}
    (h : Carries strict 1 w car) (l r : Stream sym) :
  (rev w *> l) <{{D}} r -->* l <{{D}} (car *> r).
Proof.
  specialize (h l r). destruct strict; [exact (p_to_s h) | exact h].
Qed.

Lemma Carries_of_absorbs_trans {strict : bool} :
  forall (amt c : nat) {w w1 car : list sym},
    Absorbs amt w w1 -> Carries strict c w1 car -> Carries strict (amt + c) w car.
Proof.
  induction amt as [| amt ih]; intros c w w1 car ha hc.
  - simpl in ha. subst w1. simpl. exact hc.
  - destruct ha as [wm [hstep hrest]].
    pose proof (Carries_pos hc) as hcpos.
    destruct (amt + c) as [| k] eqn:hk; [lia |].
    replace (S amt + c) with (S (S k)) by lia.
    change (exists wm0,
      (forall l r, (rev w *> l) <{{D}} r -->+ (rev wm0 *> l) {{A}}> r) /\
      Carries strict (S k) wm0 car).
    exists wm. split; [exact hstep |].
    rewrite <- hk. exact (ih c wm w1 car hrest hc).
Qed.

Lemma Carries_db_zero {strict : bool} (m : nat) (hm : 1 <= m) :
  forall (c : nat),
    forall {w car : list sym},
      Carries strict c w car ->
      Carries true (c * 4 ^ m) (w ++ dBlockBits m 0) (car ++ cBits m).
Proof.
  induction c as [c ih] using strong_induction.
  intros w car hc.
  destruct c as [| [| c']].
  - contradiction.
  - pose proof (pow4_pos m) as hp.
    assert (h1 : Absorbs (4 ^ m - 1) (w ++ dBlockBits m 0) (w ++ dBlockBits m (4 ^ m - 1))).
    { apply Absorbs_congr_left.
      pose proof (Absorbs_db_lt m (4 ^ m - 1) 0 ltac:(lia)) as ha.
      simpl in ha. exact ha. }
    assert (hlast : Carries true 1 (w ++ dBlockBits m (4 ^ m - 1)) (car ++ cBits m)).
    { intros l r. rewrite rev_app_distr, Str_app_assoc, Str_app_assoc.
      eapply ps_trans; [exact (dBlock_pulse_carry_plus hm (rev w *> l) r) |].
      exact (Carries_toStar_one hc l (cBits m *> r)). }
    pose proof (Carries_of_absorbs_trans (4 ^ m - 1) 1 h1 hlast) as hres.
    replace (4 ^ m - 1 + 1) with (1 * 4 ^ m) in hres by lia.
    exact hres.
  - destruct hc as [w1 [hstep hrest]].
    pose proof (Absorbs_db_wrap m hstep) as hwrap.
    pose proof (ih (S c') ltac:(lia) w1 car hrest) as htail.
    pose proof (Carries_of_absorbs_trans (4 ^ m) (S c' * 4 ^ m) hwrap htail) as hres.
    replace (4 ^ m + S c' * 4 ^ m) with (S (S c') * 4 ^ m) in hres by lia.
    exact hres.
Qed.

Lemma Carries_db {strict : bool} (m val : nat) (hm : 1 <= m) (hval : val < 4 ^ m)
    {c : nat} {w car : list sym}
    (hc : Carries strict c w car) :
  Carries true (c * 4 ^ m - val) (w ++ dBlockBits m val) (car ++ cBits m).
Proof.
  pose proof (pow4_pos m) as hp.
  assert (h1 : Absorbs (4 ^ m - 1 - val) (w ++ dBlockBits m val) (w ++ dBlockBits m (4 ^ m - 1))).
  { apply Absorbs_congr_left.
    pose proof (Absorbs_db_lt m (4 ^ m - 1 - val) val ltac:(lia)) as ha.
    replace (val + (4 ^ m - 1 - val)) with (4 ^ m - 1) in ha by lia.
    exact ha. }
  destruct c as [| [| c']].
  - contradiction.
  - assert (hlast : Carries true 1 (w ++ dBlockBits m (4 ^ m - 1)) (car ++ cBits m)).
    { intros l r. rewrite rev_app_distr, Str_app_assoc, Str_app_assoc.
      eapply ps_trans; [exact (dBlock_pulse_carry_plus hm (rev w *> l) r) |].
      exact (Carries_toStar_one hc l (cBits m *> r)). }
    pose proof (Carries_of_absorbs_trans (4 ^ m - 1 - val) 1 h1 hlast) as hres.
    replace (4 ^ m - 1 - val + 1) with (1 * 4 ^ m - val) in hres by lia.
    exact hres.
  - destruct hc as [w1 [hstep hrest]].
    assert (hmid : Absorbs 1 (w ++ dBlockBits m (4 ^ m - 1)) (w1 ++ dBlockBits m 0)).
    { simpl. exists (w1 ++ dBlockBits m 0). split; [| reflexivity].
      intros l r. rewrite !rev_app_distr, !Str_app_assoc.
      eapply ps_trans.
      - eapply sp_trans; [exact (dBlock_pulse_carry m (rev w *> l) r) | exact (hstep l (cBits m *> r))].
      - exact (sweep_A_c m (rev w1 *> l) r). }
    pose proof (Carries_db_zero m hm (S c') hrest) as htail.
    pose proof (Carries_of_absorbs_trans _ _ (Absorbs_trans h1 hmid) htail) as hres.
    replace (4 ^ m - 1 - val + 1 + S c' * 4 ^ m) with (S (S c') * 4 ^ m - val) in hres by nia.
    exact hres.
Qed.

Lemma Carries_p1 {strict : bool} :
  forall (c : nat) {w car : list sym},
    Carries strict c w car ->
    Carries true ((c + 1) / 2) (w ++ [S0; S1])
      (car ++ (if Nat.eqb ((c - 1) mod 2) 0 then [S0; S0] else [S1; S1])).
Proof.
  induction c as [c ih] using strong_induction.
  intros w car hc.
  destruct c as [| [| [| c']]].
  - contradiction.
  - change (Carries true 1 (w ++ [S0; S1]) (car ++ [S0; S0])).
    intros l r. rewrite rev_app_distr, Str_app_assoc, Str_app_assoc.
    eapply ps_trans; [exact (micro_P_pulse (rev w *> l) r) |].
    exact (Carries_toStar_one hc l ([S0; S0] *> r)).
  - change (Carries true 1 (w ++ [S0; S1]) (car ++ [S1; S1])).
    destruct hc as [w1 [hstep hc1]].
    intros l r. rewrite rev_app_distr, Str_app_assoc, Str_app_assoc.
    eapply ps_trans; [exact (micro_P_pulse (rev w *> l) r) |].
    eapply etrans; [exact (p_to_s (hstep l ([S0; S0] *> r))) |].
    eapply etrans; [exact (p_to_s (micro_A_00_bounce (rev w1 *> l) r)) |].
    exact (Carries_toStar_one hc1 l ([S1; S1] *> r)).
  - destruct hc as [w1 [h1 [w2 [h2 hrest]]]].
    pose proof (ih (S c') ltac:(lia) w2 car hrest) as hih.
    assert (hstep1 : Absorbs 1 (w ++ [S0; S1]) (w2 ++ [S0; S1])).
    { simpl. exists (w2 ++ [S0; S1]). split; [| reflexivity].
      intros l r. rewrite !rev_app_distr, !Str_app_assoc.
      eapply ps_trans.
      - eapply ptrans; [| exact (h2 l ([S1; S1] *> r))].
        eapply ptrans; [| exact (micro_A_00_bounce (rev w1 *> l) r)].
        eapply ptrans; [exact (micro_P_pulse (rev w *> l) r) | exact (h1 l ([S0; S0] *> r))].
      - exact (p_to_s (micro_A_o1 (rev w2 *> l) r)). }
    pose proof (Carries_of_absorbs_trans 1 ((S c' + 1) / 2) hstep1 hih) as hres.
    replace (1 + (S c' + 1) / 2) with ((S (S (S c')) + 1) / 2) in hres by lia.
    replace ((S c' - 1) mod 2) with ((S (S (S c')) - 1) mod 2) in hres by lia.
    exact hres.
Qed.

Lemma Carries_p :
  forall (n : nat), 1 <= n ->
    forall {strict : bool} {c : nat} {w car : list sym},
      Carries strict c w car ->
      Carries true ((c + 2 ^ n - 1) / 2 ^ n) (w ++ pBits n) (car ++ zoBits n (c - 1)).
Proof.
  induction n as [| n ih]; intros hn strict c w car hc; [lia |].
  destruct n as [| n'].
  - pose proof (Carries_p1 c hc) as h1.
    replace (2 ^ 1) with 2 by reflexivity.
    replace ((c + 2 - 1) / 2) with ((c + 1) / 2) by lia.
    unfold pBits, zoBits; simpl repBits. rewrite !app_nil_r. exact h1.
  - pose proof (Carries_pos hc) as hcpos.
    pose proof (Carries_p1 c hc) as h1.
    pose proof (ih ltac:(lia) true ((c + 1) / 2) (w ++ [S0; S1]) _ h1) as h2.
    replace ((c + 1) / 2 - 1) with ((c - 1) / 2) in h2 by lia.
    assert (hdiv : ((c + 1) / 2 + 2 ^ S n' - 1) / 2 ^ S n' = (c + 2 ^ S (S n') - 1) / 2 ^ S (S n')).
    { pose proof (pow2_pos (S n')) as hp.
      replace ((c + 1) / 2 + 2 ^ S n' - 1) with ((c - 1 + 2 * 2 ^ S n') / 2) by lia.
      rewrite Nat.Div0.div_div.
      replace (2 * 2 ^ S n') with (2 ^ S (S n')) by reflexivity.
      f_equal. lia. }
    rewrite hdiv in h2.
    replace ((w ++ [S0; S1]) ++ pBits (S n')) with (w ++ pBits (S (S n'))) in h2
      by (unfold pBits; simpl; rewrite <- app_assoc; reflexivity).
    replace ((car ++ (if Nat.eqb ((c - 1) mod 2) 0 then [S0; S0] else [S1; S1])) ++
             zoBits (S n') ((c - 1) / 2))
      with (car ++ zoBits (S (S n')) (c - 1)) in h2
      by (cbn [zoBits]; rewrite <- app_assoc; reflexivity).
    exact h2.
Qed.

(* Binary Counter (ZO) Theorems for R2 *)

Lemma zo_absorb :
  forall (k mval : nat) {w w' : list sym},
    mval < 2 ^ k ->
    Absorbs (2 ^ k - 1 - mval) w w' ->
    forall l r,
      (rev w *> l) {{A}}> (zoBits k mval *> r) -->*
      (rev (w' ++ pBits k) *> l) {{A}}> r.
Proof.
  induction k as [| k ih]; intros mval w w' hm habs l r.
  - simpl in hm. assert (mval = 0) by lia. subst mval.
    simpl in habs. subst w'.
    unfold zoBits, pBits; simpl. rewrite app_nil_r. apply evstep_refl.
  - cbn [zoBits]. rewrite Str_app_assoc.
    pose proof (pow2_pos k) as hp.
    assert (hm' : mval / 2 < 2 ^ k) by (cbn [Nat.pow] in hm; lia).
    destruct (Nat.eqb (mval mod 2) 0) eqn:hpar.
    + apply Nat.eqb_eq in hpar.
      replace (2 ^ S k - 1 - mval) with (S (2 * (2 ^ k - 1 - mval / 2))) in habs by (cbn [Nat.add Nat.mul Nat.pow]; lia).
      destruct habs as [w1 [hstep1 hrest]].
      pose proof (Absorbs_p1 (2 ^ k - 1 - mval / 2) hrest) as habsP.
      pose proof (ih (mval / 2) (w1 ++ [S0; S1]) (w' ++ [S0; S1]) hm' habsP l r) as s4.
      rewrite rev_app_distr, Str_app_assoc in s4.
      replace ((w' ++ [S0; S1]) ++ pBits k) with (w' ++ pBits (S k)) in s4
        by (unfold pBits; simpl; rewrite <- app_assoc; reflexivity).
      eapply etrans; [exact (p_to_s (micro_A_00_bounce (rev w *> l) _)) |].
      eapply etrans; [exact (p_to_s (hstep1 l ([S1; S1] *> _))) |].
      eapply etrans; [exact (p_to_s (micro_A_o1 (rev w1 *> l) _)) | exact s4].
    + apply Nat.eqb_neq in hpar.
      replace (2 ^ S k - 1 - mval) with (2 * (2 ^ k - 1 - mval / 2)) in habs by (cbn [Nat.add Nat.mul Nat.pow]; lia).
      pose proof (Absorbs_p1 (2 ^ k - 1 - mval / 2) habs) as habsP.
      pose proof (ih (mval / 2) (w ++ [S0; S1]) (w' ++ [S0; S1]) hm' habsP l r) as s2.
      rewrite rev_app_distr, Str_app_assoc in s2.
      replace ((w' ++ [S0; S1]) ++ pBits k) with (w' ++ pBits (S k)) in s2
        by (unfold pBits; simpl; rewrite <- app_assoc; reflexivity).
      eapply etrans; [exact (p_to_s (micro_A_o1 (rev w *> l) _)) | exact s2].
Qed.

Lemma zo_absorb_plus {k mval : nat} (hk : 1 <= k) {w w' : list sym}
    (hm : mval < 2 ^ k)
    (habs : Absorbs (2 ^ k - 1 - mval) w w') (l r : Stream sym) :
  (rev w *> l) {{A}}> (zoBits k mval *> r) -->+
  (rev (w' ++ pBits k) *> l) {{A}}> r.
Proof.
  destruct k as [| k']; [lia |].
  cbn [zoBits]. rewrite Str_app_assoc.
  pose proof (pow2_pos k') as hp.
  assert (hm' : mval / 2 < 2 ^ k') by (cbn [Nat.pow] in hm; lia).
  destruct (Nat.eqb (mval mod 2) 0) eqn:hpar.
  - apply Nat.eqb_eq in hpar.
    replace (2 ^ S k' - 1 - mval) with (S (2 * (2 ^ k' - 1 - mval / 2))) in habs by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    destruct habs as [w1 [hstep1 hrest]].
    pose proof (Absorbs_p1 (2 ^ k' - 1 - mval / 2) hrest) as habsP.
    pose proof (zo_absorb k' (mval / 2) hm' habsP l r) as s4.
    rewrite rev_app_distr, Str_app_assoc in s4.
    replace ((w' ++ [S0; S1]) ++ pBits k') with (w' ++ pBits (S k')) in s4
      by (unfold pBits; simpl; rewrite <- app_assoc; reflexivity).
    eapply ps_trans; [exact (micro_A_00_bounce (rev w *> l) _) |].
    eapply etrans; [exact (p_to_s (hstep1 l ([S1; S1] *> _))) |].
    eapply etrans; [exact (p_to_s (micro_A_o1 (rev w1 *> l) _)) | exact s4].
  - apply Nat.eqb_neq in hpar.
    replace (2 ^ S k' - 1 - mval) with (2 * (2 ^ k' - 1 - mval / 2)) in habs by (cbn [Nat.add Nat.mul Nat.pow]; lia).
    pose proof (Absorbs_p1 (2 ^ k' - 1 - mval / 2) habs) as habsP.
    pose proof (zo_absorb k' (mval / 2) hm' habsP l r) as s2.
    rewrite rev_app_distr, Str_app_assoc in s2.
    replace ((w' ++ [S0; S1]) ++ pBits k') with (w' ++ pBits (S k')) in s2
      by (unfold pBits; simpl; rewrite <- app_assoc; reflexivity).
    eapply ps_trans; [exact (micro_A_o1 (rev w *> l) _) | exact s2].
Qed.

Lemma zo_carry :
  forall (k mval c : nat) {strict : bool} {w car : list sym},
    Carries strict c w car ->
    mval + c < 2 ^ k ->
    forall l r,
      (rev w *> l) {{A}}> (zoBits k mval *> r) -->+
      l <{{D}} ((car ++ zoBits k (mval + c)) *> r).
Proof.
  induction k as [| k ih]; intros mval c strict w car hc hlt l r.
  - pose proof (Carries_pos hc). simpl in hlt. lia.
  - pose proof (Carries_pos hc) as hcpos.
    pose proof (pow2_pos k) as hp.
    cbn [zoBits]. rewrite Str_app_assoc.
    destruct (Nat.eqb (mval mod 2) 0) eqn:hpar.
    + apply Nat.eqb_eq in hpar.
      destruct c as [| [| c']].
      * contradiction.
      * assert (hmod1 : (mval + 1) mod 2 = 1) by lia.
        assert (hdiv1 : (mval + 1) / 2 = mval / 2) by lia.
        rewrite hmod1, hdiv1. simpl Nat.eqb.
        rewrite !Str_app_assoc.
        eapply ps_trans; [exact (micro_A_00_bounce (rev w *> l) _) |].
        exact (Carries_toStar_one hc l ([S1; S1] *> _)).
      * destruct hc as [w1 [hstep1 hrest]].
        pose proof (Carries_p1 (S c') hrest) as hcP.
        assert (hlt' : mval / 2 + (S c' + 1) / 2 < 2 ^ k) by (cbn [Nat.pow] in hlt; lia).
        pose proof (ih (mval / 2) ((S c' + 1) / 2) _ _ _ hcP hlt' l r) as s4.
        rewrite rev_app_distr, Str_app_assoc in s4.
        replace (mval / 2 + (S c' + 1) / 2) with ((mval + S (S c')) / 2) in s4 by lia.
        replace ((S c' - 1) mod 2) with ((mval + S (S c')) mod 2) in s4 by lia.
        rewrite <- app_assoc in s4.
        eapply ptrans; [| exact s4].
        eapply ps_trans; [| exact (p_to_s (micro_A_o1 (rev w1 *> l) _))].
        eapply ptrans; [exact (micro_A_00_bounce (rev w *> l) _) | exact (hstep1 l ([S1; S1] *> _))].
    + apply Nat.eqb_neq in hpar.
      pose proof (Carries_p1 c hc) as hcP.
      assert (hlt' : mval / 2 + (c + 1) / 2 < 2 ^ k) by (cbn [Nat.pow] in hlt; lia).
      pose proof (ih (mval / 2) ((c + 1) / 2) _ _ _ hcP hlt' l r) as s2.
      rewrite rev_app_distr, Str_app_assoc in s2.
      replace (mval / 2 + (c + 1) / 2) with ((mval + c) / 2) in s2 by lia.
      replace ((c - 1) mod 2) with ((mval + c) mod 2) in s2 by lia.
      rewrite <- app_assoc in s2.
      eapply ptrans; [exact (micro_A_o1 (rev w *> l) _) | exact s2].
Qed.


(* ========================================================================== *)
(* Section 4: Binary N <-> Peano nat Bridge Lemmas                            *)
(* ========================================================================== *)

Lemma N2Nat_div (a b : N) (hb : (0 < b)%N) :
  N.to_nat (a / b)%N = N.to_nat a / N.to_nat b.
Proof.
  pose proof (N.div_mod a b ltac:(lia)) as hdm.
  pose proof (N.mod_lt a b ltac:(lia)) as hlt.
  apply (Nat.div_unique (N.to_nat a) (N.to_nat b)
    (N.to_nat (a / b)%N) (N.to_nat (a mod b)%N)); nia.
Qed.

Lemma N2Nat_mod (a b : N) (hb : (0 < b)%N) :
  N.to_nat (a mod b)%N = N.to_nat a mod N.to_nat b.
Proof.
  pose proof (N.div_mod a b ltac:(lia)) as hdm.
  pose proof (N.mod_lt a b ltac:(lia)) as hlt.
  apply (Nat.mod_unique (N.to_nat a) (N.to_nat b) (N.to_nat (a / b)%N)); nia.
Qed.

Lemma N2Nat_pow2 : forall k : N, N.to_nat (2 ^ k)%N = 2 ^ N.to_nat k.
Proof.
  induction k as [| k ih] using N.peano_ind.
  - reflexivity.
  - rewrite N.pow_succ_r', N2Nat.inj_succ, N2Nat.inj_mul, ih.
    cbn [Nat.pow]. change (N.to_nat 2) with 2. lia.
Qed.

Lemma pow4_eq_pow2_dbl : forall m : nat, 2 ^ (2 * m) = 4 ^ m.
Proof.
  induction m as [| m ih].
  - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    cbn [Nat.pow]. rewrite ih. lia.
Qed.

Lemma N2Nat_shiftl (a k : N) :
  N.to_nat (N.shiftl a k) = N.to_nat a * 2 ^ N.to_nat k.
Proof.
  rewrite N.shiftl_mul_pow2, N2Nat.inj_mul, N2Nat_pow2. reflexivity.
Qed.

Lemma N2Nat_shiftl_1 (k : N) :
  N.to_nat (N.shiftl 1 k) = 2 ^ N.to_nat k.
Proof.
  rewrite N2Nat_shiftl. change (N.to_nat 1) with 1. lia.
Qed.

Lemma N2Nat_shiftl_pow4 (m : N) :
  N.to_nat (N.shiftl 1 (2 * m)) = 4 ^ N.to_nat m.
Proof.
  rewrite N2Nat_shiftl_1, N2Nat.inj_mul.
  change (N.to_nat 2) with 2. apply pow4_eq_pow2_dbl.
Qed.

Lemma N2Nat_shiftl_mul_pow4 (a m : N) :
  N.to_nat (N.shiftl a (2 * m)) = N.to_nat a * 4 ^ N.to_nat m.
Proof.
  rewrite N2Nat_shiftl, N2Nat.inj_mul.
  change (N.to_nat 2) with 2. rewrite pow4_eq_pow2_dbl. reflexivity.
Qed.

Lemma N2Nat_shiftr (a k : N) :
  N.to_nat (N.shiftr a k) = N.to_nat a / 2 ^ N.to_nat k.
Proof.
  rewrite N.shiftr_div_pow2, N2Nat_div, N2Nat_pow2.
  - reflexivity.
  - pose proof (N2Nat_pow2 k). pose proof (pow2_pos (N.to_nat k)). lia.
Qed.

Lemma N2Nat_shiftr_pow4 (a m : N) :
  N.to_nat (N.shiftr a (2 * m)) = N.to_nat a / 4 ^ N.to_nat m.
Proof.
  rewrite N2Nat_shiftr, N2Nat.inj_mul.
  change (N.to_nat 2) with 2. rewrite pow4_eq_pow2_dbl. reflexivity.
Qed.

Lemma N2Nat_land_ones (a k : N) :
  N.to_nat (N.land a (N.ones k)) = N.to_nat a mod 2 ^ N.to_nat k.
Proof.
  rewrite N.land_ones, N2Nat_mod, N2Nat_pow2.
  - reflexivity.
  - pose proof (N2Nat_pow2 k). pose proof (pow2_pos (N.to_nat k)). lia.
Qed.

Lemma N2Nat_land_ones_pow4 (a m : N) :
  N.to_nat (N.land a (N.ones (2 * m))) = N.to_nat a mod 4 ^ N.to_nat m.
Proof.
  rewrite N2Nat_land_ones, N2Nat.inj_mul.
  change (N.to_nat 2) with 2. rewrite pow4_eq_pow2_dbl. reflexivity.
Qed.

Lemma N2Nat_ones (k : N) :
  N.to_nat (N.ones k) = 2 ^ N.to_nat k - 1.
Proof.
  unfold N.ones. rewrite N.shiftl_1_l, N.pred_sub, N2Nat.inj_sub, N2Nat_pow2.
  reflexivity.
Qed.

Lemma N2Nat_shiftr2 (val : N) : N.to_nat (N.shiftr val 2) = N.to_nat val / 4.
Proof. rewrite N2Nat_shiftr. reflexivity. Qed.

Lemma N2Nat_land3 (val : N) : N.to_nat (N.land val 3) = N.to_nat val mod 4.
Proof. change 3%N with (N.ones 2). rewrite N2Nat_land_ones. reflexivity. Qed.

Lemma N2Nat_pos_pred (p : positive) :
  N.to_nat (Npos p) = S (N.to_nat (Pos.pred_N p)).
Proof. lia. Qed.

(* ========================================================================== *)
(* Section 5: Compressed Token Tape, Push/Pop & Sweep Loops                   *)
(* ========================================================================== *)

Inductive QState : Type := QA | QB | QC | QD | QE | QF.

Definition qToQ (q : QState) : Q :=
  match q with
  | QA => A | QB => B | QC => C | QD => D | QE => E | QF => F
  end.

Inductive Tok : Type :=
  | tb0 : Tok
  | tb1 : Tok
  | tz : N -> Tok
  | to_ : N -> Tok
  | tp : N -> Tok
  | tt10 : N -> Tok
  | tc : N -> Tok
  | tdb : N -> N -> Tok.

Definition beqTok (t1 t2 : Tok) : bool :=
  match t1, t2 with
  | tb0, tb0 => true
  | tb1, tb1 => true
  | tz a, tz b => (a =? b)%N
  | to_ a, to_ b => (a =? b)%N
  | tp a, tp b => (a =? b)%N
  | tt10 a, tt10 b => (a =? b)%N
  | tc a, tc b => (a =? b)%N
  | tdb m1 v1, tdb m2 v2 => (m1 =? m2)%N && (v1 =? v2)%N
  | _, _ => false
  end.

Lemma beqTok_eq (t1 t2 : Tok) (h : beqTok t1 t2 = true) : t1 = t2.
Proof.
  destruct t1, t2; simpl in h; try discriminate; try reflexivity;
    try (apply N.eqb_eq in h; subst; reflexivity).
  apply andb_true_iff in h as [h1 h2].
  apply N.eqb_eq in h1. apply N.eqb_eq in h2. subst. reflexivity.
Qed.

Fixpoint beqTokList (xs ys : list Tok) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => beqTok x y && beqTokList xs' ys'
  | _, _ => false
  end.

Lemma beqTokList_eq : forall xs ys : list Tok, beqTokList xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs ih]; intros [| y ys] h; simpl in h;
    try discriminate; [reflexivity |].
  apply andb_true_iff in h as [hx hxs].
  rewrite (beqTok_eq x y hx), (ih ys hxs). reflexivity.
Qed.

Definition tokBits (t : Tok) : list sym :=
  match t with
  | tb0 => [S0]
  | tb1 => [S1]
  | tz n => zBits (N.to_nat n)
  | to_ n => oBits (N.to_nat n)
  | tp n => pBits (N.to_nat n)
  | tt10 n => t10Bits (N.to_nat n)
  | tc n => cBits (N.to_nat n)
  | tdb m val => dBlockBits (N.to_nat m) (N.to_nat val)
  end.

Fixpoint encodeL (restL : Stream sym) (ls : list Tok) : Stream sym :=
  match ls with
  | [] => restL
  | t :: ts => rev (tokBits t) *> encodeL restL ts
  end.

Fixpoint encodeR (rs : list Tok) : Stream sym :=
  match rs with
  | [] => 0inf
  | t :: ts => tokBits t *> encodeR ts
  end.

Lemma encodeL_append (restL : Stream sym) : forall xs ys : list Tok,
  encodeL restL (xs ++ ys) = encodeL (encodeL restL ys) xs.
Proof.
  induction xs as [| x xs ih]; intros ys; simpl; [reflexivity |].
  rewrite ih. reflexivity.
Qed.

Inductive State : Type :=
  | St_mk : QState -> list Tok -> list Tok -> State
  | St_err : State.

Definition encode (restL : Stream sym) (s : State) : Q * tape :=
  match s with
  | St_mk q ls rs => (encodeL restL ls) {{qToQ q}}> (encodeR rs)
  | St_err => c0
  end.

Definition pushL (t : Tok) (ls : list Tok) : list Tok :=
  match t with
  | tb0 => tb0 :: ls
  | tb1 => tb1 :: ls
  | tz n =>
    if (n =? 0)%N then ls else
    match ls with
    | tz n0 :: ts => tz (n0 + n)%N :: ts
    | _ => tz n :: ls
    end
  | to_ n =>
    if (n =? 0)%N then ls else
    match ls with
    | to_ n0 :: ts => to_ (n0 + n)%N :: ts
    | _ => to_ n :: ls
    end
  | tp n =>
    if (n =? 0)%N then ls else
    match ls with
    | tp n0 :: ts => tp (n0 + n)%N :: ts
    | _ => tp n :: ls
    end
  | tt10 n =>
    if (n =? 0)%N then ls else
    match ls with
    | tt10 n0 :: ts => tt10 (n0 + n)%N :: ts
    | _ => tt10 n :: ls
    end
  | tc n =>
    if (n =? 0)%N then ls else
    match ls with
    | tc n0 :: ts => tc (n0 + n)%N :: ts
    | _ => tc n :: ls
    end
  | tdb m val =>
    if (m =? 0)%N then ls else
    match ls with
    | tdb m0 v0 :: ts =>
      let sh := (2 * m)%N in
      let p4 := N.shiftl 1 sh in
      let v := if (p4 <=? val)%N then N.land val (N.ones sh) else val in
      tdb (m0 + m)%N (N.shiftl v0 sh + v)%N :: ts
    | _ => tdb m val :: ls
    end
  end.

Lemma encodeL_pushL (restL : Stream sym) (t : Tok) (ls : list Tok) :
  encodeL restL (pushL t ls) = rev (tokBits t) *> encodeL restL ls.
Proof.
  destruct t as [| | n | n | n | n | n | m val]; cbn [pushL].
  - reflexivity.
  - reflexivity.
  - destruct (n =? 0)%N eqn:h0.
    + apply N.eqb_eq in h0; subst n; reflexivity.
    + destruct ls as [| [| | n0 | | | | | ] ts]; try reflexivity.
      cbn [encodeL tokBits]. unfold zBits.
      rewrite N2Nat.inj_add, repBits_add, rev_app_distr, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0.
    + apply N.eqb_eq in h0; subst n; reflexivity.
    + destruct ls as [| [| | | n0 | | | | ] ts]; try reflexivity.
      cbn [encodeL tokBits]. unfold oBits.
      rewrite N2Nat.inj_add, repBits_add, rev_app_distr, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0.
    + apply N.eqb_eq in h0; subst n; reflexivity.
    + destruct ls as [| [| | | | n0 | | | ] ts]; try reflexivity.
      cbn [encodeL tokBits]. unfold pBits.
      rewrite N2Nat.inj_add, repBits_add, rev_app_distr, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0.
    + apply N.eqb_eq in h0; subst n; reflexivity.
    + destruct ls as [| [| | | | | n0 | | ] ts]; try reflexivity.
      cbn [encodeL tokBits]. unfold t10Bits.
      rewrite N2Nat.inj_add, repBits_add, rev_app_distr, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0.
    + apply N.eqb_eq in h0; subst n; reflexivity.
    + destruct ls as [| [| | | | | | n0 | ] ts]; try reflexivity.
      cbn [encodeL tokBits]. unfold cBits.
      rewrite N2Nat.inj_add, repBits_add, rev_app_distr, Str_app_assoc. reflexivity.
  - destruct (m =? 0)%N eqn:h0.
    + apply N.eqb_eq in h0; subst m; reflexivity.
    + destruct ls as [| [| | | | | | | m0 v0] ts]; try reflexivity.
      cbn [encodeL tokBits].
      rewrite !N2Nat.inj_add, N2Nat_shiftl_mul_pow4.
      destruct (N.shiftl 1 (2 * m) <=? val)%N eqn:hble.
      * rewrite N2Nat_land_ones_pow4, dBlockBits_append, rev_app_distr, Str_app_assoc.
        reflexivity.
      * apply N.leb_gt in hble.
        pose proof (N2Nat_shiftl_pow4 m) as hp4.
        assert (hlt : N.to_nat val < 4 ^ N.to_nat m) by lia.
        replace (N.to_nat val) with (N.to_nat val mod 4 ^ N.to_nat m) at 1
          by (apply Nat.mod_small; exact hlt).
        rewrite dBlockBits_append, rev_app_distr, Str_app_assoc. reflexivity.
Qed.

Definition pushR (t : Tok) (rs : list Tok) : list Tok :=
  match t with
  | tb0 => tb0 :: rs
  | tb1 => tb1 :: rs
  | tz n =>
    if (n =? 0)%N then rs else
    match rs with
    | tz n0 :: ts => tz (n + n0)%N :: ts
    | _ => tz n :: rs
    end
  | to_ n =>
    if (n =? 0)%N then rs else
    match rs with
    | to_ n0 :: ts => to_ (n + n0)%N :: ts
    | _ => to_ n :: rs
    end
  | tp n =>
    if (n =? 0)%N then rs else
    match rs with
    | tp n0 :: ts => tp (n + n0)%N :: ts
    | _ => tp n :: rs
    end
  | tt10 n =>
    if (n =? 0)%N then rs else
    match rs with
    | tt10 n0 :: ts => tt10 (n + n0)%N :: ts
    | _ => tt10 n :: rs
    end
  | tc n =>
    if (n =? 0)%N then rs else
    match rs with
    | tc n0 :: ts => tc (n + n0)%N :: ts
    | _ => tc n :: rs
    end
  | tdb m val => if (m =? 0)%N then rs else tdb m val :: rs
  end.

Lemma encodeR_pushR (t : Tok) (rs : list Tok) :
  encodeR (pushR t rs) = tokBits t *> encodeR rs.
Proof.
  destruct t as [| | n | n | n | n | n | m val]; cbn [pushR].
  - reflexivity.
  - reflexivity.
  - destruct (n =? 0)%N eqn:h0; [apply N.eqb_eq in h0; subst n; reflexivity |].
    destruct rs as [| [| | n0 | | | | | ] ts]; try reflexivity.
    cbn [encodeR tokBits]. unfold zBits.
    rewrite N2Nat.inj_add, repBits_add, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0; [apply N.eqb_eq in h0; subst n; reflexivity |].
    destruct rs as [| [| | | n0 | | | | ] ts]; try reflexivity.
    cbn [encodeR tokBits]. unfold oBits.
    rewrite N2Nat.inj_add, repBits_add, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0; [apply N.eqb_eq in h0; subst n; reflexivity |].
    destruct rs as [| [| | | | n0 | | | ] ts]; try reflexivity.
    cbn [encodeR tokBits]. unfold pBits.
    rewrite N2Nat.inj_add, repBits_add, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0; [apply N.eqb_eq in h0; subst n; reflexivity |].
    destruct rs as [| [| | | | | n0 | | ] ts]; try reflexivity.
    cbn [encodeR tokBits]. unfold t10Bits.
    rewrite N2Nat.inj_add, repBits_add, Str_app_assoc. reflexivity.
  - destruct (n =? 0)%N eqn:h0; [apply N.eqb_eq in h0; subst n; reflexivity |].
    destruct rs as [| [| | | | | | n0 | ] ts]; try reflexivity.
    cbn [encodeR tokBits]. unfold cBits.
    rewrite N2Nat.inj_add, repBits_add, Str_app_assoc. reflexivity.
  - destruct (m =? 0)%N eqn:h0; [apply N.eqb_eq in h0; subst m; reflexivity | reflexivity].
Qed.

Inductive PopBitL : Type :=
  | PBL_bit0 : list Tok -> PopBitL
  | PBL_bit1 : list Tok -> PopBitL
  | PBL_underflow : PopBitL.

Fixpoint popBitL (leftBlank : bool) (ls : list Tok) : PopBitL :=
  match ls with
  | [] => if leftBlank then PBL_bit0 [] else PBL_underflow
  | tb0 :: ts => PBL_bit0 ts
  | tb1 :: ts => PBL_bit1 ts
  | tz N0 :: ts => popBitL leftBlank ts
  | tz (Npos pn) :: ts => PBL_bit0 (tb0 :: pushL (tz (Pos.pred_N pn)) ts)
  | to_ N0 :: ts => popBitL leftBlank ts
  | to_ (Npos pn) :: ts => PBL_bit1 (tb1 :: pushL (to_ (Pos.pred_N pn)) ts)
  | tp N0 :: ts => popBitL leftBlank ts
  | tp (Npos pn) :: ts => PBL_bit1 (tb0 :: pushL (tp (Pos.pred_N pn)) ts)
  | tt10 N0 :: ts => popBitL leftBlank ts
  | tt10 (Npos pn) :: ts => PBL_bit0 (tb1 :: pushL (tt10 (Pos.pred_N pn)) ts)
  | tc N0 :: ts => popBitL leftBlank ts
  | tc (Npos pn) :: ts => PBL_bit0 (tb1 :: tb1 :: tb0 :: tb1 :: tb1 :: pushL (tc (Pos.pred_N pn)) ts)
  | tdb N0 _ :: ts => popBitL leftBlank ts
  | tdb (Npos pm) val :: ts =>
    let m := Pos.pred_N pm in
    let d := N.land val 3 in
    let v' := N.shiftr val 2 in
    let tail := pushL (tdb m v') ts in
    match d with
    | 0%N => PBL_bit1 (tb0 :: tb0 :: tb1 :: tb1 :: tb0 :: tail)
    | 1%N => PBL_bit1 (tb0 :: tb0 :: tb1 :: tb0 :: tb0 :: tail)
    | 2%N => PBL_bit1 (tb0 :: tb0 :: tb1 :: tb1 :: tb1 :: tail)
    | _   => PBL_bit1 (tb0 :: tb0 :: tb1 :: tb0 :: tb1 :: tail)
    end
  end.

Lemma popBitL_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf) :
  forall ls : list Tok,
    match popBitL leftBlank ls with
    | PBL_bit0 ls' => encodeL restL ls = S0 >> encodeL restL ls'
    | PBL_bit1 ls' => encodeL restL ls = S1 >> encodeL restL ls'
    | PBL_underflow => True
    end.
Proof.
  induction ls as [| t ts ih].
  - cbn [popBitL]. destruct leftBlank.
    + cbn [encodeL]. rewrite (hrest eq_refl), cons_zero_0inf. reflexivity.
    + exact I.
  - destruct t as [| | [| pn] | [| pn] | [| pn] | [| pn] | [| pn] | [| pm] val].
    + reflexivity.
    + reflexivity.
    + exact ih.
    + cbn [popBitL encodeL tokBits]. unfold zBits.
      rewrite N2Nat_pos_pred, encodeL_pushL, repBits_succ_right, rev_app_distr, Str_app_assoc.
      reflexivity.
    + exact ih.
    + cbn [popBitL encodeL tokBits]. unfold oBits.
      rewrite N2Nat_pos_pred, encodeL_pushL, repBits_succ_right, rev_app_distr, Str_app_assoc.
      reflexivity.
    + exact ih.
    + cbn [popBitL encodeL tokBits]. unfold pBits.
      rewrite N2Nat_pos_pred, encodeL_pushL, repBits_succ_right, rev_app_distr, Str_app_assoc.
      reflexivity.
    + exact ih.
    + cbn [popBitL encodeL tokBits]. unfold t10Bits.
      rewrite N2Nat_pos_pred, encodeL_pushL, repBits_succ_right, rev_app_distr, Str_app_assoc.
      reflexivity.
    + exact ih.
    + cbn [popBitL encodeL tokBits]. unfold cBits.
      rewrite N2Nat_pos_pred, encodeL_pushL, repBits_succ_right, rev_app_distr, Str_app_assoc.
      reflexivity.
    + exact ih.
    + cbn [popBitL].
      pose proof (N2Nat_land3 val) as hland.
      pose proof (N2Nat_shiftr2 val) as hsh.
      assert (hd :
        (N.land val 3 = 0%N /\ N.to_nat val mod 4 = 0) \/
        (N.land val 3 = 1%N /\ N.to_nat val mod 4 = 1) \/
        (N.land val 3 = 2%N /\ N.to_nat val mod 4 = 2) \/
        (N.land val 3 = 3%N /\ N.to_nat val mod 4 = 3)) by lia.
      destruct hd as [[hd0 hm0] | [[hd1 hm1] | [[hd2 hm2] | [hd3 hm3]]]];
        [rewrite hd0 | rewrite hd1 | rewrite hd2 | rewrite hd3];
        cbn [encodeL tokBits];
        rewrite N2Nat_pos_pred; cbn [dBlockBits];
        rewrite encodeL_pushL; cbn [tokBits];
        rewrite hsh;
        [rewrite hm0 | rewrite hm1 | rewrite hm2 | rewrite hm3];
        rewrite rev_app_distr, Str_app_assoc; reflexivity.
Qed.

Inductive PopBitR : Type :=
  | PBR_bit0 : list Tok -> PopBitR
  | PBR_bit1 : list Tok -> PopBitR.

Fixpoint popBitR (rs : list Tok) : PopBitR :=
  match rs with
  | [] => PBR_bit0 []
  | tb0 :: ts => PBR_bit0 ts
  | tb1 :: ts => PBR_bit1 ts
  | tz N0 :: ts => popBitR ts
  | tz (Npos pn) :: ts => PBR_bit0 (tb0 :: pushR (tz (Pos.pred_N pn)) ts)
  | to_ N0 :: ts => popBitR ts
  | to_ (Npos pn) :: ts => PBR_bit1 (tb1 :: pushR (to_ (Pos.pred_N pn)) ts)
  | tp N0 :: ts => popBitR ts
  | tp (Npos pn) :: ts => PBR_bit0 (tb1 :: pushR (tp (Pos.pred_N pn)) ts)
  | tt10 N0 :: ts => popBitR ts
  | tt10 (Npos pn) :: ts => PBR_bit1 (tb0 :: pushR (tt10 (Pos.pred_N pn)) ts)
  | tc N0 :: ts => popBitR ts
  | tc (Npos pn) :: ts => PBR_bit1 (tb1 :: tb0 :: tb1 :: tb1 :: tb0 :: pushR (tc (Pos.pred_N pn)) ts)
  | tdb N0 _ :: ts => popBitR ts
  | tdb (Npos pm) val :: ts =>
    let m := Pos.pred_N pm in
    let sh := (2 * m)%N in
    let d := N.land (N.shiftr val sh) 3 in
    let r := N.land val (N.ones sh) in
    let tail := pushR (tdb m r) ts in
    match d with
    | 0%N => PBR_bit0 (tb1 :: tb1 :: tb0 :: tb0 :: tb1 :: tail)
    | 1%N => PBR_bit0 (tb0 :: tb1 :: tb0 :: tb0 :: tb1 :: tail)
    | 2%N => PBR_bit1 (tb1 :: tb1 :: tb0 :: tb0 :: tb1 :: tail)
    | _   => PBR_bit1 (tb0 :: tb1 :: tb0 :: tb0 :: tb1 :: tail)
    end
  end.

Lemma popBitR_sound : forall rs : list Tok,
  match popBitR rs with
  | PBR_bit0 rs' => encodeR rs = S0 >> encodeR rs'
  | PBR_bit1 rs' => encodeR rs = S1 >> encodeR rs'
  end.
Proof.
  induction rs as [| t ts ih].
  - cbn [popBitR encodeR]. rewrite cons_zero_0inf. reflexivity.
  - destruct t as [| | [| pn] | [| pn] | [| pn] | [| pn] | [| pn] | [| pm] val].
    + reflexivity.
    + reflexivity.
    + exact ih.
    + cbn [popBitR encodeR tokBits]. unfold zBits.
      rewrite N2Nat_pos_pred, encodeR_pushR; cbn [repBits tokBits];
      rewrite Str_app_assoc; reflexivity.
    + exact ih.
    + cbn [popBitR encodeR tokBits]. unfold oBits.
      rewrite N2Nat_pos_pred, encodeR_pushR; cbn [repBits tokBits];
      rewrite Str_app_assoc; reflexivity.
    + exact ih.
    + cbn [popBitR encodeR tokBits]. unfold pBits.
      rewrite N2Nat_pos_pred, encodeR_pushR; cbn [repBits tokBits];
      rewrite Str_app_assoc; reflexivity.
    + exact ih.
    + cbn [popBitR encodeR tokBits]. unfold t10Bits.
      rewrite N2Nat_pos_pred, encodeR_pushR; cbn [repBits tokBits];
      rewrite Str_app_assoc; reflexivity.
    + exact ih.
    + cbn [popBitR encodeR tokBits]. unfold cBits.
      rewrite N2Nat_pos_pred, encodeR_pushR; cbn [repBits tokBits];
      rewrite Str_app_assoc; reflexivity.
    + exact ih.
    + cbn [popBitR].
      set (m := Pos.pred_N pm).
      pose proof (N2Nat_land3 (N.shiftr val (2 * m))) as hland.
      pose proof (N2Nat_shiftr_pow4 val m) as hsh.
      pose proof (N2Nat_land_ones_pow4 val m) as hrem.
      rewrite hsh in hland.
      assert (hd :
        (N.land (N.shiftr val (2 * m)) 3 = 0%N /\ (N.to_nat val / 4 ^ N.to_nat m) mod 4 = 0) \/
        (N.land (N.shiftr val (2 * m)) 3 = 1%N /\ (N.to_nat val / 4 ^ N.to_nat m) mod 4 = 1) \/
        (N.land (N.shiftr val (2 * m)) 3 = 2%N /\ (N.to_nat val / 4 ^ N.to_nat m) mod 4 = 2) \/
        (N.land (N.shiftr val (2 * m)) 3 = 3%N /\ (N.to_nat val / 4 ^ N.to_nat m) mod 4 = 3)) by lia.
      destruct hd as [[hd0 hm0] | [[hd1 hm1] | [[hd2 hm2] | [hd3 hm3]]]];
        [rewrite hd0 | rewrite hd1 | rewrite hd2 | rewrite hd3];
        cbn [encodeR tokBits];
        rewrite N2Nat_pos_pred; fold m;
        rewrite dBlockBits_cons_left, encodeR_pushR; cbn [tokBits];
        rewrite hrem;
        [rewrite hm0 | rewrite hm1 | rewrite hm2 | rewrite hm3];
        rewrite Str_app_assoc; reflexivity.
Qed.

Inductive WTok : Type :=
  | wdb : N -> N -> WTok
  | wp : N -> WTok.

Definition wTokBits (w : WTok) : list sym :=
  match w with
  | wdb m val => dBlockBits (N.to_nat m) (N.to_nat val)
  | wp n => pBits (N.to_nat n)
  end.

Inductive PopW : Type :=
  | PW_none : PopW
  | PW_db : N -> N -> list Tok -> PopW
  | PW_p : N -> list Tok -> PopW.

Definition popWTokSlow (ls : list Tok) : PopW :=
  match popBitL false ls with
  | PBL_bit1 ls1 =>
    match popBitL false ls1 with
    | PBL_bit0 ls2 =>
      match popBitL false ls2 with
      | PBL_bit0 ls3 =>
        match popBitL false ls3 with
        | PBL_bit1 ls4 =>
          match popBitL false ls4 with
          | PBL_bit1 ls5 =>
            match popBitL false ls5 with
            | PBL_bit0 ls6 => PW_db 1 0 ls6
            | PBL_bit1 ls6 => PW_db 1 2 ls6
            | PBL_underflow => PW_p 1 ls2
            end
          | PBL_bit0 ls5 =>
            match popBitL false ls5 with
            | PBL_bit0 ls6 => PW_db 1 1 ls6
            | PBL_bit1 ls6 => PW_db 1 3 ls6
            | PBL_underflow => PW_p 1 ls2
            end
          | PBL_underflow => PW_p 1 ls2
          end
        | _ => PW_p 1 ls2
        end
      | _ => PW_p 1 ls2
      end
    | _ => PW_none
    end
  | _ => PW_none
  end.

Definition popWTok (ls : list Tok) : PopW :=
  match ls with
  | tdb N0 val :: ts => popWTokSlow (tdb N0 val :: ts)
  | tdb (Npos pm) val :: ts =>
    let m := Npos pm in
    let sh := (2 * m)%N in
    let p4 := N.shiftl 1 sh in
    let v := if (p4 <=? val)%N then N.land val (N.ones sh) else val in
    PW_db m v ts
  | tp N0 :: ts => popWTokSlow (tp N0 :: ts)
  | tp (Npos pn) :: ts => PW_p (Npos pn) ts
  | _ => popWTokSlow ls
  end.

Lemma popWTokSlow_sound (restL : Stream sym) (ls : list Tok) :
  match popWTokSlow ls with
  | PW_none => True
  | PW_db m val ls' =>
    1 <= N.to_nat m /\ N.to_nat val < 4 ^ N.to_nat m /\
    encodeL restL ls = rev (dBlockBits (N.to_nat m) (N.to_nat val)) *> encodeL restL ls'
  | PW_p n ls' =>
    1 <= N.to_nat n /\
    encodeL restL ls = rev (pBits (N.to_nat n)) *> encodeL restL ls'
  end.
Proof.
  unfold popWTokSlow.
  assert (hf : false = true -> restL = 0inf) by discriminate.
  pose proof (popBitL_sound false restL hf ls) as h1.
  destruct (popBitL false ls) as [| ls1 |]; [exact I | | exact I].
  pose proof (popBitL_sound false restL hf ls1) as h2.
  destruct (popBitL false ls1) as [ls2 | |]; [| exact I | exact I].
  assert (h12 : encodeL restL ls = S1 >> S0 >> encodeL restL ls2) by (rewrite h1, h2; reflexivity).
  pose proof (popBitL_sound false restL hf ls2) as h3.
  destruct (popBitL false ls2) as [ls3 | |]; [| split; [lia | exact h12] | split; [lia | exact h12]].
  pose proof (popBitL_sound false restL hf ls3) as h4.
  destruct (popBitL false ls3) as [| ls4 |]; [split; [lia | exact h12] | | split; [lia | exact h12]].
  pose proof (popBitL_sound false restL hf ls4) as h5.
  destruct (popBitL false ls4) as [ls5 | ls5 |].
  - pose proof (popBitL_sound false restL hf ls5) as h6.
    destruct (popBitL false ls5) as [ls6 | ls6 |].
    + repeat split; [lia | simpl; lia |]. rewrite h12, h3, h4, h5, h6. reflexivity.
    + repeat split; [lia | simpl; lia |]. rewrite h12, h3, h4, h5, h6. reflexivity.
    + split; [lia | exact h12].
  - pose proof (popBitL_sound false restL hf ls5) as h6.
    destruct (popBitL false ls5) as [ls6 | ls6 |].
    + repeat split; [lia | simpl; lia |]. rewrite h12, h3, h4, h5, h6. reflexivity.
    + repeat split; [lia | simpl; lia |]. rewrite h12, h3, h4, h5, h6. reflexivity.
    + split; [lia | exact h12].
  - split; [lia | exact h12].
Qed.

Lemma popWTok_sound (restL : Stream sym) (ls : list Tok) :
  match popWTok ls with
  | PW_none => True
  | PW_db m val ls' =>
    1 <= N.to_nat m /\ N.to_nat val < 4 ^ N.to_nat m /\
    encodeL restL ls = rev (dBlockBits (N.to_nat m) (N.to_nat val)) *> encodeL restL ls'
  | PW_p n ls' =>
    1 <= N.to_nat n /\
    encodeL restL ls = rev (pBits (N.to_nat n)) *> encodeL restL ls'
  end.
Proof.
  destruct ls as [| t ts]; [exact (popWTokSlow_sound restL []) |].
  destruct t as [| | n | n | [| pn] | n | n | [| pm] val];
    cbn [popWTok]; try apply popWTokSlow_sound.
  - cbn [popWTok encodeL tokBits]. refine (conj _ _); [lia | reflexivity].
  - cbn [popWTok].
    set (m := Npos pm).
    pose proof (N2Nat_shiftl_pow4 m) as hp4.
    pose proof (pow4_pos (N.to_nat m)) as hpos.
    destruct (N.shiftl 1 (2 * m) <=? val)%N eqn:hble.
    + rewrite N2Nat_land_ones_pow4.
      refine (conj _ (conj _ _)); [unfold m; lia | apply Nat.mod_upper_bound; lia |].
      cbn [encodeL tokBits]. fold m. rewrite dBlockBits_mod. reflexivity.
    + apply N.leb_gt in hble.
      refine (conj _ (conj _ _)); [unfold m; lia | lia | reflexivity].
Qed.

Fixpoint sweepA0 (ls rs : list Tok) {struct rs} : State :=
  match rs with
  | [] => St_mk QA ls [tb0]
  | tc (Npos pn) :: ts =>
    let n := Pos.pred_N pn in
    sweepA0 (pushL (tp 1) (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: tb1 :: ls))) ts
  | t :: ts => St_mk QA ls (tb0 :: t :: ts)
  end.

Lemma sweepA0_sound (restL : Stream sym) : forall rs ls : list Tok,
  (encodeL restL ls {{A}}> (S0 >> encodeR rs)) -->* encode restL (sweepA0 ls rs).
Proof.
  induction rs as [| t ts ih]; intros ls.
  - cbn [sweepA0 encode encodeR tokBits Str_app]. apply evstep_refl.
  - destruct t as [| | n | n | n | n | [| pn] | m val];
      try (cbn [sweepA0 encode encodeR tokBits Str_app]; apply evstep_refl).
    cbn [sweepA0 encodeR tokBits].
    set (n := Pos.pred_N pn).
    pose proof (p_to_s (sweep_A_0c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
      (encodeL restL ls) (encodeR ts))) as h1.
    replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
    assert (hL :
      encodeL restL (pushL (tp 1) (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: tb1 :: ls))) =
      rev ([S1; S0; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1]) *> encodeL restL ls).
    { rewrite !encodeL_pushL. cbn [encodeL tokBits pBits repBits].
      rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
    rewrite <- hL in h1.
    exact (etrans h1 (ih _)).
Qed.

Fixpoint sweepALoop (ls rs : list Tok) {struct rs} : State :=
  match rs with
  | [] => St_mk QA ls []
  | tc (Npos pn) :: ts => sweepALoop (pushL (tdb (Npos pn) 0) ls) ts
  | to_ (Npos pn) :: ts => sweepALoop (pushL (tp (Npos pn)) ls) ts
  | tt10 (Npos pn) :: ts => sweepALoop (pushL (tp (Npos pn)) ls) ts
  | tp (Npos pn) :: ts => sweepALoop (pushL (tt10 (Npos pn)) ls) ts
  | tb0 :: tc (Npos pn) :: ts2 =>
    let n := Pos.pred_N pn in
    sweepA0 (pushL (tp 1) (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: tb1 :: ls))) ts2
  | tb0 :: ts => St_mk QA ls (tb0 :: ts)
  | t :: ts => St_mk QA ls (t :: ts)
  end.

Lemma sweepALoop_sound (restL : Stream sym) : forall rs ls : list Tok,
  (encodeL restL ls {{A}}> encodeR rs) -->* encode restL (sweepALoop ls rs).
Proof.
  induction rs as [| t ts ih]; intros ls.
  - cbn [sweepALoop encode]. apply evstep_refl.
  - destruct t as [| | n | [| pn] | [| pn] | [| pn] | [| pn] | m val].
    + destruct ts as [| t2 ts2]; [cbn [sweepALoop encode]; apply evstep_refl |].
      destruct t2 as [| | n2 | n2 | n2 | n2 | [| pn2] | m2 val2];
        try (cbn [sweepALoop encode]; apply evstep_refl).
      cbn [sweepALoop encodeR tokBits Str_app].
      set (n2 := Pos.pred_N pn2).
      pose proof (p_to_s (sweep_A_0c_plus (n := N.to_nat (Npos pn2)) ltac:(lia)
        (encodeL restL ls) (encodeR ts2))) as h1.
      replace (N.to_nat (Npos pn2) - 1) with (N.to_nat n2) in h1 by (unfold n2; lia).
      assert (hL :
        encodeL restL (pushL (tp 1) (pushL (tdb n2 0) (tb1 :: tb0 :: tb0 :: tb1 :: ls))) =
        rev ([S1; S0; S0; S1] ++ dBlockBits (N.to_nat n2) 0 ++ [S0; S1]) *> encodeL restL ls).
      { rewrite !encodeL_pushL. cbn [encodeL tokBits pBits repBits].
        rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
      rewrite <- hL in h1.
      exact (etrans h1 (sweepA0_sound restL ts2 _)).
    + cbn [sweepALoop encode]; apply evstep_refl.
    + cbn [sweepALoop encode]; apply evstep_refl.
    + cbn [sweepALoop encode]; apply evstep_refl.
    + cbn [sweepALoop encodeR tokBits].
      pose proof (p_to_s (sweep_A_o_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts))) as h1.
      pose proof (encodeL_pushL restL (tp (Npos pn)) ls) as hL.
      cbn [tokBits] in hL. rewrite <- hL in h1.
      exact (etrans h1 (ih _)).
    + cbn [sweepALoop encode]; apply evstep_refl.
    + cbn [sweepALoop encodeR tokBits].
      pose proof (p_to_s (sweep_A_p_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts))) as h1.
      pose proof (encodeL_pushL restL (tt10 (Npos pn)) ls) as hL.
      cbn [tokBits] in hL. rewrite <- hL in h1.
      exact (etrans h1 (ih _)).
    + cbn [sweepALoop encode]; apply evstep_refl.
    + cbn [sweepALoop encodeR tokBits].
      pose proof (p_to_s (sweep_A_t10_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts))) as h1.
      pose proof (encodeL_pushL restL (tp (Npos pn)) ls) as hL.
      cbn [tokBits] in hL. rewrite <- hL in h1.
      exact (etrans h1 (ih _)).
    + cbn [sweepALoop encode]; apply evstep_refl.
    + cbn [sweepALoop encodeR tokBits].
      pose proof (p_to_s (sweep_A_c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts))) as h1.
      pose proof (encodeL_pushL restL (tdb (Npos pn) 0) ls) as hL.
      cbn [tokBits] in hL. change (N.to_nat 0) with 0 in hL. rewrite <- hL in h1.
      exact (etrans h1 (ih _)).
    + cbn [sweepALoop encode]; apply evstep_refl.
Qed.

Inductive Buf : Type := Buf_none | Buf_011 | Buf_01100 | Buf_0.

Definition bufBits (buf : Buf) : list sym :=
  match buf with
  | Buf_none => []
  | Buf_011 => [S0; S1; S1]
  | Buf_01100 => [S0; S1; S1; S0; S0]
  | Buf_0 => [S0]
  end.

Definition flushBuf (buf : Buf) (ls : list Tok) : list Tok :=
  match buf with
  | Buf_none => ls
  | Buf_011 => tb1 :: tb1 :: tb0 :: ls
  | Buf_01100 => tb0 :: tb0 :: tb1 :: tb1 :: tb0 :: ls
  | Buf_0 => tb0 :: ls
  end.

Lemma encodeL_flushBuf (restL : Stream sym) (buf : Buf) (ls : list Tok) :
  encodeL restL (flushBuf buf ls) = rev (bufBits buf) *> encodeL restL ls.
Proof. destruct buf; reflexivity. Qed.

Fixpoint sweepBELoop (isE : bool) (buf : Buf) (ls rs : list Tok) {struct rs} : State :=
  match rs with
  | [] => St_mk (if isE then QE else QB) (flushBuf buf ls) []
  | tc (Npos pn) :: ts =>
    let n := Pos.pred_N pn in
    if isE then
      match buf with
      | Buf_0 => sweepBELoop false Buf_011 (pushL (tdb n 0) (pushL (tp 2) ls)) ts
      | Buf_01100 => sweepBELoop false Buf_011 (pushL (tdb n 0) (pushL (tp 1) (pushL (tdb 1 0) ls))) ts
      | _ => sweepBELoop false Buf_011 (pushL (tdb n 0) (tb1 :: tb0 :: tb1 :: flushBuf buf ls)) ts
      end
    else
      match buf with
      | Buf_011 => sweepBELoop false Buf_011 (pushL (tdb (Npos pn) 0) ls) ts
      | _ => sweepBELoop false Buf_011 (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: flushBuf buf ls)) ts
      end
  | to_ (Npos pn) :: ts =>
    let n := Pos.pred_N pn in
    if isE then
      match buf with
      | Buf_0 => sweepBELoop true Buf_0 (pushL (tp (Npos pn)) ls) ts
      | Buf_01100 => sweepBELoop true Buf_0 (pushL (tp n) (pushL (tdb 1 0) ls)) ts
      | _ => sweepBELoop true Buf_none (pushL (tt10 (Npos pn)) (flushBuf buf ls)) ts
      end
    else
      match buf with
      | Buf_011 =>
        match n with
        | N0 => sweepBELoop true Buf_01100 ls ts
        | Npos pn' =>
          let n' := Pos.pred_N pn' in
          sweepBELoop true Buf_0 (pushL (tp n') (pushL (tdb 1 0) ls)) ts
        end
      | _ => sweepBELoop true Buf_none (pushL (tt10 n) (pushL (tz 1) (flushBuf buf ls))) ts
      end
  | t :: ts => St_mk (if isE then QE else QB) (flushBuf buf ls) (t :: ts)
  end.

Lemma sweepBELoop_sound (restL : Stream sym) :
  forall (rs : list Tok) (isE : bool) (buf : Buf) (ls : list Tok),
    ((rev (bufBits buf) *> encodeL restL ls) {{if isE then E else B}}> encodeR rs) -->*
    encode restL (sweepBELoop isE buf ls rs).
Proof.
  induction rs as [| t ts ih]; intros isE buf ls.
  - cbn [sweepBELoop encode]. rewrite encodeL_flushBuf.
    destruct isE; apply evstep_refl.
  - destruct t as [| | n | [| pn] | n | n | [| pn] | m val];
      try (cbn [sweepBELoop encode]; rewrite encodeL_flushBuf; destruct isE; apply evstep_refl).
    + (* to_ (Npos pn) *)
      set (n := Pos.pred_N pn).
      destruct isE.
      * cbn [sweepBELoop encodeR tokBits]. fold n.
        pose proof (p_to_s (sweep_E_o_plus (n := N.to_nat (Npos pn)) ltac:(lia)
          (rev (bufBits buf) *> encodeL restL ls) (encodeR ts))) as h1.
        destruct buf.
        -- (* Buf_none *)
           assert (hL :
             rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 (Npos pn)) (flushBuf Buf_none ls)) =
             rev (t10Bits (N.to_nat (Npos pn))) *> (rev (bufBits Buf_none) *> encodeL restL ls)).
           { rewrite encodeL_pushL. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_none _)).
        -- (* Buf_011 *)
           assert (hL :
             rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 (Npos pn)) (flushBuf Buf_011 ls)) =
             rev (t10Bits (N.to_nat (Npos pn))) *> (rev (bufBits Buf_011) *> encodeL restL ls)).
           { rewrite encodeL_pushL, encodeL_flushBuf. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_none _)).
        -- (* Buf_01100 *)
           assert (hL :
             rev (bufBits Buf_0) *> encodeL restL (pushL (tp n) (pushL (tdb 1 0) ls)) =
             rev (t10Bits (N.to_nat (Npos pn))) *> (rev (bufBits Buf_01100) *> encodeL restL ls)).
           { rewrite !encodeL_pushL. cbn [bufBits tokBits dBlockBits digitBits].
             rewrite <- !Str_app_assoc, <- !rev_app_distr. f_equal; f_equal.
             rewrite (N2Nat_pos_pred pn); fold n. cbn [t10Bits repBits].
             pose proof (zero_t10Bits_eq (N.to_nat n)) as hzt.
             change ([S0; S1; S1; S0; S0; S1] ++ pBits (N.to_nat n) ++ [S0] =
                     [S0; S1; S1; S0; S0] ++ ([S1; S0] ++ t10Bits (N.to_nat n))).
             rewrite <- hzt. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_0 _)).
        -- (* Buf_0 *)
           assert (hL :
             rev (bufBits Buf_0) *> encodeL restL (pushL (tp (Npos pn)) ls) =
             rev (t10Bits (N.to_nat (Npos pn))) *> (rev (bufBits Buf_0) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits tokBits].
             rewrite <- !Str_app_assoc, <- !rev_app_distr. f_equal; f_equal.
             symmetry. apply zero_t10Bits_eq. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_0 _)).
      * cbn [sweepBELoop encodeR tokBits]. fold n.
        pose proof (p_to_s (sweep_B_o_plus (n := N.to_nat (Npos pn)) ltac:(lia)
          (rev (bufBits buf) *> encodeL restL ls) (encodeR ts))) as h1.
        replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
        destruct buf.
        -- (* Buf_none *)
           assert (hL :
             rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 n) (pushL (tz 1) (flushBuf Buf_none ls))) =
             rev ([S0; S0] ++ t10Bits (N.to_nat n)) *> (rev (bufBits Buf_none) *> encodeL restL ls)).
           { rewrite !encodeL_pushL, encodeL_flushBuf. cbn [bufBits tokBits zBits repBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_none _)).
        -- (* Buf_011 *)
           destruct n as [| pn'].
           ++ assert (hL :
                rev (bufBits Buf_01100) *> encodeL restL ls =
                rev ([S0; S0] ++ t10Bits 0) *> (rev (bufBits Buf_011) *> encodeL restL ls)).
              { cbn [bufBits t10Bits repBits]. reflexivity. }
              change (N.to_nat 0) with 0 in h1.
              rewrite <- hL in h1. exact (etrans h1 (ih true Buf_01100 _)).
           ++ set (n' := Pos.pred_N pn').
              assert (hL :
                rev (bufBits Buf_0) *> encodeL restL (pushL (tp n') (pushL (tdb 1 0) ls)) =
                rev ([S0; S0] ++ t10Bits (N.to_nat (Npos pn'))) *> (rev (bufBits Buf_011) *> encodeL restL ls)).
              { rewrite !encodeL_pushL. cbn [bufBits tokBits dBlockBits digitBits].
                rewrite <- !Str_app_assoc, <- !rev_app_distr. f_equal; f_equal.
                rewrite (N2Nat_pos_pred pn'); fold n'. cbn [t10Bits repBits].
                pose proof (zero_t10Bits_eq (N.to_nat n')) as hzt.
                change ([S0; S1; S1; S0; S0; S1] ++ pBits (N.to_nat n') ++ [S0] =
                        [S0; S1; S1] ++ ([S0; S0] ++ ([S1; S0] ++ t10Bits (N.to_nat n')))).
                rewrite <- hzt. reflexivity. }
              rewrite <- hL in h1. exact (etrans h1 (ih true Buf_0 _)).
        -- (* Buf_01100 *)
           assert (hL :
             rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 n) (pushL (tz 1) (flushBuf Buf_01100 ls))) =
             rev ([S0; S0] ++ t10Bits (N.to_nat n)) *> (rev (bufBits Buf_01100) *> encodeL restL ls)).
           { rewrite !encodeL_pushL, encodeL_flushBuf. cbn [bufBits tokBits zBits repBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_none _)).
        -- (* Buf_0 *)
           assert (hL :
             rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 n) (pushL (tz 1) (flushBuf Buf_0 ls))) =
             rev ([S0; S0] ++ t10Bits (N.to_nat n)) *> (rev (bufBits Buf_0) *> encodeL restL ls)).
           { rewrite !encodeL_pushL, encodeL_flushBuf. cbn [bufBits tokBits zBits repBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih true Buf_none _)).
    + (* tc (Npos pn) *)
      set (n := Pos.pred_N pn).
      destruct isE.
      * cbn [sweepBELoop encodeR tokBits]. fold n.
        pose proof (p_to_s (sweep_E_c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
          (rev (bufBits buf) *> encodeL restL ls) (encodeR ts))) as h1.
        replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
        destruct buf.
        -- (* Buf_none *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb1 :: flushBuf Buf_none ls)) =
             rev ([S1; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_none) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits flushBuf encodeL tokBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
        -- (* Buf_011 *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb1 :: flushBuf Buf_011 ls)) =
             rev ([S1; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_011) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits flushBuf encodeL tokBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
        -- (* Buf_01100 *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (pushL (tp 1) (pushL (tdb 1 0) ls))) =
             rev ([S1; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_01100) *> encodeL restL ls)).
           { rewrite !encodeL_pushL. cbn [bufBits tokBits pBits repBits dBlockBits digitBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
        -- (* Buf_0 *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (pushL (tp 2) ls)) =
             rev ([S1; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_0) *> encodeL restL ls)).
           { rewrite !encodeL_pushL. cbn [bufBits tokBits pBits repBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
      * cbn [sweepBELoop encodeR tokBits]. fold n.
        pose proof (p_to_s (sweep_B_c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
          (rev (bufBits buf) *> encodeL restL ls) (encodeR ts))) as h1.
        replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
        destruct buf.
        -- (* Buf_none *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: flushBuf Buf_none ls)) =
             rev ([S0; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_none) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits flushBuf encodeL tokBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
        -- (* Buf_011 *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb (Npos pn) 0) ls) =
             rev ([S0; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_011) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits tokBits].
             rewrite (N2Nat_pos_pred pn); fold n.
             rewrite !dBlockBits_zero_val. cbn [repBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
        -- (* Buf_01100 *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: flushBuf Buf_01100 ls)) =
             rev ([S0; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_01100) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits flushBuf encodeL tokBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
        -- (* Buf_0 *)
           assert (hL :
             rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: flushBuf Buf_0 ls)) =
             rev ([S0; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> (rev (bufBits Buf_0) *> encodeL restL ls)).
           { rewrite encodeL_pushL. cbn [bufBits flushBuf encodeL tokBits].
             rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
           rewrite <- hL in h1. exact (etrans h1 (ih false Buf_011 _)).
Qed.


(* ========================================================================== *)
(* Section 6: R1/R2 Accelerated Carry/Absorb Helpers & stepMacro              *)
(* ========================================================================== *)

Fixpoint encodeW (ws : list WTok) : list sym :=
  match ws with
  | [] => []
  | w :: ws' => wTokBits w ++ encodeW ws'
  end.

Lemma encodeW_append : forall xs ys : list WTok,
  encodeW (xs ++ ys) = encodeW xs ++ encodeW ys.
Proof.
  induction xs as [| x xs ih]; intros ys; cbn [app encodeW]; [reflexivity |].
  rewrite ih, <- app_assoc. reflexivity.
Qed.

Fixpoint encodeToks (ts : list Tok) : list sym :=
  match ts with
  | [] => []
  | t :: ts' => tokBits t ++ encodeToks ts'
  end.

Fixpoint revAppendTokLoop (xs ls : list Tok) : list Tok :=
  match xs with
  | [] => ls
  | t :: ts => revAppendTokLoop ts (t :: ls)
  end.

Lemma encodeL_revAppendTokLoop (restL : Stream sym) :
  forall xs ls : list Tok,
    encodeL restL (revAppendTokLoop xs ls) = rev (encodeToks xs) *> encodeL restL ls.
Proof.
  induction xs as [| t ts ih]; intros ls; [reflexivity |].
  cbn [revAppendTokLoop encodeToks].
  rewrite ih; cbn [encodeL]; rewrite rev_app_distr, Str_app_assoc. reflexivity.
Qed.

Definition revPushTokL (xs ls : list Tok) : list Tok :=
  match xs with
  | [] => ls
  | t :: ts => revAppendTokLoop ts (pushL t ls)
  end.

Lemma encodeL_revPushTokL (restL : Stream sym) (xs ls : list Tok) :
  encodeL restL (revPushTokL xs ls) = rev (encodeToks xs) *> encodeL restL ls.
Proof.
  destruct xs as [| t ts]; [reflexivity |].
  cbn [revPushTokL encodeToks].
  rewrite encodeL_revAppendTokLoop, encodeL_pushL, rev_app_distr, Str_app_assoc.
  reflexivity.
Qed.

Fixpoint WValid (ws : list WTok) : Prop :=
  match ws with
  | [] => True
  | wdb m val :: ws' => 1 <= N.to_nat m /\ N.to_nat val < 4 ^ N.to_nat m /\ WValid ws'
  | wp n :: ws' => 1 <= N.to_nat n /\ WValid ws'
  end.

Lemma WValid_append : forall xs ys : list WTok,
  WValid xs -> WValid ys -> WValid (xs ++ ys).
Proof.
  induction xs as [| [m val | n] xs ih]; intros ys hx hy; cbn [app WValid] in *.
  - exact hy.
  - destruct hx as [hm [hv hxs]]. refine (conj hm (conj hv (ih ys hxs hy))).
  - destruct hx as [hn hxs]. refine (conj hn (ih ys hxs hy)).
Qed.

Inductive AbsRes : Type :=
  | Abs_absorbed : list Tok -> list Tok -> AbsRes
  | Abs_carried : AbsRes
  | Abs_err : AbsRes.

Inductive FastAbsRes : Type :=
  | FastAbs_absorbed : list Tok -> list Tok -> FastAbsRes
  | FastAbs_carried : FastAbsRes
  | FastAbs_fallback : list Tok -> N -> list Tok -> FastAbsRes.

Definition absDbStep (m val : N) (ts : list Tok)
    (cont : N -> list Tok -> FastAbsRes) (amt : N) (outRev : list Tok) : FastAbsRes :=
  let sh := (2 * m)%N in
  let p4 := N.shiftl 1 sh in
  let v := if (p4 <=? val)%N then N.land val (N.ones sh) else val in
  let s := (v + amt)%N in
  if (s <? p4)%N then
    FastAbs_absorbed (tdb m s :: outRev) ts
  else
    cont (N.shiftr s sh) (tdb m (N.land s (N.ones sh)) :: outRev).

Fixpoint tryAbsorbRun (ls : list Tok) (amt : N) (outRev : list Tok) {struct ls} : FastAbsRes :=
  match ls with
  | [] => FastAbs_carried
  | tp (Npos pn) :: ts =>
    tryAbsorbRun ts (N.shiftl amt (Npos pn)) (tp (Npos pn) :: outRev)
  | tdb (Npos pm) val :: ts =>
    absDbStep (Npos pm) val ts (tryAbsorbRun ts) amt outRev
  | t :: ts => FastAbs_fallback (t :: ts) amt outRev
  end.

Lemma absDbStep_sound (restL : Stream sym) (m val : N) (ts : list Tok)
    (cont : N -> list Tok -> FastAbsRes) (amt : N) (outRev : list Tok)
    (hcont : forall amt' outRev',
      match cont amt' outRev' with
      | FastAbs_carried => True
      | FastAbs_absorbed out' ls' =>
        exists wOrig wOut : list sym,
          encodeL restL ts = rev wOrig *> encodeL restL ls' /\
          encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev') *> encodeL restL ls' /\
          Absorbs (N.to_nat amt') wOrig wOut
      | FastAbs_fallback ls1 amt1 out1 =>
        forall (wOrig1 wOut1 : list sym) (out' ls' : list Tok),
          encodeL restL ls1 = rev wOrig1 *> encodeL restL ls' ->
          encodeL restL (revPushTokL out' ls') = rev (wOut1 ++ encodeToks out1) *> encodeL restL ls' ->
          Absorbs (N.to_nat amt1) wOrig1 wOut1 ->
          exists wOrig wOut : list sym,
            encodeL restL ts = rev wOrig *> encodeL restL ls' /\
            encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev') *> encodeL restL ls' /\
            Absorbs (N.to_nat amt') wOrig wOut
      end) :
  match absDbStep m val ts cont amt outRev with
  | FastAbs_carried => True
  | FastAbs_absorbed out' ls' =>
    exists wOrig wOut : list sym,
      encodeL restL (tdb m val :: ts) = rev wOrig *> encodeL restL ls' /\
      encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev) *> encodeL restL ls' /\
      Absorbs (N.to_nat amt) wOrig wOut
  | FastAbs_fallback ls1 amt1 out1 =>
    forall (wOrig1 wOut1 : list sym) (out' ls' : list Tok),
      encodeL restL ls1 = rev wOrig1 *> encodeL restL ls' ->
      encodeL restL (revPushTokL out' ls') = rev (wOut1 ++ encodeToks out1) *> encodeL restL ls' ->
      Absorbs (N.to_nat amt1) wOrig1 wOut1 ->
      exists wOrig wOut : list sym,
        encodeL restL (tdb m val :: ts) = rev wOrig *> encodeL restL ls' /\
        encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev) *> encodeL restL ls' /\
        Absorbs (N.to_nat amt) wOrig wOut
  end.
Proof.
  unfold absDbStep.
  set (sh := (2 * m)%N).
  set (p4 := N.shiftl 1 sh).
  pose proof (N2Nat_shiftl_pow4 m) as hp4. fold sh p4 in hp4.
  pose proof (pow4_pos (N.to_nat m)) as hpos4.
  assert (hred : exists v : N,
    (if (p4 <=? val)%N then N.land val (N.ones sh) else val) = v /\
    N.to_nat v < 4 ^ N.to_nat m /\
    dBlockBits (N.to_nat m) (N.to_nat val) = dBlockBits (N.to_nat m) (N.to_nat v)).
  { destruct (p4 <=? val)%N eqn:hbv.
    - exists (N.land val (N.ones sh)). refine (conj eq_refl (conj _ _)).
      + unfold sh; rewrite N2Nat_land_ones_pow4. apply Nat.mod_upper_bound; lia.
      + unfold sh; rewrite N2Nat_land_ones_pow4, dBlockBits_mod. reflexivity.
    - apply N.leb_gt in hbv. exists val. refine (conj eq_refl (conj _ eq_refl)). lia. }
  destruct hred as [v [hv_eq [hv_lt hdb_eq]]].
  rewrite hv_eq.
  destruct ((v + amt)%N <? p4)%N eqn:hslt.
  - apply N.ltb_lt in hslt.
    assert (hs : N.to_nat v + N.to_nat amt < 4 ^ N.to_nat m) by lia.
    assert (habs0 : Absorbs ((N.to_nat v + N.to_nat amt) / 4 ^ N.to_nat m) [] [])
      by (rewrite (Nat.div_small _ _ hs); reflexivity).
    pose proof (Absorbs_db (N.to_nat m) (N.to_nat v) (N.to_nat amt) hv_lt habs0) as habs1.
    rewrite (Nat.mod_small _ _ hs) in habs1. cbn [app] in habs1.
    exists (dBlockBits (N.to_nat m) (N.to_nat v)),
           (dBlockBits (N.to_nat m) (N.to_nat v + N.to_nat amt)).
    refine (conj _ (conj _ habs1)).
    + cbn [encodeL tokBits]. rewrite hdb_eq. reflexivity.
    + rewrite encodeL_revPushTokL. cbn [encodeToks tokBits].
      rewrite N2Nat.inj_add. reflexivity.
  - set (q := N.shiftr (v + amt)%N sh).
    set (r := N.land (v + amt)%N (N.ones sh)).
    assert (hq_nat : N.to_nat q = (N.to_nat v + N.to_nat amt) / 4 ^ N.to_nat m)
      by (unfold q, sh; rewrite N2Nat_shiftr_pow4, N2Nat.inj_add; reflexivity).
    assert (hr_nat : N.to_nat r = (N.to_nat v + N.to_nat amt) mod 4 ^ N.to_nat m)
      by (unfold r, sh; rewrite N2Nat_land_ones_pow4, N2Nat.inj_add; reflexivity).
    specialize (hcont q (tdb m r :: outRev)).
    destruct (cont q (tdb m r :: outRev)) as [out' ls'' | | ls1 amt1 out1].
    + destruct hcont as [wOrig [wOut [hL' [hout' habs]]]].
      rewrite hq_nat in habs.
      exists (wOrig ++ dBlockBits (N.to_nat m) (N.to_nat v)),
             (wOut ++ dBlockBits (N.to_nat m) ((N.to_nat v + N.to_nat amt) mod 4 ^ N.to_nat m)).
      refine (conj _ (conj _ (Absorbs_db (N.to_nat m) (N.to_nat v) (N.to_nat amt) hv_lt habs))).
      * cbn [encodeL tokBits]. rewrite hdb_eq, hL', rev_app_distr, Str_app_assoc. reflexivity.
      * rewrite hout'. cbn [encodeToks tokBits]. rewrite hr_nat, app_assoc. reflexivity.
    + exact I.
    + intros wOrig1 wOut1 out' ls'' hL1 hout1 habs1.
      destruct (hcont wOrig1 wOut1 out' ls'' hL1 hout1 habs1) as [wOrig [wOut [hL' [hout' habs]]]].
      rewrite hq_nat in habs.
      exists (wOrig ++ dBlockBits (N.to_nat m) (N.to_nat v)),
             (wOut ++ dBlockBits (N.to_nat m) ((N.to_nat v + N.to_nat amt) mod 4 ^ N.to_nat m)).
      refine (conj _ (conj _ (Absorbs_db (N.to_nat m) (N.to_nat v) (N.to_nat amt) hv_lt habs))).
      * cbn [encodeL tokBits]. rewrite hdb_eq, hL', rev_app_distr, Str_app_assoc. reflexivity.
      * rewrite hout'. cbn [encodeToks tokBits]. rewrite hr_nat, app_assoc. reflexivity.
Qed.

Lemma tryAbsorbRun_sound (restL : Stream sym) :
  forall (ls : list Tok) (amt : N) (outRev : list Tok),
    match tryAbsorbRun ls amt outRev with
    | FastAbs_carried => True
    | FastAbs_absorbed out' ls' =>
      exists wOrig wOut : list sym,
        encodeL restL ls = rev wOrig *> encodeL restL ls' /\
        encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev) *> encodeL restL ls' /\
        Absorbs (N.to_nat amt) wOrig wOut
    | FastAbs_fallback ls1 amt1 out1 =>
      forall (wOrig1 wOut1 : list sym) (out' ls' : list Tok),
        encodeL restL ls1 = rev wOrig1 *> encodeL restL ls' ->
        encodeL restL (revPushTokL out' ls') = rev (wOut1 ++ encodeToks out1) *> encodeL restL ls' ->
        Absorbs (N.to_nat amt1) wOrig1 wOut1 ->
        exists wOrig wOut : list sym,
          encodeL restL ls = rev wOrig *> encodeL restL ls' /\
          encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev) *> encodeL restL ls' /\
          Absorbs (N.to_nat amt) wOrig wOut
    end.
Proof.
  induction ls as [| t ts ih]; intros amt outRev; [exact I |].
  destruct t as [| | n | n | [| pn] | n | n | [| pm] val];
    try (cbn [tryAbsorbRun]; intros wOrig1 wOut1 out' ls' hL1 hout1 habs1;
         exists wOrig1, wOut1; exact (conj hL1 (conj hout1 habs1))).
  - (* tp (Npos pn) *)
    cbn [tryAbsorbRun].
    specialize (ih (N.shiftl amt (Npos pn)) (tp (Npos pn) :: outRev)).
    destruct (tryAbsorbRun ts (N.shiftl amt (Npos pn)) (tp (Npos pn) :: outRev))
      as [out' ls'' | | ls1 amt1 out1].
    + destruct ih as [wOrig [wOut [hL' [hout' habs]]]].
      rewrite N2Nat_shiftl in habs.
      exists (wOrig ++ pBits (N.to_nat (Npos pn))),
             (wOut ++ pBits (N.to_nat (Npos pn))).
      refine (conj _ (conj _ (Absorbs_p (N.to_nat (Npos pn)) (N.to_nat amt) habs))).
      * cbn [encodeL tokBits]. rewrite hL', rev_app_distr, Str_app_assoc. reflexivity.
      * rewrite hout'. cbn [encodeToks tokBits]. rewrite app_assoc. reflexivity.
    + exact I.
    + intros wOrig1 wOut1 out' ls'' hL1 hout1 habs1.
      destruct (ih wOrig1 wOut1 out' ls'' hL1 hout1 habs1) as [wOrig [wOut [hL' [hout' habs]]]].
      rewrite N2Nat_shiftl in habs.
      exists (wOrig ++ pBits (N.to_nat (Npos pn))),
             (wOut ++ pBits (N.to_nat (Npos pn))).
      refine (conj _ (conj _ (Absorbs_p (N.to_nat (Npos pn)) (N.to_nat amt) habs))).
      * cbn [encodeL tokBits]. rewrite hL', rev_app_distr, Str_app_assoc. reflexivity.
      * rewrite hout'. cbn [encodeToks tokBits]. rewrite app_assoc. reflexivity.
  - (* tdb (Npos pm) val *)
    cbn [tryAbsorbRun].
    exact (absDbStep_sound restL (Npos pm) val ts (tryAbsorbRun ts) amt outRev ih).
Qed.

Fixpoint tryAbsorbSlow (fuel : nat) (amt : N) (ls outRev : list Tok) {struct fuel} : AbsRes :=
  match fuel with
  | 0 => Abs_err
  | S fuel' =>
    match tryAbsorbRun ls amt outRev with
    | FastAbs_absorbed out' ls' => Abs_absorbed out' ls'
    | FastAbs_carried => Abs_carried
    | FastAbs_fallback ls1 amt1 out1 =>
      match popWTokSlow ls1 with
      | PW_none => Abs_carried
      | PW_p n ls' => tryAbsorbSlow fuel' (N.shiftl amt1 n) ls' (tp n :: out1)
      | PW_db m val ls' =>
        let sh := (2 * m)%N in
        let p4 := N.shiftl 1 sh in
        let s := (val + amt1)%N in
        if (s <? p4)%N then
          Abs_absorbed (tdb m s :: out1) ls'
        else
          tryAbsorbSlow fuel' (N.shiftr s sh) ls' (tdb m (N.land s (N.ones sh)) :: out1)
      end
    end
  end.

Lemma tryAbsorbSlow_sound (restL : Stream sym) :
  forall (fuel : nat) (amt : N) (ls outRev : list Tok),
    match tryAbsorbSlow fuel amt ls outRev with
    | Abs_err => True
    | Abs_carried => True
    | Abs_absorbed out' ls' =>
      exists wOrig wOut : list sym,
        encodeL restL ls = rev wOrig *> encodeL restL ls' /\
        encodeL restL (revPushTokL out' ls') = rev (wOut ++ encodeToks outRev) *> encodeL restL ls' /\
        Absorbs (N.to_nat amt) wOrig wOut
    end.
Proof.
  induction fuel as [| fuel ih]; intros amt ls outRev; [exact I |].
  cbn [tryAbsorbSlow].
  pose proof (tryAbsorbRun_sound restL ls amt outRev) as hrun.
  destruct (tryAbsorbRun ls amt outRev) as [out' ls' | | ls1 amt1 out1].
  - exact hrun.
  - exact I.
  - pose proof (popWTokSlow_sound restL ls1) as hp.
    destruct (popWTokSlow ls1) as [| m val ls' | n ls'].
    + exact I.
    + destruct hp as [_ [hval hL]].
      set (sh := (2 * m)%N).
      set (p4 := N.shiftl 1 sh).
      pose proof (N2Nat_shiftl_pow4 m) as hp4; fold sh p4 in hp4.
      destruct ((val + amt1)%N <? p4)%N eqn:hslt.
      * apply N.ltb_lt in hslt.
        assert (hs : N.to_nat val + N.to_nat amt1 < 4 ^ N.to_nat m) by lia.
        assert (habs0 : Absorbs ((N.to_nat val + N.to_nat amt1) / 4 ^ N.to_nat m) [] [])
          by (rewrite (Nat.div_small _ _ hs); reflexivity).
        pose proof (Absorbs_db (N.to_nat m) (N.to_nat val) (N.to_nat amt1) hval habs0) as habs1.
        rewrite (Nat.mod_small _ _ hs) in habs1; cbn [app] in habs1.
        apply (hrun (dBlockBits (N.to_nat m) (N.to_nat val))
                    (dBlockBits (N.to_nat m) (N.to_nat val + N.to_nat amt1))
                    (tdb m (val + amt1)%N :: out1) ls').
        -- exact hL.
        -- rewrite encodeL_revPushTokL. cbn [encodeToks tokBits].
           rewrite N2Nat.inj_add. reflexivity.
        -- exact habs1.
      * set (q := N.shiftr (val + amt1)%N sh).
        set (r := N.land (val + amt1)%N (N.ones sh)).
        specialize (ih q ls' (tdb m r :: out1)).
        destruct (tryAbsorbSlow fuel q ls' (tdb m r :: out1)) as [out' ls'' | | ];
          [| exact I | exact I].
        destruct ih as [wOrig [wOut [hL' [hout' habs]]]].
        assert (hq_nat : N.to_nat q = (N.to_nat val + N.to_nat amt1) / 4 ^ N.to_nat m)
          by (unfold q, sh; rewrite N2Nat_shiftr_pow4, N2Nat.inj_add; reflexivity).
        assert (hr_nat : N.to_nat r = (N.to_nat val + N.to_nat amt1) mod 4 ^ N.to_nat m)
          by (unfold r, sh; rewrite N2Nat_land_ones_pow4, N2Nat.inj_add; reflexivity).
        rewrite hq_nat in habs.
        apply (hrun (wOrig ++ dBlockBits (N.to_nat m) (N.to_nat val))
                    (wOut ++ dBlockBits (N.to_nat m) ((N.to_nat val + N.to_nat amt1) mod 4 ^ N.to_nat m))
                    out' ls'').
        -- rewrite hL, hL', rev_app_distr, Str_app_assoc. reflexivity.
        -- rewrite hout'. cbn [encodeToks tokBits]. rewrite hr_nat, app_assoc. reflexivity.
        -- exact (Absorbs_db (N.to_nat m) (N.to_nat val) (N.to_nat amt1) hval habs).
    + destruct hp as [_ hL].
      specialize (ih (N.shiftl amt1 n) ls' (tp n :: out1)).
      destruct (tryAbsorbSlow fuel (N.shiftl amt1 n) ls' (tp n :: out1)) as [out' ls'' | | ];
        [| exact I | exact I].
      destruct ih as [wOrig [wOut [hL' [hout' habs]]]].
      rewrite N2Nat_shiftl in habs.
      apply (hrun (wOrig ++ pBits (N.to_nat n))
                  (wOut ++ pBits (N.to_nat n)) out' ls'').
      * rewrite hL, hL', rev_app_distr, Str_app_assoc. reflexivity.
      * rewrite hout'. cbn [encodeToks tokBits]. rewrite app_assoc. reflexivity.
      * exact (Absorbs_p (N.to_nat n) (N.to_nat amt1) habs).
Qed.

Definition tryAbsorb (amt : N) (ls : list Tok) : AbsRes :=
  if (amt =? 0)%N then Abs_absorbed [] ls
  else tryAbsorbSlow 2000 amt ls [].

Lemma tryAbsorb_sound (restL : Stream sym) (amt : N) (ls : list Tok) :
  match tryAbsorb amt ls with
  | Abs_err => True
  | Abs_carried => True
  | Abs_absorbed out' ls' =>
    exists wOrig wOut : list sym,
      encodeL restL ls = rev wOrig *> encodeL restL ls' /\
      encodeL restL (revPushTokL out' ls') = rev wOut *> encodeL restL ls' /\
      Absorbs (N.to_nat amt) wOrig wOut
  end.
Proof.
  unfold tryAbsorb. destruct (amt =? 0)%N eqn:h0.
  - apply N.eqb_eq in h0; subst amt.
    exists (@nil sym), (@nil sym). refine (conj eq_refl (conj eq_refl eq_refl)).
  - pose proof (tryAbsorbSlow_sound restL 2000 amt ls []) as hf.
    destruct (tryAbsorbSlow 2000 amt ls []) as [out' ls' | | ]; [| exact I | exact I].
    destruct hf as [wOrig [wOut [hL' [hout' habs]]]].
    cbn [encodeToks] in hout'. rewrite app_nil_r in hout'.
    exists wOrig, wOut. exact (conj hL' (conj hout' habs)).
Qed.

(* W-Extraction (extractWRun / extractWLoop / extractWFast) *)

Inductive ExtWRes : Type :=
  | ExtW_ok : list WTok -> list Tok -> ExtWRes
  | ExtW_err : ExtWRes.

Inductive FastExtWRes : Type :=
  | FastExtW_ok : list WTok -> list Tok -> FastExtWRes
  | FastExtW_fallback : list Tok -> list WTok -> FastExtWRes.

Fixpoint extractWRun (ls : list Tok) (acc : list WTok) {struct ls} : FastExtWRes :=
  match ls with
  | [] => FastExtW_ok acc []
  | tp (Npos pn) :: ts => extractWRun ts (wp (Npos pn) :: acc)
  | tdb (Npos pm) val :: ts =>
    let m := Npos pm in
    let sh := (2 * m)%N in
    let p4 := N.shiftl 1 sh in
    let v := if (p4 <=? val)%N then N.land val (N.ones sh) else val in
    extractWRun ts (wdb m v :: acc)
  | t :: ts => FastExtW_fallback (t :: ts) acc
  end.

Lemma extractWRun_sound (restL : Stream sym) :
  forall (ls : list Tok) (acc : list WTok),
    WValid acc ->
    match extractWRun ls acc with
    | FastExtW_ok ws ls' =>
      exists pref : list WTok,
        ws = pref ++ acc /\ WValid pref /\
        encodeL restL ls = rev (encodeW pref) *> encodeL restL ls'
    | FastExtW_fallback ls1 acc1 =>
      WValid acc1 /\
      exists pref : list WTok,
        acc1 = pref ++ acc /\ WValid pref /\
        encodeL restL ls = rev (encodeW pref) *> encodeL restL ls1
    end.
Proof.
  induction ls as [| t ts ih]; intros acc hv.
  - cbn [extractWRun]. exists (@nil WTok). exact (conj eq_refl (conj I eq_refl)).
  - destruct t as [| | n | n | [| pn] | n | n | [| pm] val];
      try (cbn [extractWRun]; refine (conj hv _); exists (@nil WTok);
           exact (conj eq_refl (conj I eq_refl))).
    + (* tp (Npos pn) *)
      cbn [extractWRun].
      assert (hn : 1 <= N.to_nat (Npos pn)) by lia.
      specialize (ih (wp (Npos pn) :: acc) (conj hn hv)).
      destruct (extractWRun ts (wp (Npos pn) :: acc)) as [ws ls'' | ls1 acc1].
      * destruct ih as [pref [hEq [hvp hL']]].
        exists (pref ++ [wp (Npos pn)]).
        refine (conj _ (conj (WValid_append pref [wp (Npos pn)] hvp (conj hn I)) _)).
        -- rewrite hEq, <- app_assoc. reflexivity.
        -- cbn [encodeL tokBits]. rewrite hL', encodeW_append.
           cbn [encodeW wTokBits]. rewrite app_nil_r, rev_app_distr, Str_app_assoc.
           reflexivity.
      * destruct ih as [hv1 [pref [hEq [hvp hL']]]].
        refine (conj hv1 _).
        exists (pref ++ [wp (Npos pn)]).
        refine (conj _ (conj (WValid_append pref [wp (Npos pn)] hvp (conj hn I)) _)).
        -- rewrite hEq, <- app_assoc. reflexivity.
        -- cbn [encodeL tokBits]. rewrite hL', encodeW_append.
           cbn [encodeW wTokBits]. rewrite app_nil_r, rev_app_distr, Str_app_assoc.
           reflexivity.
    + (* tdb (Npos pm) val *)
      cbn [extractWRun].
      set (m := Npos pm).
      set (sh := (2 * m)%N).
      set (p4 := N.shiftl 1 sh).
      pose proof (N2Nat_shiftl_pow4 m) as hp4; fold sh p4 in hp4.
      pose proof (pow4_pos (N.to_nat m)) as hpos4.
      assert (hm : 1 <= N.to_nat m) by (unfold m; lia).
      assert (hred : exists v : N,
        (if (p4 <=? val)%N then N.land val (N.ones sh) else val) = v /\
        N.to_nat v < 4 ^ N.to_nat m /\
        dBlockBits (N.to_nat m) (N.to_nat val) = dBlockBits (N.to_nat m) (N.to_nat v)).
      { destruct (p4 <=? val)%N eqn:hbv.
        - exists (N.land val (N.ones sh)). refine (conj eq_refl (conj _ _)).
          + unfold sh; rewrite N2Nat_land_ones_pow4. apply Nat.mod_upper_bound; lia.
          + unfold sh; rewrite N2Nat_land_ones_pow4, dBlockBits_mod. reflexivity.
        - apply N.leb_gt in hbv. exists val. refine (conj eq_refl (conj _ eq_refl)); lia. }
      destruct hred as [v [hv_eq [hv_lt hdb_eq]]].
      rewrite hv_eq.
      specialize (ih (wdb m v :: acc) (conj hm (conj hv_lt hv))).
      destruct (extractWRun ts (wdb m v :: acc)) as [ws ls'' | ls1 acc1].
      * destruct ih as [pref [hEq [hvp hL']]].
        exists (pref ++ [wdb m v]).
        refine (conj _ (conj (WValid_append pref [wdb m v] hvp (conj hm (conj hv_lt I))) _)).
        -- rewrite hEq, <- app_assoc. reflexivity.
        -- cbn [encodeL tokBits]; fold m. rewrite hdb_eq, hL', encodeW_append.
           cbn [encodeW wTokBits]. rewrite app_nil_r, rev_app_distr, Str_app_assoc.
           reflexivity.
      * destruct ih as [hv1 [pref [hEq [hvp hL']]]].
        refine (conj hv1 _).
        exists (pref ++ [wdb m v]).
        refine (conj _ (conj (WValid_append pref [wdb m v] hvp (conj hm (conj hv_lt I))) _)).
        -- rewrite hEq, <- app_assoc. reflexivity.
        -- cbn [encodeL tokBits]; fold m. rewrite hdb_eq, hL', encodeW_append.
           cbn [encodeW wTokBits]. rewrite app_nil_r, rev_app_distr, Str_app_assoc.
           reflexivity.
Qed.

Fixpoint extractWLoop (fuel : nat) (ls : list Tok) (acc : list WTok) {struct fuel} : ExtWRes :=
  match fuel with
  | 0 => ExtW_err
  | S fuel' =>
    match extractWRun ls acc with
    | FastExtW_ok ws ls' => ExtW_ok ws ls'
    | FastExtW_fallback ls1 acc1 =>
      match popWTokSlow ls1 with
      | PW_none => ExtW_ok acc1 ls1
      | PW_p n ls' => extractWLoop fuel' ls' (wp n :: acc1)
      | PW_db m val ls' => extractWLoop fuel' ls' (wdb m val :: acc1)
      end
    end
  end.

Lemma extractWLoop_sound (restL : Stream sym) :
  forall (fuel : nat) (ls : list Tok) (acc : list WTok),
    WValid acc ->
    match extractWLoop fuel ls acc with
    | ExtW_err => True
    | ExtW_ok ws ls' =>
      exists pref : list WTok,
        ws = pref ++ acc /\ WValid pref /\
        encodeL restL ls = rev (encodeW pref) *> encodeL restL ls'
    end.
Proof.
  induction fuel as [| fuel ih]; intros ls acc hv; [exact I |].
  cbn [extractWLoop].
  pose proof (extractWRun_sound restL ls acc hv) as hrun.
  destruct (extractWRun ls acc) as [ws ls' | ls1 acc1]; [exact hrun |].
  destruct hrun as [hv1 [pref1 [hEq1 [hvp1 hL1]]]].
  pose proof (popWTokSlow_sound restL ls1) as hp.
  destruct (popWTokSlow ls1) as [| m val ls' | n ls'].
  - exists pref1. exact (conj hEq1 (conj hvp1 hL1)).
  - destruct hp as [hm [hval hL]].
    specialize (ih ls' (wdb m val :: acc1) (conj hm (conj hval hv1))).
    destruct (extractWLoop fuel ls' (wdb m val :: acc1)) as [ws ls'' | ]; [| exact I].
    destruct ih as [pref2 [hEq2 [hvp2 hL2]]].
    exists (pref2 ++ (wdb m val :: pref1)).
    refine (conj _ (conj (WValid_append pref2 (wdb m val :: pref1) hvp2 (conj hm (conj hval hvp1))) _)).
    + rewrite hEq2, hEq1, <- app_assoc. reflexivity.
    + rewrite hL1, hL, hL2, encodeW_append. cbn [encodeW wTokBits].
      rewrite !rev_app_distr, !Str_app_assoc. reflexivity.
  - destruct hp as [hn hL].
    specialize (ih ls' (wp n :: acc1) (conj hn hv1)).
    destruct (extractWLoop fuel ls' (wp n :: acc1)) as [ws ls'' | ]; [| exact I].
    destruct ih as [pref2 [hEq2 [hvp2 hL2]]].
    exists (pref2 ++ (wp n :: pref1)).
    refine (conj _ (conj (WValid_append pref2 (wp n :: pref1) hvp2 (conj hn hvp1)) _)).
    + rewrite hEq2, hEq1, <- app_assoc. reflexivity.
    + rewrite hL1, hL, hL2, encodeW_append. cbn [encodeW wTokBits].
      rewrite !rev_app_distr, !Str_app_assoc. reflexivity.
Qed.

Definition extractWFast (ls : list Tok) (acc : list WTok) : ExtWRes :=
  extractWLoop 2000 ls acc.

Lemma extractWFast_sound (restL : Stream sym) (ls : list Tok) (acc : list WTok) (hv : WValid acc) :
  match extractWFast ls acc with
  | ExtW_err => True
  | ExtW_ok ws ls' =>
    exists pref : list WTok,
      ws = pref ++ acc /\ WValid pref /\
      encodeL restL ls = rev (encodeW pref) *> encodeL restL ls'
  end.
Proof. exact (extractWLoop_sound restL 2000 ls acc hv). Qed.

(* pushZORev, pushZORevTrim, revPushR & carryWLoop *)

Fixpoint revTokBits (acc : list Tok) : list sym :=
  match acc with
  | [] => []
  | t :: ts => revTokBits ts ++ tokBits t
  end.

Fixpoint revAppendRLoop (acc rs : list Tok) : list Tok :=
  match acc with
  | [] => rs
  | t :: ts => revAppendRLoop ts (t :: rs)
  end.

Lemma encodeR_revAppendRLoop : forall acc rs : list Tok,
  encodeR (revAppendRLoop acc rs) = revTokBits acc *> encodeR rs.
Proof.
  induction acc as [| t ts ih]; intros rs; [reflexivity |].
  cbn [revAppendRLoop revTokBits].
  rewrite ih; cbn [encodeR]; rewrite Str_app_assoc. reflexivity.
Qed.

Definition revPushR (acc rs : list Tok) : list Tok :=
  match acc with
  | [] => rs
  | t :: ts => revAppendRLoop ts (pushR t rs)
  end.

Lemma encodeR_revPushR_bits (acc rs : list Tok) :
  encodeR (revPushR acc rs) = revTokBits acc *> encodeR rs.
Proof.
  destruct acc as [| t ts]; [reflexivity |].
  cbn [revPushR revTokBits].
  rewrite encodeR_revAppendRLoop, encodeR_pushR, Str_app_assoc. reflexivity.
Qed.

Definition accZ (rem : N) (acc : list Tok) : list Tok :=
  if (rem =? 0)%N then acc else
  match acc with
  | tz n :: ts => tz (n + rem)%N :: ts
  | _ => tz rem :: acc
  end.

Definition accO (rem : N) (acc : list Tok) : list Tok :=
  if (rem =? 0)%N then acc else
  match acc with
  | to_ n :: ts => to_ (n + rem)%N :: ts
  | _ => to_ rem :: acc
  end.

Definition accC (m : N) (acc : list Tok) : list Tok :=
  match acc with
  | tc m0 :: ts => tc (m0 + m)%N :: ts
  | _ => tc m :: acc
  end.

Lemma revTokBits_accZ (rem : N) (acc : list Tok) :
  revTokBits (accZ rem acc) = revTokBits acc ++ zBits (N.to_nat rem).
Proof.
  unfold accZ. destruct (rem =? 0)%N eqn:h0.
  - apply N.eqb_eq in h0; subst rem. cbn [N.to_nat zBits repBits].
    rewrite app_nil_r. reflexivity.
  - destruct acc as [| [| | n | | | | | ] ts];
      try (cbn [revTokBits tokBits]; reflexivity).
    cbn [revTokBits tokBits]. unfold zBits.
    rewrite N2Nat.inj_add, repBits_add, app_assoc. reflexivity.
Qed.

Lemma revTokBits_accO (rem : N) (acc : list Tok) :
  revTokBits (accO rem acc) = revTokBits acc ++ oBits (N.to_nat rem).
Proof.
  unfold accO. destruct (rem =? 0)%N eqn:h0.
  - apply N.eqb_eq in h0; subst rem. cbn [N.to_nat oBits repBits].
    rewrite app_nil_r. reflexivity.
  - destruct acc as [| [| | | n | | | | ] ts];
      try (cbn [revTokBits tokBits]; reflexivity).
    cbn [revTokBits tokBits]. unfold oBits.
    rewrite N2Nat.inj_add, repBits_add, app_assoc. reflexivity.
Qed.

Lemma revTokBits_accC (m : N) (acc : list Tok) :
  revTokBits (accC m acc) = revTokBits acc ++ cBits (N.to_nat m).
Proof.
  unfold accC. destruct acc as [| [| | | | | | m0 | ] ts];
    try (cbn [revTokBits tokBits]; reflexivity).
  cbn [revTokBits tokBits]. unfold cBits.
  rewrite N2Nat.inj_add, repBits_add, app_assoc. reflexivity.
Qed.

Fixpoint pushZORevPos (p : positive) (k : N) (acc : list Tok) {struct p} : list Tok :=
  match k with
  | N0 => acc
  | Npos pk =>
    let k' := Pos.pred_N pk in
    match p with
    | xH => accZ k' (accO 1 acc)
    | xO q => pushZORevPos q k' (accZ 1 acc)
    | xI q => pushZORevPos q k' (accO 1 acc)
    end
  end.

Definition pushZORev (k val : N) (acc : list Tok) : list Tok :=
  match val with
  | N0 => accZ k acc
  | Npos p => pushZORevPos p k acc
  end.

Lemma revTokBits_pushZORevPos : forall (p : positive) (k : N) (acc : list Tok),
  revTokBits (pushZORevPos p k acc) = revTokBits acc ++ zoBits (N.to_nat k) (N.to_nat (Npos p)).
Proof.
  induction p as [q ih | q ih | ]; intros [| pk] acc.
  - cbn [pushZORevPos N.to_nat zoBits]. rewrite app_nil_r. reflexivity.
  - cbn [pushZORevPos]. set (k' := Pos.pred_N pk).
    rewrite ih, revTokBits_accO, (N2Nat_pos_pred pk); fold k'. cbn [zoBits].
    assert (hmod : N.to_nat (Npos (xI q)) mod 2 = 1) by lia.
    assert (hdiv : N.to_nat (Npos (xI q)) / 2 = N.to_nat (Npos q)) by lia.
    rewrite hmod, hdiv. change (oBits (N.to_nat 1)) with [S1; S1].
    cbn [Nat.eqb]. rewrite <- app_assoc. reflexivity.
  - cbn [pushZORevPos N.to_nat zoBits]. rewrite app_nil_r. reflexivity.
  - cbn [pushZORevPos]. set (k' := Pos.pred_N pk).
    rewrite ih, revTokBits_accZ, (N2Nat_pos_pred pk); fold k'. cbn [zoBits].
    assert (hmod : N.to_nat (Npos (xO q)) mod 2 = 0) by lia.
    assert (hdiv : N.to_nat (Npos (xO q)) / 2 = N.to_nat (Npos q)) by lia.
    rewrite hmod, hdiv. change (zBits (N.to_nat 1)) with [S0; S0].
    cbn [Nat.eqb]. rewrite <- app_assoc. reflexivity.
  - cbn [pushZORevPos N.to_nat zoBits]. rewrite app_nil_r. reflexivity.
  - cbn [pushZORevPos]. set (k' := Pos.pred_N pk).
    rewrite revTokBits_accZ, revTokBits_accO, (N2Nat_pos_pred pk); fold k'. cbn [zoBits].
    replace (N.to_nat 1 mod 2) with 1 by reflexivity.
    replace (N.to_nat 1 / 2) with 0 by reflexivity.
    change (oBits (N.to_nat 1)) with [S1; S1].
    rewrite zoBits_zeros, <- app_assoc. reflexivity.
Qed.

Lemma revTokBits_pushZORev (k val : N) (acc : list Tok) :
  revTokBits (pushZORev k val acc) = revTokBits acc ++ zoBits (N.to_nat k) (N.to_nat val).
Proof.
  destruct val as [| p].
  - cbn [pushZORev N.to_nat]. rewrite revTokBits_accZ, zoBits_zeros. reflexivity.
  - exact (revTokBits_pushZORevPos p k acc).
Qed.

Fixpoint pushZORevTrimPos (p : positive) (k : N) (acc : list Tok) {struct p} : list Tok :=
  match k with
  | N0 => acc
  | Npos pk =>
    let k' := Pos.pred_N pk in
    match p with
    | xH => accO 1 acc
    | xO q => pushZORevTrimPos q k' (accZ 1 acc)
    | xI q => pushZORevTrimPos q k' (accO 1 acc)
    end
  end.

Definition pushZORevTrim (k val : N) (acc : list Tok) : list Tok :=
  match val with
  | N0 => acc
  | Npos p => pushZORevTrimPos p k acc
  end.

Lemma encodeR_revPushR_trimPos : forall (p : positive) (k : N) (acc : list Tok),
  encodeR (revPushR (pushZORevTrimPos p k acc) []) =
    revTokBits acc *> (zoBits (N.to_nat k) (N.to_nat (Npos p)) *> 0inf).
Proof.
  induction p as [q ih | q ih | ]; intros [| pk] acc.
  - cbn [pushZORevTrimPos N.to_nat zoBits Str_app]. apply encodeR_revPushR_bits.
  - cbn [pushZORevTrimPos]. set (k' := Pos.pred_N pk).
    rewrite ih, revTokBits_accO, (N2Nat_pos_pred pk); fold k'. cbn [zoBits].
    assert (hmod : N.to_nat (Npos (xI q)) mod 2 = 1) by lia.
    assert (hdiv : N.to_nat (Npos (xI q)) / 2 = N.to_nat (Npos q)) by lia.
    rewrite hmod, hdiv. change (oBits (N.to_nat 1)) with [S1; S1].
    cbn [Nat.eqb]. rewrite !Str_app_assoc. reflexivity.
  - cbn [pushZORevTrimPos N.to_nat zoBits Str_app]. apply encodeR_revPushR_bits.
  - cbn [pushZORevTrimPos]. set (k' := Pos.pred_N pk).
    rewrite ih, revTokBits_accZ, (N2Nat_pos_pred pk); fold k'. cbn [zoBits].
    assert (hmod : N.to_nat (Npos (xO q)) mod 2 = 0) by lia.
    assert (hdiv : N.to_nat (Npos (xO q)) / 2 = N.to_nat (Npos q)) by lia.
    rewrite hmod, hdiv. change (zBits (N.to_nat 1)) with [S0; S0].
    cbn [Nat.eqb]. rewrite !Str_app_assoc. reflexivity.
  - cbn [pushZORevTrimPos N.to_nat zoBits Str_app]. apply encodeR_revPushR_bits.
  - cbn [pushZORevTrimPos]. set (k' := Pos.pred_N pk).
    rewrite encodeR_revPushR_bits, revTokBits_accO, (N2Nat_pos_pred pk); fold k'. cbn [zoBits].
    replace (N.to_nat 1 mod 2) with 1 by reflexivity.
    replace (N.to_nat 1 / 2) with 0 by reflexivity.
    change (oBits (N.to_nat 1)) with [S1; S1].
    cbn [Nat.eqb]. rewrite !Str_app_assoc, zoBits_zero_default. reflexivity.
Qed.

Lemma encodeR_revPushR_trim (k val : N) (acc : list Tok) :
  encodeR (revPushR (pushZORevTrim k val acc) []) =
    revTokBits acc *> (zoBits (N.to_nat k) (N.to_nat val) *> 0inf).
Proof.
  destruct val as [| p].
  - cbn [pushZORevTrim N.to_nat].
    rewrite encodeR_revPushR_bits, zoBits_zero_default. reflexivity.
  - exact (encodeR_revPushR_trimPos p k acc).
Qed.

Inductive CarryRes : Type :=
  | Carry_mk : N -> list Tok -> CarryRes.

Fixpoint carryWLoop (c : N) (carRev : list Tok) (ws : list WTok) : CarryRes :=
  match ws with
  | [] => Carry_mk c carRev
  | wdb m val :: ws' =>
    let c' := (N.shiftl c (2 * m) - val)%N in
    carryWLoop c' (accC m carRev) ws'
  | wp n :: ws' =>
    let d := (c - 1)%N in
    let c' := (N.shiftr d n + 1)%N in
    let rem := N.land d (N.ones n) in
    carryWLoop c' (pushZORev n rem carRev) ws'
  end.

Lemma carryWLoop_sound :
  forall (ws : list WTok) (strict : bool) (c : N) (carRev : list Tok) (w : list sym),
    WValid ws ->
    Carries strict (N.to_nat c) w (revTokBits carRev) ->
    match carryWLoop c carRev ws with
    | Carry_mk c' carRev' =>
      Carries (strict || match ws with [] => false | _ => true end)
        (N.to_nat c') (w ++ encodeW ws) (revTokBits carRev')
    end.
Proof.
  induction ws as [| [m val | n] ws ih]; intros strict c carRev w hv hc.
  - cbn [carryWLoop encodeW]. rewrite app_nil_r, orb_false_r. exact hc.
  - cbn [carryWLoop encodeW wTokBits].
    destruct hv as [hm [hval hvs]].
    pose proof (Carries_db (N.to_nat m) (N.to_nat val) hm hval hc) as hcdb.
    rewrite <- revTokBits_accC in hcdb.
    replace (N.to_nat c * 4 ^ N.to_nat m - N.to_nat val)
      with (N.to_nat (N.shiftl c (2 * m) - val)%N) in hcdb
      by (rewrite N2Nat.inj_sub, N2Nat_shiftl_mul_pow4; reflexivity).
    pose proof (ih true (N.shiftl c (2 * m) - val)%N (accC m carRev)
      (w ++ dBlockBits (N.to_nat m) (N.to_nat val)) hvs hcdb) as hih.
    destruct (carryWLoop (N.shiftl c (2 * m) - val)%N (accC m carRev) ws) as [c' carRev'].
    rewrite orb_true_r, app_assoc. exact hih.
  - cbn [carryWLoop encodeW wTokBits].
    destruct hv as [hn hvs].
    pose proof (Carries_pos hc) as hcpos.
    pose proof (pow2_pos (N.to_nat n)) as hp2.
    pose proof (Carries_p (N.to_nat n) hn hc) as hcp.
    set (d := (c - 1)%N).
    set (c' := (N.shiftr d n + 1)%N).
    set (rem := N.land d (N.ones n)).
    assert (hc'_eq : N.to_nat c' = (N.to_nat c + 2 ^ N.to_nat n - 1) / 2 ^ N.to_nat n).
    { unfold c', d.
      rewrite N2Nat.inj_add, N2Nat_shiftr, N2Nat.inj_sub.
      change (N.to_nat 1) with 1.
      replace (N.to_nat c + 2 ^ N.to_nat n - 1)
        with (1 * 2 ^ N.to_nat n + (N.to_nat c - 1)) by lia.
      rewrite (add_mul_div_left 1 (N.to_nat c - 1) (2 ^ N.to_nat n) hp2). lia. }
    assert (hrem_eq : revTokBits (pushZORev n rem carRev) =
      revTokBits carRev ++ zoBits (N.to_nat n) (N.to_nat c - 1)).
    { rewrite revTokBits_pushZORev. unfold rem, d.
      rewrite N2Nat_land_ones, N2Nat.inj_sub, zoBits_mod. reflexivity. }
    rewrite <- hc'_eq, <- hrem_eq in hcp.
    pose proof (ih true c' (pushZORev n rem carRev) (w ++ pBits (N.to_nat n)) hvs hcp) as hih.
    destruct (carryWLoop c' (pushZORev n rem carRev) ws) as [c'' carRev'].
    rewrite orb_true_r, app_assoc. exact hih.
Qed.

(* extractZOLoop for Right-Hand Binary Counter *)

Inductive ExtZORes : Type :=
  | ExtZO_mk : N -> N -> N -> list Tok -> ExtZORes.

Fixpoint extractZOLoop (fuel : nat) (k mval rval : N) (rs : list Tok) {struct fuel} : ExtZORes :=
  match fuel with
  | 0 => ExtZO_mk k mval rval rs
  | S fuel' =>
    match rs with
    | [] => ExtZO_mk k mval rval []
    | tz N0 :: ts => extractZOLoop fuel' k mval rval ts
    | tz (Npos pn) :: ts =>
      let n := Npos pn in
      let mask := N.shiftl (N.ones n) k in
      extractZOLoop fuel' (k + n)%N mval (rval + mask)%N ts
    | to_ N0 :: ts => extractZOLoop fuel' k mval rval ts
    | to_ (Npos pn) :: ts =>
      let n := Npos pn in
      let mask := N.shiftl (N.ones n) k in
      extractZOLoop fuel' (k + n)%N (mval + mask)%N rval ts
    | _ =>
      match popBitR rs with
      | PBR_bit0 rs1 =>
        match rs1 with
        | [] => ExtZO_mk (k + 1)%N mval (rval + N.shiftl 1 k)%N []
        | _ =>
          match popBitR rs1 with
          | PBR_bit0 rs2 =>
            extractZOLoop fuel' (k + 1)%N mval (rval + N.shiftl 1 k)%N rs2
          | PBR_bit1 rs2 => ExtZO_mk k mval rval (tb0 :: tb1 :: rs2)
          end
        end
      | PBR_bit1 rs1 =>
        match rs1 with
        | [] => ExtZO_mk k mval rval [tb1]
        | _ =>
          match popBitR rs1 with
          | PBR_bit1 rs2 =>
            extractZOLoop fuel' (k + 1)%N (mval + N.shiftl 1 k)%N rval rs2
          | PBR_bit0 rs2 => ExtZO_mk k mval rval (tb1 :: tb0 :: rs2)
          end
        end
      end
    end
  end.

Lemma extractZOLoop_sound :
  forall (fuel : nat) (k mval rval : N) (rs : list Tok),
    N.to_nat mval + N.to_nat rval + 1 = 2 ^ N.to_nat k ->
    match extractZOLoop fuel k mval rval rs with
    | ExtZO_mk k' mval' rval' rs' =>
      N.to_nat k <= N.to_nat k' /\
      N.to_nat mval' + N.to_nat rval' + 1 = 2 ^ N.to_nat k' /\
      zoBits (N.to_nat k) (N.to_nat mval) *> encodeR rs =
        zoBits (N.to_nat k') (N.to_nat mval') *> encodeR rs'
    end.
Proof.
  induction fuel as [| fuel ih]; intros k mval rval rs hsum.
  - cbn [extractZOLoop]. refine (conj (Nat.le_refl _) (conj hsum eq_refl)).
  - cbn [extractZOLoop].
    assert (hslow : forall rs0 : list Tok,
      match (match popBitR rs0 with
        | PBR_bit0 rs1 =>
          match rs1 with
          | [] => ExtZO_mk (k + 1)%N mval (rval + N.shiftl 1 k)%N []
          | _ =>
            match popBitR rs1 with
            | PBR_bit0 rs2 =>
              extractZOLoop fuel (k + 1)%N mval (rval + N.shiftl 1 k)%N rs2
            | PBR_bit1 rs2 => ExtZO_mk k mval rval (tb0 :: tb1 :: rs2)
            end
          end
        | PBR_bit1 rs1 =>
          match rs1 with
          | [] => ExtZO_mk k mval rval [tb1]
          | _ =>
            match popBitR rs1 with
            | PBR_bit1 rs2 =>
              extractZOLoop fuel (k + 1)%N (mval + N.shiftl 1 k)%N rval rs2
            | PBR_bit0 rs2 => ExtZO_mk k mval rval (tb1 :: tb0 :: rs2)
            end
          end
        end) with
      | ExtZO_mk k' mval' rval' rs' =>
        N.to_nat k <= N.to_nat k' /\
        N.to_nat mval' + N.to_nat rval' + 1 = 2 ^ N.to_nat k' /\
        zoBits (N.to_nat k) (N.to_nat mval) *> encodeR rs0 =
          zoBits (N.to_nat k') (N.to_nat mval') *> encodeR rs'
      end).
    { intros rs0.
      pose proof (pow2_pos (N.to_nat k)) as hpk.
      pose proof (N2Nat_shiftl_1 k) as hsh1.
      assert (hk1 : N.to_nat (k + 1)%N = N.to_nat k + 1) by lia.
      assert (hle1 : N.to_nat k <= N.to_nat (k + 1)%N) by lia.
      assert (hp2k1 : 2 ^ N.to_nat (k + 1)%N = 2 * 2 ^ N.to_nat k)
        by (rewrite hk1, Nat.pow_add_r; cbn [Nat.pow]; lia).
      pose proof (popBitR_sound rs0) as hp1.
      destruct (popBitR rs0) as [rs1 | rs1].
      - destruct rs1 as [| r1 rs1'].
        + assert (hsum' : N.to_nat mval + N.to_nat (rval + N.shiftl 1 k)%N + 1 = 2 ^ N.to_nat (k + 1)%N)
            by (rewrite N2Nat.inj_add, hsh1, hp2k1; lia).
          refine (conj hle1 (conj hsum' _)).
          rewrite hk1, zoBits_add, (Nat.div_small (N.to_nat mval) (2 ^ N.to_nat k) ltac:(lia)), zoBits_zeros.
          cbn [encodeR] in hp1 |- *.
          rewrite hp1, cons_zero_0inf, Str_app_assoc.
          cbn [zBits repBits app Str_app].
          rewrite !cons_zero_0inf. reflexivity.
        + pose proof (popBitR_sound (r1 :: rs1')) as hp2.
          destruct (popBitR (r1 :: rs1')) as [rs2 | rs2].
          * assert (hsum' : N.to_nat mval + N.to_nat (rval + N.shiftl 1 k)%N + 1 = 2 ^ N.to_nat (k + 1)%N)
              by (rewrite N2Nat.inj_add, hsh1, hp2k1; lia).
            specialize (ih (k + 1)%N mval (rval + N.shiftl 1 k)%N rs2 hsum').
            destruct (extractZOLoop fuel (k + 1)%N mval (rval + N.shiftl 1 k)%N rs2)
              as [k' mval' rval' rs'].
            destruct ih as [hk' [hsum_end hbits_end]].
            assert (hle' : N.to_nat k <= N.to_nat k') by lia.
            refine (conj hle' (conj hsum_end _)).
            rewrite <- hbits_end, hk1, zoBits_add,
              (Nat.div_small (N.to_nat mval) (2 ^ N.to_nat k) ltac:(lia)), zoBits_zeros.
            rewrite hp1, hp2, Str_app_assoc. reflexivity.
          * refine (conj (Nat.le_refl _) (conj hsum _)).
            rewrite hp1, hp2. reflexivity.
      - destruct rs1 as [| r1 rs1'].
        + refine (conj (Nat.le_refl _) (conj hsum _)).
          rewrite hp1. reflexivity.
        + pose proof (popBitR_sound (r1 :: rs1')) as hp2.
          destruct (popBitR (r1 :: rs1')) as [rs2 | rs2].
          * refine (conj (Nat.le_refl _) (conj hsum _)).
            rewrite hp1, hp2. reflexivity.
          * assert (hsum' : N.to_nat (mval + N.shiftl 1 k)%N + N.to_nat rval + 1 = 2 ^ N.to_nat (k + 1)%N)
              by (rewrite N2Nat.inj_add, hsh1, hp2k1; lia).
            specialize (ih (k + 1)%N (mval + N.shiftl 1 k)%N rval rs2 hsum').
            destruct (extractZOLoop fuel (k + 1)%N (mval + N.shiftl 1 k)%N rval rs2)
              as [k' mval' rval' rs'].
            destruct ih as [hk' [hsum_end hbits_end]].
            assert (hle' : N.to_nat k <= N.to_nat k') by lia.
            refine (conj hle' (conj hsum_end _)).
            rewrite <- hbits_end, hk1, zoBits_add.
            rewrite N2Nat.inj_add, hsh1.
            assert (hMlt : N.to_nat mval < 2 ^ N.to_nat k) by lia.
            replace (N.to_nat mval + 2 ^ N.to_nat k) with (1 * 2 ^ N.to_nat k + N.to_nat mval) by lia.
            rewrite <- (zoBits_mod (N.to_nat k) (1 * 2 ^ N.to_nat k + N.to_nat mval)).
            rewrite (add_mul_mod_left 1 (N.to_nat mval) (2 ^ N.to_nat k) hpk),
              (Nat.mod_small _ _ hMlt).
            rewrite (add_mul_div_left 1 (N.to_nat mval) (2 ^ N.to_nat k) hpk),
              (Nat.div_small _ _ hMlt).
            replace (1 + 0) with 1 by lia.
            rewrite hp1, hp2, Str_app_assoc. reflexivity. }
    destruct rs as [| t ts].
    + refine (conj (Nat.le_refl _) (conj hsum eq_refl)).
    + pose proof (hslow (t :: ts)) as hst.
      destruct t as [| | [| pn] | [| pn] | n | n | n | m val];
        try exact hst.
      * cbn [encodeR tokBits zBits repBits Str_app]. exact (ih k mval rval ts hsum).
      * set (n := Npos pn).
        set (mask := N.shiftl (N.ones n) k).
        pose proof (pow2_pos (N.to_nat k)) as hpk.
        pose proof (pow2_pos (N.to_nat n)) as hpn.
        assert (hmask : N.to_nat mask = (2 ^ N.to_nat n - 1) * 2 ^ N.to_nat k)
          by (unfold mask; rewrite N2Nat_shiftl, N2Nat_ones; reflexivity).
        assert (hkn : N.to_nat (k + n)%N = N.to_nat k + N.to_nat n) by lia.
        assert (hpow : 2 ^ N.to_nat (k + n)%N = 2 ^ N.to_nat k * 2 ^ N.to_nat n)
          by (rewrite hkn, Nat.pow_add_r; reflexivity).
        assert (hsum' : N.to_nat mval + N.to_nat (rval + mask)%N + 1 = 2 ^ N.to_nat (k + n)%N)
          by (rewrite N2Nat.inj_add, hmask, hpow; nia).
        specialize (ih (k + n)%N mval (rval + mask)%N ts hsum').
        destruct (extractZOLoop fuel (k + n)%N mval (rval + mask)%N ts) as [k' mval' rval' rs'].
        destruct ih as [hk' [hsum_end hbits_end]].
        assert (hle' : N.to_nat k <= N.to_nat k') by lia.
        refine (conj hle' (conj hsum_end _)).
        rewrite <- hbits_end, hkn, zoBits_add,
          (Nat.div_small (N.to_nat mval) (2 ^ N.to_nat k) ltac:(lia)), zoBits_zeros.
        cbn [encodeR tokBits]; fold n. rewrite Str_app_assoc. reflexivity.
      * cbn [encodeR tokBits oBits repBits Str_app]. exact (ih k mval rval ts hsum).
      * set (n := Npos pn).
        set (mask := N.shiftl (N.ones n) k).
        pose proof (pow2_pos (N.to_nat k)) as hpk.
        pose proof (pow2_pos (N.to_nat n)) as hpn.
        assert (hmask : N.to_nat mask = (2 ^ N.to_nat n - 1) * 2 ^ N.to_nat k)
          by (unfold mask; rewrite N2Nat_shiftl, N2Nat_ones; reflexivity).
        assert (hkn : N.to_nat (k + n)%N = N.to_nat k + N.to_nat n) by lia.
        assert (hpow : 2 ^ N.to_nat (k + n)%N = 2 ^ N.to_nat k * 2 ^ N.to_nat n)
          by (rewrite hkn, Nat.pow_add_r; reflexivity).
        assert (hsum' : N.to_nat (mval + mask)%N + N.to_nat rval + 1 = 2 ^ N.to_nat (k + n)%N)
          by (rewrite N2Nat.inj_add, hmask, hpow; nia).
        specialize (ih (k + n)%N (mval + mask)%N rval ts hsum').
        destruct (extractZOLoop fuel (k + n)%N (mval + mask)%N rval ts) as [k' mval' rval' rs'].
        destruct ih as [hk' [hsum_end hbits_end]].
        assert (hle' : N.to_nat k <= N.to_nat k') by lia.
        refine (conj hle' (conj hsum_end _)).
        rewrite <- hbits_end, hkn, zoBits_add, N2Nat.inj_add, hmask.
        assert (hMlt : N.to_nat mval < 2 ^ N.to_nat k) by lia.
        replace (N.to_nat mval + (2 ^ N.to_nat n - 1) * 2 ^ N.to_nat k)
          with ((2 ^ N.to_nat n - 1) * 2 ^ N.to_nat k + N.to_nat mval) by lia.
        rewrite <- (zoBits_mod (N.to_nat k)
          ((2 ^ N.to_nat n - 1) * 2 ^ N.to_nat k + N.to_nat mval)).
        rewrite (add_mul_mod_left (2 ^ N.to_nat n - 1) (N.to_nat mval) (2 ^ N.to_nat k) hpk),
          (Nat.mod_small _ _ hMlt).
        rewrite (add_mul_div_left (2 ^ N.to_nat n - 1) (N.to_nat mval) (2 ^ N.to_nat k) hpk),
          (Nat.div_small _ _ hMlt).
        replace (2 ^ N.to_nat n - 1 + 0) with (2 ^ N.to_nat n - 1) by lia.
        rewrite zoBits_ones. cbn [encodeR tokBits]; fold n.
        rewrite Str_app_assoc. reflexivity.
Qed.

(* rawStep, finishLeftD, tryR2, tryR1, stepMacro & runStepsPos *)

Definition rawStep (leftBlank : bool) (q : QState) (ls rs : list Tok) : State :=
  match popBitR rs with
  | PBR_bit0 rs' =>
    match q with
    | QA => St_mk QB (pushL tb1 ls) rs'
    | QB =>
      match popBitL leftBlank ls with
      | PBL_bit0 ls' => St_mk QC ls' (tb0 :: tb1 :: rs')
      | PBL_bit1 ls' => St_mk QC ls' (tb1 :: tb1 :: rs')
      | PBL_underflow => St_err
      end
    | QC => St_mk QE (pushL tb1 ls) rs'
    | QD =>
      match popBitL leftBlank ls with
      | PBL_bit0 ls' => St_mk QB ls' (tb0 :: tb0 :: rs')
      | PBL_bit1 ls' => St_mk QB ls' (tb1 :: tb0 :: rs')
      | PBL_underflow => St_err
      end
    | QE => St_mk QA (pushL tb1 ls) rs'
    | QF =>
      match popBitL leftBlank ls with
      | PBL_bit0 ls' => St_mk QD ls' (tb0 :: tb0 :: rs')
      | PBL_bit1 ls' => St_mk QD ls' (tb1 :: tb0 :: rs')
      | PBL_underflow => St_err
      end
    end
  | PBR_bit1 rs' =>
    match q with
    | QA => St_mk QE (pushL tb0 ls) rs'
    | QB => St_mk QA (pushL tb0 ls) rs'
    | QC =>
      match popBitL leftBlank ls with
      | PBL_bit0 ls' => St_mk QD ls' (tb0 :: tb1 :: rs')
      | PBL_bit1 ls' => St_mk QD ls' (tb1 :: tb1 :: rs')
      | PBL_underflow => St_err
      end
    | QD =>
      match popBitL leftBlank ls with
      | PBL_bit0 ls' => St_mk QF ls' (tb0 :: tb0 :: rs')
      | PBL_bit1 ls' => St_mk QF ls' (tb1 :: tb0 :: rs')
      | PBL_underflow => St_err
      end
    | QE => St_mk QA (pushL tb1 ls) rs'
    | QF => St_err
    end
  end.

Lemma rawStep_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (q : QState) (ls rs : list Tok) (s' : State)
    (h : rawStep leftBlank q ls rs = s') (hs' : s' <> St_err) :
  encode restL (St_mk q ls rs) -->+ encode restL s'.
Proof.
  unfold rawStep in h.
  pose proof (popBitR_sound rs) as hpr.
  destruct (popBitR rs) as [rs' | rs'].
  - destruct q.
    + subst s'; cbn [encode qToQ]; rewrite hpr, encodeL_pushL; cbn [tokBits rev Str_app]; start_progress.
    + pose proof (popBitL_sound leftBlank restL hrest ls) as hpl.
      destruct (popBitL leftBlank ls) as [ls' | ls' | ]; [| | subst s'; contradiction].
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
    + subst s'; cbn [encode qToQ]; rewrite hpr, encodeL_pushL; cbn [tokBits rev Str_app]; start_progress.
    + pose proof (popBitL_sound leftBlank restL hrest ls) as hpl.
      destruct (popBitL leftBlank ls) as [ls' | ls' | ]; [| | subst s'; contradiction].
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
    + subst s'; cbn [encode qToQ]; rewrite hpr, encodeL_pushL; cbn [tokBits rev Str_app]; start_progress.
    + pose proof (popBitL_sound leftBlank restL hrest ls) as hpl.
      destruct (popBitL leftBlank ls) as [ls' | ls' | ]; [| | subst s'; contradiction].
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
  - destruct q.
    + subst s'; cbn [encode qToQ]; rewrite hpr, encodeL_pushL; cbn [tokBits rev Str_app]; start_progress.
    + subst s'; cbn [encode qToQ]; rewrite hpr, encodeL_pushL; cbn [tokBits rev Str_app]; start_progress.
    + pose proof (popBitL_sound leftBlank restL hrest ls) as hpl.
      destruct (popBitL leftBlank ls) as [ls' | ls' | ]; [| | subst s'; contradiction].
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
    + pose proof (popBitL_sound leftBlank restL hrest ls) as hpl.
      destruct (popBitL leftBlank ls) as [ls' | ls' | ]; [| | subst s'; contradiction].
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
      * subst s'; cbn [encode qToQ encodeR tokBits Str_app]; rewrite hpr, hpl; start_progress.
    + subst s'; cbn [encode qToQ]; rewrite hpr, encodeL_pushL; cbn [tokBits rev Str_app]; start_progress.
    + subst s'; contradiction.
Qed.

Definition finishLeftD (leftBlank : bool) (ls rs : list Tok) : State :=
  match popBitL leftBlank ls with
  | PBL_bit0 ls' => St_mk QD ls' (tb0 :: rs)
  | PBL_bit1 ls' => St_mk QD ls' (tb1 :: rs)
  | PBL_underflow => St_err
  end.

Lemma finishLeftD_eq (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (ls rs : list Tok) (s' : State)
    (h : finishLeftD leftBlank ls rs = s') (hs' : s' <> St_err) :
  (encodeL restL ls <{{D}} encodeR rs) = encode restL s'.
Proof.
  unfold finishLeftD in h.
  pose proof (popBitL_sound leftBlank restL hrest ls) as hpl.
  destruct (popBitL leftBlank ls) as [ls' | ls' | ]; [| | subst s'; contradiction].
  - subst s'; rewrite hpl; reflexivity.
  - subst s'; rewrite hpl; reflexivity.
Qed.

Definition tryR2 (leftBlank : bool) (ls rs : list Tok) : State :=
  match extractZOLoop 2000 0 0 0 rs with
  | ExtZO_mk k mval rval rtail =>
    match rtail with
    | _ :: _ =>
      if (k =? 0)%N then rawStep leftBlank QA ls rs
      else
        match tryAbsorb rval ls with
        | Abs_err => St_err
        | Abs_absorbed outRev ls' =>
          St_mk QA (pushL (tp k) (revPushTokL outRev ls')) rtail
        | Abs_carried =>
          match extractWFast ls [] with
          | ExtW_err => St_err
          | ExtW_ok ws ls' =>
            match carryWLoop 1 [] ws with
            | Carry_mk capW carRev =>
              if (capW <=? rval)%N then
                let mp := (mval + capW)%N in
                let r1 := revPushR (pushZORev k mp []) rtail in
                let r2 := revPushR carRev r1 in
                finishLeftD leftBlank ls' r2
              else St_err
            end
          end
        end
    | [] =>
      match extractWFast ls [] with
      | ExtW_err => St_err
      | ExtW_ok ws ls' =>
        match carryWLoop 1 [] ws with
        | Carry_mk capW carRev =>
          let bl := N.size capW in
          let ktot := (N.max k bl + 1)%N in
          let mp := (mval + capW)%N in
          if ((mp + 1 <=? N.shiftl 1 ktot)%N && (k <=? ktot)%N) then
            let r1 := revPushR (pushZORevTrim ktot mp []) [] in
            let r2 := revPushR carRev r1 in
            finishLeftD leftBlank ls' r2
          else St_err
        end
      end
    end
  end.

Local Opaque extractZOLoop extractWFast tryAbsorb carryWLoop finishLeftD rawStep
             popBitR popBitL popWTok sweepA0 sweepALoop sweepBELoop.

Lemma tryR2_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (ls rs : list Tok) (s' : State)
    (h : tryR2 leftBlank ls rs = s') (hs' : s' <> St_err) :
  encode restL (St_mk QA ls rs) -->+ encode restL s'.
Proof.
  unfold tryR2 in h.
  pose proof (extractZOLoop_sound 2000 0 0 0 rs eq_refl) as hzo.
  destruct (extractZOLoop 2000 0 0 0 rs) as [k mval rval rtail].
  destruct hzo as [_ [hsum hR_eq]].
  cbn [N.to_nat zoBits Str_app] in hR_eq.
  destruct rtail as [| rt rts].
  - (* rtail = [] *)
    pose proof (extractWFast_sound restL ls [] I) as hew.
    destruct (extractWFast ls []) as [ws ls' | ]; [| subst s'; contradiction].
    destruct hew as [pref [hEq [hvp hL_eq]]].
    rewrite app_nil_r in hEq; subst ws.
    pose proof (carryWLoop_sound pref false 1 [] [] hvp Carries_nil) as hcw.
    destruct (carryWLoop 1 [] pref) as [capW carRev].
    cbn [app] in hcw.
    set (bl := N.size capW) in h.
    set (ktot := (N.max k bl + 1)%N) in h.
    set (mp := (mval + capW)%N) in h.
    destruct ((mp + 1 <=? N.shiftl 1 ktot)%N && (k <=? ktot)%N) eqn:hguard;
      [| subst s'; contradiction].
    apply andb_true_iff in hguard as [hble1 hble2].
    apply N.leb_le in hble1. apply N.leb_le in hble2.
    assert (hble1_nat : N.to_nat (mp + 1)%N <= N.to_nat (N.shiftl 1 ktot)) by lia.
    unfold mp in hble1_nat.
    rewrite !N2Nat.inj_add, (N2Nat_shiftl_1 ktot) in hble1_nat.
    change (N.to_nat 1) with 1 in hble1_nat.
    assert (hlt : N.to_nat mval + N.to_nat capW < 2 ^ N.to_nat ktot) by lia.
    assert (hkle : N.to_nat k <= N.to_nat ktot) by lia.
    assert (hMlt : N.to_nat mval < 2 ^ N.to_nat k) by lia.
    pose proof (zo_carry (N.to_nat ktot) (N.to_nat mval) (N.to_nat capW)
      hcw hlt (encodeL restL ls') 0inf) as hstep.
    pose proof (finishLeftD_eq leftBlank restL hrest ls'
      (revPushR carRev (revPushR (pushZORevTrim ktot mp []) [])) s' h hs') as hfin.
    rewrite <- hfin. cbn [encode qToQ].
    rewrite hR_eq, hL_eq; cbn [encodeR].
    rewrite <- (zoBits_pad_default (N.to_nat k) (N.to_nat ktot) (N.to_nat mval) hMlt hkle).
    rewrite encodeR_revPushR_bits, encodeR_revPushR_trim.
    cbn [revTokBits Str_app]. unfold mp. rewrite N2Nat.inj_add, <- Str_app_assoc.
    exact hstep.
  - (* rtail = rt :: rts *)
    destruct (k =? 0)%N eqn:hk0.
    + exact (rawStep_sound leftBlank restL hrest QA ls rs s' h hs').
    + apply N.eqb_neq in hk0.
      assert (hk1 : 1 <= N.to_nat k) by lia.
      pose proof (tryAbsorb_sound restL rval ls) as habs.
      destruct (tryAbsorb rval ls) as [outRev ls' | | ]; [| | subst s'; contradiction].
      * (* Abs_absorbed *)
        destruct habs as [wOrig [wOut [hL_eq [hout_eq hA]]]].
        subst s'; cbn [encode qToQ].
        rewrite hR_eq, hL_eq, encodeL_pushL, hout_eq.
        assert (hMlt : N.to_nat mval < 2 ^ N.to_nat k) by lia.
        replace (N.to_nat rval) with (2 ^ N.to_nat k - 1 - N.to_nat mval) in hA by lia.
        pose proof (@zo_absorb_plus (N.to_nat k) (N.to_nat mval) hk1 wOrig wOut hMlt hA
          (encodeL restL ls') (encodeR (rt :: rts))) as hstep.
        cbn [tokBits]. rewrite rev_app_distr, Str_app_assoc in hstep.
        exact hstep.
      * (* Abs_carried *)
        pose proof (extractWFast_sound restL ls [] I) as hew.
        destruct (extractWFast ls []) as [ws ls' | ]; [| subst s'; contradiction].
        destruct hew as [pref [hEq [hvp hL_eq]]].
        rewrite app_nil_r in hEq; subst ws.
        pose proof (carryWLoop_sound pref false 1 [] [] hvp Carries_nil) as hcw.
        destruct (carryWLoop 1 [] pref) as [capW carRev].
        cbn [app] in hcw.
        destruct (capW <=? rval)%N eqn:hble; [| subst s'; contradiction].
        apply N.leb_le in hble.
        assert (hlt : N.to_nat mval + N.to_nat capW < 2 ^ N.to_nat k) by lia.
        pose proof (zo_carry (N.to_nat k) (N.to_nat mval) (N.to_nat capW)
          hcw hlt (encodeL restL ls') (encodeR (rt :: rts))) as hstep.
        pose proof (finishLeftD_eq leftBlank restL hrest ls'
          (revPushR carRev (revPushR (pushZORev k (mval + capW)%N []) (rt :: rts)))
          s' h hs') as hfin.
        rewrite <- hfin. cbn [encode qToQ].
        rewrite hR_eq, hL_eq, !encodeR_revPushR_bits, revTokBits_pushZORev.
        cbn [revTokBits app]. rewrite N2Nat.inj_add, <- Str_app_assoc.
        exact hstep.
Qed.

Local Opaque tryR2.

Definition tryR1Carry (leftBlank : bool) (ls1 rs' : list Tok) : State :=
  match tryAbsorb 1 ls1 with
  | Abs_err => St_err
  | Abs_absorbed outRev ls' => St_mk QA (revPushTokL outRev ls') rs'
  | Abs_carried =>
    match extractWFast ls1 [] with
    | ExtW_err => St_err
    | ExtW_ok ws ls' =>
      match carryWLoop 1 [] ws with
      | Carry_mk capW carRev =>
        if (capW =? 1)%N then
          match ws with
          | [] => St_err
          | _ :: _ => finishLeftD leftBlank ls' (revPushR carRev rs')
          end
        else St_err
      end
    end
  end.

Lemma tryR1Carry_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (ls1 rs' : list Tok) (s' : State)
    (h : tryR1Carry leftBlank ls1 rs' = s') (hs' : s' <> St_err) :
  (encodeL restL ls1 <{{D}} encodeR rs') -->+ encode restL s'.
Proof.
  unfold tryR1Carry in h.
  pose proof (tryAbsorb_sound restL 1 ls1) as habs.
  destruct (tryAbsorb 1 ls1) as [outRev ls' | | ]; [| | subst s'; contradiction].
  - destruct habs as [wOrig [wOut [hL_eq [hout_eq hA]]]].
    subst s'. cbn [N.to_nat Pos.to_nat Absorbs] in hA.
    destruct hA as [w1 [hstep <-]].
    cbn [encode qToQ]. rewrite hL_eq, hout_eq.
    exact (hstep (encodeL restL ls') (encodeR rs')).
  - pose proof (extractWFast_sound restL ls1 [] I) as hew.
    destruct (extractWFast ls1 []) as [ws ls' | ]; [| subst s'; contradiction].
    destruct hew as [pref [hEq [hvp hL_eq]]].
    rewrite app_nil_r in hEq; subst ws.
    pose proof (carryWLoop_sound pref false 1 [] [] hvp Carries_nil) as hcw.
    destruct (carryWLoop 1 [] pref) as [capW carRev].
    cbn [app] in hcw.
    destruct (capW =? 1)%N eqn:hcap; [| subst s'; contradiction].
    apply N.eqb_eq in hcap; subst capW.
    destruct pref as [| w0 ws]; [subst s'; contradiction |].
    cbn [orb N.to_nat Pos.to_nat Carries] in hcw.
    pose proof (hcw (encodeL restL ls') (encodeR rs')) as hstep.
    pose proof (finishLeftD_eq leftBlank restL hrest ls' (revPushR carRev rs') s' h hs') as hfin.
    rewrite hL_eq, <- hfin, encodeR_revPushR_bits.
    exact hstep.
Qed.

Local Opaque tryR1Carry.

Definition tryR1 (leftBlank : bool) (ls rs : list Tok) : State :=
  match popBitR rs with
  | PBR_bit0 rs' =>
    let ls1 := tb0 :: ls in
    match popWTok ls1 with
    | PW_none => rawStep leftBlank QD ls rs
    | _ => tryR1Carry leftBlank ls1 rs'
    end
  | PBR_bit1 rs' =>
    let ls1 := tb1 :: ls in
    match popWTok ls1 with
    | PW_none => rawStep leftBlank QD ls rs
    | _ => tryR1Carry leftBlank ls1 rs'
    end
  end.

Lemma tryR1_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (ls rs : list Tok) (s' : State)
    (h : tryR1 leftBlank ls rs = s') (hs' : s' <> St_err) :
  encode restL (St_mk QD ls rs) -->+ encode restL s'.
Proof.
  unfold tryR1 in h.
  pose proof (popBitR_sound rs) as hpr.
  destruct (popBitR rs) as [rs' | rs'].
  - destruct (popWTok (tb0 :: ls)).
    + exact (rawStep_sound leftBlank restL hrest QD ls rs s' h hs').
    + pose proof (tryR1Carry_sound leftBlank restL hrest (tb0 :: ls) rs' s' h hs') as hs.
      cbn [encode qToQ]; rewrite hpr; exact hs.
    + pose proof (tryR1Carry_sound leftBlank restL hrest (tb0 :: ls) rs' s' h hs') as hs.
      cbn [encode qToQ]; rewrite hpr; exact hs.
  - destruct (popWTok (tb1 :: ls)).
    + exact (rawStep_sound leftBlank restL hrest QD ls rs s' h hs').
    + pose proof (tryR1Carry_sound leftBlank restL hrest (tb1 :: ls) rs' s' h hs') as hs.
      cbn [encode qToQ]; rewrite hpr; exact hs.
    + pose proof (tryR1Carry_sound leftBlank restL hrest (tb1 :: ls) rs' s' h hs') as hs.
      cbn [encode qToQ]; rewrite hpr; exact hs.
Qed.

Definition startsWith00 (rs : list Tok) : bool :=
  match rs with
  | [] => true
  | tz (Npos _) :: _ => true
  | tb0 :: [] => true
  | tb0 :: tb0 :: _ => true
  | tb0 :: tz (Npos _) :: _ => true
  | tb0 :: tp (Npos _) :: _ => true
  | _ => false
  end.

Local Opaque tryR1.

Definition stepAFallback (leftBlank : bool) (ls rs : list Tok) : State :=
  if startsWith00 rs then
    match popWTok ls with
    | PW_none => rawStep leftBlank QA ls rs
    | _ => tryR2 leftBlank ls rs
    end
  else rawStep leftBlank QA ls rs.

Lemma stepAFallback_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (ls rs : list Tok) (s' : State)
    (h : stepAFallback leftBlank ls rs = s') (hs' : s' <> St_err) :
  encode restL (St_mk QA ls rs) -->+ encode restL s'.
Proof.
  unfold stepAFallback in h.
  destruct (startsWith00 rs); [| exact (rawStep_sound leftBlank restL hrest QA ls rs s' h hs')].
  destruct (popWTok ls);
    [exact (rawStep_sound leftBlank restL hrest QA ls rs s' h hs')
    | exact (tryR2_sound leftBlank restL hrest ls rs s' h hs')
    | exact (tryR2_sound leftBlank restL hrest ls rs s' h hs')].
Qed.

Local Opaque stepAFallback.

Definition stepMacro (leftBlank : bool) (s : State) : State :=
  match s with
  | St_err => St_err
  | St_mk QA ls (tc (Npos pn) :: ts) => sweepALoop (pushL (tdb (Npos pn) 0) ls) ts
  | St_mk QA ls (to_ (Npos pn) :: ts) => sweepALoop (pushL (tp (Npos pn)) ls) ts
  | St_mk QA ls (tt10 (Npos pn) :: ts) => sweepALoop (pushL (tp (Npos pn)) ls) ts
  | St_mk QA ls (tp (Npos pn) :: ts) => sweepALoop (pushL (tt10 (Npos pn)) ls) ts
  | St_mk QA ls (tb0 :: tc (Npos pn) :: ts) =>
    let n := Pos.pred_N pn in
    sweepA0 (pushL (tp 1) (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: tb1 :: ls))) ts
  | St_mk QA ls rs => stepAFallback leftBlank ls rs
  | St_mk QB ls (tc (Npos pn) :: ts) =>
    let n := Pos.pred_N pn in
    sweepBELoop false Buf_011 (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: ls)) ts
  | St_mk QB ls (to_ (Npos pn) :: ts) =>
    let n := Pos.pred_N pn in
    sweepBELoop true Buf_none (pushL (tt10 n) (pushL (tz 1) ls)) ts
  | St_mk QB ls (tt10 (Npos pn) :: ts) => St_mk QB (pushL (tp (Npos pn)) ls) ts
  | St_mk QE ls (tc (Npos pn) :: ts) =>
    let n := Pos.pred_N pn in
    sweepBELoop false Buf_011 (pushL (tdb n 0) (tb1 :: tb0 :: tb1 :: ls)) ts
  | St_mk QE ls (to_ (Npos pn) :: ts) =>
    sweepBELoop true Buf_none (pushL (tt10 (Npos pn)) ls) ts
  | St_mk QE ls (tp (Npos pn) :: ts) => St_mk QE (pushL (tt10 (Npos pn)) ls) ts
  | St_mk QD ls rs => tryR1 leftBlank ls rs
  | St_mk q ls rs => rawStep leftBlank q ls rs
  end.

Lemma stepMacro_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf)
    (s s' : State) (h : stepMacro leftBlank s = s') (hs' : s' <> St_err) :
  encode restL s -->+ encode restL s'.
Proof.
  destruct s as [q ls rs | ]; [| cbn [stepMacro] in h; subst s'; contradiction].
  destruct q.
  - (* QA *)
    destruct rs as [| t ts];
      [exact (stepAFallback_sound leftBlank restL hrest ls [] s' h hs') |].
    destruct t as [| | n | [| pn] | [| pn] | [| pn] | [| pn] | m val];
      try (apply (stepAFallback_sound leftBlank restL hrest); assumption).
    + destruct ts as [| t2 ts2];
        [exact (stepAFallback_sound leftBlank restL hrest ls [tb0] s' h hs') |].
      destruct t2 as [| | n2 | n2 | n2 | n2 | [| pn2] | m2 val2];
        try (apply (stepAFallback_sound leftBlank restL hrest); assumption).
      cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits Str_app].
      set (n2 := Pos.pred_N pn2).
      pose proof (sweep_A_0c_plus (n := N.to_nat (Npos pn2)) ltac:(lia)
        (encodeL restL ls) (encodeR ts2)) as h1.
      replace (N.to_nat (Npos pn2) - 1) with (N.to_nat n2) in h1 by (unfold n2; lia).
      assert (hL :
        encodeL restL (pushL (tp 1) (pushL (tdb n2 0) (tb1 :: tb0 :: tb0 :: tb1 :: ls))) =
        rev ([S1; S0; S0; S1] ++ dBlockBits (N.to_nat n2) 0 ++ [S0; S1]) *> encodeL restL ls).
      { rewrite !encodeL_pushL. cbn [encodeL tokBits pBits repBits].
        rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
      rewrite <- hL in h1.
      exact (ps_trans h1 (sweepA0_sound restL ts2 _)).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_A_o_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      pose proof (encodeL_pushL restL (tp (Npos pn)) ls) as hL.
      cbn [tokBits] in hL; rewrite <- hL in h1.
      exact (ps_trans h1 (sweepALoop_sound restL ts _)).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_A_p_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      pose proof (encodeL_pushL restL (tt10 (Npos pn)) ls) as hL.
      cbn [tokBits] in hL; rewrite <- hL in h1.
      exact (ps_trans h1 (sweepALoop_sound restL ts _)).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_A_t10_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      pose proof (encodeL_pushL restL (tp (Npos pn)) ls) as hL.
      cbn [tokBits] in hL; rewrite <- hL in h1.
      exact (ps_trans h1 (sweepALoop_sound restL ts _)).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_A_c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      pose proof (encodeL_pushL restL (tdb (Npos pn) 0) ls) as hL.
      cbn [tokBits] in hL; change (N.to_nat 0) with 0 in hL; rewrite <- hL in h1.
      exact (ps_trans h1 (sweepALoop_sound restL ts _)).
  - (* QB *)
    destruct rs as [| t ts];
      [exact (rawStep_sound leftBlank restL hrest QB ls [] s' h hs') |].
    destruct t as [| | n | [| pn] | n | [| pn] | [| pn] | m val];
      try (apply (rawStep_sound leftBlank restL hrest); assumption).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      set (n := Pos.pred_N pn).
      pose proof (sweep_B_o_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
      assert (hL :
        rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 n) (pushL (tz 1) ls)) =
        rev ([S0; S0] ++ t10Bits (N.to_nat n)) *> encodeL restL ls).
      { rewrite !encodeL_pushL. cbn [bufBits tokBits zBits repBits].
        rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
      rewrite <- hL in h1.
      exact (ps_trans h1 (sweepBELoop_sound restL ts true Buf_none _)).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_B_t10_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      pose proof (encodeL_pushL restL (tp (Npos pn)) ls) as hL.
      cbn [tokBits] in hL; rewrite <- hL in h1. exact h1.
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      set (n := Pos.pred_N pn).
      pose proof (sweep_B_c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
      assert (hL :
        rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb0 :: ls)) =
        rev ([S0; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> encodeL restL ls).
      { rewrite encodeL_pushL. cbn [bufBits encodeL tokBits].
        rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
      rewrite <- hL in h1.
      exact (ps_trans h1 (sweepBELoop_sound restL ts false Buf_011 _)).
  - (* QC *)
    exact (rawStep_sound leftBlank restL hrest QC ls rs s' h hs').
  - (* QD *)
    exact (tryR1_sound leftBlank restL hrest ls rs s' h hs').
  - (* QE *)
    destruct rs as [| t ts];
      [exact (rawStep_sound leftBlank restL hrest QE ls [] s' h hs') |].
    destruct t as [| | n | [| pn] | [| pn] | n | [| pn] | m val];
      try (apply (rawStep_sound leftBlank restL hrest); assumption).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_E_o_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      assert (hL :
        rev (bufBits Buf_none) *> encodeL restL (pushL (tt10 (Npos pn)) ls) =
        rev (t10Bits (N.to_nat (Npos pn))) *> encodeL restL ls).
      { rewrite encodeL_pushL. reflexivity. }
      rewrite <- hL in h1.
      exact (ps_trans h1 (sweepBELoop_sound restL ts true Buf_none _)).
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      pose proof (sweep_E_p_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      pose proof (encodeL_pushL restL (tt10 (Npos pn)) ls) as hL.
      cbn [tokBits] in hL; rewrite <- hL in h1. exact h1.
    + cbn [stepMacro] in h; subst s'. cbn [encode qToQ encodeR tokBits].
      set (n := Pos.pred_N pn).
      pose proof (sweep_E_c_plus (n := N.to_nat (Npos pn)) ltac:(lia)
        (encodeL restL ls) (encodeR ts)) as h1.
      replace (N.to_nat (Npos pn) - 1) with (N.to_nat n) in h1 by (unfold n; lia).
      assert (hL :
        rev (bufBits Buf_011) *> encodeL restL (pushL (tdb n 0) (tb1 :: tb0 :: tb1 :: ls)) =
        rev ([S1; S0; S1] ++ dBlockBits (N.to_nat n) 0 ++ [S0; S1; S1]) *> encodeL restL ls).
      { rewrite encodeL_pushL. cbn [bufBits encodeL tokBits].
        rewrite !rev_app_distr, !Str_app_assoc. reflexivity. }
      rewrite <- hL in h1.
      exact (ps_trans h1 (sweepBELoop_sound restL ts false Buf_011 _)).
  - (* QF *)
    exact (rawStep_sound leftBlank restL hrest QF ls rs s' h hs').
Qed.

Definition runStepsPos (leftBlank : bool) (p : positive) (s : State) : State :=
  Pos.iter (stepMacro leftBlank) s p.

Lemma iter_stepMacro_err (leftBlank : bool) :
  forall p : positive, Pos.iter (stepMacro leftBlank) St_err p = St_err.
Proof.
  induction p as [p ih | p ih | ]; cbn [Pos.iter]; try rewrite !ih; reflexivity.
Qed.

Lemma runStepsPos_sound (leftBlank : bool) (restL : Stream sym)
    (hrest : leftBlank = true -> restL = 0inf) :
  forall (p : positive) (s s' : State),
    runStepsPos leftBlank p s = s' -> s' <> St_err ->
    encode restL s -->+ encode restL s'.
Proof.
  unfold runStepsPos.
  induction p as [p ih | p ih | ]; intros s s' h hs'; cbn [Pos.iter] in h.
  - set (s1 := Pos.iter (stepMacro leftBlank) s p) in h.
    set (s2 := Pos.iter (stepMacro leftBlank) s1 p) in h.
    assert (hs2 : s2 <> St_err)
      by (intros he; rewrite he in h; cbn [stepMacro] in h; subst s'; exact (hs' eq_refl)).
    assert (hs1 : s1 <> St_err)
      by (intros he; unfold s2 in hs2; rewrite he, iter_stepMacro_err in hs2; exact (hs2 eq_refl)).
    pose proof (ih s s1 eq_refl hs1) as hp1.
    pose proof (ih s1 s2 eq_refl hs2) as hp2.
    pose proof (stepMacro_sound leftBlank restL hrest s2 s' h hs') as hp3.
    exact (ptrans (ptrans hp1 hp2) hp3).
  - set (s1 := Pos.iter (stepMacro leftBlank) s p) in h.
    assert (hs1 : s1 <> St_err)
      by (intros he; rewrite he, iter_stepMacro_err in h; subst s'; exact (hs' eq_refl)).
    pose proof (ih s s1 eq_refl hs1) as hp1.
    pose proof (ih s1 s' h hs') as hp2.
    exact (ptrans hp1 hp2).
  - exact (stepMacro_sound leftBlank restL hrest s s' h hs').
Qed.

Local Opaque stepMacro runStepsPos.

(* ========================================================================== *)
(* Section 7: Window Certificates & Top-Level Non-Halting Theorem             *)
(* ========================================================================== *)

Definition cycTopL : list Tok :=
  [tb1; tp 2; tdb 1 2; tb0; tb1; tp 1; tdb 1 0; tb1; tb0; tb0;
   tb1; tb0; tb0; tb1; tb0; tb1; tb0; tb1; tt10 1; tb0;
   tb0; tb1; tp 3; tdb 5 6; tb1; tb0; tb0; tb1; tb0; tb0;
   tb0; tb1; tb1; tb0; tb1; tb0; tb0; tb1; tb0; tb0].

Definition cycR : list Tok := [tb0; tc 1; tz 2; to_ 1].

Definition cycStart : State := St_mk QD cycTopL cycR.

Definition checkWindow (s : State) : bool :=
  match s with
  | St_mk QD ls rs => beqTokList rs cycR && beqTokList (firstn 40 ls) cycTopL
  | _ => false
  end.

Lemma checkWindow_sound (restL : Stream sym) (s : State) (h : checkWindow s = true) :
  s <> St_err /\ exists restL' : Stream sym, encode restL s = encode restL' cycStart.
Proof.
  destruct s as [[| | | | | ] ls rs | ]; cbn [checkWindow] in h; try discriminate.
  apply andb_true_iff in h as [hrs hls].
  apply beqTokList_eq in hrs.
  apply beqTokList_eq in hls.
  refine (conj _ _); [discriminate |].
  exists (encodeL restL (skipn 40 ls)).
  subst rs. cbn [encode cycStart].
  rewrite <- (firstn_skipn 40 ls) at 1.
  rewrite hls, encodeL_append. reflexivity.
Qed.

Definition checkEntry : bool :=
  checkWindow (runStepsPos true 84472%positive (St_mk QA [] [])).

Definition checkCyc : bool :=
  checkWindow (runStepsPos false 6419%positive cycStart).

Lemma entry_cert : checkEntry = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cyc_cert : checkCyc = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma init_reaches_cyc : exists restL0 : Stream sym, c0 -->* encode restL0 cycStart.
Proof.
  destruct (checkWindow_sound 0inf _ entry_cert) as [hne [restL0 heq]].
  exists restL0.
  change c0 with (encode 0inf (St_mk QA [] [])).
  rewrite <- heq.
  apply p_to_s.
  exact (runStepsPos_sound true 0inf (fun _ => eq_refl) 84472%positive (St_mk QA [] []) _ eq_refl hne).
Qed.

Lemma cyc_progress (restL : Stream sym) :
  exists restL' : Stream sym, encode restL cycStart -->+ encode restL' cycStart.
Proof.
  destruct (checkWindow_sound restL _ cyc_cert) as [hne [restL' heq]].
  exists restL'.
  rewrite <- heq.
  exact (runStepsPos_sound false restL (fun h : false = true => False_ind _ (diff_false_true h))
    6419%positive cycStart _ eq_refl hne).
Qed.

Definition InCyc (cfg : Q * tape) : Prop :=
  exists restL : Stream sym, cfg = encode restL cycStart.

Lemma cyc_closed : forall cfg, InCyc cfg -> exists cfg', InCyc cfg' /\ cfg -->+ cfg'.
Proof.
  intros _ [restL ->].
  destruct (cyc_progress restL) as [restL' hstep].
  exists (encode restL' cycStart).
  exact (conj (ex_intro _ restL' eq_refl) hstep).
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  destruct init_reaches_cyc as [restL0 hinit].
  eapply multistep_nonhalt; [exact hinit |].
  eapply (progress_nonhalt tm InCyc); [exact cyc_closed |].
  exact (ex_intro _ restL0 eq_refl).
Qed.
