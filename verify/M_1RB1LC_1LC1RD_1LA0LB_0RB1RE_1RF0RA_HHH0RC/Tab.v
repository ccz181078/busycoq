(** The 12-digit table of Check.v: what the formal run of a chunk of digits does (chunk_inv, for all lists), and
    that the table holds it (TP_spec, checked entry by entry). *)
From Coq Require Import ZArith Lia List Uint63 PArray Bool.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check Block.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).

(** The accumulators along the digits: (q, ds, a mod 2, s mod 2). *)
Definition tz (x : Z * Z * Z * Z) (g : bool) : Z * Z * Z * Z :=
  let '(q, ds, ap, sp) := x in
  if g then (2 * q + (if ap =? 1 then -3 else -5) - ds, ds + 3, ap, 1 - sp)
  else (2 * q + 2 + ds, ds + 4, (sp + 1) mod 2, sp).
Definition zfold (L : list bool) (ap sp : Z) := fold_left tz L (0, 0, ap, sp).
Definition dval (L : list bool) : Z := fold_left (fun v (g : bool) => 2 * v + (if g then 1 else 0)) L 0.

Lemma chunk_inv L : forall a b,
  let '(A, B) := drun L (a, b) in
  let '(q, ds, ap, sp) := zfold L (a mod 2) ((a + b) mod 2) in
  B - A = 2 ^ Z.of_nat (List.length L) * (b - a) - (a + b) * (2 * dval L - 2 ^ Z.of_nat (List.length L) + 1) + q /\
  A + B = a + b + ds /\ A mod 2 = ap /\ (A + B) mod 2 = sp.
Proof.
  induction L as [|g L IH] using rev_ind; intros a b.
  - cbn [drun zfold dval fold_left List.length Z.of_nat]. rewrite Z.pow_0_r. lia.
  - specialize (IH a b). unfold zfold, dval in *. rewrite drun_app, !fold_left_app, List.app_length.
    cbn [drun fold_left List.length]. rewrite Nat.add_1_r, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct (drun L (a, b)) as [A B].
    destruct (fold_left tz L (0, 0, a mod 2, (a + b) mod 2)) as [[[q ds] ap] sp].
    set (v := fold_left _ L 0) in *. set (P := 2 ^ Z.of_nat (List.length L)) in *.
    destruct IH as (I1 & I2 & I3 & I4).
    unfold tz, dstep. destruct g.
    + destruct (Z.even A) eqn:E.
      * apply Z.even_spec in E as [k Hk]. destruct (Z.eqb_spec ap 1). { clear -I3 Hk e; lia. } (split; [clear I3 I4; nia|split; [clear I1 I3 I4; lia|split; clear I1; lia]]).
      * assert (O : Z.odd A = true) by (rewrite <- Z.negb_even, E; reflexivity).
        apply Z.odd_spec in O as [k Hk]. destruct (Z.eqb_spec ap 1) as [e|e]; [|clear -I3 Hk e; lia]. (split; [clear I3 I4; nia|split; [clear I1 I3 I4; lia|split; clear I1; lia]]).
    + (split; [clear I3 I4; nia|split; [clear I1 I3 I4; lia|split; clear I1; lia]]).
Qed.

(** The digits of a 12-bit chunk, most significant first. *)
Definition bits12 (bt : Z) : list bool := map (fun i => Z.testbit bt (11 - Z.of_nat i)) (seq 0 12).

Definition ent_ok (k : Z) : bool :=
  let st := k / 4096 in let bt := k mod 4096 in
  let '(q, ds, ap, sp) := zfold (bits12 bt) (st mod 2) (st / 2) in
  let v := TP.[of_Z k] in
  (φ (v land 3) =? ap + 2 * sp) && (φ ((v >> 2) land 63) =? ds) &&
  (φ ((v >> 8) - (1 << 30))%uint63 =? q mod wB) &&
  (- 2 ^ 20 <? q) && (q <? 2 ^ 20) && (0 <=? ds) && (ds <=? 48) && (dval (bits12 bt) =? bt).

Fixpoint all_ok (n : nat) : bool := match n with O => true | S n => ent_ok (Z.of_nat n) && all_ok n end.

Lemma all_ok_true : all_ok 16384 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_ok_spec n : all_ok n = true -> forall k, 0 <= k < Z.of_nat n -> ent_ok k = true.
Proof.
  induction n as [|n IH]; intros H k Hk; [lia|]. cbn [all_ok] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec k (Z.of_nat n)) as [->|]; [exact H1|]. apply IH; [exact H2|lia].
Qed.

Lemma TP_spec k : 0 <= k < 16384 -> ent_ok k = true.
Proof.
  intros. apply (all_ok_spec 16384 all_ok_true).
  assert (E : Z.of_nat 16384 = 16384) by (vm_compute; reflexivity). lia.
Qed.

Lemma bits12_length bt : List.length (bits12 bt) = 12%nat.
Proof. reflexivity. Qed.
