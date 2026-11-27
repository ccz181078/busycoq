(** Shared counter-wall invariant for PRs 115–119.
    Two machines use a four-mode transducer; three use a six-mode
    transducer that is related to the same [BigF]/[BigD1] rules. *)

From Coq Require Import Bool List Lists.Streams PeanoNat Compare_dec Lia String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Set Default Goal Selector "!".

Module CounterWall.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

(* ========================================================================== *)
(* Arithmetic Tactic for Division and Modulo by 3                             *)
(* ========================================================================== *)

Definition Dm3Seen (x : nat) : Prop := True.

Lemma div_mod_3_spec (x : nat) :
  Dm3Seen x /\ x = 3 * (x / 3) + x mod 3 /\ x mod 3 < 3.
Proof.
  refine (conj I (conj (Nat.div_mod x 3 _) (Nat.mod_upper_bound x 3 _))); lia.
Qed.

Ltac pose_dm3 x :=
  lazymatch goal with
  | _: Dm3Seen x |- _ => fail
  | _ =>
    let Hseen := fresh "Hdm_seen" in
    let Heq := fresh "Hdm_eq" in
    let Hlt := fresh "Hdm_lt" in
    destruct (div_mod_3_spec x) as [Hseen [Heq Hlt]]
  end.

Ltac scan_dm3 :=
  repeat match goal with
  | |- context [?x / 3] => pose_dm3 x
  | |- context [?x mod 3] => pose_dm3 x
  | H : context [?x / 3] |- _ => pose_dm3 x
  | H : context [?x mod 3] |- _ => pose_dm3 x
  end.

Ltac dlia := scan_dm3; lia.

(* ========================================================================== *)
(* Stack Configurations and Macro-Step Transition                             *)
(* ========================================================================== *)

Definition Seg : Type := (nat * bool)%type.

Inductive Mode581 : Type :=
  | FR0
  | BL0
  | DR0
  | DL0.

Record Cfg581 : Type := mkCfg581 {
  cfg_mode : Mode581;
  cfg_L : list nat;
  cfg_R : list Seg
}.

Definition bumpL (ls : list nat) : list nat :=
  match ls with
  | [] => [0]
  | a :: ls' => S a :: ls'
  end.

Definition bumpR (rs : list Seg) : list Seg :=
  match rs with
  | [] => [(0, false)]
  | (d, b) :: rs' => (S d, b) :: rs'
  end.

Fixpoint ones (n : nat) : list Seg :=
  match n with
  | 0 => []
  | S n' => (1, false) :: ones n'
  end.

Lemma bumpR_nonempty (rs : list Seg) : bumpR rs <> [].
Proof.
  destruct rs as [| [d b] xs]; discriminate.
Qed.

Lemma append_nonempty_of_right {X : Type} (l1 l2 : list X) (h : l2 <> []) :
  l1 ++ l2 <> [].
Proof.
  destruct l1 as [| x xs].
  - exact h.
  - discriminate.
Qed.

Definition step581 (c : Cfg581) : option Cfg581 :=
  match cfg_mode c, cfg_L c, cfg_R c with
  | FR0, ls, [] => Some (mkCfg581 BL0 ls [(0, false)])
  | FR0, ls, (0, false) :: rs => Some (mkCfg581 BL0 ls (bumpR (bumpR rs)))
  | FR0, ls, (0, true) :: rs => Some (mkCfg581 BL0 ls ((1, false) :: rs))
  | FR0, ls, (1, false) :: rs => Some (mkCfg581 FR0 (1 :: ls) rs)
  | FR0, ls, (1, true) :: rs => Some (mkCfg581 BL0 (1 :: ls) (bumpR rs))
  | FR0, ls, (2, b) :: rs => Some (mkCfg581 DR0 (0 :: ls) ((0, b) :: rs))
  | FR0, ls, (S (S (S d)), b) :: rs => Some (mkCfg581 DL0 (1 :: ls) ((d, b) :: rs))
  | BL0, [], _ => None
  | BL0, 0 :: ls', rs => Some (mkCfg581 DL0 (bumpL (bumpL ls')) rs)
  | BL0, 1 :: ls', rs => Some (mkCfg581 BL0 ls' ((0, true) :: rs))
  | BL0, 2 :: [], _ => None
  | BL0, 2 :: a' :: ls', rs => Some (mkCfg581 DL0 (S a' :: ls') ((1, false) :: rs))
  | BL0, S (S (S a)) :: ls', rs => Some (mkCfg581 FR0 (a :: ls') ((0, true) :: rs))
  | DR0, ls, [] => Some (mkCfg581 FR0 (bumpL ls) [])
  | DR0, ls, (0, false) :: rs => Some (mkCfg581 FR0 ls (bumpR (bumpR rs)))
  | DR0, ls, (0, true) :: rs => Some (mkCfg581 FR0 ls ((1, false) :: rs))
  | DR0, ls, (1, false) :: rs => Some (mkCfg581 FR0 (bumpL (bumpL (bumpL ls))) rs)
  | DR0, ls, (1, true) :: rs => Some (mkCfg581 BL0 (bumpL (bumpL (bumpL ls))) (bumpR rs))
  | DR0, ls, (2, b) :: rs => Some (mkCfg581 DR0 (bumpL (bumpL ls)) ((0, b) :: rs))
  | DR0, ls, (S (S (S d)), b) :: rs => Some (mkCfg581 DL0 (bumpL (bumpL (bumpL ls))) ((d, b) :: rs))
  | DL0, [], rs => Some (mkCfg581 FR0 [0] rs)
  | DL0, 0 :: [], [] => None
  | DL0, 0 :: a' :: ls', [] => Some (mkCfg581 DL0 (S a' :: ls') [(0, true); (0, false)])
  | DL0, S a :: ls', [] => Some (mkCfg581 FR0 (a :: ls') [(1, false)])
  | DL0, a :: ls', (0, false) :: rs => Some (mkCfg581 FR0 (S (S a) :: ls') rs)
  | DL0, a :: ls', (0, true) :: rs => Some (mkCfg581 BL0 (S (S a) :: ls') (bumpR rs))
  | DL0, a :: ls', (1, b) :: rs => Some (mkCfg581 DR0 (S a :: ls') ((0, b) :: rs))
  | DL0, a :: ls', (S (S d), b) :: rs => Some (mkCfg581 DL0 (S (S a) :: ls') ((d, b) :: rs))
  end.

Fixpoint run581 (n : nat) (c : Cfg581) : option Cfg581 :=
  match n with
  | 0 => Some c
  | S n' =>
    match step581 c with
    | None => None
    | Some c' => run581 n' c'
    end
  end.

Lemma run581_add (m n : nat) (c c' : Cfg581) (h : run581 m c = Some c') :
  run581 (m + n) c = run581 n c'.
Proof.
  revert c h.
  induction m as [| k ih]; intros c h.
  - cbn in h. inversion h; subst. reflexivity.
  - cbn in h |- *.
    destruct (step581 c) as [c1 |] eqn:hs; [| discriminate h].
    exact (ih c1 h).
Qed.

Lemma halts_after_run {m n : nat} {c c' : Cfg581}
    (hrun : run581 m c = Some c') (hhalt : run581 n c = None) :
  m <= n /\ run581 (n - m) c' = None.
Proof.
  revert n c hrun hhalt.
  induction m as [| k ih]; intros n c hrun hhalt.
  - cbn in hrun. inversion hrun; subst.
    rewrite Nat.sub_0_r. exact (conj (Nat.le_0_l n) hhalt).
  - destruct n as [| n']; [discriminate hhalt |].
    cbn in hrun, hhalt.
    destruct (step581 c) as [c1 |] eqn:hs; [| discriminate hrun].
    destruct (ih n' c1 hrun hhalt) as [hle hrem].
    split; [lia | exact hrem].
Qed.

Lemma halts_after_step {n : nat} {c c' : Cfg581}
    (hhalt : run581 n c = None) (hs : step581 c = Some c') :
  1 <= n /\ run581 (n - 1) c' = None.
Proof.
  apply (@halts_after_run 1 n c c'); [| exact hhalt].
  cbn. rewrite hs. reflexivity.
Qed.

(* ========================================================================== *)
(* Exact Wall Reflections and (+3q) Shift Reduction                           *)
(* ========================================================================== *)

Lemma wall_9 (rs : list Seg) :
  run581 9 (mkCfg581 BL0 [1; 3; 2] rs) = Some (mkCfg581 FR0 [1; 0; 5] rs).
Proof. reflexivity. Qed.

Lemma wall_15 (rs : list Seg) :
  run581 15 (mkCfg581 BL0 [1; 0; 5] rs) = Some (mkCfg581 FR0 [1; 3; 2] (bumpR rs)).
Proof. reflexivity. Qed.

Lemma wall_27 (tail : list Seg) :
  run581 27 (mkCfg581 BL0 [1; 3; 2] ((0, true) :: tail)) =
    Some (mkCfg581 FR0 [0; 1; 3; 2] (bumpR (bumpR tail))).
Proof.
  pose proof (wall_9 ((0, true) :: tail)) as h1.
  assert (h10 : run581 10 (mkCfg581 BL0 [1; 3; 2] ((0, true) :: tail)) =
    Some (mkCfg581 BL0 [1; 0; 5] ((1, false) :: tail))).
  { change 10 with (9 + 1). rewrite (run581_add 9 1 _ _ h1). reflexivity. }
  assert (h25 : run581 25 (mkCfg581 BL0 [1; 3; 2] ((0, true) :: tail)) =
    Some (mkCfg581 FR0 [1; 3; 2] ((2, false) :: tail))).
  { change 25 with (10 + 15). rewrite (run581_add 10 15 _ _ h10).
    exact (wall_15 ((1, false) :: tail)). }
  change 27 with (25 + 2). rewrite (run581_add 25 2 _ _ h25). reflexivity.
Qed.

Lemma bl0_shift_3 (a : nat) (ls : list nat) (rs : list Seg) :
  run581 2 (mkCfg581 BL0 (S (S (S a)) :: ls) rs) =
    Some (mkCfg581 BL0 (a :: ls) ((1, false) :: rs)).
Proof. reflexivity. Qed.

Lemma ones_snoc (k : nat) (rs : list Seg) :
  ones k ++ (1, false) :: rs = ones (S k) ++ rs.
Proof.
  induction k as [| j ih]; [reflexivity |].
  cbn. rewrite ih. reflexivity.
Qed.

Lemma bl0_shift_3q (q rem : nat) (ls : list nat) (rs : list Seg) :
  run581 (2 * q) (mkCfg581 BL0 ((3 * q + rem) :: ls) rs) =
    Some (mkCfg581 BL0 (rem :: ls) (ones q ++ rs)).
Proof.
  revert rs.
  induction q as [| k ih]; intro rs; [reflexivity |].
  replace (3 * S k + rem) with (S (S (S (3 * k + rem)))) by lia.
  replace (2 * S k) with (2 + 2 * k) by lia.
  rewrite (run581_add 2 (2 * k) _ _ (bl0_shift_3 (3 * k + rem) ls rs)).
  rewrite (ih ((1, false) :: rs)).
  rewrite ones_snoc. reflexivity.
Qed.

(* ========================================================================== *)
(* Depth-Indexed Mutual Big-Step System (BigF, BigD1)                         *)
(* ========================================================================== *)

Inductive BigF : nat -> list Seg -> nat -> list Seg -> Prop :=
  | BF_nil : BigF 0 [] 0 [(0, false)]
  | BF_zeroF (Y : list Seg) : BigF 0 ((0, false) :: Y) 0 (bumpR (bumpR Y))
  | BF_zeroT (Y : list Seg) : BigF 0 ((0, true) :: Y) 0 ((1, false) :: Y)
  | BF_oneT (Y : list Seg) : BigF 0 ((1, true) :: Y) 0 ((0, true) :: bumpR Y)
  | BF_oneF_rem1 {k1 : nat} {Y R1 : list Seg} {dlt1 : nat} :
      BigF k1 Y dlt1 R1 -> (1 + dlt1) mod 3 = 1 ->
      BigF (k1 + 1) ((1, false) :: Y) 0 ((0, true) :: ones ((1 + dlt1) / 3) ++ R1)
  | BF_oneF_rem2 {k1 k2 : nat} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigF k1 Y dlt1 R1 -> (1 + dlt1) mod 3 = 2 ->
      BigD1 k2 (ones (S ((1 + dlt1) / 3)) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((1, false) :: Y) dlt2 R2
  | BF_oneF_rem0 {k1 k2 : nat} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigF k1 Y dlt1 R1 -> (1 + dlt1) mod 3 = 0 ->
      BigD1 k2 (ones ((1 + dlt1) / 3) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((1, false) :: Y) (dlt2 + 1) R2
  | BF_twoF_rem1 {k1 : nat} {Y R1 : list Seg} {dlt1 : nat} :
      BigF k1 (bumpR (bumpR Y)) dlt1 R1 -> dlt1 mod 3 = 1 ->
      BigF (k1 + 1) ((2, false) :: Y) 0 ((0, true) :: ones (dlt1 / 3) ++ R1)
  | BF_twoF_rem2 {k1 k2 : nat} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigF k1 (bumpR (bumpR Y)) dlt1 R1 -> dlt1 mod 3 = 2 ->
      BigD1 k2 (ones (S (dlt1 / 3)) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((2, false) :: Y) dlt2 R2
  | BF_twoF_rem0 {k1 k2 : nat} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigF k1 (bumpR (bumpR Y)) dlt1 R1 -> dlt1 mod 3 = 0 ->
      BigD1 k2 (ones (dlt1 / 3) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((2, false) :: Y) (dlt2 + 1) R2
  | BF_twoT_rem1 {k1 : nat} {Y R1 : list Seg} {dlt1 : nat} :
      BigF k1 ((1, false) :: Y) dlt1 R1 -> dlt1 mod 3 = 1 ->
      BigF (k1 + 1) ((2, true) :: Y) 0 ((0, true) :: ones (dlt1 / 3) ++ R1)
  | BF_twoT_rem2 {k1 k2 : nat} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigF k1 ((1, false) :: Y) dlt1 R1 -> dlt1 mod 3 = 2 ->
      BigD1 k2 (ones (S (dlt1 / 3)) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((2, true) :: Y) dlt2 R2
  | BF_twoT_rem0 {k1 k2 : nat} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigF k1 ((1, false) :: Y) dlt1 R1 -> dlt1 mod 3 = 0 ->
      BigD1 k2 (ones (dlt1 / 3) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((2, true) :: Y) (dlt2 + 1) R2
  | BF_ge3_rem1 {k1 d : nat} {b : bool} {Y R1 : list Seg} {dlt1 : nat} :
      BigD1 k1 ((d, b) :: Y) dlt1 R1 -> dlt1 mod 3 = 1 ->
      BigF (k1 + 1) ((S (S (S d)), b) :: Y) 0 ((0, true) :: ones (dlt1 / 3) ++ R1)
  | BF_ge3_rem2 {k1 k2 d : nat} {b : bool} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigD1 k1 ((d, b) :: Y) dlt1 R1 -> dlt1 mod 3 = 2 ->
      BigD1 k2 (ones (S (dlt1 / 3)) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((S (S (S d)), b) :: Y) dlt2 R2
  | BF_ge3_rem0 {k1 k2 d : nat} {b : bool} {Y R1 R2 : list Seg} {dlt1 dlt2 : nat} :
      BigD1 k1 ((d, b) :: Y) dlt1 R1 -> dlt1 mod 3 = 0 ->
      BigD1 k2 (ones (dlt1 / 3) ++ R1) dlt2 R2 ->
      BigF (k1 + k2 + 1) ((S (S (S d)), b) :: Y) (dlt2 + 1) R2

with BigD1 : nat -> list Seg -> nat -> list Seg -> Prop :=
  | BD_nil : BigD1 0 [] 0 [(0, true); (0, false)]
  | BD_zeroF {k : nat} {Y R_fin : list Seg} {dlt : nat} :
      BigF k Y dlt R_fin -> BigD1 (k + 1) ((0, false) :: Y) (dlt + 3) R_fin
  | BD_zeroT (Y : list Seg) : BigD1 0 ((0, true) :: Y) 3 (bumpR Y)
  | BD_oneF {k : nat} {Y R_fin : list Seg} {dlt : nat} :
      BigF k (bumpR (bumpR Y)) dlt R_fin -> BigD1 (k + 1) ((1, false) :: Y) (dlt + 2) R_fin
  | BD_oneT {k : nat} {Y R_fin : list Seg} {dlt : nat} :
      BigF k ((1, false) :: Y) dlt R_fin -> BigD1 (k + 1) ((1, true) :: Y) (dlt + 2) R_fin
  | BD_ge2 {k d : nat} {b : bool} {Y R_fin : list Seg} {dlt' : nat} :
      BigD1 k ((d, b) :: Y) dlt' R_fin -> BigD1 (k + 1) ((S (S d), b) :: Y) (dlt' + 2) R_fin.

(* ========================================================================== *)
(* Master Inversion Theorem (step581 -> BigF / BigD1)                         *)
(* ========================================================================== *)

Lemma dispatch_halts {n val a : nat} {ls : list nat} {R1 : list Seg}
    (hhalt : run581 n (mkCfg581 BL0 (val :: a :: ls) R1) = None)
    (ihD : forall k, k < n -> forall a' ls' rs',
      run581 k (mkCfg581 DL0 (S a' :: ls') rs') = None ->
      exists k', k' < k /\ exists s dlt' R_fin,
        BigD1 s rs' dlt' R_fin /\ run581 k' (mkCfg581 BL0 ((a' + dlt') :: ls') R_fin) = None) :
  (val mod 3 = 1 /\ exists k', k' < n /\
    run581 k' (mkCfg581 BL0 (a :: ls) ((0, true) :: ones (val / 3) ++ R1)) = None) \/
  (val mod 3 = 2 /\ exists k', k' < n /\ exists s dlt2 R2,
    BigD1 s (ones (S (val / 3)) ++ R1) dlt2 R2 /\
    run581 k' (mkCfg581 BL0 ((a + dlt2) :: ls) R2) = None) \/
  (val mod 3 = 0 /\ exists k', k' < n /\ exists s dlt2 R2,
    BigD1 s (ones (val / 3) ++ R1) dlt2 R2 /\
    run581 k' (mkCfg581 BL0 ((a + (dlt2 + 1)) :: ls) R2) = None).
Proof.
  assert (hdiv : 3 * (val / 3) + val mod 3 = val) by dlia.
  assert (hsh : run581 (2 * (val / 3)) (mkCfg581 BL0 (val :: a :: ls) R1) =
    Some (mkCfg581 BL0 ((val mod 3) :: a :: ls) (ones (val / 3) ++ R1))).
  { pose proof (bl0_shift_3q (val / 3) (val mod 3) (a :: ls) R1) as h0.
    rewrite hdiv in h0. exact h0. }
  destruct (halts_after_run hsh hhalt) as [hle hrem].
  assert (hmod : val mod 3 = 0 \/ val mod 3 = 1 \/ val mod 3 = 2) by dlia.
  destruct hmod as [h0 | [h1 | h2]].
  - rewrite h0 in hrem.
    destruct (halts_after_step hrem eq_refl) as [h1le hdl].
    assert (hlt : n - 2 * (val / 3) - 1 < n) by dlia.
    destruct (ihD _ hlt (S a) ls (ones (val / 3) ++ R1) hdl)
      as [k' [hk' [s [dlt2 [R2 [hD hfin]]]]]].
    right. right. split; [exact h0 |].
    exists k'. split; [dlia |].
    exists s, dlt2, R2. split; [exact hD |].
    replace (a + (dlt2 + 1)) with (S a + dlt2) by lia.
    exact hfin.
  - rewrite h1 in hrem.
    destruct (halts_after_step hrem eq_refl) as [h1le hbl].
    left. split; [exact h1 |].
    exists (n - 2 * (val / 3) - 1). split; [dlia | exact hbl].
  - rewrite h2 in hrem.
    destruct (halts_after_step hrem eq_refl) as [h1le hdl].
    assert (hlt : n - 2 * (val / 3) - 1 < n) by dlia.
    destruct (ihD _ hlt a ls (ones (S (val / 3)) ++ R1) hdl)
      as [k' [hk' [s [dlt2 [R2 [hD hfin]]]]]].
    right. left. split; [exact h2 |].
    exists k'. split; [dlia |].
    exists s, dlt2, R2. exact (conj hD hfin).
Qed.

Lemma halts_inversion (n : nat) :
  (forall a ls rs, run581 n (mkCfg581 FR0 (a :: ls) rs) = None ->
    exists k, k < n /\ exists s dlt R_fin,
      BigF s rs dlt R_fin /\ run581 k (mkCfg581 BL0 ((a + dlt) :: ls) R_fin) = None) /\
  (forall a ls rs, run581 n (mkCfg581 DL0 (S a :: ls) rs) = None ->
    exists k, k < n /\ exists s dlt' R_fin,
      BigD1 s rs dlt' R_fin /\ run581 k (mkCfg581 BL0 ((a + dlt') :: ls) R_fin) = None).
Proof.
  induction n as [m ih] using strong_induction.
  split.
  - intros a ls rs hhalt.
    destruct rs as [| [d b] Y].
    + destruct (halts_after_step hhalt eq_refl) as [h1 hr].
      exists (m - 1). split; [lia |].
      exists 0, 0, [(0, false)]. split; [exact BF_nil |].
      rewrite Nat.add_0_r. exact hr.
    + destruct d as [| [| [| d3]]].
      * destruct b.
        -- destruct (halts_after_step hhalt eq_refl) as [h1 hr].
           exists (m - 1). split; [lia |].
           exists 0, 0, ((1, false) :: Y). split; [exact (BF_zeroT Y) |].
           rewrite Nat.add_0_r. exact hr.
        -- destruct (halts_after_step hhalt eq_refl) as [h1 hr].
           exists (m - 1). split; [lia |].
           exists 0, 0, (bumpR (bumpR Y)). split; [exact (BF_zeroF Y) |].
           rewrite Nat.add_0_r. exact hr.
      * destruct b.
        -- assert (h2 : run581 2 (mkCfg581 FR0 (a :: ls) ((1, true) :: Y)) =
             Some (mkCfg581 BL0 (a :: ls) ((0, true) :: bumpR Y))) by reflexivity.
           destruct (halts_after_run h2 hhalt) as [hle hr].
           exists (m - 2). split; [lia |].
           exists 0, 0, ((0, true) :: bumpR Y). split; [exact (BF_oneT Y) |].
           rewrite Nat.add_0_r. exact hr.
        -- destruct (halts_after_step hhalt eq_refl) as [h1 hr1].
           destruct (proj1 (ih (m - 1) ltac:(lia)) 1 (a :: ls) Y hr1)
             as [k1 [hk1 [s1 [dlt1 [R1 [hF1 hbl1]]]]]].
           destruct (dispatch_halts hbl1 (fun k hk => proj2 (ih k ltac:(lia))))
             as [[hrem [k' [hk' hfin]]] | [[hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]] |
                                           [hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]]]].
           ++ exists k'. split; [lia |].
              exists (s1 + 1), 0, ((0, true) :: ones ((1 + dlt1) / 3) ++ R1).
              split; [exact (BF_oneF_rem1 hF1 hrem) |].
              rewrite Nat.add_0_r. exact hfin.
           ++ exists k'. split; [lia |].
              exists (s1 + s2 + 1), dlt2, R2.
              exact (conj (BF_oneF_rem2 hF1 hrem hD2) hfin).
           ++ exists k'. split; [lia |].
              exists (s1 + s2 + 1), (dlt2 + 1), R2.
              exact (conj (BF_oneF_rem0 hF1 hrem hD2) hfin).
      * destruct b.
        -- assert (h2 : run581 2 (mkCfg581 FR0 (a :: ls) ((2, true) :: Y)) =
             Some (mkCfg581 FR0 (0 :: a :: ls) ((1, false) :: Y))) by reflexivity.
           destruct (halts_after_run h2 hhalt) as [hle hr1].
           destruct (proj1 (ih (m - 2) ltac:(lia)) 0 (a :: ls) ((1, false) :: Y) hr1)
             as [k1 [hk1 [s1 [dlt1 [R1 [hF1 hbl1]]]]]].
           cbn [Nat.add] in hbl1.
           destruct (dispatch_halts hbl1 (fun k hk => proj2 (ih k ltac:(lia))))
             as [[hrem [k' [hk' hfin]]] | [[hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]] |
                                           [hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]]]].
           ++ exists k'. split; [lia |].
              exists (s1 + 1), 0, ((0, true) :: ones (dlt1 / 3) ++ R1).
              split; [exact (BF_twoT_rem1 hF1 hrem) |].
              rewrite Nat.add_0_r. exact hfin.
           ++ exists k'. split; [lia |].
              exists (s1 + s2 + 1), dlt2, R2.
              exact (conj (BF_twoT_rem2 hF1 hrem hD2) hfin).
           ++ exists k'. split; [lia |].
              exists (s1 + s2 + 1), (dlt2 + 1), R2.
              exact (conj (BF_twoT_rem0 hF1 hrem hD2) hfin).
        -- assert (h2 : run581 2 (mkCfg581 FR0 (a :: ls) ((2, false) :: Y)) =
             Some (mkCfg581 FR0 (0 :: a :: ls) (bumpR (bumpR Y)))) by reflexivity.
           destruct (halts_after_run h2 hhalt) as [hle hr1].
           destruct (proj1 (ih (m - 2) ltac:(lia)) 0 (a :: ls) (bumpR (bumpR Y)) hr1)
             as [k1 [hk1 [s1 [dlt1 [R1 [hF1 hbl1]]]]]].
           cbn [Nat.add] in hbl1.
           destruct (dispatch_halts hbl1 (fun k hk => proj2 (ih k ltac:(lia))))
             as [[hrem [k' [hk' hfin]]] | [[hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]] |
                                           [hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]]]].
           ++ exists k'. split; [lia |].
              exists (s1 + 1), 0, ((0, true) :: ones (dlt1 / 3) ++ R1).
              split; [exact (BF_twoF_rem1 hF1 hrem) |].
              rewrite Nat.add_0_r. exact hfin.
           ++ exists k'. split; [lia |].
              exists (s1 + s2 + 1), dlt2, R2.
              exact (conj (BF_twoF_rem2 hF1 hrem hD2) hfin).
           ++ exists k'. split; [lia |].
              exists (s1 + s2 + 1), (dlt2 + 1), R2.
              exact (conj (BF_twoF_rem0 hF1 hrem hD2) hfin).
      * destruct (halts_after_step hhalt eq_refl) as [h1 hr1].
        destruct (proj2 (ih (m - 1) ltac:(lia)) 0 (a :: ls) ((d3, b) :: Y) hr1)
          as [k1 [hk1 [s1 [dlt1 [R1 [hD1 hbl1]]]]]].
        cbn [Nat.add] in hbl1.
        destruct (dispatch_halts hbl1 (fun k hk => proj2 (ih k ltac:(lia))))
          as [[hrem [k' [hk' hfin]]] | [[hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]] |
                                        [hrem [k' [hk' [s2 [dlt2 [R2 [hD2 hfin]]]]]]]]].
        -- exists k'. split; [lia |].
           exists (s1 + 1), 0, ((0, true) :: ones (dlt1 / 3) ++ R1).
           split; [exact (BF_ge3_rem1 hD1 hrem) |].
           rewrite Nat.add_0_r. exact hfin.
        -- exists k'. split; [lia |].
           exists (s1 + s2 + 1), dlt2, R2.
           exact (conj (BF_ge3_rem2 hD1 hrem hD2) hfin).
        -- exists k'. split; [lia |].
           exists (s1 + s2 + 1), (dlt2 + 1), R2.
           exact (conj (BF_ge3_rem0 hD1 hrem hD2) hfin).
  - intros a ls rs hhalt.
    destruct rs as [| [d b] Y].
    + assert (h4 : run581 4 (mkCfg581 DL0 (S a :: ls) []) =
        Some (mkCfg581 BL0 (a :: ls) [(0, true); (0, false)])) by reflexivity.
      destruct (halts_after_run h4 hhalt) as [hle hr].
      exists (m - 4). split; [lia |].
      exists 0, 0, [(0, true); (0, false)]. split; [exact BD_nil |].
      rewrite Nat.add_0_r. exact hr.
    + destruct d as [| [| d2]].
      * destruct b.
        -- destruct (halts_after_step hhalt eq_refl) as [h1 hr1].
           exists (m - 1). split; [lia |].
           exists 0, 3, (bumpR Y). split; [exact (BD_zeroT Y) |].
           replace (a + 3) with (S (S (S a))) by lia. exact hr1.
        -- destruct (halts_after_step hhalt eq_refl) as [h1 hr1].
           destruct (proj1 (ih (m - 1) ltac:(lia)) (S (S (S a))) ls Y hr1)
             as [k1 [hk1 [s [dlt [R_fin [hF hfin]]]]]].
           exists k1. split; [lia |].
           exists (s + 1), (dlt + 3), R_fin. split; [exact (BD_zeroF hF) |].
           replace (a + (dlt + 3)) with (S (S (S a)) + dlt) by lia. exact hfin.
      * destruct b.
        -- assert (h2 : run581 2 (mkCfg581 DL0 (S a :: ls) ((1, true) :: Y)) =
             Some (mkCfg581 FR0 (S (S a) :: ls) ((1, false) :: Y))) by reflexivity.
           destruct (halts_after_run h2 hhalt) as [hle hr1].
           destruct (proj1 (ih (m - 2) ltac:(lia)) (S (S a)) ls ((1, false) :: Y) hr1)
             as [k1 [hk1 [s [dlt [R_fin [hF hfin]]]]]].
           exists k1. split; [lia |].
           exists (s + 1), (dlt + 2), R_fin. split; [exact (BD_oneT hF) |].
           replace (a + (dlt + 2)) with (S (S a) + dlt) by lia. exact hfin.
        -- assert (h2 : run581 2 (mkCfg581 DL0 (S a :: ls) ((1, false) :: Y)) =
             Some (mkCfg581 FR0 (S (S a) :: ls) (bumpR (bumpR Y)))) by reflexivity.
           destruct (halts_after_run h2 hhalt) as [hle hr1].
           destruct (proj1 (ih (m - 2) ltac:(lia)) (S (S a)) ls (bumpR (bumpR Y)) hr1)
             as [k1 [hk1 [s [dlt [R_fin [hF hfin]]]]]].
           exists k1. split; [lia |].
           exists (s + 1), (dlt + 2), R_fin. split; [exact (BD_oneF hF) |].
           replace (a + (dlt + 2)) with (S (S a) + dlt) by lia. exact hfin.
      * destruct (halts_after_step hhalt eq_refl) as [h1 hr1].
        destruct (proj2 (ih (m - 1) ltac:(lia)) (S (S a)) ls ((d2, b) :: Y) hr1)
          as [k1 [hk1 [s [dlt' [R_fin [hD hfin]]]]]].
        exists k1. split; [lia |].
        exists (s + 1), (dlt' + 2), R_fin. split; [exact (BD_ge2 hD) |].
        replace (a + (dlt' + 2)) with (S (S a) + dlt') by lia. exact hfin.
Qed.

(* ========================================================================== *)
(* Wall Invariant Non-Halting Bridge                                          *)
(* ========================================================================== *)

Lemma wall_no_halt_of_bigF_inv (W : list Seg -> Prop)
    (hW : forall rs, W rs -> exists tail, rs = (0, true) :: tail /\
      forall s dlt R_fin, BigF s (bumpR (bumpR tail)) dlt R_fin ->
        dlt mod 3 = 1 /\ W ((0, true) :: ones (dlt / 3) ++ R_fin)) :
  forall n rs, W rs -> run581 n (mkCfg581 BL0 [1; 3; 2] rs) <> None.
Proof.
  intro n.
  induction n as [m ih] using strong_induction.
  intros rs hWR hhalt.
  destruct (hW rs hWR) as [tail [-> hstep]].
  destruct (halts_after_run (wall_27 tail) hhalt) as [hle27 hfr].
  destruct (proj1 (halts_inversion (m - 27)) 0 [1; 3; 2] (bumpR (bumpR tail)) hfr)
    as [k1 [hk1 [s [dlt [R_fin [hF hbl]]]]]].
  cbn [Nat.add] in hbl.
  destruct (hstep s dlt R_fin hF) as [hrem1 hW'].
  assert (hdiv : 3 * (dlt / 3) + 1 = dlt) by dlia.
  assert (hsh : run581 (2 * (dlt / 3)) (mkCfg581 BL0 (dlt :: [1; 3; 2]) R_fin) =
    Some (mkCfg581 BL0 (1 :: [1; 3; 2]) (ones (dlt / 3) ++ R_fin))).
  { pose proof (bl0_shift_3q (dlt / 3) 1 [1; 3; 2] R_fin) as h0.
    rewrite hdiv in h0. exact h0. }
  destruct (halts_after_run hsh hbl) as [hle2 hbl1].
  destruct (halts_after_step hbl1 eq_refl) as [h1le hnext].
  exact (ih (k1 - 2 * (dlt / 3) - 1) ltac:(dlia)
    ((0, true) :: ones (dlt / 3) ++ R_fin) hW' hnext).
Qed.

(* ========================================================================== *)
(* Structural Properties: Bounds, Determinism, NoNonlast0F                    *)
(* ========================================================================== *)

Scheme BI_F := Induction for BigF Sort Prop
  with BI_D := Induction for BigD1 Sort Prop.
Combined Scheme BI_FD from BI_F, BI_D.

(* Structural recursion follows the two actual calls. Their particular
   rank formula is irrelevant to bounds and functional determinism. *)
Local Lemma FD_bounds :
  (forall s rs d R, BigF s rs d R -> d <> 1 /\ R <> []) /\
  (forall s rs d R, BigD1 s rs d R -> (rs <> [] -> 2 <= d) /\ R <> []).
Proof.
  apply BI_FD; intros;
    try solve [split; [lia | discriminate]];
    try solve [split; [lia | apply bumpR_nonempty]];
    try solve [split; [intro h; contradiction (h eq_refl) | discriminate]];
    try solve [split; [intro; lia | tauto]].
  all: match goal with
  | H : (ones _ ++ ?X <> [] -> _) /\ _, Hx : _ /\ ?X <> [] |- _ =>
      pose proof (proj1 H (append_nonempty_of_right _ _ (proj2 Hx)));
      split; [lia | exact (proj2 H)]
  end.
Qed.

Lemma bigFD_bounds (s : nat) :
  (forall rs dlt R_fin, BigF s rs dlt R_fin -> dlt <> 1 /\ R_fin <> []) /\
  (forall rs dlt' R_fin, BigD1 s rs dlt' R_fin -> (rs <> [] -> 2 <= dlt') /\ R_fin <> []).
Proof. split; [apply (proj1 FD_bounds) | apply (proj2 FD_bounds)]. Qed.

Local Lemma FD_det :
  (forall k X d Y, BigF k X d Y -> forall s e Z, BigF s X e Z -> d = e /\ Y = Z) /\
  (forall k X d Y, BigD1 k X d Y -> forall s e Z, BigD1 s X e Z -> d = e /\ Y = Z).
Proof.
  apply BI_FD;
    repeat lazymatch goal with
    | |- forall s e Z, BigF s _ e Z -> _ =>
      intros s_other e_other Z_other h_other
    | |- forall s e Z, BigD1 s _ e Z -> _ =>
      intros s_other e_other Z_other h_other
    | |- forall _, _ => intro
    end;
    inverts h_other as h1 hrem h2;
    try solve [split; reflexivity].
  all: try (lazymatch type of h1 with
    | BigF _ ?X _ _ =>
      match goal with
      | IH : forall s e Z, BigF s X e Z -> _ |- _ => destruct (IH _ _ _ h1) as [-> ->]
      end
    | BigD1 _ ?X _ _ =>
      match goal with
      | IH : forall s e Z, BigD1 s X e Z -> _ |- _ => destruct (IH _ _ _ h1) as [-> ->]
      end
  end); try solve [split; reflexivity | lia].
  all: lazymatch type of h2 with BigD1 _ ?X _ _ =>
    match goal with IH : forall s e Z, BigD1 s X e Z -> _ |- _ =>
      destruct (IH _ _ _ h2) as [-> ->]; split; reflexivity
    end
  end.
Qed.

Lemma bigFD_det (s1 : nat) :
  (forall s2 rs dlt1 dlt2 R1 R2, BigF s1 rs dlt1 R1 -> BigF s2 rs dlt2 R2 -> dlt1 = dlt2 /\ R1 = R2) /\
  (forall s2 rs dlt1 dlt2 R1 R2, BigD1 s1 rs dlt1 R1 -> BigD1 s2 rs dlt2 R2 -> dlt1 = dlt2 /\ R1 = R2).
Proof. split; intros; [eapply (proj1 FD_det) | eapply (proj2 FD_det)]; eassumption. Qed.


Fixpoint NoNonlast0F (rs : list Seg) : Prop :=
  match rs with
  | [] => True
  | x :: rest =>
    match rest with
    | [] => True
    | _ =>
      match x with
      | (0, false) => False
      | _ => NoNonlast0F rest
      end
    end
  end.

Definition NoInterior0F (rs : list Seg) : Prop :=
  match rs with
  | [] => True
  | _ :: xs => NoNonlast0F xs
  end.

Lemma noNonlast0F_tail {x : Seg} {xs : list Seg} (h : NoNonlast0F (x :: xs)) :
  NoNonlast0F xs.
Proof.
  destruct xs as [| y ys]; [exact I |].
  destruct x as [[| d] []]; try exact h.
  contradiction h.
Qed.

Lemma noNonlast0F_cons_ne0F {x : Seg} {xs : list Seg}
    (hne : x <> (0, false)) (h : NoNonlast0F xs) :
  NoNonlast0F (x :: xs).
Proof.
  destruct xs as [| y ys]; [exact I |].
  destruct x as [[| d] []]; try exact h.
  contradiction (hne eq_refl).
Qed.

Lemma nnf_0T {xs : list Seg} (h : NoNonlast0F xs) : NoNonlast0F ((0, true) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma nnf_1F {xs : list Seg} (h : NoNonlast0F xs) : NoNonlast0F ((1, false) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma nnf_1T {xs : list Seg} (h : NoNonlast0F xs) : NoNonlast0F ((1, true) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma nnf_2F {xs : list Seg} (h : NoNonlast0F xs) : NoNonlast0F ((2, false) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma nnf_Sd (d : nat) (b : bool) {xs : list Seg} (h : NoNonlast0F xs) :
  NoNonlast0F ((S d, b) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma noNonlast0F_bumpR {rs : list Seg} (h : NoNonlast0F rs) :
  NoNonlast0F (bumpR rs).
Proof.
  destruct rs as [| [d b] xs]; [exact I |].
  exact (nnf_Sd d b (noNonlast0F_tail h)).
Qed.

Lemma noNonlast0F_ones_append (q : nat) {rs : list Seg} (h : NoNonlast0F rs) :
  NoNonlast0F (ones q ++ rs).
Proof.
  induction q as [| k ih]; [exact h |].
  exact (nnf_1F ih).
Qed.

Lemma noNonlast0F_imp_noInterior0F {rs : list Seg} (h : NoNonlast0F rs) :
  NoInterior0F rs.
Proof.
  destruct rs as [| x xs]; [exact I | exact (noNonlast0F_tail h)].
Qed.

(* The tail invariant follows the same mutual call tree as the bounds. *)
Local Lemma FD_nnf :
  (forall s X d Y, BigF s X d Y -> NoNonlast0F X -> NoNonlast0F Y) /\
  (forall s X d Y, BigD1 s X d Y -> NoInterior0F X -> NoNonlast0F Y).
Proof.
  apply BI_FD; intros.
  all: try solve [exact I].
  all: try match goal with H : NoNonlast0F (_ :: _) |- _ =>
    pose proof (noNonlast0F_tail H)
  end.
  all: repeat match goal with
  | H : NoNonlast0F ?X -> NoNonlast0F ?Y |- _ =>
    let S := fresh "hnf" in
    assert (S : NoNonlast0F Y) by (apply H; solve [eauto 4 using nnf_1F, noNonlast0F_bumpR]);
    clear H
  | H : NoInterior0F ?X -> NoNonlast0F ?Y |- _ =>
    let S := fresh "hnd" in
    assert (S : NoNonlast0F Y) by
      (apply H; solve [eauto 4 using noNonlast0F_ones_append, noNonlast0F_imp_noInterior0F]);
    clear H
  end.
  all: try solve [eauto 5 using nnf_0T, nnf_1F, noNonlast0F_tail,
      noNonlast0F_bumpR, noNonlast0F_ones_append, noNonlast0F_imp_noInterior0F].
  all: match goal with H : NoNonlast0F ((0,false) :: ?X) |- _ =>
    destruct X; [exact I | contradiction H]
  end.
Qed.

Lemma bigFD_noNonlast0F (s : nat) :
  (forall rs dlt R_fin, BigF s rs dlt R_fin -> NoNonlast0F rs -> NoNonlast0F R_fin) /\
  (forall rs dlt' R_fin, BigD1 s rs dlt' R_fin -> NoInterior0F rs -> NoNonlast0F R_fin).
Proof. split; [apply (proj1 FD_nnf) | apply (proj2 FD_nnf)]. Qed.


(* ========================================================================== *)
(* Basic Algebraic Identities and Head Constraints                            *)
(* ========================================================================== *)

Lemma bigD1_1_1_inv {s dlt' : nat} {X R_fin : list Seg}
    (h : BigD1 s ((1, false) :: (1, false) :: X) dlt' R_fin) :
  exists s', s' < s /\ exists dlt0, dlt' = dlt0 + 2 /\ BigF s' ((3, false) :: X) dlt0 R_fin.
Proof.
  inverts h as hF.
  match type of hF with
  | BigF ?s' _ ?dlt0 _ =>
    exists s'; split; [lia | exists dlt0; exact (conj eq_refl hF)]
  end.
Qed.

Lemma bigF_3_0s_inv {s dlt : nat} {X R_fin : list Seg}
    (h : BigF s ((3, false) :: (0, true) :: X) dlt R_fin) :
  exists s', s' < s /\ exists dlt0, dlt = dlt0 + 3 /\ BigF s' ((3, false) :: X) dlt0 R_fin.
Proof.
  assert (hD0 : BigD1 1 ((0, false) :: (0, true) :: X) 3 ((1, false) :: X))
    by exact (BD_zeroF (BF_zeroT X)).
  inverts h as h1 hrem h2.
  - destruct (proj2 (bigFD_det _) _ _ _ _ _ _ h1 hD0) as [-> ->]; dlia.
  - destruct (proj2 (bigFD_det _) _ _ _ _ _ _ h1 hD0) as [-> ->]; dlia.
  - destruct (proj2 (bigFD_det _) _ _ _ _ _ _ h1 hD0) as [-> ->].
    destruct (bigD1_1_1_inv h2) as [s' [hs' [dlt0 [-> hF]]]].
    exists s'. split; [lia |].
    exists dlt0. split; [lia | exact hF].
Qed.

Lemma bigF_3_1s_inv {s dlt : nat} {X R_fin : list Seg}
    (h : BigF s ((3, false) :: (1, true) :: X) dlt R_fin) :
  exists s', s' < s /\ exists dlt0, dlt = dlt0 + 3 /\ BigF s' ((2, true) :: bumpR X) dlt0 R_fin.
Proof.
  assert (hD0 : BigD1 1 ((0, false) :: (1, true) :: X) 3 ((0, true) :: bumpR X))
    by exact (BD_zeroF (BF_oneT X)).
  inverts h as h1 hrem h2.
  - destruct (proj2 (bigFD_det _) _ _ _ _ _ _ h1 hD0) as [-> ->]; dlia.
  - destruct (proj2 (bigFD_det _) _ _ _ _ _ _ h1 hD0) as [-> ->]; dlia.
  - destruct (proj2 (bigFD_det _) _ _ _ _ _ _ h1 hD0) as [-> ->].
    cbn in h2. inverts h2 as hF.
    match type of hF with
    | BigF ?s' _ ?dlt0 _ =>
      exists s'; split; [lia | exists dlt0; split; [lia | exact hF]]
    end.
Qed.

Lemma bigF_2s_0s_exists (X : list Seg) :
  BigF 2 ((2, true) :: (0, true) :: X) 4 ((2, false) :: X).
Proof.
  exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_zeroT X) eq_refl) eq_refl (BD_zeroT ((1, false) :: X))).
Qed.

Lemma bigF_3_1_1_1s_exists (X : list Seg) :
  BigF 7 ((3, false) :: (1, false) :: (1, false) :: (1, true) :: X) 7
    ((2, false) :: (0, true) :: bumpR X).
Proof.
  assert (h1 : BigD1 3 ((0, false) :: (1, false) :: (1, false) :: (1, true) :: X) 3
    ((0, true) :: (0, true) :: (0, true) :: bumpR X))
    by exact (BD_zeroF (BF_oneF_rem1 (BF_oneF_rem1 (BF_oneT X) eq_refl) eq_refl)).
  exact (BF_ge3_rem0 h1 eq_refl
    (BD_oneF (Y := (0, true) :: (0, true) :: (0, true) :: bumpR X)
      (bigF_2s_0s_exists ((0, true) :: bumpR X)))).
Qed.

Lemma bigF_zero_head_nnf {s : nat} {rs R_fin : list Seg}
    (hF : BigF s rs 0 R_fin) (hN : NoNonlast0F rs) :
  exists x xs, R_fin = x :: xs /\ (x = (0, false) \/ x = (0, true) \/ x = (1, false)).
Proof.
  inverts hF as h1 hrem h2 h0eq; try lia.
  - exists (0, false), ([] : list Seg). split; [reflexivity | left; reflexivity].
  - match type of hN with NoNonlast0F ((0, false) :: ?Y) => destruct Y; [| contradiction hN] end.
    exists (1, false), ([] : list Seg). split; [reflexivity | right; right; reflexivity].
  - eexists (1, false), _. split; [reflexivity | right; right; reflexivity].
  - eexists (0, true), _. split; [reflexivity | right; left; reflexivity].
  - eexists (0, true), _. split; [reflexivity | right; left; reflexivity].
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - eexists (0, true), _. split; [reflexivity | right; left; reflexivity].
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - eexists (0, true), _. split; [reflexivity | right; left; reflexivity].
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - eexists (0, true), _. split; [reflexivity | right; left; reflexivity].
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj2 (bigFD_bounds _) _ _ _ h1)))).
    lia.
Qed.

Lemma bumpR_bumpR_ge2 {rs : list Seg} (hne : rs <> []) :
  exists d b Y, bumpR (bumpR rs) = (S (S d), b) :: Y.
Proof.
  destruct rs as [| [d b] xs]; [contradiction (hne eq_refl) |].
  exists d, b, xs. reflexivity.
Qed.

Lemma ones_pos_cons {q : nat} (hq : 1 <= q) (rs : list Seg) :
  exists Z, ones q ++ rs = (1, false) :: Z.
Proof.
  destruct q as [| k]; [lia |].
  exists (ones k ++ rs). reflexivity.
Qed.

Lemma bigF_ge2_zero_head {s d : nat} {b : bool} {Y R_fin : list Seg}
    (hF : BigF s ((S (S d), b) :: Y) 0 R_fin) :
  exists Z, R_fin = (0, true) :: (1, false) :: Z.
Proof.
  inverts hF as h1 hrem h2 h0eq; try lia.
  - pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ h1)) as hne1.
    match goal with
    | |- exists Z, (0, true) :: ones (?d1 / 3) ++ ?R1 = _ =>
      destruct (ones_pos_cons (q := d1 / 3) ltac:(dlia) R1) as [Z hZ];
      exists Z; cbn [app]; rewrite hZ; reflexivity
    end.
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ h1)) as hne1.
    match goal with
    | |- exists Z, (0, true) :: ones (?d1 / 3) ++ ?R1 = _ =>
      destruct (ones_pos_cons (q := d1 / 3) ltac:(dlia) R1) as [Z hZ];
      exists Z; cbn [app]; rewrite hZ; reflexivity
    end.
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h1) ltac:(discriminate)) as hge2.
    match goal with
    | |- exists Z, (0, true) :: ones (?d1 / 3) ++ ?R1 = _ =>
      destruct (ones_pos_cons (q := d1 / 3) ltac:(dlia) R1) as [Z hZ];
      exists Z; cbn [app]; rewrite hZ; reflexivity
    end.
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj2 (bigFD_bounds _) _ _ _ h1)))).
    lia.
Qed.

Lemma bigF_oneF_zero_head {s : nat} {Y R_fin : list Seg}
    (hF : BigF s ((1, false) :: Y) 0 R_fin) :
  exists Z, R_fin = (0, true) :: Z.
Proof.
  inverts hF as h1 hrem h2 h0eq; try lia.
  - eexists. reflexivity.
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
Qed.

Lemma bigD1_oneF_two_head {s : nat} {tail R_fin : list Seg}
    (hne : tail <> []) (hD : BigD1 s ((1, false) :: tail) 2 R_fin) :
  exists Z, R_fin = (0, true) :: (1, false) :: Z.
Proof.
  inverts hD as hF heq.
  match type of hF with
  | BigF _ _ ?dlt _ => assert (dlt = 0) by lia; subst dlt
  end.
  destruct (bumpR_bumpR_ge2 hne) as [d [b [Y hEq]]].
  rewrite hEq in hF.
  exact (bigF_ge2_zero_head hF).
Qed.

Lemma bigF_two_head {s : nat} {rs R_fin : list Seg} (hF : BigF s rs 2 R_fin) :
  exists Z, R_fin = (0, true) :: (1, false) :: Z.
Proof.
  inverts hF as h1 hrem h2 heq; try lia.
  - exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1))) h2).
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1))) h2).
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1))) h2).
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)))).
    lia.
  - exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ (proj2 (proj2 (bigFD_bounds _) _ _ _ h1))) h2).
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj2 (bigFD_bounds _) _ _ _ h1)))).
    lia.
Qed.

Lemma bigF_three_head {s : nat} {rs R_fin : list Seg} (hF : BigF s rs 3 R_fin) :
  exists Z, R_fin = (0, true) :: (1, false) :: Z.
Proof.
  remember 3 as dlt_three eqn:hthree.
  inverts hF as h1 hrem h2 heq; subst; try lia.
  - inverts h2 as h3 heq2.
    match type of h3 with BigF _ _ ?dlt _ => assert (dlt = 1) by lia; subst dlt end.
    contradiction (proj1 (proj1 (bigFD_bounds _) _ _ _ h3) eq_refl).
  - match type of h2 with
    | BigD1 _ (ones ?q ++ ?R1) ?dlt2 _ =>
      assert (dlt2 = 2) by lia; subst dlt2;
      pose proof (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)) as hne;
      destruct q as [| k] eqn:hqq; [dlia |];
      exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2)
    end.
  - inverts h2 as h3 heq2.
    match type of h3 with BigF _ _ ?dlt _ => assert (dlt = 1) by lia; subst dlt end.
    contradiction (proj1 (proj1 (bigFD_bounds _) _ _ _ h3) eq_refl).
  - match type of h1 with
    | BigF _ (bumpR (bumpR ?Y)) ?dlt1 ?R1 =>
      match type of h2 with
      | BigD1 _ _ ?dlt2 _ =>
        assert (dlt2 = 2) by lia; subst dlt2;
        destruct dlt1 as [| k];
        [ cbn in h2;
          assert (h0t : exists Z, R1 = (0, true) :: Z) by
            (destruct Y as [| [d b] xs];
             [ exact (bigF_oneF_zero_head h1)
             | destruct (bigF_ge2_zero_head h1) as [Z hZ]; exists ((1, false) :: Z); exact hZ ]);
          destruct h0t as [Z ->]; inverts h2
        | pose proof (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)) as hne;
          destruct (S k / 3) as [| m] eqn:hqq; [dlia |];
          exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2) ]
      end
    end.
  - inverts h2 as h3 heq2.
    match type of h3 with BigF _ _ ?dlt _ => assert (dlt = 1) by lia; subst dlt end.
    contradiction (proj1 (proj1 (bigFD_bounds _) _ _ _ h3) eq_refl).
  - match type of h1 with
    | BigF _ ((1, false) :: ?Y) ?dlt1 ?R1 =>
      match type of h2 with
      | BigD1 _ _ ?dlt2 _ =>
        assert (dlt2 = 2) by lia; subst dlt2;
        destruct dlt1 as [| k];
        [ cbn in h2; destruct (bigF_oneF_zero_head h1) as [Z ->]; inverts h2
        | pose proof (proj2 (proj1 (bigFD_bounds _) _ _ _ h1)) as hne;
          destruct (S k / 3) as [| m] eqn:hqq; [dlia |];
          exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2) ]
      end
    end.
  - inverts h2 as h3 heq2.
    match type of h3 with BigF _ _ ?dlt _ => assert (dlt = 1) by lia; subst dlt end.
    contradiction (proj1 (proj1 (bigFD_bounds _) _ _ _ h3) eq_refl).
  - match type of h2 with
    | BigD1 _ (ones ?q ++ ?R1) ?dlt2 _ =>
      assert (dlt2 = 2) by lia; subst dlt2;
      pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h1) ltac:(discriminate)) as hge;
      pose proof (proj2 (proj2 (bigFD_bounds _) _ _ _ h1)) as hne;
      destruct q as [| m] eqn:hqq; [dlia |];
      exact (bigD1_oneF_two_head (append_nonempty_of_right _ _ hne) h2)
    end.
Qed.

Definition ValidHead (rs : list Seg) : Prop :=
  match rs with
  | (0, false) :: _ => True
  | (0, true) :: _ => True
  | (1, false) :: _ => True
  | (1, true) :: _ => True
  | (2, false) :: _ => True
  | _ => False
  end.

Lemma bigF_head_nnf (s : nat) :
  forall rs dlt R_fin, BigF s rs dlt R_fin -> NoNonlast0F rs -> ValidHead R_fin.
Proof.
  induction s as [m ih] using strong_induction.
  assert (ihF : forall k rs dlt R_fin,
    BigF k rs dlt R_fin -> NoNonlast0F rs -> k < m -> ValidHead R_fin)
    by (intros k ? ? ? h hN hk; exact (ih k hk _ _ _ h hN)).
  clear ih.
  intros rs dlt R_fin hF hN.
  inverts hF as h1 hrem h2.
  - exact I.
  - match type of hN with NoNonlast0F ((0, false) :: ?Y) => destruct Y; [exact I | contradiction hN] end.
  - exact I.
  - exact I.
  - exact I.
  - pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h1 (noNonlast0F_tail hN)) as h1N.
    inverts h2 as h3.
    exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia)).
  - pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h1 (noNonlast0F_tail hN)) as h1N.
    match type of h2 with
    | BigD1 _ (ones ?q ++ _) _ _ =>
      destruct q as [| k] eqn:hq; [dlia |];
      inverts h2 as h3;
      exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia))
    end.
  - exact I.
  - pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h1 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN)))) as h1N.
    inverts h2 as h3.
    exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia)).
  - pose proof (noNonlast0F_tail hN) as hYN.
    pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h1 (noNonlast0F_bumpR (noNonlast0F_bumpR hYN))) as h1N.
    match type of h1 with
    | BigF _ (bumpR (bumpR ?Y)) ?dlt1 ?R1 =>
      destruct dlt1 as [| k];
      [ cbn [Nat.div ones app] in h2;
        destruct Y as [| [d b] xs];
        [ inverts h1 as ha h0rem hb; try lia;
          [ match type of ha with
            | BigF _ _ ?dlt0 _ =>
              destruct dlt0 as [| kk0];
              [ inverts h2;
                destruct (bigF_zero_head_nnf ha I) as [x [xs [-> [-> | [-> | ->]]]]]; exact I
              | destruct ((1 + S kk0) / 3) as [| jj0] eqn:hq0; [dlia | inverts h2; exact I] ]
            end
          | pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ hb)
              (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ ha)))); lia ]
        | destruct (bigF_ge2_zero_head h1) as [Z ->]; inverts h2; exact I ]
      | destruct (S k / 3) as [| jj] eqn:hq; [dlia |];
        inverts h2 as h3;
        exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia)) ]
    end.
  - exact I.
  - pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h1 (nnf_1F (noNonlast0F_tail hN))) as h1N.
    inverts h2 as h3.
    exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia)).
  - pose proof (noNonlast0F_tail hN) as hYN.
    pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h1 (nnf_1F hYN)) as h1N.
    match type of h1 with
    | BigF _ ((1, false) :: ?Y) ?dlt1 ?R1 =>
      destruct dlt1 as [| k];
      [ cbn [Nat.div ones app] in h2;
        inverts h1 as ha h0rem hb; try lia;
        [ match type of ha with
          | BigF _ _ ?dlt0 _ =>
            destruct dlt0 as [| kk0];
            [ inverts h2;
              destruct (bigF_zero_head_nnf ha hYN) as [x [xs [-> [-> | [-> | ->]]]]]; exact I
            | destruct ((1 + S kk0) / 3) as [| jj0] eqn:hq0; [dlia | inverts h2; exact I] ]
          end
        | pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ hb)
            (append_nonempty_of_right _ _ (proj2 (proj1 (bigFD_bounds _) _ _ _ ha)))); lia ]
      | destruct (S k / 3) as [| jj] eqn:hq; [dlia |];
        inverts h2 as h3;
        exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia)) ]
    end.
  - exact I.
  - pose proof (proj2 (bigFD_noNonlast0F _) _ _ _ h1 (noNonlast0F_tail hN)) as h1N.
    inverts h2 as h3.
    exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia)).
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h1) ltac:(discriminate)) as hge.
    pose proof (proj2 (bigFD_noNonlast0F _) _ _ _ h1 (noNonlast0F_tail hN)) as h1N.
    match type of h2 with
    | BigD1 _ (ones ?q ++ _) _ _ =>
      destruct q as [| kk] eqn:hq; [dlia |];
      inverts h2 as h3;
      exact (ihF _ _ _ _ h3 (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_ones_append _ h1N))) ltac:(lia))
    end.
Qed.

Local Notation "'0inf'" := (@const Sym S0).

(* ========================================================================== *)
(* Tape Helpers, Step-Indexed Safety, and Raw TM Soundness                    *)
(* ========================================================================== *)

Lemma zero_cons_default581 : S0 >> 0inf = 0inf.
Proof.
  exact (eq_sym (const_unfold Sym S0)).
Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app];
  repeat rewrite zero_cons_default581.

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl';
   cbn [Streams.hd Streams.tl];
   repeat rewrite zero_cons_default581;
   (reflexivity || (repeat rewrite <- const_unfold; reflexivity)))
  || finish_progress.

Ltac run_steps :=
  cbn [Str_app Streams.hd Streams.tl];
  repeat rewrite zero_cons_default581;
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

Fixpoint rep1 (n : nat) (s : side) : side :=
  match n with
  | 0 => s
  | S n' => S1 >> rep1 n' s
  end.

Fixpoint encLeft581 (ls : list nat) : side :=
  match ls with
  | [] => 0inf
  | a :: ls' => S1 >> rep1 a (S0 >> encLeft581 ls')
  end.

Fixpoint encRight581 (rs : list Seg) : side :=
  match rs with
  | [] => 0inf
  | (d, false) :: rs' => S1 >> rep1 d (S0 >> encRight581 rs')
  | (d, true) :: rs' => S1 >> rep1 d (S0 >> S0 >> encRight581 rs')
  end.

Definition evalCfg581 (fr bl dl : Q) (c : Cfg581) : Q * tape :=
  match cfg_mode c with
  | FR0 => encLeft581 (cfg_L c) {{fr}}> encRight581 (cfg_R c)
  | BL0 => encLeft581 (cfg_L c) <{{bl}} encRight581 (cfg_R c)
  | DR0 => encLeft581 (cfg_L c) {{dl}}> encRight581 (cfg_R c)
  | DL0 => encLeft581 (cfg_L c) <{{dl}} encRight581 (cfg_R c)
  end.

Lemma encLeft581_bumpL (ls : list nat) :
  encLeft581 (bumpL ls) = S1 >> encLeft581 ls.
Proof.
  destruct ls as [| a ls']; cbn; [rewrite zero_cons_default581 |]; reflexivity.
Qed.

Lemma encRight581_bumpR (rs : list Seg) :
  encRight581 (bumpR rs) = S1 >> encRight581 rs.
Proof.
  destruct rs as [| [d b] rs']; cbn.
  - rewrite zero_cons_default581. reflexivity.
  - destruct b; reflexivity.
Qed.

Tactic Notation "prove_step581" hyp(c) hyp(h) :=
  (
  destruct c as [m ls rs];
  destruct m;
  [ destruct rs as [| [d b] rs2];
    [ idtac | destruct d as [| [| [| d3]]]; destruct b ]
  | destruct ls as [| [| [| [| a3]]] ls2]; try discriminate h;
    [ idtac | idtac | destruct ls2 as [| a' ls3] | idtac ]
  | destruct rs as [| [d b] rs2];
    [ idtac | destruct d as [| [| [| d3]]]; destruct b ]
  | destruct ls as [| a ls2];
    [ idtac | destruct rs as [| [d b] rs2];
      [ destruct a as [| a1]; [destruct ls2 as [| a' ls3] | idtac]
      | (* Expose the right-hand digit before reducing the left encoding. *)
        destruct a as [| a1]; [destruct ls2 as [| a' ls3] | idtac];
        destruct d as [| [| d2]]; destruct b ] ] ];
  cbn [step581 cfg_mode cfg_L cfg_R] in h; try discriminate h;
  inversion h; subst; clear h;
  unfold evalCfg581;
  cbn [cfg_mode cfg_L cfg_R encLeft581 encRight581 rep1];
  repeat rewrite encLeft581_bumpL;
  repeat rewrite encRight581_bumpR;
  run_steps).

Section Soundness.

Context (tm : TM) (interpret : Cfg581 -> Q * tape).

Hypothesis step581_sound : forall c c', step581 c = Some c' ->
  interpret c -[ tm ]->+ interpret c'.

Definition Safe (k : nat) (c : Q * tape) : Prop :=
  forall j, j <= k -> ~ halts_in tm c j.

Arguments Safe _ _ : simpl never.

Lemma Safe_of_stepPlus {k : nat} {c c' : Q * tape}
    (Hstep : c -[ tm ]->+ c')
    (Hsafe : forall k', k' < k -> Safe k' c') :
  Safe k c.
Proof.
  intros j Hj Hhalt.
  destruct (progress_multistep _ _ _ Hstep) as [n Hms].
  destruct (Nat.leb_spec (S n) j) as [Hle | Hlt].
  - assert (Hlt_k : j - S n < k) by lia.
    apply (Hsafe (j - S n) Hlt_k (j - S n) (Nat.le_refl _)).
    exact (preceeds_halt _ _ _ _ _ Hhalt Hms Hle).
  - assert (Hgt : S n > j) by lia.
    exact (exceeds_halt _ _ _ _ _ Hhalt Hgt Hms).
Qed.

Lemma nonhalt_of_forall_safe (c_start : Q * tape)
    (Hinit : c0 -[ tm ]->+ c_start)
    (Hsafe : forall k, Safe k c_start) :
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact (progress_evstep _ _ _ Hinit).
  - intros [k Hhalt].
    exact (Hsafe k k (Nat.le_refl k) Hhalt).
Qed.

Lemma run581_evstep (k : nat) :
  forall c c', run581 k c = Some c' -> interpret c -[ tm ]->* interpret c'.
Proof.
  induction k as [| k' ih]; intros c c' h.
  - cbn in h. inversion h; subst. apply evstep_refl.
  - cbn in h.
    destruct (step581 c) as [c1 |] eqn:hs; [| discriminate h].
    apply progress_evstep.
    eapply progress_evstep_trans.
    + exact (step581_sound c c1 hs).
    + exact (ih c1 c' h).
Qed.

Lemma safe_of_run581_no_halt (k : nat) :
  forall c, (forall n, run581 n c <> None) -> Safe k (interpret c).
Proof.
  induction k as [k ih] using strong_induction.
  intros c hno.
  destruct (step581 c) as [c' |] eqn:hs.
  - eapply Safe_of_stepPlus; [exact (step581_sound c c' hs) |].
    intros k' hk'.
    apply ih; [exact hk' |].
    intro n.
    pose proof (hno (S n)) as hn.
    cbn in hn. rewrite hs in hn. exact hn.
  - exfalso.
    apply (hno 1).
    cbn. rewrite hs. reflexivity.
Qed.

Lemma nonhalt_of_run581_no_halt (c_wall : Cfg581)
    (hreach : c0 -[ tm ]->+ interpret c_wall)
    (hno : forall n, run581 n c_wall <> None) :
  ~ halts tm c0.
Proof.
  exact (nonhalt_of_forall_safe (interpret c_wall) hreach
    (fun k => safe_of_run581_no_halt k c_wall hno)).
Qed.

End Soundness.


(* ========================================================================== *)
(* Master Inversion and Existence Lemmas                                      *)
(* ========================================================================== *)

Lemma bigD1_oneF_inv {s dlt' : nat} {Y R_fin : list Seg}
    (h : BigD1 s ((1, false) :: Y) dlt' R_fin) :
  exists s', s' < s /\ exists dlt0, dlt' = dlt0 + 2 /\ BigF s' (bumpR (bumpR Y)) dlt0 R_fin.
Proof.
  inverts h as h0.
  match type of h0 with
  | BigF ?s' _ ?dlt0 _ =>
    exists s'; split; [lia | exists dlt0; exact (conj eq_refl h0)]
  end.
Qed.

Lemma bigD1_zeroF_inv {s dlt' : nat} {Y R_fin : list Seg}
    (h : BigD1 s ((0, false) :: Y) dlt' R_fin) :
  exists s', s' < s /\ exists dlt0, dlt' = dlt0 + 3 /\ BigF s' Y dlt0 R_fin.
Proof.
  inverts h as h0.
  match type of h0 with
  | BigF ?s' _ ?dlt0 _ =>
    exists s'; split; [lia | exists dlt0; exact (conj eq_refl h0)]
  end.
Qed.

Lemma bigD1_zeroT_inv {s dlt' : nat} {Y R_fin : list Seg}
    (h : BigD1 s ((0, true) :: Y) dlt' R_fin) :
  dlt' = 3 /\ R_fin = bumpR Y.
Proof.
  inverts h. exact (conj eq_refl eq_refl).
Qed.

Lemma bigF_3_inv {s dlt : nat} {Y R_fin : list Seg}
    (h : BigF s ((3, false) :: Y) dlt R_fin) :
  exists s1, s1 < s /\ exists dlt0 R1, BigF s1 Y dlt0 R1 /\
    ( (dlt0 mod 3 = 1 /\ 4 <= dlt0 /\ dlt = 0 /\
        R_fin = (0, true) :: (1, false) :: (1, false) :: ones (dlt0 / 3 - 1) ++ R1) \/
      (dlt0 mod 3 = 2 /\ exists s2, s2 < s /\ exists dlt3, dlt = dlt3 + 2 /\
        BigF s2 ((3, false) :: ones (dlt0 / 3) ++ R1) dlt3 R_fin) \/
      (dlt0 = 0 /\ exists s2, s2 < s /\ exists dlt3, dlt = dlt3 + 3 /\
        BigF s2 (bumpR (bumpR R1)) dlt3 R_fin) \/
      (dlt0 mod 3 = 0 /\ 3 <= dlt0 /\ exists s2, s2 < s /\ exists dlt3, dlt = dlt3 + 3 /\
        BigF s2 ((3, false) :: ones (dlt0 / 3 - 1) ++ R1) dlt3 R_fin) ).
Proof.
  inverts h as h1 hrem h2.
  - destruct (bigD1_zeroF_inv h1) as [s0 [hs0 [dlt0 [-> h0]]]].
    pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ h0)) as hne1.
    assert (hge4 : 4 <= dlt0) by dlia.
    assert (hdiv : (dlt0 + 3) / 3 = S (S (dlt0 / 3 - 1))) by dlia.
    exists s0. split; [lia |].
    exists dlt0. eexists. split; [exact h0 |].
    left. split; [dlia | split; [exact hge4 | split; [reflexivity |]]].
    rewrite hdiv. reflexivity.
  - destruct (bigD1_zeroF_inv h1) as [s0 [hs0 [dlt0 [-> h0]]]].
    assert (hdiv : S ((dlt0 + 3) / 3) = S (S (dlt0 / 3))) by dlia.
    rewrite hdiv in h2.
    destruct (bigD1_1_1_inv h2) as [s2 [hs2 [dlt3 [-> hF2]]]].
    exists s0. split; [lia |].
    exists dlt0. eexists. split; [exact h0 |].
    right. left. split; [dlia |].
    exists s2. split; [lia |].
    exists dlt3. exact (conj eq_refl hF2).
  - destruct (bigD1_zeroF_inv h1) as [s0 [hs0 [dlt0 [-> h0]]]].
    destruct dlt0 as [| m].
    + assert (hdiv : (0 + 3) / 3 = 1) by reflexivity.
      rewrite hdiv in h2.
      destruct (bigD1_oneF_inv h2) as [s2 [hs2 [dlt3 [-> hF2]]]].
      exists s0. split; [lia |].
      exists 0. eexists. split; [exact h0 |].
      right. right. left. split; [reflexivity |].
      exists s2. split; [lia |].
      exists dlt3. split; [lia | exact hF2].
    + assert (hge3 : 3 <= S m) by dlia.
      assert (hdiv : (S m + 3) / 3 = S (S (S m / 3 - 1))) by dlia.
      rewrite hdiv in h2.
      destruct (bigD1_1_1_inv h2) as [s2 [hs2 [dlt3 [-> hF2]]]].
      exists s0. split; [lia |].
      exists (S m). eexists. split; [exact h0 |].
      right. right. right. split; [dlia | split; [exact hge3 |]].
      exists s2. split; [lia |].
      exists dlt3. split; [lia | exact hF2].
Qed.

Lemma bigF_1_inv {s dlt : nat} {Y R_fin : list Seg}
    (h : BigF s ((1, false) :: Y) dlt R_fin) :
  exists s1, s1 < s /\ exists dlt1 R1, BigF s1 Y dlt1 R1 /\
    ( (dlt1 mod 3 = 0 /\ dlt = 0 /\ R_fin = (0, true) :: ones (dlt1 / 3) ++ R1) \/
      (dlt1 mod 3 = 1 /\ 4 <= dlt1 /\ exists s2, s2 < s /\ exists dlt3, dlt = dlt3 + 2 /\
        BigF s2 ((3, false) :: ones (dlt1 / 3 - 1) ++ R1) dlt3 R_fin) \/
      (dlt1 = 2 /\ exists s2, s2 < s /\ exists dlt3, dlt = dlt3 + 3 /\
        BigF s2 (bumpR (bumpR R1)) dlt3 R_fin) \/
      (dlt1 mod 3 = 2 /\ 5 <= dlt1 /\ exists s2, s2 < s /\ exists dlt3, dlt = dlt3 + 3 /\
        BigF s2 ((3, false) :: ones (dlt1 / 3 - 1) ++ R1) dlt3 R_fin) ).
Proof.
  inverts h as h1 hrem h2.
  - match type of h1 with
    | BigF ?k1 _ ?dlt1 ?R1 =>
      assert (hdiv : (1 + dlt1) / 3 = dlt1 / 3) by dlia;
      exists k1; split; [lia |];
      exists dlt1, R1; split; [exact h1 |];
      left; split; [dlia | split; [reflexivity | rewrite hdiv; reflexivity]]
    end.
  - match type of h1 with
    | BigF ?k1 _ ?dlt1 ?R1 =>
      pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ h1)) as hne1;
      assert (hge4 : 4 <= dlt1) by dlia;
      assert (hdiv : S ((1 + dlt1) / 3) = S (S (dlt1 / 3 - 1))) by dlia;
      rewrite hdiv in h2;
      destruct (bigD1_1_1_inv h2) as [s2 [hs2 [dlt3 [-> hF2]]]];
      exists k1; split; [lia |];
      exists dlt1, R1; split; [exact h1 |];
      right; left; split; [dlia | split; [exact hge4 |]];
      exists s2; split; [lia | exists dlt3; exact (conj eq_refl hF2)]
    end.
  - match type of h1 with
    | BigF ?k1 _ ?dlt1 ?R1 =>
      destruct (Nat.eq_dec dlt1 2) as [-> | h2ne];
      [ change ((1 + 2) / 3) with 1 in h2;
        destruct (bigD1_oneF_inv h2) as [s2 [hs2 [dlt3 [-> hF2]]]];
        exists k1; split; [lia |];
        exists 2, R1; split; [exact h1 |];
        right; right; left; split; [reflexivity |];
        exists s2; split; [lia | exists dlt3; split; [lia | exact hF2]]
      | assert (hge5 : 5 <= dlt1) by dlia;
        assert (hdiv : (1 + dlt1) / 3 = S (S (dlt1 / 3 - 1))) by dlia;
        rewrite hdiv in h2;
        destruct (bigD1_1_1_inv h2) as [s2 [hs2 [dlt3 [-> hF2]]]];
        exists k1; split; [lia |];
        exists dlt1, R1; split; [exact h1 |];
        right; right; right; split; [dlia | split; [exact hge5 |]];
        exists s2; split; [lia | exists dlt3; split; [lia | exact hF2]] ]
    end.
Qed.

(* The continuation sees only how many 1 blocks were put back on
   the right. One 1 bumps the following block, two make a leading 3.
   These are independent of which first call produced the increment. *)
Definition BurstD1 (s q : nat) (Y : list Seg) (d : nat) (Z : list Seg) : Prop :=
  match q with
  | 0 => exists k, k < s /\ BigD1 k Y d Z
  | 1 => exists k, k < s /\ exists e, d = e + 2 /\ BigF k (bumpR (bumpR Y)) e Z
  | S (S r) => exists k, k < s /\ exists e, d = e + 2 /\ BigF k ((3,false)::ones r ++ Y) e Z
  end.

Lemma burstD1_inv {s k q Y d Z} (hk : k < s) (h : BigD1 k (ones q ++ Y) d Z) :
  BurstD1 s q Y d Z.
Proof.
  destruct q as [|[|q]]; cbn [BurstD1 ones app] in *.
  - exists k; auto.
  - destruct (bigD1_oneF_inv h) as [p [? [e [? ?]]]]. exists p; split; [lia | eauto].
  - destruct (bigD1_1_1_inv h) as [p [? [e [? ?]]]]. exists p; split; [lia | eauto].
Qed.

Definition FrontAfter s v Y d Z : Prop :=
  (v mod 3 = 1 /\ 4 <= v /\ d = 0 /\ Z = (0, true) :: ones (v / 3) ++ Y) \/
  (v = 2 /\ exists k, k < s /\ exists e, d = e + 2 /\ BigF k (bumpR (bumpR Y)) e Z) \/
  (v mod 3 = 2 /\ 5 <= v /\ exists k, k < s /\ exists e, d = e + 2 /\
    BigF k ((3, false) :: ones (v / 3 - 1) ++ Y) e Z) \/
  (v = 0 /\ exists k, k < s /\ exists e, d = e + 1 /\ BigD1 k Y e Z) \/
  (v = 3 /\ exists k, k < s /\ exists e, d = e + 3 /\ BigF k (bumpR (bumpR Y)) e Z) \/
  (v mod 3 = 0 /\ 6 <= v /\ exists k, k < s /\ exists e, d = e + 3 /\
    BigF k ((3, false) :: ones (v / 3 - 2) ++ Y) e Z).

Lemma frontAfter_two {s k v Y d Z}
  (hk : k < s) (hv : v mod 3 = 2)
  (h : BigD1 k (ones (S (v / 3)) ++ Y) d Z) : FrontAfter s v Y d Z.
Proof.
  assert (H := burstD1_inv hk h).
  destruct (Nat.eq_dec v 2) as [-> | Hne].
  - right; left. exact (conj eq_refl H).
  - assert (Hq : S (v / 3) = S (S (v / 3 - 1))) by dlia.
    rewrite Hq in H. right; right; left. split; [exact hv|split; [dlia|exact H]].
Qed.

Lemma frontAfter_zero {s k v Y d Z}
  (hk : k < s) (hv : v mod 3 = 0)
  (h : BigD1 k (ones (v / 3) ++ Y) d Z) : FrontAfter s v Y (d + 1) Z.
Proof.
  assert (H := burstD1_inv hk h).
  do 3 right.
  destruct (Nat.eq_dec v 0) as [-> | H0].
  - left. destruct H as [p [Hp Hd]]. split; [reflexivity| eauto].
  - right; destruct (Nat.eq_dec v 3) as [-> | H3].
    + left. destruct H as [p [Hp [e [-> HF]]]].
      split; [reflexivity|]. exists p; split; [lia | exists e; split; [lia | exact HF]].
    + assert (Hq : v / 3 = S (S (v / 3 - 2))) by dlia.
      rewrite Hq in H. destruct H as [p [Hp [e [-> HF]]]].
      right; split; [exact hv | split; [dlia |]].
      exists p; split; [lia | exists e; split; [lia | exact HF]].
Qed.

Lemma bigF_two_inv {s dlt b Y Z} (h : BigF s ((2,b) :: Y) dlt Z) :
  exists k, k < s /\ exists v X,
    BigF k (if b then (1,false)::Y else bumpR (bumpR Y)) v X /\
    FrontAfter s v X dlt Z.
Proof.
  destruct b; inverts h as h1 hr h2.
  all: lazymatch type of h1 with BigF ?k _ ?v ?X =>
    exists k; split; [lia | exists v, X; split; [exact h1|]] end.
  all: first [
    lazymatch goal with |- FrontAfter ?s _ _ _ _ =>
      lazymatch type of h2 with BigD1 ?k _ _ _ =>
        let Hk := fresh "Hk" in assert (Hk : k < s) by lia;
        first [exact (frontAfter_two Hk hr h2) | exact (frontAfter_zero Hk hr h2)]
      end
    end
  | left; pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ h1));
    split; [exact hr | split; [dlia | split; reflexivity]]].
Qed.

Lemma bigF_2_inv {s dlt : nat} {Y R_fin : list Seg}
    (h : BigF s ((2, false) :: Y) dlt R_fin) :
  exists s1, s1 < s /\ exists dlt1 R1, BigF s1 (bumpR (bumpR Y)) dlt1 R1 /\
    FrontAfter s dlt1 R1 dlt R_fin.
Proof. exact (bigF_two_inv h). Qed.

Lemma bigF_2s_inv {s dlt : nat} {Y R_fin : list Seg}
    (h : BigF s ((2, true) :: Y) dlt R_fin) :
  exists s1, s1 < s /\ exists dlt1 R1, BigF s1 ((1,false)::Y) dlt1 R1 /\
    FrontAfter s dlt1 R1 dlt R_fin.
Proof. exact (bigF_two_inv h). Qed.


Lemma bigF_3s_inv {s dlt : nat} {Y R_fin : list Seg}
    (h : BigF s ((3, true) :: Y) dlt R_fin) :
  exists s', s' < s /\ exists dlt0, dlt = dlt0 + 3 /\ BigF s' (bumpR (bumpR (bumpR Y))) dlt0 R_fin.
Proof.
  inverts h as h1 hrem h2.
  - destruct (bigD1_zeroT_inv h1) as [-> ->]; dlia.
  - destruct (bigD1_zeroT_inv h1) as [-> ->]; dlia.
  - destruct (bigD1_zeroT_inv h1) as [-> ->].
    destruct (bigD1_oneF_inv h2) as [s' [hs' [dlt0 [-> hF']]]].
    exists s'. split; [lia | exists dlt0; split; [lia | exact hF']].
Qed.

Lemma bigF_3_1_0s_inv {s dlt : nat} {Y R_fin : list Seg}
    (h : BigF s ((3, false) :: (1, false) :: (0, true) :: Y) dlt R_fin) :
  exists s', s' < s /\ exists dlt0, dlt = dlt0 + 3 /\ BigF s' ((2, true) :: (1, false) :: Y) dlt0 R_fin.
Proof.
  assert (h10 : BigF 1 ((1, false) :: (0, true) :: Y) 0 ((0, true) :: (1, false) :: Y))
    by exact (BF_oneF_rem1 (BF_zeroT Y) eq_refl).
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [hF1 hcases]]]]].
  destruct (proj1 (bigFD_det _) _ _ _ _ _ _ hF1 h10) as [-> ->].
  destruct hcases as [[? [hge4 _]] | [[hrem _] | [[? [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [hge3 _]]]]]; try dlia.
  exists s2. split; [exact hs2 | exists dlt3; exact (conj eq_refl hF2)].
Qed.

Lemma bigF_3_1_1_0s_exists (Y : list Seg) :
  BigF 7 ((3, false) :: (1, false) :: (1, false) :: (0, true) :: Y) 7 ((2, false) :: (1, false) :: Y).
Proof.
  assert (h1 : BigD1 3 ((0, false) :: (1, false) :: (1, false) :: (0, true) :: Y) 3
    ((0, true) :: (0, true) :: (1, false) :: Y))
    by exact (BD_zeroF (BF_oneF_rem1 (BF_oneF_rem1 (BF_zeroT Y) eq_refl) eq_refl)).
  exact (BF_ge3_rem0 h1 eq_refl
    (BD_oneF (Y := (0, true) :: (0, true) :: (1, false) :: Y)
      (bigF_2s_0s_exists ((1, false) :: Y)))).
Qed.

Lemma bigF_2s_1_0s_exists (Y : list Seg) :
  BigF 3 ((2, true) :: (1, false) :: (0, true) :: Y) 4 ((1, true) :: (1, false) :: Y).
Proof.
  exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneF_rem1 (BF_zeroT Y) eq_refl) eq_refl) eq_refl
    (BD_zeroT ((0, true) :: (1, false) :: Y))).
Qed.

Lemma bigF_2s_0_exists :
  BigF 2 ((2, true) :: [(0, false)]) 4 [(2, false)].
Proof.
  exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_zeroF []) eq_refl) eq_refl (BD_zeroT [(1, false)])).
Qed.

Lemma bigF_2_nil_exists :
  exists s, BigF s [(2, false)] 4 [(1, false)].
Proof.
  eexists.
  exact (BF_twoF_rem0 (Y := []) (BF_oneF_rem1 BF_nil eq_refl) eq_refl (BD_zeroT [(0, false)])).
Qed.

Lemma bigF_3_nil_exists :
  exists s, BigF s [(3, false)] 7 [(1, false)].
Proof.
  destruct bigF_2_nil_exists as [s2 h2].
  eexists.
  exact (BF_ge3_rem0 (BD_zeroF BF_nil) eq_refl (BD_oneF (Y := [(0, false)]) h2)).
Qed.

Lemma bigF_2_1s_0_exists :
  exists s, BigF s [(2, false); (1, true); (0, false)] 0
    [(0, true); (1, false); (1, false); (1, false); (1, false)].
Proof.
  destruct bigF_3_nil_exists as [s3 h3].
  assert (h3s : BigF (0 + (s3 + 1) + 1) (bumpR (bumpR [(1, true); (0, false)])) 10 [(1, false)])
    by exact (BF_ge3_rem0 (BD_zeroT [(0, false)]) eq_refl (BD_oneF (Y := [(1, false)]) h3)).
  eexists.
  exact (BF_twoF_rem1 (Y := [(1, true); (0, false)]) h3s eq_refl).
Qed.

Lemma bigF_3_zero_prefix {s : nat} {Y R_fin : list Seg}
    (h : BigF s ((3, false) :: Y) 0 R_fin) :
  exists Z, R_fin = (0, true) :: (1, false) :: (1, false) :: Z.
Proof.
  destruct (bigF_3_inv h) as [? [? [? [? [? hcases]]]]].
  destruct hcases as [[? [? [? ->]]] | [[? [? [? [? [hEq _]]]]] | [[? [? [? [? [hEq _]]]]] | [? [? [? [? [? [hEq _]]]]]]]]]; try lia.
  eexists. reflexivity.
Qed.

Lemma bigD1_four_head {s d : nat} {b : bool} {Y R_fin : list Seg}
    (h : BigD1 s ((d, b) :: Y) 4 R_fin) :
  exists Z, R_fin = (0, true) :: Z.
Proof.
  inverts h as h0 heq; try lia.
  - match type of h0 with BigF _ _ ?dlt _ => assert (dlt = 1) by lia; subst dlt end.
    contradiction (proj1 (proj1 (bigFD_bounds _) _ _ _ h0) eq_refl).
  - match type of h0 with BigF _ _ ?dlt _ => assert (dlt = 2) by lia; subst dlt end.
    destruct (bigF_two_head h0) as [Z hZ].
    exists ((1, false) :: Z). exact hZ.
  - match type of h0 with BigF _ _ ?dlt _ => assert (dlt = 2) by lia; subst dlt end.
    destruct (bigF_two_head h0) as [Z hZ].
    exists ((1, false) :: Z). exact hZ.
  - match type of h0 with BigD1 _ _ ?dlt0 _ => assert (dlt0 = 2) by lia; subst dlt0 end.
    inverts h0 as ha heq2; try lia.
    + match type of ha with
      | BigF _ (bumpR (bumpR ?Y0)) ?dlta _ =>
        assert (dlta = 0) by lia; subst dlta;
        destruct Y0 as [| [d1 b1] xs];
        [ exact (bigF_oneF_zero_head ha)
        | destruct (bigF_ge2_zero_head ha) as [Z hZ]; exists ((1, false) :: Z); exact hZ ]
      end.
    + match type of ha with BigF _ _ ?dlta _ => assert (dlta = 0) by lia; subst dlta end.
      exact (bigF_oneF_zero_head ha).
    + match type of ha with BigD1 _ _ ?dlta _ => assert (dlta = 0) by lia; subst dlta end.
      pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ ha) ltac:(discriminate)). lia.
Qed.

Lemma bigF_ge3_zero_prefix {s d : nat} {b : bool} {Y R_fin : list Seg}
    (h : BigF s ((S (S (S d)), b) :: Y) 0 R_fin) :
  (exists Z, R_fin = (0, true) :: (1, false) :: (1, false) :: Z) \/
  (exists Z, R_fin = (0, true) :: (1, false) :: (0, true) :: Z).
Proof.
  inverts h as h1 hrem h2 heq; try lia.
  - match type of h1 with
    | BigD1 _ _ ?dlt1 ?R1 =>
      pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h1) ltac:(discriminate)) as hge2;
      destruct (Nat.eq_dec dlt1 4) as [-> | h4ne];
      [ destruct (bigD1_four_head h1) as [Z ->];
        right; exists Z; reflexivity
      | assert (hge7 : 7 <= dlt1) by dlia;
        assert (hdiv : dlt1 / 3 = S (S (dlt1 / 3 - 2))) by dlia;
        rewrite hdiv;
        left; exists (ones (dlt1 / 3 - 2) ++ R1); reflexivity ]
    end.
  - pose proof (proj1 (proj2 (bigFD_bounds _) _ _ _ h2)
      (append_nonempty_of_right _ _ (proj2 (proj2 (bigFD_bounds _) _ _ _ h1)))).
    lia.
Qed.

Lemma bigF_ne_one {s : nat} {rs R_fin : list Seg} (h : BigF s rs 1 R_fin) : False.
Proof.
  exact (proj1 (proj1 (bigFD_bounds s) rs 1 R_fin h) eq_refl).
Qed.

Lemma bigD1_ge2_of_ne_nil {s : nat} {rs R_fin : list Seg} {dlt : nat}
    (h : BigD1 s rs dlt R_fin) (hne : rs <> []) : 2 <= dlt.
Proof.
  exact (proj1 (proj2 (bigFD_bounds s) rs dlt R_fin h) hne).
Qed.

Lemma bigF_out_ne_nil {s : nat} {rs R_fin : list Seg} {dlt : nat}
    (h : BigF s rs dlt R_fin) : R_fin <> [].
Proof.
  exact (proj2 (proj1 (bigFD_bounds s) rs dlt R_fin h)).
Qed.

Lemma bigD1_out_ne_nil {s : nat} {rs R_fin : list Seg} {dlt : nat}
    (h : BigD1 s rs dlt R_fin) : R_fin <> [].
Proof.
  exact (proj2 (proj2 (bigFD_bounds s) rs dlt R_fin h)).
Qed.

Lemma bumpR_head_ne_zeroT (rs Z : list Seg) :
  bumpR rs <> (0, true) :: Z.
Proof.
  destruct rs as [| [d b] xs]; discriminate.
Qed.

Lemma bigF_zero_oneF_head {s : nat} {Y Z : list Seg}
    (h : BigF s Y 0 ((1, false) :: Z)) (hnnf : NoNonlast0F Y) :
  (Y = [(0, false)] /\ Z = []) \/ Y = (0, true) :: Z.
Proof.
  remember 0 as dlt eqn:hdlt.
  remember ((1, false) :: Z) as R_fin eqn:hR.
  inverts h as h1 hrem h2; try lia; try discriminate hR.
  - match type of hnnf with
    | NoNonlast0F ((0, false) :: ?Y0) =>
      destruct Y0 as [| [d b] xs]; [| contradiction hnnf];
      cbn in h1; inversion h1; subst;
      left; exact (conj eq_refl eq_refl)
    end.
  - right. reflexivity.
  - pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))). lia.
  - pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))). lia.
  - pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))). lia.
  - pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigD1_out_ne_nil h1))). lia.
Qed.

Lemma bigF_2s_0s_full_exists (W : list Seg) :
  BigF 2 ((2, true) :: (0, true) :: W) 4 ((2, false) :: W).
Proof.
  exact (bigF_2s_0s_exists W).
Qed.

Lemma bigF_2s_1_1_0s_exists (U : list Seg) :
  BigF 4 ((2, true) :: (1, false) :: (1, false) :: (0, true) :: U) 4
    ((1, true) :: (0, true) :: (1, false) :: U).
Proof.
  assert (h0 : BigF 0 ((0, true) :: U) 0 ((1, false) :: U)) by exact (BF_zeroT U).
  assert (h1 : BigF 1 ((1, false) :: (0, true) :: U) 0 ((0, true) :: (1, false) :: U))
    by exact (BF_oneF_rem1 h0 eq_refl).
  assert (h2 : BigF 2 ((1, false) :: (1, false) :: (0, true) :: U) 0
    ((0, true) :: (0, true) :: (1, false) :: U))
    by exact (BF_oneF_rem1 h1 eq_refl).
  assert (h3 : BigF 3 ((1, false) :: (1, false) :: (1, false) :: (0, true) :: U) 0
    ((0, true) :: (0, true) :: (0, true) :: (1, false) :: U))
    by exact (BF_oneF_rem1 h2 eq_refl).
  exact (BF_twoT_rem0 h3 eq_refl (BD_zeroT ((0, true) :: (0, true) :: (1, false) :: U))).
Qed.

Lemma bigF_zero_head_3 {s : nat} {Y R1 : list Seg}
    (h : BigF s Y 0 R1) (hN : NoNonlast0F Y) :
  R1 = [(0, false)] \/
  (exists Z, R1 = (0, true) :: Z) \/
  (exists Z, R1 = (1, false) :: Z).
Proof.
  pose proof (proj1 (bigFD_noNonlast0F _) _ _ _ h hN) as hN1.
  destruct (bigF_zero_head_nnf h hN) as [x [xs [-> [-> | [-> | ->]]]]].
  - destruct xs as [| y ys]; [left; reflexivity | contradiction hN1].
  - right. left. exists xs. reflexivity.
  - right. right. exists xs. reflexivity.
Qed.

Lemma bigD1_two_head_nnf {s d : nat} {b : bool} {Y R1 : list Seg}
    (h : BigD1 s ((d, b) :: Y) 2 R1) (hNY : NoNonlast0F Y) :
  R1 = [(0, true); (0, false)] \/
  (exists Z, R1 = (0, true) :: (0, true) :: Z) \/
  (exists Z, R1 = (0, true) :: (1, false) :: Z).
Proof.
  inverts h as h0 heq; try lia.
  - match type of h0 with BigF _ _ ?dlt0 _ => assert (dlt0 = 0) by lia; subst dlt0 end.
    destruct Y as [| [d' b'] xs].
    + cbn in h0. inverts h0 as h1 hrem h2 heq2; try lia.
      * inverts h1. left. reflexivity.
      * pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))). lia.
    + destruct (bigF_ge2_zero_head h0) as [Z hZ].
      right. right. exists Z. exact hZ.
  - match type of h0 with BigF _ _ ?dlt0 _ => assert (dlt0 = 0) by lia; subst dlt0 end.
    inverts h0 as h1 hrem h2 heq2; try lia.
    + match type of h1 with
      | BigF _ _ ?dlt0 ?R0 =>
        destruct (Nat.eq_dec dlt0 0) as [-> | h0ne];
        [ destruct (bigF_zero_head_3 h1 hNY) as [-> | [[Z ->] | [Z ->]]];
          [ left; reflexivity
          | right; left; exists Z; reflexivity
          | right; right; exists Z; reflexivity ]
        | assert (hq : 1 <= (1 + dlt0) / 3) by dlia;
          destruct (ones_pos_cons hq R0) as [Z hZ];
          right; right; exists Z; cbn [app]; rewrite hZ; reflexivity ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))). lia.
  - match type of h0 with BigD1 _ _ ?dlt0 _ => assert (dlt0 = 0) by lia; subst dlt0 end.
    pose proof (bigD1_ge2_of_ne_nil h0 ltac:(discriminate)). lia.
Qed.

(* ========================================================================== *)
(* Syntactic Predicates and Conversion Lemmas                                 *)
(* ========================================================================== *)

Definition Head0s11 (rs : list Seg) : Prop :=
  exists Z, rs = (0, true) :: (1, false) :: (1, false) :: Z.

Definition Head0s111 (rs : list Seg) : Prop :=
  exists Z, rs = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z.

Definition GoodZero111Head (Y : list Seg) : Prop :=
  (forall Z, Y <> (0, true) :: Z) \/ (exists Z, Y = (0, true) :: (1, false) :: Z).

Definition GoodF2U (U : list Seg) : Prop :=
  (exists W, U = (1, false) :: W) \/
  (exists W, U = (1, true) :: W) \/
  (exists W, U = (2, false) :: W) \/
  Head0s11 U.

Lemma goodF2U_to_goodZero111Head {U : list Seg} (h : GoodF2U U) : GoodZero111Head U.
Proof.
  destruct h as [[W ->] | [[W ->] | [[W ->] | [Z ->]]]].
  - left. intros ? hEq; discriminate hEq.
  - left. intros ? hEq; discriminate hEq.
  - left. intros ? hEq; discriminate hEq.
  - right. exists ((1, false) :: Z). reflexivity.
Qed.

Definition Good1 (rs : list Seg) : Prop :=
  rs = [(1, true); (0, true); (0, false)] \/
  (exists Z, rs = (1, true) :: (0, true) :: (0, true) :: Z) \/
  rs = [(1, true); (0, true); (1, false)] \/
  rs = [(1, true); (0, true); (1, false); (0, false)] \/
  (exists Z, rs = (1, true) :: (0, true) :: (1, false) :: (0, true) :: Z) \/
  (exists Z, rs = (1, true) :: (0, true) :: (1, false) :: (1, false) :: Z) \/
  (exists Z, rs = (1, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z) \/
  (exists Z, rs = (1, true) :: (1, false) :: (1, false) :: (1, false) :: Z /\ GoodF2U Z) \/
  (exists Z, rs = (2, false) :: (1, false) :: (1, false) :: Z).

Inductive Good2 : list Seg -> Prop :=
  | G2_of_good1 {rs : list Seg} : Good1 rs -> Good2 rs
  | G2_c_2_0 : Good2 [(2, false); (0, false)]
  | G2_c_2_1 : Good2 [(2, false); (1, false)]
  | G2_c_2_1_2 : Good2 [(2, false); (1, false); (2, false)]
  | G2_c_2_0s (Z : list Seg) : Good2 ((2, false) :: (0, true) :: Z)
  | G2_c_2_1s_0 : Good2 [(2, false); (1, true); (0, false)]
  | G2_c_2_1s_0s (Z : list Seg) : Good2 ((2, false) :: (1, true) :: (0, true) :: Z)
  | G2_c_2_1s_1 : Good2 [(2, false); (1, true); (1, false)]
  | G2_c_2_1s_1_0 : Good2 [(2, false); (1, true); (1, false); (0, false)]
  | G2_c_2_1s_1_0s (Z : list Seg) : Good2 ((2, false) :: (1, true) :: (1, false) :: (0, true) :: Z)
  | G2_c_2_1s_1_1 (Z : list Seg) : Good2 ((2, false) :: (1, true) :: (1, false) :: (1, false) :: Z)
  | G2_c_2_1_0s (Z : list Seg) : Good2 ((2, false) :: (1, false) :: (0, true) :: Z)
  | G2_c_2_1_1 (Z : list Seg) : Good2 ((2, false) :: (1, false) :: (1, false) :: Z)
  | G2_c_2_1_1s (Z : list Seg) : Good2 ((2, false) :: (1, false) :: (1, true) :: Z)
  | G2_c_2_2_0s_1_1 (Z : list Seg) : Good2 ((2, false) :: (2, false) :: (0, true) :: (1, false) :: (1, false) :: Z)
  | G2_c_2_2_1_0s_1_1 (Z : list Seg) : Good2 ((2, false) :: (2, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z)
  | G2_c_2_2_1_1_gf {Z : list Seg} : GoodF2U Z -> Good2 ((2, false) :: (2, false) :: (1, false) :: (1, false) :: Z)
  | G2_step_21 {G : list Seg} : Good2 G -> Good2 ((2, false) :: (1, false) :: G).

Definition GoodStrongHead (U : list Seg) : Prop :=
  U = [] \/
  U = [(0, false)] \/
  (exists W, U = (0, true) :: W /\ (W = [] \/ Good2 ((2, false) :: W))) \/
  (exists W, U = (1, false) :: W) \/
  (exists W, U = (1, true) :: W) \/
  Good2 U.

Definition Strong2 (G : list Seg) : Prop :=
  Good2 G /\ (forall U, G = (2, false) :: (0, true) :: U -> GoodStrongHead U).

Definition GoodTail (Z : list Seg) : Prop :=
  Good2 Z \/ Head0s11 Z \/
  (exists W, Z = (1, false) :: W /\ (Good2 W \/ Head0s11 W)) \/
  (exists W, Z = (1, false) :: (1, false) :: W).

Definition Good1Safe (rs : list Seg) : Prop :=
  Good1 rs /\ (forall Z, rs = (2, false) :: (1, false) :: (1, false) :: Z -> GoodTail Z).

Definition SafeU (U : list Seg) : Prop :=
  (exists Z, U = (1, false) :: (1, false) :: (1, false) :: Z) \/
  (exists Z, U = (1, false) :: (1, false) :: Z /\ (Good2 Z \/ Head0s11 Z)) \/
  (exists Z, U = (1, false) :: Z /\ (Good2 Z \/ Head0s11 Z)) \/
  Head0s111 U \/
  Good1Safe U.

Definition Safe0s (rs : list Seg) : Prop :=
  exists U, rs = (0, true) :: (1, false) :: (1, false) :: U /\ SafeU U.

Inductive Good4Out : list Seg -> Prop :=
  | G4_two_one_one : Good4Out [(2, false); (1, false); (1, false)]
  | G4_of_1_1_1s (Z : list Seg) : Good4Out ((2, false) :: (1, false) :: (1, false) :: (1, false) :: (1, true) :: Z)
  | G4_of_safeU {U : list Seg} : SafeU U -> Good4Out ((2, false) :: (1, false) :: U)
  | G4_step_21 {Z : list Seg} : Good4Out Z -> Good4Out ((2, false) :: (1, false) :: Z).

Definition Zero111 (rs : list Seg) : Prop :=
  rs = [(0, true); (0, true); (0, true); (0, false)] \/
  (exists Z, rs = (0, true) :: (0, true) :: (0, true) :: (0, true) :: Z) \/
  (exists Z, rs = (0, true) :: (0, true) :: (0, true) :: (1, false) :: Z) \/
  (exists Z, rs = (0, true) :: (0, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z) \/
  (exists Z, rs = (0, true) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z /\ GoodF2U Z) \/
  (exists Z, rs = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z /\ GoodTail Z).

Definition TightZero111 (rs : list Seg) : Prop :=
  Zero111 rs /\
  (forall Z, rs = (0, true) :: (0, true) :: (0, true) :: (1, false) :: Z ->
    Z = [] \/ (exists W, Z = (0, true) :: W) \/ (exists W, Z = (1, false) :: W)).

Lemma head0s111_to_head0s11 {rs : list Seg} (h : Head0s111 rs) : Head0s11 rs.
Proof.
  destruct h as [Z ->]. exists ((1, false) :: Z). reflexivity.
Qed.

Lemma safe0s_to_head0s11 {rs : list Seg} (h : Safe0s rs) : Head0s11 rs.
Proof.
  destruct h as [U [-> _]]. exists U. reflexivity.
Qed.

Lemma safeU_to_goodF2U {U : list Seg} (h : SafeU U) : GoodF2U U.
Proof.
  destruct h as [[Z ->] | [[Z [-> _]] | [[Z [-> _]] | [[Z ->] | [hG1 _]]]]].
  - left. eexists. reflexivity.
  - left. eexists. reflexivity.
  - left. eexists. reflexivity.
  - right. right. right. exists ((1, false) :: Z). reflexivity.
  - destruct hG1 as [-> | [[Z ->] | [-> | [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z ->]]]]]]]]].
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. left. eexists. reflexivity.
    + right. right. left. eexists. reflexivity.
Qed.

Lemma good1_to_good2 {rs : list Seg} (h : Good1 rs) : Good2 rs.
Proof. exact (G2_of_good1 h). Qed.

Lemma good1_to_strong2 {rs : list Seg} (h : Good1 rs) : Strong2 rs.
Proof.
  split; [exact (G2_of_good1 h) |].
  intros W hEq.
  destruct h as [-> | [[Z ->] | [-> | [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z ->]]]]]]]]];
    discriminate hEq.
Qed.

Lemma good1Safe_to_good2 {rs : list Seg} (h : Good1Safe rs) : Good2 rs.
Proof. exact (G2_of_good1 (proj1 h)). Qed.

Lemma good1Safe_to_strong2 {rs : list Seg} (h : Good1Safe rs) : Strong2 rs.
Proof. exact (good1_to_strong2 (proj1 h)). Qed.

Lemma good2_of_2_0s (Z : list Seg) : Good2 ((2, false) :: (0, true) :: Z).
Proof. exact (G2_c_2_0s Z). Qed.

Lemma good2_of_2_1_1 (Z : list Seg) : Good2 ((2, false) :: (1, false) :: (1, false) :: Z).
Proof. exact (G2_c_2_1_1 Z). Qed.

Lemma strong2_of_2_1_1 (Z : list Seg) : Strong2 ((2, false) :: (1, false) :: (1, false) :: Z).
Proof.
  split; [exact (G2_c_2_1_1 Z) | intros ? hEq; discriminate hEq].
Qed.

Lemma good2_of_2_1_0s (Z : list Seg) : Good2 ((2, false) :: (1, false) :: (0, true) :: Z).
Proof. exact (G2_c_2_1_0s Z). Qed.

Lemma good2_to_goodF2U {G : list Seg} (hG : Good2 G) : GoodF2U G.
Proof.
  destruct hG.
  - destruct H as [-> | [[Z ->] | [-> | [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z ->]]]]]]]]];
      try (right; left; eexists; reflexivity).
    right. right. left. eexists. reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
Qed.

Lemma goodTail_to_goodF2U {Z : list Seg} (hT : GoodTail Z) : GoodF2U Z.
Proof.
  destruct hT as [hG | [hH | [[W [-> _]] | [W ->]]]].
  - exact (good2_to_goodF2U hG).
  - right; right; right; exact hH.
  - left; exists W; reflexivity.
  - left; exists ((1, false) :: W); reflexivity.
Qed.

Lemma strong2_of_2_0s {U : list Seg} (hU : GoodStrongHead U) :
  Strong2 ((2, false) :: (0, true) :: U).
Proof.
  split; [exact (G2_c_2_0s U) | intros U' hEq; inversion hEq; subst; exact hU].
Qed.

Lemma strong2_of_2_1_0s (Z : list Seg) : Strong2 ((2, false) :: (1, false) :: (0, true) :: Z).
Proof. split; [exact (G2_c_2_1_0s Z) | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_step_21 {G : list Seg} (hG : Good2 G) :
  Strong2 ((2, false) :: (1, false) :: G).
Proof. split; [exact (G2_step_21 hG) | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_1s_0 : Strong2 [(2, false); (1, true); (0, false)].
Proof. split; [exact G2_c_2_1s_0 | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_1s_0s (Z : list Seg) : Strong2 ((2, false) :: (1, true) :: (0, true) :: Z).
Proof. split; [exact (G2_c_2_1s_0s Z) | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_1s_1 : Strong2 [(2, false); (1, true); (1, false)].
Proof. split; [exact G2_c_2_1s_1 | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_1s_1_0 : Strong2 [(2, false); (1, true); (1, false); (0, false)].
Proof. split; [exact G2_c_2_1s_1_0 | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_1s_1_0s (Z : list Seg) :
  Strong2 ((2, false) :: (1, true) :: (1, false) :: (0, true) :: Z).
Proof. split; [exact (G2_c_2_1s_1_0s Z) | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_1s_1_1 (Z : list Seg) :
  Strong2 ((2, false) :: (1, true) :: (1, false) :: (1, false) :: Z).
Proof. split; [exact (G2_c_2_1s_1_1 Z) | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_2_1_0s_1_1 (Z : list Seg) :
  Strong2 ((2, false) :: (2, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z).
Proof. split; [exact (G2_c_2_2_1_0s_1_1 Z) | intros ? hEq; discriminate hEq]. Qed.

Lemma strong2_of_2_2_1_1_gf {Z : list Seg} (hZ : GoodF2U Z) :
  Strong2 ((2, false) :: (2, false) :: (1, false) :: (1, false) :: Z).
Proof. split; [exact (G2_c_2_2_1_1_gf hZ) | intros ? hEq; discriminate hEq]. Qed.

Lemma good2_ne_zeroT {G : list Seg} (h : Good2 G) (Z : list Seg) : G <> (0, true) :: Z.
Proof.
  destruct h; try (intro hEq; discriminate hEq).
  destruct H as [-> | [[W ->] | [-> | [-> | [[W ->] | [[W ->] | [[W ->] | [[W [-> _]] | [W ->]]]]]]]]];
    intro hEq; discriminate hEq.
Qed.

Lemma goodTail_ones_append (k : nat) {rs : list Seg} (h : Good2 rs \/ Head0s11 rs) :
  GoodTail (ones k ++ rs).
Proof.
  destruct k as [| [| k'']].
  - destruct h as [hG | hH]; [left; exact hG | right; left; exact hH].
  - right; right; left; exists rs; exact (conj eq_refl h).
  - right; right; right; exists (ones k'' ++ rs); reflexivity.
Qed.

Lemma good1Safe_of_1s_0s_0 : Good1Safe [(1, true); (0, true); (0, false)].
Proof. split; [left; reflexivity | intros ? h; discriminate h]. Qed.

Lemma good1Safe_of_1s_0s_0s (Z : list Seg) : Good1Safe ((1, true) :: (0, true) :: (0, true) :: Z).
Proof. split; [right; left; exists Z; reflexivity | intros ? h; discriminate h]. Qed.

Lemma good1Safe_of_1s_0s_1_nil : Good1Safe [(1, true); (0, true); (1, false)].
Proof. split; [right; right; left; reflexivity | intros ? h; discriminate h]. Qed.

Lemma good1Safe_of_1s_0s_1_0s (Z : list Seg) :
  Good1Safe ((1, true) :: (0, true) :: (1, false) :: (0, true) :: Z).
Proof. split; [right; right; right; right; left; exists Z; reflexivity | intros ? h; discriminate h]. Qed.

Lemma good1Safe_of_1s_0s_1_1 (Z : list Seg) :
  Good1Safe ((1, true) :: (0, true) :: (1, false) :: (1, false) :: Z).
Proof. split; [right; right; right; right; right; left; exists Z; reflexivity | intros ? h; discriminate h]. Qed.

Lemma good1Safe_of_1s_1_1_0s_1_1 (Z : list Seg) :
  Good1Safe ((1, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z).
Proof. split; [right; right; right; right; right; right; left; exists Z; reflexivity | intros ? h; discriminate h]. Qed.

Lemma good1Safe_of_1s_1_1_1 {Z : list Seg} (hZ : GoodF2U Z) :
  Good1Safe ((1, true) :: (1, false) :: (1, false) :: (1, false) :: Z).
Proof.
  split; [right; right; right; right; right; right; right; left; exists Z; exact (conj eq_refl hZ) |
    intros ? h; discriminate h].
Qed.

Lemma good1Safe_of_2_1_1 {Z : list Seg} (hT : GoodTail Z) :
  Good1Safe ((2, false) :: (1, false) :: (1, false) :: Z).
Proof.
  split; [right; right; right; right; right; right; right; right; exists Z; reflexivity |].
  intros Z' h; inversion h; subst; exact hT.
Qed.

(* ========================================================================== *)
(* Master Strong-Induction Invariant Record InvAt (m : nat)                   *)
(* ========================================================================== *)

Record InvAt (m : nat) : Prop := mkInvAt {
  f_258 : forall {rs dlt R_fin}, BigF m rs dlt R_fin -> NoNonlast0F rs ->
    (dlt = 2 \/ dlt = 5 \/ dlt = 8) -> Head0s11 R_fin;
  f_25_goodF2U : forall {rs dlt R_fin}, BigF m rs dlt R_fin -> NoNonlast0F rs ->
    (dlt = 2 \/ dlt = 5) ->
    exists U, R_fin = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U;
  f_pos_0s : forall {rs dlt R_fin W}, BigF m rs dlt R_fin -> NoNonlast0F rs -> 0 < dlt ->
    R_fin = (0, true) :: W -> exists Z, R_fin = (0, true) :: (1, false) :: Z;
  f_4_head : forall {rs R_fin}, BigF m rs 4 R_fin -> NoNonlast0F rs ->
    R_fin = [(1, false)] \/ (exists W, R_fin = (1, true) :: W) \/ (exists W, R_fin = (2, false) :: W);
  f_11 : forall {rs R_fin}, BigF m rs 11 R_fin -> NoNonlast0F rs -> Head0s11 R_fin \/ Strong2 R_fin;

  f3_ne24 : forall {Y dlt R_fin}, BigF m ((3, false) :: Y) dlt R_fin -> NoNonlast0F Y ->
    dlt <> 2 /\ dlt <> 4;
  f3_36 : forall {Y dlt R_fin}, BigF m ((3, false) :: Y) dlt R_fin -> NoNonlast0F Y ->
    (dlt = 3 \/ dlt = 6) -> Head0s11 R_fin;
  f3_3_non0s : forall {Y R_fin}, BigF m ((3, false) :: Y) 3 R_fin -> NoNonlast0F Y ->
    (forall Z, Y <> (0, true) :: Z) -> Safe0s R_fin;
  f3_5_0111 : forall {Y R_fin}, BigF m ((3, false) :: Y) 5 R_fin -> NoNonlast0F Y -> Head0s111 R_fin;
  f3_9 : forall {Y R_fin}, BigF m ((3, false) :: Y) 9 R_fin -> NoNonlast0F Y ->
    Head0s11 R_fin \/ Strong2 R_fin;
  f3_1_ne6 : forall {Y R_fin}, BigF m ((3, false) :: (1, false) :: Y) 6 R_fin -> NoNonlast0F Y -> False;
  f3_11 : forall {Y dlt R_fin}, BigF m ((3, false) :: (1, false) :: (1, false) :: Y) dlt R_fin ->
    NoNonlast0F Y -> dlt = 0 \/ dlt = 7 \/ (dlt = 10 /\ Good2 R_fin);
  f3_111 : forall {Y dlt R_fin}, BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin ->
    NoNonlast0F Y -> (dlt = 7 \/ dlt = 10) /\ Good2 R_fin /\ (dlt = 10 -> Strong2 R_fin);
  f3_1111 : forall {Y dlt R_fin},
    BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin ->
    NoNonlast0F Y -> dlt = 7 /\ Good2 R_fin /\ (GoodZero111Head Y -> Strong2 R_fin);

  f1 : forall {Y dlt R_fin}, BigF m ((1, false) :: Y) dlt R_fin -> NoNonlast0F Y ->
    dlt <> 3 /\ dlt <> 4 /\
    (dlt = 5 -> Safe0s R_fin) /\
    (dlt = 6 -> Head0s11 R_fin) /\
    (dlt = 7 -> Head0s111 R_fin \/ Good1Safe R_fin) /\
    (dlt = 10 -> Head0s11 R_fin \/ Good2 R_fin) /\
    (dlt = 13 -> Head0s11 R_fin \/ Good2 R_fin) /\
    (dlt = 14 -> Head0s11 R_fin \/ Strong2 R_fin);
  f11 : forall {Y dlt R_fin}, BigF m ((1, false) :: (1, false) :: Y) dlt R_fin -> NoNonlast0F Y ->
    dlt mod 3 <> 2 /\ dlt <> 3 /\ dlt <> 6 /\
    (dlt = 7 -> Good1Safe R_fin) /\
    (((dlt mod 3 = 0 /\ 9 <= dlt) \/ dlt = 10) -> Good2 R_fin) /\
    (dlt = 13 -> GoodF2U Y -> Strong2 R_fin) /\
    (dlt = 10 -> Strong2 R_fin);
  f111 : forall {Y dlt R_fin}, BigF m ((1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin ->
    NoNonlast0F Y ->
    (dlt = 0 /\ Zero111 R_fin /\ (GoodZero111Head Y -> TightZero111 R_fin)) \/
    (dlt mod 3 = 0 /\ 9 <= dlt /\ Good2 R_fin /\
      (dlt = 9 -> GoodF2U Y -> Strong2 R_fin) /\ (dlt = 12 -> Strong2 R_fin));

  f2s : forall {Y dlt R_fin}, BigF m ((2, true) :: Y) dlt R_fin -> NoNonlast0F Y ->
    dlt <> 2 /\ dlt <> 5 /\
    (dlt = 0 -> Safe0s R_fin) /\
    (dlt = 3 -> Head0s11 R_fin) /\
    (dlt = 6 -> Head0s11 R_fin \/ Good1Safe R_fin) /\
    (dlt = 9 -> Head0s11 R_fin \/ Strong2 R_fin) /\
    (dlt = 12 -> Head0s11 R_fin \/ Good2 R_fin);
  f2s_1 : forall {Y dlt R_fin}, BigF m ((2, true) :: (1, false) :: Y) dlt R_fin -> NoNonlast0F Y ->
    dlt = 0 \/ dlt = 4 \/ dlt = 10 \/ dlt = 13;
  f2s_11 : forall {Y dlt R_fin}, BigF m ((2, true) :: (1, false) :: (1, false) :: Y) dlt R_fin ->
    NoNonlast0F Y ->
    (dlt = 4 /\ (GoodZero111Head Y -> Good1Safe R_fin)) \/
    (dlt = 10 /\ (GoodF2U Y -> Strong2 R_fin)) \/
    dlt = 13;
  f2s_111 : forall {Y dlt R_fin},
    BigF m ((2, true) :: (1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin ->
    NoNonlast0F Y -> dlt = 4 /\ Good1Safe R_fin;

  good2_f : forall {G dlt R_fin}, Good2 G -> BigF m G dlt R_fin -> NoNonlast0F G ->
    dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
    (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
    (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W));
  good2_f1 : forall {G dlt R_fin}, Good2 G -> BigF m ((1, false) :: G) dlt R_fin -> NoNonlast0F G ->
    dlt = 0 \/ (dlt = 9 /\ Good2 R_fin) \/ (dlt = 12 /\ Strong2 R_fin) \/ (dlt mod 3 = 0 /\ 15 <= dlt);
  good2_f11 : forall {G dlt R_fin}, Good2 G -> BigF m ((1, false) :: (1, false) :: G) dlt R_fin ->
    NoNonlast0F G -> dlt = 0;
  good2_f31 : forall {G dlt R_fin}, Good2 G -> BigF m ((3, false) :: (1, false) :: G) dlt R_fin ->
    NoNonlast0F G -> (dlt = 7 \/ (dlt = 10 /\ Good2 R_fin)) /\ (Strong2 G -> Strong2 R_fin);
  good2_f311 : forall {G dlt R_fin}, Good2 G -> BigF m ((3, false) :: (1, false) :: (1, false) :: G) dlt R_fin ->
    NoNonlast0F G -> dlt = 7 /\ Strong2 R_fin;
  good2_f3111 : forall {G dlt R_fin}, Good2 G ->
    BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: G) dlt R_fin ->
    NoNonlast0F G -> dlt = 7 /\ Good2 R_fin /\ (Strong2 G -> Strong2 R_fin);
  good1_f3121 : forall {G dlt R_fin}, Good1 G ->
    BigF m ((3, false) :: (1, false) :: (2, false) :: (1, false) :: G) dlt R_fin ->
    NoNonlast0F G -> (dlt = 7 \/ dlt = 10) /\ Good2 R_fin
}.

Arguments f_258 {m} _ {rs dlt R_fin} _ _ _.
Arguments f_25_goodF2U {m} _ {rs dlt R_fin} _ _ _.
Arguments f_pos_0s {m} _ {rs dlt R_fin W} _ _ _ _.
Arguments f_4_head {m} _ {rs R_fin} _ _.
Arguments f_11 {m} _ {rs R_fin} _ _.
Arguments f3_ne24 {m} _ {Y dlt R_fin} _ _.
Arguments f3_36 {m} _ {Y dlt R_fin} _ _ _.
Arguments f3_3_non0s {m} _ {Y R_fin} _ _ _.
Arguments f3_5_0111 {m} _ {Y R_fin} _ _.
Arguments f3_9 {m} _ {Y R_fin} _ _.
Arguments f3_1_ne6 {m} _ {Y R_fin} _ _.
Arguments f3_11 {m} _ {Y dlt R_fin} _ _.
Arguments f3_111 {m} _ {Y dlt R_fin} _ _.
Arguments f3_1111 {m} _ {Y dlt R_fin} _ _.
Arguments f1 {m} _ {Y dlt R_fin} _ _.
Arguments f11 {m} _ {Y dlt R_fin} _ _.
Arguments f111 {m} _ {Y dlt R_fin} _ _.
Arguments f2s {m} _ {Y dlt R_fin} _ _.
Arguments f2s_1 {m} _ {Y dlt R_fin} _ _.
Arguments f2s_11 {m} _ {Y dlt R_fin} _ _.
Arguments f2s_111 {m} _ {Y dlt R_fin} _ _.
Arguments good2_f {m} _ {G dlt R_fin} _ _ _.
Arguments good2_f1 {m} _ {G dlt R_fin} _ _ _.
Arguments good2_f11 {m} _ {G dlt R_fin} _ _ _.
Arguments good2_f31 {m} _ {G dlt R_fin} _ _ _.
Arguments good2_f311 {m} _ {G dlt R_fin} _ _ _.
Arguments good2_f3111 {m} _ {G dlt R_fin} _ _ _.
Arguments good1_f3121 {m} _ {G dlt R_fin} _ _ _.

Lemma InvAt_f_4_ne0s {m : nat} (hInv : InvAt m) {rs R_fin Z : list Seg}
    (h : BigF m rs 4 R_fin) (hN : NoNonlast0F rs) : R_fin <> (0, true) :: Z.
Proof.
  destruct (f_4_head hInv h hN) as [-> | [[W ->] | [W ->]]]; discriminate.
Qed.

Definition InvLt (m : nat) : Prop := forall k, k < m -> InvAt k.

Lemma bigF_bump2_of_d1_two {m s1 s3 d dlt3 : nat} {b : bool} {Y R1 R_fin : list Seg}
    (ih : InvLt m) (hs3 : s3 < m)
    (h1 : BigD1 s1 ((d, b) :: Y) 2 R1) (hNY : NoNonlast0F Y)
    (hF : BigF s3 (bumpR (bumpR R1)) dlt3 R_fin) :
  (dlt3 = 0 /\ Safe0s R_fin) \/ dlt3 = 4 \/ dlt3 = 10 \/ dlt3 = 13.
Proof.
  pose proof (proj2 (bigFD_noNonlast0F _) _ _ _ h1 hNY) as hN1.
  destruct (bigD1_two_head_nnf h1 hNY) as [-> | [[Z ->] | [Z ->]]].
  - cbn in hF.
    destruct (proj1 (bigFD_det _) _ _ _ _ _ _ hF bigF_2s_0_exists) as [-> _].
    right; left; reflexivity.
  - cbn in hF.
    destruct (proj1 (bigFD_det _) _ _ _ _ _ _ hF (bigF_2s_0s_exists Z)) as [-> _].
    right; left; reflexivity.
  - pose proof (noNonlast0F_tail (noNonlast0F_tail hN1)) as hN_Z.
    cbn in hF.
    destruct (f2s_1 (ih s3 hs3) hF hN_Z) as [-> | [-> | [-> | ->]]].
    + pose proof (proj1 (proj2 (proj2 (f2s (ih s3 hs3) hF (nnf_1F hN_Z)))) eq_refl) as hS.
      left; exact (conj eq_refl hS).
    + right; left; reflexivity.
    + right; right; left; reflexivity.
    + right; right; right; reflexivity.
Qed.

(* ========================================================================== *)
(* Constructive Helpers and Shorthands                                        *)
(* ========================================================================== *)

Lemma dec_head_0s (rs : list Seg) :
  (exists W, rs = (0, true) :: W) \/ (forall W, rs <> (0, true) :: W).
Proof.
  destruct rs as [| [[| d] []] W].
  - right; intros ? h; discriminate h.
  - left; exists W; reflexivity.
  - right; intros ? h; discriminate h.
  - right; intros ? h; discriminate h.
  - right; intros ? h; discriminate h.
Qed.

Lemma dec_seg_0s (dx : nat) (bx : bool) :
  (dx = 0 /\ bx = true) \/ ~(dx = 0 /\ bx = true).
Proof.
  destruct dx as [| d'], bx.
  - left; exact (conj eq_refl eq_refl).
  - right; intros [? h]; discriminate h.
  - right; intros [h ?]; discriminate h.
  - right; intros [h ?]; discriminate h.
Qed.

Lemma bigF_det {s1 s2 : nat} {rs : list Seg} {dlt1 dlt2 : nat} {R1 R2 : list Seg}
    (h1 : BigF s1 rs dlt1 R1) (h2 : BigF s2 rs dlt2 R2) :
  dlt1 = dlt2 /\ R1 = R2.
Proof. exact (proj1 (bigFD_det s1) s2 rs dlt1 dlt2 R1 R2 h1 h2). Qed.

Lemma bigF_nnf {s : nat} {rs : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF s rs dlt R_fin) (hN : NoNonlast0F rs) : NoNonlast0F R_fin.
Proof. exact (proj1 (bigFD_noNonlast0F s) rs dlt R_fin h hN). Qed.

Lemma bigD1_nnf {s : nat} {rs : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigD1 s rs dlt R_fin) (hI : NoInterior0F rs) : NoNonlast0F R_fin.
Proof. exact (proj2 (bigFD_noNonlast0F s) rs dlt R_fin h hI). Qed.

Lemma nnf_3F {xs : list Seg} (h : NoNonlast0F xs) : NoNonlast0F ((3, false) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma nnf_2T {xs : list Seg} (h : NoNonlast0F xs) : NoNonlast0F ((2, true) :: xs).
Proof. destruct xs; [exact I | exact h]. Qed.

Lemma bigF_3_zero_goodF2U {m s : nat} (ih : InvLt m) (hs : s < m)
    {Y R_fin : list Seg} (h : BigF s ((3, false) :: Y) 0 R_fin) (hN : NoNonlast0F Y) :
  exists U, R_fin = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U.
Proof.
  destruct (bigF_3_inv h) as [s4 [hs4 [dlt4 [R4 [h4 hc4]]]]].
  destruct hc4 as [[hrem4 [hge4 [? ->]]] | [[? [? [? [? [hadd4 _]]]]] |
                  [[? [? [? [? [hadd4 _]]]]] | [? [? [? [? [? [hadd4 _]]]]]]]]]; try lia.
  destruct (Nat.eq_dec dlt4 4) as [-> | h4ne].
  - destruct (f_4_head (ih s4 ltac:(lia)) h4 hN) as [-> | [[W ->] | [W ->]]].
    + exists [(1, false)]. split; [reflexivity | left; exists ([] : list Seg); reflexivity].
    + exists ((1, true) :: W). split; [reflexivity | right; left; exists W; reflexivity].
    + exists ((2, false) :: W). split; [reflexivity | right; right; left; exists W; reflexivity].
  - assert (hsp : dlt4 / 3 - 1 = S (dlt4 / 3 - 2)) by dlia.
    rewrite hsp.
    exists ((1, false) :: ones (dlt4 / 3 - 2) ++ R4).
    split; [reflexivity | left; exists (ones (dlt4 / 3 - 2) ++ R4); reflexivity].
Qed.

Lemma head0s11_to_head0s1 {rs : list Seg} (h : Head0s11 rs) :
  exists Z, rs = (0, true) :: (1, false) :: Z.
Proof.
  destruct h as [Z ->]. exists ((1, false) :: Z). reflexivity.
Qed.

(* What the first subcall can hand to the dispatcher. *)
Inductive Incoming (m : nat) : nat -> list Seg -> Prop :=
| in_one s i X Y : s < m -> NoNonlast0F X -> BigF s X i Y ->
    Incoming m (1 + i) Y
| in_twoF s i X Y : s < m -> NoNonlast0F X -> BigF s (bumpR (bumpR X)) i Y ->
    Incoming m i Y
| in_twoT s i X Y : s < m -> NoNonlast0F X -> BigF s ((1,false)::X) i Y ->
    Incoming m i Y
| in_three s i d c X Y : s < m -> NoNonlast0F X -> BigD1 s ((d,c)::X) i Y ->
    Incoming m i Y.

Inductive PostCall (m v : nat) (Y : list Seg) : nat -> list Seg -> Prop :=
| post_two s i Z : v mod 3 = 2 -> s < m -> BigD1 s (ones (S (v/3)) ++ Y) i Z ->
    PostCall m v Y i Z
| post_zero s i Z : v mod 3 = 0 -> s < m -> BigD1 s (ones (v/3) ++ Y) i Z ->
    PostCall m v Y (i + 1) Z.

Lemma bigF_dispatch m X i Z : BigF m X i Z -> NoNonlast0F X ->
  i = 0 \/ exists v Y, Incoming m v Y /\ PostCall m v Y i Z.
Proof.
  intros hf hn. inverts hf as h1 hrem h2; try (left; reflexivity).
  all: right; eexists; eexists; split;
    [ | first [solve [eapply post_two; [exact hrem | | exact h2]; lia]
              | solve [eapply post_zero; [exact hrem | | exact h2]; lia]] ].
  all: first [ solve [eapply in_one; [| | exact h1]; [lia | exact (noNonlast0F_tail hn)]]
             | solve [eapply in_twoF; [| | exact h1]; [lia | exact (noNonlast0F_tail hn)]]
             | solve [eapply in_twoT; [| | exact h1]; [lia | exact (noNonlast0F_tail hn)]]
             | solve [eapply in_three; [| | exact h1]; [lia | exact (noNonlast0F_tail hn)]] ].
Qed.

Lemma incoming_nnf m v Y : Incoming m v Y -> NoNonlast0F Y.
Proof.
  intro h. destruct h; eauto using bigF_nnf, bigD1_nnf, nnf_1F, noNonlast0F_bumpR.
Qed.

Definition BeforeZero Y :=
  Y = [(0,true);(0,false)] \/ (exists W, Y = (0,true)::(0,true)::W) \/
  (exists W, Y = (0,true)::(1,false)::W).
Definition FourHead Z :=
  Z = [(1,false)] \/ (exists W, Z = (1,true)::W) \/ (exists W, Z = (2,false)::W).
Definition ZeroOne Z := exists W, Z = (0,true)::(1,false)::W.
Definition SmallTwo n Z := (n = 0 /\ Safe0s Z) \/ n = 4 \/ n = 10 \/ n = 13.

Lemma incoming_zero m Y : Incoming m 0 Y -> BeforeZero Y.
Proof.
  intro h. inverts h as hs hn h.
  - destruct X as [|[d b] X].
    + change (BigF s [(1,false)] 0 Y) in h.
      destruct (bigF_det h (BF_oneF_rem1 BF_nil eq_refl)) as [_ ->].
      left; reflexivity.
    + destruct (bigF_ge2_zero_head h) as [W ->]. right; right; eauto.
  - inverts h as h1 hrem h2; try lia.
    + match type of h1 with BigF _ _ ?i _ => destruct (Nat.eq_dec i 0) as [-> | hne] end.
      * destruct (bigF_zero_head_3 h1 hn) as [-> | [[W ->] | [W ->]]].
        -- left; reflexivity.
        -- right; left; exists W; reflexivity.
        -- right; right; exists W; reflexivity.
      * assert (hq : 1 <= (1 + dlt1) / 3) by dlia.
        destruct (ones_pos_cons hq R1) as [W ->]. right; right; eauto.
    + pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1))). lia.
  - pose proof (bigD1_ge2_of_ne_nil h ltac:(discriminate)). lia.
Qed.

Lemma incoming_two {m Y s n Z} (ih : InvLt m) :
  Incoming m 2 Y -> s < m -> BigF s (bumpR (bumpR Y)) n Z -> SmallTwo n Z.
Proof.
  intros h hs hf. inverts h as ht hn htape.
  - contradiction (bigF_ne_one htape).
  - pose proof (bigF_nnf htape (noNonlast0F_bumpR (noNonlast0F_bumpR hn))) as hy.
    destruct (f_258 (ih _ ht) htape (noNonlast0F_bumpR (noNonlast0F_bumpR hn)) (or_introl eq_refl)) as [W ->].
    cbn [bumpR] in hf.
    destruct (f2s_11 (ih _ hs) hf (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hy))))
      as [[h4 _] | [[h10 _] | h13]]; unfold SmallTwo; auto.
  - pose proof (bigF_nnf htape (nnf_1F hn)) as hy.
    destruct (f_258 (ih _ ht) htape (nnf_1F hn) (or_introl eq_refl)) as [W ->].
    cbn [bumpR] in hf.
    destruct (f2s_11 (ih _ hs) hf (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hy))))
      as [[h4 _] | [[h10 _] | h13]]; unfold SmallTwo; auto.
  - exact (bigF_bump2_of_d1_two ih hs htape hn hf).
Qed.

Lemma incoming_three {m Y s Z} (ih : InvLt m) :
  Incoming m 3 Y -> s < m -> BigF s (bumpR (bumpR Y)) 0 Z -> ZeroOne Z.
Proof.
  intros h hs hf. inverts h as ht hn htape.
  - pose proof (bigF_nnf htape hn) as hy.
    destruct (f_258 (ih _ ht) htape hn (or_introl eq_refl)) as [W ->].
    cbn [bumpR] in hf.
    destruct (f2s_11 (ih _ hs) hf (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hy))))
      as [[h4 _] | [[h10 _] | h13]]; lia.
  - pose proof (bigF_nnf htape (noNonlast0F_bumpR (noNonlast0F_bumpR hn))) as hy.
    destruct (bigF_three_head htape) as [W ->]. cbn [bumpR] in hf.
    exact (head0s11_to_head0s1 (safe0s_to_head0s11
      (proj1 (proj2 (proj2 (f2s (ih _ hs) hf (noNonlast0F_tail hy)))) eq_refl))).
  - contradiction (proj1 (f1 (ih _ ht) htape hn) eq_refl).
  - pose proof (bigD1_nnf htape hn) as hy.
    remember 3 as d3 eqn:hd3; inverts htape as h0f heq; subst; try lia.
    + match type of h0f with BigF _ _ ?i _ => assert (i = 0) by lia; subst i end.
      destruct (bigF_zero_head_3 h0f hn) as [-> | [[W ->] | [W ->]]]; cbn [bumpR] in hf.
      * destruct bigF_2_nil_exists as [? he]. destruct (bigF_det hf he) as [h4 _]. lia.
      * exact (head0s11_to_head0s1 (safe0s_to_head0s11
          (proj1 (proj2 (proj2 (f2s (ih _ hs) hf (noNonlast0F_tail hy)))) eq_refl))).
      * exact (head0s11_to_head0s1 (bigF_3_zero_prefix hf)).
    + match type of hf with BigF _ (bumpR (bumpR (bumpR ?Y))) _ _ => destruct Y as [|[d b] Y] end;
        cbn [bumpR] in hf.
      * destruct bigF_2_nil_exists as [? he]. destruct (bigF_det hf he) as [h4 _]. lia.
      * destruct (bigF_ge3_zero_prefix hf) as [[W ->] | [W ->]]; unfold ZeroOne; eauto.
    + match type of h0f with BigF _ _ ?i _ => assert (i = 1) by lia; subst i end.
      contradiction (bigF_ne_one h0f).
    + match type of h0f with BigF _ _ ?i _ => assert (i = 1) by lia; subst i end.
      contradiction (bigF_ne_one h0f).
    + pose proof (bigD1_ge2_of_ne_nil h0f ltac:(discriminate)). lia.
Qed.

(* All five general F invariants see only this view of the last call:
   many ones become a leading 3; short dispatches use their own contracts. *)
Inductive ReturnView (m : nat) : nat -> list Seg -> Prop :=
| rv_zero Z : ReturnView m 0 Z
| rv_four Z : FourHead Z -> ReturnView m 4 Z
| rv_three s n a X Z : (a = 2 \/ a = 3) -> s < m -> NoNonlast0F X ->
    BigF s ((3,false)::X) n Z -> ReturnView m (n+a) Z
| rv_small_two s n X Z : s < m -> NoNonlast0F X -> BigF s X n Z ->
    SmallTwo n Z -> ReturnView m (n+2) Z
| rv_small_zero s n X Z : s < m -> NoNonlast0F X -> BigF s X n Z ->
    (n = 0 -> ZeroOne Z) -> ReturnView m (n+3) Z.

Lemma last_call_view {m v Y i Z} (ih : InvLt m) :
  Incoming m v Y -> PostCall m v Y i Z -> ReturnView m i Z.
Proof.
  intros hin hp. pose proof (incoming_nnf _ _ _ hin) as hy.
  destruct hp as [s i Z hmod hs hd | s i Z hmod hs hd].
  - destruct (v / 3) as [| q] eqn:hq.
    + destruct (bigD1_oneF_inv hd) as [t [ht [n [-> hf]]]].
      eapply rv_small_two; [| | exact hf |].
      1: lia. 1: now repeat apply noNonlast0F_bumpR.
      assert (v = 2) by dlia. subst v.
      exact (incoming_two (s := t) ih hin ltac:(lia) hf).
    + destruct (bigD1_1_1_inv hd) as [t [ht [n [-> hf]]]].
      eapply rv_three with (s := t) (n := n) (a := 2);
        [now left | lia | | exact hf]. now apply noNonlast0F_ones_append.
  - destruct (v / 3) as [| [| q]] eqn:hq.
    + assert (v = 0) by dlia. subst v. cbn [ones app] in hd.
      destruct (incoming_zero _ _ hin) as [-> | [[W ->] | [W ->]]];
        destruct (bigD1_zeroT_inv hd) as [-> ->]; apply rv_four; unfold FourHead;
        cbn [bumpR]; eauto.
    + destruct (bigD1_oneF_inv hd) as [t [ht [n [-> hf]]]].
      replace (n+2+1) with (n+3) by lia.
      eapply rv_small_zero; [| | exact hf |].
      1: lia. 1: now repeat apply noNonlast0F_bumpR.
      intros ->. assert (v = 3) by dlia. subst v.
      exact (incoming_three (s := t) ih hin ltac:(lia) hf).
    + destruct (bigD1_1_1_inv hd) as [t [ht [n [-> hf]]]].
      replace (n+2+1) with (n+3) by lia.
      eapply rv_three with (s := t) (n := n) (a := 3);
        [now right | lia | | exact hf]. now apply noNonlast0F_ones_append.
Qed.

Lemma bigF_return_view {m X i Z} (ih : InvLt m) :
  BigF m X i Z -> NoNonlast0F X -> ReturnView m i Z.
Proof.
  intros hf hn. destruct (bigF_dispatch _ _ _ _ hf hn) as [-> | [v [Y [hin hp]]]].
  - apply rv_zero.
  - exact (last_call_view ih hin hp).
Qed.

Lemma step_f_258 {m X i Z} (ih : InvLt m) :
  BigF m X i Z -> NoNonlast0F X -> i = 2 \/ i = 5 \/ i = 8 -> Head0s11 Z.
Proof.
  intros hf hn hi. destruct (bigF_return_view ih hf hn) as [| |s n a Y Z ha hs hN h|s n Y Z hs hN h hr|s n Y Z hs hN h hr]; try lia.
  - destruct ha as [-> | ->].
    + destruct (Nat.eq_dec n 0) as [-> | hn0].
      * exact (bigF_3_zero_prefix h).
      * eapply (f3_36 (ih _ hs) h hN); lia.
    + eapply (f_258 (ih _ hs) h (nnf_3F hN)); lia.
  - destruct hr as [[-> hS] | [-> | [-> | ->]]]; try lia.
    exact (safe0s_to_head0s11 hS).
  - eapply (f_258 (ih _ hs) h hN); lia.
Qed.

Lemma f3_three_qualified {m s Y Z} (ih : InvLt m) :
  s < m -> BigF s ((3,false)::Y) 3 Z -> NoNonlast0F Y ->
  exists U, Z = (0,true)::(1,false)::(1,false)::U /\ GoodF2U U.
Proof.
  intros hs hf hn.
  destruct (dec_head_0s Y) as [[W ->] | hn0].
  - destruct (bigF_3_0s_inv hf) as [t [ht [n [he h]]]].
    assert (n=0) by lia. subst n.
    exact (bigF_3_zero_goodF2U (s := t) ih ltac:(lia) h (noNonlast0F_tail hn)).
  - destruct (f3_3_non0s (ih _ hs) hf hn hn0) as [W [-> h]].
    exists W. exact (conj eq_refl (safeU_to_goodF2U h)).
Qed.

Lemma step_f_25_goodF2U {m X i Z} (ih : InvLt m) :
  BigF m X i Z -> NoNonlast0F X -> i = 2 \/ i = 5 ->
  exists U, Z = (0,true)::(1,false)::(1,false)::U /\ GoodF2U U.
Proof.
  intros hf hn hi. destruct (bigF_return_view ih hf hn) as [| |s n a Y Z ha hs hN h|s n Y Z hs hN h hr|s n Y Z hs hN h hr]; try lia.
  - destruct ha as [-> | ->].
    + destruct (Nat.eq_dec n 0) as [-> | hn0].
      * exact (bigF_3_zero_goodF2U ih hs h hN).
      * assert (n=3) by lia. subst n. exact (f3_three_qualified ih hs h hN).
    + assert (n=2) by lia. subst n.
      contradiction (proj1 (f3_ne24 (ih _ hs) h hN) eq_refl).
  - destruct hr as [[-> [W [-> hS]]] | [-> | [-> | ->]]]; try lia.
    exists W. exact (conj eq_refl (safeU_to_goodF2U hS)).
  - eapply (f_25_goodF2U (ih _ hs) h hN); lia.
Qed.

Lemma step_f_pos_0s {m X i Z W} (ih : InvLt m) :
  BigF m X i Z -> NoNonlast0F X -> 0 < i -> Z = (0,true)::W -> ZeroOne Z.
Proof.
  intros hf hn hi he. destruct (bigF_return_view ih hf hn) as [|Z hr|s n a Y Z ha hs hN h|s n Y Z hs hN h hr|s n Y Z hs hN h hr]; try lia.
  - destruct hr as [-> | [[U ->] | [U ->]]]; discriminate.
  - destruct (Nat.eq_dec n 0) as [-> | hn0].
    + exact (head0s11_to_head0s1 (bigF_3_zero_prefix h)).
    + exact (f_pos_0s (ih _ hs) h (nnf_3F hN) ltac:(lia) he).
  - destruct hr as [[-> hS] | [-> | [-> | ->]]].
    + exact (head0s11_to_head0s1 (safe0s_to_head0s11 hS)).
    + exact (f_pos_0s (ih _ hs) h hN ltac:(lia) he).
    + exact (f_pos_0s (ih _ hs) h hN ltac:(lia) he).
    + exact (f_pos_0s (ih _ hs) h hN ltac:(lia) he).
  - destruct (Nat.eq_dec n 0) as [-> | hn0].
    + exact (hr eq_refl).
    + exact (f_pos_0s (ih _ hs) h hN ltac:(lia) he).
Qed.

Lemma step_f_4_head {m X Z} (ih : InvLt m) :
  BigF m X 4 Z -> NoNonlast0F X -> FourHead Z.
Proof.
  remember 4 as i eqn:hi. intros hf hn.
  destruct (bigF_return_view ih hf hn) as [|Z hr|s n a Y Z ha hs hN h|s n Y Z hs hN h hr|s n Y Z hs hN h hr]; try lia.
  - exact hr.
  - destruct ha as [-> | ->].
    + assert (n=2) by lia. subst n.
      contradiction (proj1 (f3_ne24 (ih _ hs) h hN) eq_refl).
    + assert (n=1) by lia. subst n. contradiction (bigF_ne_one h).
  - destruct hr as [[-> _] | [-> | [-> | ->]]]; lia.
  - assert (n=1) by lia. subst n. contradiction (bigF_ne_one h).
Qed.

Lemma step_f_11 {m X Z} (ih : InvLt m) :
  BigF m X 11 Z -> NoNonlast0F X -> Head0s11 Z \/ Strong2 Z.
Proof.
  remember 11 as i eqn:hi. intros hf hn.
  destruct (bigF_return_view ih hf hn) as [|Z hr|s n a Y Z ha hs hN h|s n Y Z hs hN h hr|s n Y Z hs hN h hr]; try lia.
  - destruct ha as [-> | ->].
    + assert (n=9) by lia. subst n. exact (f3_9 (ih _ hs) h hN).
    + assert (n=8) by lia. subst n. left. exact (f_258 (ih _ hs) h (nnf_3F hN) (or_intror (or_intror eq_refl))).
  - destruct hr as [[-> _] | [-> | [-> | ->]]]; lia.
  - assert (n=8) by lia. subst n. left. exact (f_258 (ih _ hs) h hN (or_intror (or_intror eq_refl))).
Qed.

(* ========================================================================== *)
(* Group 2 Step Lemmas (F(3 :: Y) family)                                     *)
(* ========================================================================== *)

Lemma step_f3_ne24 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((3, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  dlt <> 2 /\ dlt <> 4.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [? [-> _]]] | [[hrem [s2 [hs2 [dlt3 [-> hF2]]]]] |
                     [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] | [hrem [hge3 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - split; lia.
  - pose proof (f3_ne24 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [hne2 _].
    split; [| lia].
    intro h2e. assert (dlt3 = 0) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt0 2) as [-> | hne02].
    + destruct (f_258 (ih s1 hs1) h1 hN (or_introl eq_refl)) as [U ->].
      cbn [ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [? [? [? [hadd _]]]]; lia.
    + destruct (Nat.eq_dec dlt0 5) as [-> | hne05].
      * destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_introl eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [? [? [? [hadd _]]]]; lia.
      * destruct (Nat.eq_dec dlt0 8) as [-> | hne08].
        -- destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_intror eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
        -- assert (hq3 : dlt0 / 3 = S (S (S (dlt0 / 3 - 3)))) by dlia.
           rewrite hq3 in hF2. cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [h710 _]; lia.
  - split; [lia |].
    intro h4; assert (dlt3 = 1) by lia; subst dlt3; exact (bigF_ne_one hF2).
  - split; [lia |].
    intro h4; assert (dlt3 = 1) by lia; subst dlt3; exact (bigF_ne_one hF2).
Qed.

Lemma step_f3_36 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((3, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y)
    (hdlt : dlt = 3 \/ dlt = 6) : Head0s11 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [? [-> _]]] | [[? [s2 [hs2 [dlt3 [-> hF2]]]]] |
                     [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [? [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - lia.
  - destruct hdlt as [h3 | h6].
    + assert (dlt3 = 1) by lia; subst dlt3; contradiction (bigF_ne_one hF2).
    + contradiction (proj2 (f3_ne24 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
  - destruct hdlt as [h3 | h6].
    + assert (dlt3 = 0) by lia; subst dlt3.
      destruct (bigF_zero_head_3 h1 hN) as [-> | [[Z ->] | [Z ->]]]; cbn [bumpR] in hF2.
      * destruct bigF_2_nil_exists as [? hEx].
        destruct (bigF_det hF2 hEx) as [h4 _]; lia.
      * exact (safe0s_to_head0s11 (proj1 (proj2 (proj2 (f2s (ih s2 hs2) hF2 (noNonlast0F_tail hN1)))) eq_refl)).
      * exact (bigF_3_zero_prefix hF2).
    + assert (dlt3 = 3) by lia; subst dlt3.
      destruct (bigF_zero_head_3 h1 hN) as [-> | [[Z ->] | [Z ->]]]; cbn [bumpR] in hF2.
      * destruct bigF_2_nil_exists as [? hEx].
        destruct (bigF_det hF2 hEx) as [h4 _]; lia.
      * exact (proj1 (proj2 (proj2 (proj2 (f2s (ih s2 hs2) hF2 (noNonlast0F_tail hN1))))) eq_refl).
      * exact (f3_36 (ih s2 hs2) hF2 (noNonlast0F_tail hN1) (or_introl eq_refl)).
  - destruct hdlt as [h3 | h6].
    + assert (dlt3 = 0) by lia; subst dlt3; exact (bigF_3_zero_prefix hF2).
    + assert (dlt3 = 3) by lia; subst dlt3.
      exact (f3_36 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1) (or_introl eq_refl)).
Qed.

Lemma step_f3_3_non0s {m : nat} (ih : InvLt m)
    {Y R_fin : list Seg}
    (h : BigF m ((3, false) :: Y) 3 R_fin) (hN : NoNonlast0F Y)
    (hnon0s : forall Z, Y <> (0, true) :: Z) : Safe0s R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [? [h0 _]]] | [[? [s2 [hs2 [dlt3 [hadd hF2]]]]] |
                     [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] | [hrem [hge3 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 1) by lia; subst dlt3; contradiction (bigF_ne_one hF2).
  - assert (dlt3 = 0) by lia; subst dlt3.
    destruct (bigF_zero_head_3 h1 hN) as [-> | [[Z ->] | [Z ->]]]; cbn [bumpR] in hF2.
    + destruct bigF_2_nil_exists as [? hEx].
      destruct (bigF_det hF2 hEx) as [h4 _]; lia.
    + exact (proj1 (proj2 (proj2 (f2s (ih s2 hs2) hF2 (noNonlast0F_tail hN1)))) eq_refl).
    + destruct (bigF_zero_oneF_head h1 hN) as [[-> ->] | ->].
      * destruct bigF_3_nil_exists as [? hEx].
        destruct (bigF_det hF2 hEx) as [h7 _]; lia.
      * contradiction (hnon0s Z eq_refl).
  - assert (dlt3 = 0) by lia; subst dlt3.
    destruct (bigF_3_inv hF2) as [s4 [hs4 [dlt4 [R4 [h4 hc4]]]]].
    destruct hc4 as [[hrem4 [hge4 [? ->]]] | [[? [? [? [? [hadd4 _]]]]] |
                    [[? [? [? [? [hadd4 _]]]]] | [? [? [? [? [? [hadd4 _]]]]]]]]]; try lia.
    destruct (le_lt_dec 13 dlt4) as [hge13 | hlt13].
    + assert (hsplit4 : dlt4 / 3 - 1 = S (S (S (dlt4 / 3 - 4)))) by dlia.
      rewrite hsplit4.
      exists ((1, false) :: (1, false) :: (1, false) :: ones (dlt4 / 3 - 4) ++ R4).
      split; [reflexivity | left; exists (ones (dlt4 / 3 - 4) ++ R4); reflexivity].
    + destruct (Nat.eq_dec dlt4 10) as [-> | hne10].
      * assert (hGH : Good2 R4 \/ Head0s11 R4).
        { destruct (dlt0 / 3 - 1) as [| [| [| k'']]] eqn:hq.
          - assert (dlt0 = 3) by dlia; subst dlt0.
            cbn [ones app] in h4.
            destruct (bigF_three_head h1) as [W ->].
            inverts h4; lia.
          - cbn [ones app] in h4.
            destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (f1 (ih s4 ltac:(lia)) h4 hN1)))))) eq_refl) as [hH | hG2]; auto.
          - cbn [ones app] in h4.
            left; exact (proj1 (proj2 (proj2 (proj2 (proj2 (f11 (ih s4 ltac:(lia)) h4 hN1))))) (or_intror eq_refl)).
          - cbn [ones app] in h4.
            destruct (f111 (ih s4 ltac:(lia)) h4 (noNonlast0F_ones_append k'' hN1)) as [[h0 _] | [hm _]]; dlia. }
        exists ((1, false) :: (1, false) :: R4).
        split; [reflexivity | right; left; exists R4; exact (conj eq_refl hGH)].
      * destruct (Nat.eq_dec dlt4 7) as [-> | hne7].
        -- assert (hGH : Good2 R4 \/ Head0s11 R4).
           { destruct (dlt0 / 3 - 1) as [| [| [| k'']]] eqn:hq.
             - assert (dlt0 = 3) by dlia; subst dlt0.
               cbn [ones app] in h4.
               destruct (bigF_three_head h1) as [W ->].
               inverts h4; lia.
             - cbn [ones app] in h4.
               destruct (proj1 (proj2 (proj2 (proj2 (proj2 (f1 (ih s4 ltac:(lia)) h4 hN1))))) eq_refl) as [hH | hG1].
               + right; exact (head0s111_to_head0s11 hH).
               + left; exact (good1Safe_to_good2 hG1).
             - cbn [ones app] in h4.
               left; exact (good1Safe_to_good2 (proj1 (proj2 (proj2 (proj2 (f11 (ih s4 ltac:(lia)) h4 hN1)))) eq_refl)).
             - cbn [ones app] in h4.
               destruct (f111 (ih s4 ltac:(lia)) h4 (noNonlast0F_ones_append k'' hN1)) as [[h0 _] | [hm _]]; dlia. }
           exists ((1, false) :: R4).
           split; [reflexivity | right; right; left; exists R4; exact (conj eq_refl hGH)].
        -- assert (dlt4 = 4) by dlia; subst dlt4.
           destruct (dlt0 / 3 - 1) as [| k] eqn:hq.
           ++ assert (dlt0 = 3) by dlia; subst dlt0.
              cbn [ones app] in h4.
              destruct (bigF_three_head h1) as [W ->].
              inverts h4; lia.
           ++ cbn [ones app] in h4.
              contradiction (proj1 (proj2 (f1 (ih s4 ltac:(lia)) h4 (noNonlast0F_ones_append k hN1))) eq_refl).
Qed.

Lemma step_f3_5_0111 {m : nat} (ih : InvLt m)
    {Y R_fin : list Seg}
    (h : BigF m ((3, false) :: Y) 5 R_fin) (hN : NoNonlast0F Y) :
  Head0s111 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [? [h0 _]]] | [[hrem [s2 [hs2 [dlt3 [hadd hF2]]]]] |
                     [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] | [? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 3) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt0 2) as [-> | hne2].
    + destruct (f_258 (ih s1 hs1) h1 hN (or_introl eq_refl)) as [U ->].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      cbn [ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
      assert (dlt4 = 0) by lia; subst dlt4.
      destruct (bigF_3_inv hF4) as [s5 [hs5 [dlt5 [R5 [h5 hc5]]]]].
      destruct hc5 as [[hrem5 [hge5 [? ->]]] | [[? [? [? [? [hadd5 _]]]]] |
                      [[? [? [? [? [hadd5 _]]]]] | [? [? [? [? [? [hadd5 _]]]]]]]]]; try lia.
      pose proof (proj1 (proj2 (f1 (ih s5 ltac:(lia)) h5 (nnf_1F hNU)))) as hne4.
      assert (hsp : dlt5 / 3 - 1 = S (dlt5 / 3 - 2)) by dlia.
      rewrite hsp. exists (ones (dlt5 / 3 - 2) ++ R5). reflexivity.
    + destruct (Nat.eq_dec dlt0 5) as [-> | hne5].
      * destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_introl eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
        destruct (f2s_111 (ih s4 ltac:(lia)) hF4 hNU) as [h4 _]; lia.
      * destruct (Nat.eq_dec dlt0 8) as [-> | hne8].
        -- destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_intror eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
        -- assert (hq3 : dlt0 / 3 = S (S (S (dlt0 / 3 - 3)))) by dlia.
           rewrite hq3 in hF2. cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [h710 _]; lia.
  - assert (dlt3 = 2) by lia; subst dlt3.
    destruct (bigF_zero_head_3 h1 hN) as [-> | [[Z ->] | [Z ->]]]; cbn [bumpR] in hF2.
    + destruct bigF_2_nil_exists as [? hEx].
      destruct (bigF_det hF2 hEx) as [h4 _]; lia.
    + contradiction (proj1 (f2s (ih s2 hs2) hF2 (noNonlast0F_tail hN1)) eq_refl).
    + contradiction (proj1 (f3_ne24 (ih s2 hs2) hF2 (noNonlast0F_tail hN1)) eq_refl).
  - contradiction (proj1 (f3_ne24 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
Qed.

Lemma step_f3_9 {m : nat} (ih : InvLt m)
    {Y R_fin : list Seg}
    (h : BigF m ((3, false) :: Y) 9 R_fin) (hN : NoNonlast0F Y) :
  Head0s11 R_fin \/ Strong2 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [? [h0 _]]] | [[hrem [s2 [hs2 [dlt3 [hadd hF2]]]]] |
                     [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] | [? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 7) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt0 2) as [-> | hne2].
    + destruct (f_258 (ih s1 hs1) h1 hN (or_introl eq_refl)) as [U ->].
      cbn [ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      contradiction (proj2 (f3_ne24 (ih s4 ltac:(lia)) hF4 (nnf_1F (nnf_1F hNU))) ltac:(lia)).
    + destruct (Nat.eq_dec dlt0 5) as [-> | hne5].
      * destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_introl eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
        right; exact (good1Safe_to_strong2 (proj2 (f2s_111 (ih s4 ltac:(lia)) hF4 hNU))).
      * destruct (Nat.eq_dec dlt0 8) as [-> | hne8].
        -- destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_intror eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [? ->].
           right; exact (strong2_of_2_1_1 ((1, false) :: U)).
        -- destruct (Nat.eq_dec dlt0 11) as [-> | hne11].
           ++ destruct (f_11 (ih s1 hs1) h1 hN) as [[U ->] | hG2].
              ** cbn [ones app] in hF2.
                 assert (hEx : BigF 8 ((3, false) :: (1, false) :: (1, false) :: (1, false) ::
                   (0, true) :: (1, false) :: (1, false) :: U) 7
                   ((2, false) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U)).
                 { pose proof (BF_zeroT ((1, false) :: (1, false) :: U)) as h0.
                   pose proof (BF_oneF_rem1 h0 eq_refl) as h1'.
                   pose proof (BF_oneF_rem1 h1' eq_refl) as h2'.
                   pose proof (BF_oneF_rem1 h2' eq_refl) as h3'.
                   pose proof (bigF_2s_0s_full_exists ((0, true) :: (1, false) :: (1, false) :: (1, false) :: U)) as h4'.
                   exact (BF_ge3_rem0 (BD_zeroF h3') eq_refl
                     (BD_oneF (Y := (0, true) :: (0, true) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U) h4')). }
                 destruct (bigF_det hF2 hEx) as [? ->].
                 right; apply strong2_of_2_0s; right; right; right; left; eexists; reflexivity.
              ** cbn [ones app] in hF2.
                 right; exact (proj2 (proj2 (good2_f3111 (ih s2 hs2) (proj1 hG2) hF2 hN1)) hG2).
           ++ assert (hq4 : dlt0 / 3 = S (S (S (S (dlt0 / 3 - 4))))) by dlia.
              rewrite hq4 in hF2. cbn [ones app] in hF2.
              assert (hGZ : GoodZero111Head (ones (dlt0 / 3 - 4) ++ R1)).
              { destruct (dlt0 / 3 - 4) as [| k] eqn:hq.
                - cbn [ones app].
                  destruct (dec_head_0s R1) as [[W hW] | hno].
                  + right; exact (f_pos_0s (ih s1 hs1) h1 hN ltac:(dlia) hW).
                  + left; exact hno.
                - left; intros ? hEq; discriminate hEq. }
              right; exact (proj2 (proj2 (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1))) hGZ).
  - assert (dlt3 = 6) by lia; subst dlt3.
    destruct (bigF_zero_head_3 h1 hN) as [-> | [[Z ->] | [Z ->]]]; cbn [bumpR] in hF2.
    + destruct bigF_2_nil_exists as [? hEx].
      destruct (bigF_det hF2 hEx) as [h4 _]; lia.
    + destruct (proj1 (proj2 (proj2 (proj2 (proj2 (f2s (ih s2 hs2) hF2 (noNonlast0F_tail hN1)))))) eq_refl) as [hH | hG1].
      * left; exact hH.
      * right; exact (good1Safe_to_strong2 hG1).
    + left; exact (f3_36 (ih s2 hs2) hF2 (noNonlast0F_tail hN1) (or_intror eq_refl)).
  - assert (dlt3 = 6) by lia; subst dlt3.
    left; exact (f3_36 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1) (or_intror eq_refl)).
Qed.

Lemma step_f3_1_ne6 {m : nat} (ih : InvLt m)
    {Y R_fin : list Seg}
    (h : BigF m ((3, false) :: (1, false) :: Y) 6 R_fin) (hN : NoNonlast0F Y) : False.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F hN)) as hN1.
  destruct hcases as [[? [? [h0 _]]] | [[? [s2 [hs2 [dlt3 [hadd hF2]]]]] |
                     [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] | [hrem [hge3 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - exact (proj2 (f3_ne24 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
  - assert (dlt3 = 3) by lia; subst dlt3.
    inverts h1 as h0f hrem0 h02 heq; try lia.
    + match type of h0f with
      | BigF ?s0 _ ?dlt0' ?R0 =>
        pose proof (bigF_nnf h0f hN) as hN0;
        destruct (Nat.eq_dec dlt0' 0) as [-> | h0ne];
        [ destruct (bigF_zero_head_3 h0f hN) as [-> | [[Z ->] | [Z ->]]];
          cbn [ones app bumpR] in hF2;
          [ destruct (bigF_det hF2 bigF_2s_0_exists) as [h4 _]; lia
          | destruct (bigF_det hF2 (bigF_2s_0s_exists Z)) as [h4 _]; lia
          | destruct (f2s_1 (ih s2 hs2) hF2 (noNonlast0F_tail hN0)) as [h' | [h' | [h' | h']]]; lia ]
        | assert (hq0 : 1 <= (1 + dlt0') / 3) by dlia;
          destruct (ones_pos_cons hq0 R0) as [Z hZ];
          assert (hNZ : NoNonlast0F Z) by
            (pose proof (noNonlast0F_ones_append ((1 + dlt0') / 3) hN0) as htmp;
             rewrite hZ in htmp; exact (noNonlast0F_tail htmp));
          cbn [app] in hF2; rewrite hZ in hF2; cbn [bumpR] in hF2;
          destruct (f2s_1 (ih s2 hs2) hF2 hNZ) as [h' | [h' | [h' | h']]]; lia ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))); lia.
  - assert (dlt3 = 3) by lia; subst dlt3.
    pose proof (proj1 (f1 (ih s1 hs1) h1 hN)) as hne3.
    destruct (Nat.eq_dec dlt0 6) as [-> | hne6].
    + destruct (proj1 (proj2 (proj2 (proj2 (f1 (ih s1 hs1) h1 hN)))) eq_refl) as [U ->].
      cbn [ones app] in hF2.
      destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      pose proof (proj1 (f2s_111 (ih s4 ltac:(lia)) hF4 hNU)); lia.
    + assert (hq2 : dlt0 / 3 - 1 = S (S (dlt0 / 3 - 3))) by dlia.
      rewrite hq2 in hF2. cbn [ones app] in hF2.
      destruct (f3_11 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [h0 | [h7 | [h10 _]]]; lia.
Qed.

Lemma f_bump2_of_f11_zero {m s1 s2 dlt3 : nat} {Y R1 R_fin : list Seg}
    (ih : InvLt m) (hs1 : s1 < m) (hs2 : s2 < m)
    (h1 : BigF s1 ((1, false) :: (1, false) :: Y) 0 R1) (hN : NoNonlast0F Y)
    (hF2 : BigF s2 (bumpR (bumpR R1)) dlt3 R_fin) :
  dlt3 = 4.
Proof.
  inverts h1 as h0 hrem0 h02 heq; try lia.
  - match type of h0 with
    | BigF ?s0 _ ?dlt0 ?R0 =>
      pose proof (bigF_nnf h0 (nnf_1F hN)) as hN0;
      pose proof (proj1 (f1 (ih s0 ltac:(lia)) h0 hN)) as hne3;
      destruct (Nat.eq_dec dlt0 0) as [-> | h0ne];
      [ destruct (bigF_oneF_zero_head h0) as [W ->];
        cbn [ones app bumpR] in hF2;
        exact (proj1 (bigF_det hF2 (bigF_2s_0s_exists W)))
      | destruct (Nat.eq_dec dlt0 6) as [-> | hne6];
        [ destruct (proj1 (proj2 (proj2 (proj2 (f1 (ih s0 ltac:(lia)) h0 hN)))) eq_refl) as [U ->];
          cbn [ones app bumpR] in hF2;
          exact (proj1 (bigF_det hF2 (bigF_2s_1_1_0s_exists ((1, false) :: (1, false) :: U))))
        | assert (hq3 : (1 + dlt0) / 3 = S (S (S ((1 + dlt0) / 3 - 3)))) by dlia;
          rewrite hq3 in hF2; cbn [ones app bumpR] in hF2;
          exact (proj1 (f2s_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN0))) ] ]
    end.
  - pose proof (bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0))); lia.
Qed.

Lemma step_f3_11 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((3, false) :: (1, false) :: (1, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  dlt = 0 \/ dlt = 7 \/ (dlt = 10 /\ Good2 R_fin).
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F (nnf_1F hN))) as hN1.
  pose proof (f11 (ih s1 hs1) h1 hN) as hf11.
  destruct hcases as [[? [? [-> _]]] | [[hrem _] |
                     [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] | [hrem [hge3 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - left; reflexivity.
  - contradiction (proj1 hf11 hrem).
  - pose proof (f_bump2_of_f11_zero ih hs1 hs2 h1 hN hF2). right; left; lia.
  - pose proof (proj1 (proj2 hf11)) as hne3.
    pose proof (proj1 (proj2 (proj2 hf11))) as hne6.
    assert (hge9 : 9 <= dlt0) by dlia.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hf11)))) (or_introl (conj hrem hge9))) as hG2.
    destruct (Nat.eq_dec dlt0 9) as [-> | hne9].
    + cbn [ones app] in hF2.
      destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS].
      right; right; exact (conj eq_refl (proj1 hS)).
    + destruct (Nat.eq_dec dlt0 12) as [-> | hne12].
      * cbn [ones app] in hF2.
        destruct (good2_f3111 (ih s2 hs2) hG2 hF2 hN1) as [-> [hG _]].
        right; right; exact (conj eq_refl hG).
      * assert (hq4 : dlt0 / 3 - 1 = S (S (S (S (dlt0 / 3 - 5))))) by dlia.
        rewrite hq4 in hF2. cbn [ones app] in hF2.
        destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [hG _]].
        right; right; exact (conj eq_refl hG).
Qed.

Lemma step_f3_111 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin)
    (hN : NoNonlast0F Y) :
  (dlt = 7 \/ dlt = 10) /\ Good2 R_fin /\ (dlt = 10 -> Strong2 R_fin).
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F (nnf_1F (nnf_1F hN)))) as hN1.
  pose proof (f111 (ih s1 hs1) h1 hN) as hf111.
  destruct hcases as [[hrem _] | [[hrem _] |
                     [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] | [hrem [hge3 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - destruct hf111 as [[h0 _] | [hm _]]; dlia.
  - destruct hf111 as [[h0 _] | [hm _]]; dlia.
  - destruct hf111 as [[? [hZ _]] | [? [hge _]]]; [| lia].
    destruct hZ as [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z [-> _]]]]]]];
      cbn [bumpR] in hF2.
    + destruct (bigF_det hF2 (bigF_2s_0s_exists [(0, true); (0, false)])) as [-> ->].
      split; [left; reflexivity | split; [exact (good2_of_2_0s [(0, false)]) | intro; lia]].
    + destruct (bigF_det hF2 (bigF_2s_0s_exists ((0, true) :: (0, true) :: Z))) as [-> ->].
      split; [left; reflexivity | split; [exact (good2_of_2_0s ((0, true) :: Z)) | intro; lia]].
    + destruct (bigF_det hF2 (bigF_2s_0s_exists ((0, true) :: (1, false) :: Z))) as [-> ->].
      split; [left; reflexivity | split; [exact (good2_of_2_0s ((1, false) :: Z)) | intro; lia]].
    + destruct (bigF_det hF2 (bigF_2s_0s_exists ((1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z))) as [-> ->].
      split; [left; reflexivity | split; [exact (good2_of_2_1_1 ((0, true) :: (1, false) :: (1, false) :: Z)) | intro; lia]].
    + destruct (bigF_det hF2 (bigF_2s_0s_exists ((1, false) :: (1, false) :: (1, false) :: Z))) as [-> ->].
      split; [left; reflexivity | split; [exact (good2_of_2_1_1 ((1, false) :: Z)) | intro; lia]].
    + pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))) as hNZ.
      destruct (f2s_111 (ih s2 hs2) hF2 hNZ) as [-> hG1].
      split; [left; reflexivity | split; [exact (good1Safe_to_good2 hG1) | intro; lia]].
  - destruct hf111 as [[h0 _] | [? [hge9 [hG2 [? hS12]]]]]; [lia |].
    destruct (Nat.eq_dec dlt0 9) as [-> | hne9].
    + cbn [ones app] in hF2.
      destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS].
      split; [right; reflexivity | split; [exact (proj1 hS) | intro; exact hS]].
    + destruct (Nat.eq_dec dlt0 12) as [-> | hne12].
      * cbn [ones app] in hF2.
        pose proof (hS12 eq_refl) as hS1.
        destruct (good2_f3111 (ih s2 hs2) hG2 hF2 hN1) as [-> [hG hS]].
        split; [right; reflexivity | split; [exact hG | intro; exact (hS hS1)]].
      * assert (hq4 : dlt0 / 3 - 1 = S (S (S (S (dlt0 / 3 - 5))))) by dlia.
        rewrite hq4 in hF2. cbn [ones app] in hF2.
        assert (hGZ : GoodZero111Head (ones (dlt0 / 3 - 5) ++ R1)).
        { destruct (dlt0 / 3 - 5) as [| k].
          - cbn [ones app]. left; exact (good2_ne_zeroT hG2).
          - left; intros ? hEq; discriminate hEq. }
        destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [hG hS]].
        split; [right; reflexivity | split; [exact hG | intro; exact (hS hGZ)]].
Qed.

Lemma step_f3_1111 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin)
    (hN : NoNonlast0F Y) :
  dlt = 7 /\ Good2 R_fin /\ (GoodZero111Head Y -> Strong2 R_fin).
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  assert (h1_zero : dlt1 = 0 /\
    ((exists Z, R1 = (0, true) :: (0, true) :: (0, true) :: Z /\
        (GoodZero111Head Y -> GoodStrongHead Z)) \/
     (exists Z, R1 = (0, true) :: (0, true) :: (1, false) :: (1, false) :: Z) \/
     (exists Z, R1 = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Z))).
  { inverts h1 as h0 hrem0 h02; try lia.
    - match type of h0 with
      | BigF ?s0 _ ?dlt0 ?R0 =>
        destruct (f111 (ih s0 ltac:(lia)) h0 hN) as [[-> [hZ hTZ]] | [hm [hge9 _]]];
        [ split; [reflexivity |];
          destruct hZ as [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z [-> _]]]]]]];
          [ left; exists [(0, true); (0, false)]; split; [reflexivity |];
            intro; right; right; left; exists [(0, false)]; exact (conj eq_refl (or_intror G2_c_2_0))
          | left; exists ((0, true) :: (0, true) :: Z); split; [reflexivity |];
            intro; right; right; left; exists ((0, true) :: Z); exact (conj eq_refl (or_intror (G2_c_2_0s Z)))
          | left; exists ((0, true) :: (1, false) :: Z); split; [reflexivity |];
            intro hGZ; right; right; left; exists ((1, false) :: Z); split; [reflexivity | right];
            destruct (proj2 (hTZ hGZ) Z eq_refl) as [-> | [[W' ->] | [W' ->]]];
            [ exact G2_c_2_1 | exact (G2_c_2_1_0s W') | exact (G2_c_2_1_1 W') ]
          | left; exists ((1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z);
            split; [reflexivity | intro; right; right; right; left; eexists; reflexivity]
          | left; exists ((1, false) :: (1, false) :: (1, false) :: Z);
            split; [reflexivity | intro; right; right; right; left; eexists; reflexivity]
          | right; left; exists ((1, false) :: Z); reflexivity ]
        | split; [reflexivity | right; right];
          assert (hq3 : (1 + dlt0) / 3 = S (S (S ((1 + dlt0) / 3 - 3)))) by dlia;
          rewrite hq3; exists (ones ((1 + dlt0) / 3 - 3) ++ R0); reflexivity ]
      end.
    - match type of h0 with
      | BigF ?s0 _ _ _ =>
        destruct (f111 (ih s0 ltac:(lia)) h0 hN) as [[h0e _] | [hm _]]; dlia
      end.
    - match type of h0 with
      | BigF ?s0 _ _ _ =>
        destruct (f111 (ih s0 ltac:(lia)) h0 hN) as [[h0e _] | [hm _]]; dlia
      end. }
  destruct h1_zero as [-> hR1].
  destruct hcases as [[hrem _] | [[hrem _] |
                     [[? [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [hge3 _]]]]]; try dlia.
  pose proof (bigF_nnf h1 (nnf_1F (nnf_1F (nnf_1F (nnf_1F hN))))) as hN1.
  destruct hR1 as [[Z [-> hZS]] | [[Z ->] | [Z ->]]]; cbn [bumpR] in hF2.
  - destruct (bigF_det hF2 (bigF_2s_0s_exists ((0, true) :: Z))) as [-> ->].
    split; [reflexivity | split; [exact (good2_of_2_0s Z) | intro hGZ; exact (strong2_of_2_0s (hZS hGZ))]].
  - destruct (bigF_det hF2 (bigF_2s_0s_exists ((1, false) :: (1, false) :: Z))) as [-> ->].
    split; [reflexivity | split; [exact (good2_of_2_1_1 Z) | intro; exact (strong2_of_2_1_1 Z)]].
  - pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))) as hNZ.
    destruct (f2s_111 (ih s2 hs2) hF2 hNZ) as [-> hG1].
    split; [reflexivity | split; [exact (good1Safe_to_good2 hG1) | intro; exact (good1Safe_to_strong2 hG1)]].
Qed.

Ltac split_and := repeat lazymatch goal with |- _ /\ _ => split end.

(* ========================================================================== *)
(* Helpers for Groups 3 and 4                                                 *)
(* ========================================================================== *)

Lemma bigF_2_ne2 {m s : nat} (ih : InvLt m) (hs : s < m)
    {V R_fin : list Seg} (h : BigF s ((2, false) :: V) 2 R_fin) (hN : NoNonlast0F V) : False.
Proof.
  destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR hN)) as hN_b2.
  pose proof (bigF_nnf h1 hN_b2) as hN1.
  destruct hcases as [[? [? [h0 _]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[hrem2 [hge5 [s2 [hs2 [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [hadd hD2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]]]; try lia.
  - assert (dlt3 = 0) by lia; subst dlt3.
    destruct (f_258 (ih s1 ltac:(lia)) h1 hN_b2 (or_introl eq_refl)) as [U ->].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 ltac:(lia)) hF2 hNU) as [[h4 _] | [[h10 _] | h13]]; lia.
  - assert (dlt3 = 0) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt1 5) as [-> | hne5].
    + destruct (f_258 (ih s1 ltac:(lia)) h1 hN_b2 (or_intror (or_introl eq_refl))) as [U ->].
      cbn [ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [? [? [? [hadd4 _]]]]; lia.
    + destruct (Nat.eq_dec dlt1 8) as [-> | hne8].
      * destruct (f_258 (ih s1 ltac:(lia)) h1 hN_b2 (or_intror (or_intror eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [? [? [? [hadd4 _]]]]; lia.
      * destruct (Nat.eq_dec dlt1 11) as [-> | hne11].
        -- destruct (f_11 (ih s1 ltac:(lia)) h1 hN_b2) as [[U ->] | hS]; cbn [ones app] in hF2.
           ++ destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
           ++ pose proof (proj1 (good2_f311 (ih s2 ltac:(lia)) (proj1 hS) hF2 hN1)); lia.
        -- assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
           rewrite hq3 in hF2. cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) as [h710 _]; lia.
  - pose proof (bigD1_ge2_of_ne_nil hD2 (bigF_out_ne_nil h1)); lia.
Qed.

Lemma bigF_2_0_exists :
  exists s, BigF s [(2, false); (0, false)] 0 [(0, true); (1, false); (1, false)].
Proof.
  destruct bigF_2_nil_exists as [s1 h1].
  eexists. exact (BF_twoF_rem1 (Y := [(0, false)]) h1 eq_refl).
Qed.

Lemma bigF_3_1_nil_exists :
  BigF 6 [(3, false); (1, false)] 7 [(2, false)].
Proof.
  assert (h1 : BigD1 2 [(0, false); (1, false)] 3 [(0, true); (0, false)])
    by exact (BD_zeroF (BF_oneF_rem1 BF_nil eq_refl)).
  exact (BF_ge3_rem0 h1 eq_refl (BD_oneF (Y := [(0, true); (0, false)]) bigF_2s_0_exists)).
Qed.

Lemma bigF_3_1_1_1_nil_exists :
  BigF 8 [(3, false); (1, false); (1, false); (1, false)] 7
    [(2, false); (0, true); (0, false)].
Proof.
  pose proof BF_nil as h0.
  pose proof (BF_oneF_rem1 h0 eq_refl) as h1.
  pose proof (BF_oneF_rem1 h1 eq_refl) as h2.
  pose proof (BF_oneF_rem1 h2 eq_refl) as h3.
  pose proof (bigF_2s_0s_full_exists [(0, true); (0, false)]) as h4.
  exact (BF_ge3_rem0 (BD_zeroF h3) eq_refl
    (BD_oneF (Y := [(0, true); (0, true); (0, true); (0, false)]) h4)).
Qed.

Lemma bigF_3_1_1_1_0s_1_1_exists (U : list Seg) :
  BigF 8 ((3, false) :: (1, false) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: U) 7
    ((2, false) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U).
Proof.
  pose proof (BF_zeroT ((1, false) :: (1, false) :: U)) as h0.
  pose proof (BF_oneF_rem1 h0 eq_refl) as h1.
  pose proof (BF_oneF_rem1 h1 eq_refl) as h2.
  pose proof (BF_oneF_rem1 h2 eq_refl) as h3.
  pose proof (bigF_2s_0s_full_exists ((0, true) :: (1, false) :: (1, false) :: (1, false) :: U)) as h4.
  exact (BF_ge3_rem0 (BD_zeroF h3) eq_refl
    (BD_oneF (Y := (0, true) :: (0, true) :: (0, true) :: (1, false) :: (1, false) :: (1, false) :: U) h4)).
Qed.

Lemma bigF_3_1_1_2_seven_strong {m s : nat} (ih : InvLt m) (hs : s < m)
    {W R_fin : list Seg} (h : BigF s ((3, false) :: (1, false) :: (1, false) :: (2, false) :: W) 7 R_fin)
    (hN : NoNonlast0F W) : Strong2 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (nnf_2F hN) as hN2W.
  pose proof (bigF_nnf h1 (nnf_1F (nnf_1F hN2W))) as hN1.
  pose proof (f11 (ih s1 ltac:(lia)) h1 hN2W) as hf11.
  destruct hcases as [[? [? [h0 _]]] | [[hrem _] |
                     [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] | [hrem [hge3 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 4) by lia; subst dlt3.
    inverts h1 as h0f hrem0f h02; try lia.
    + match type of h0f with
      | BigF ?s0 _ ?dlt0' ?R0 =>
        pose proof (bigF_nnf h0f (nnf_1F hN2W)) as hN0;
        destruct (Nat.eq_dec dlt0' 0) as [-> | h0ne];
        [ inverts h0f as hy hremy hy2; try lia;
          [ match type of hy with
            | BigF ?sy _ ?dlty ?Ry =>
              destruct (Nat.eq_dec dlty 0) as [-> | hyne];
              [ destruct W as [| [dx bx] xs];
                [ destruct bigF_2_nil_exists as [? hEx];
                  destruct (bigF_det hy hEx) as [h4 _]; lia
                | destruct (bigF_ge2_zero_head hy) as [Z ->];
                  cbn [ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, false) :: Z))) as [? ->];
                  apply strong2_of_2_0s; right; right; right; left; exists Z; reflexivity ]
              | destruct (Nat.eq_dec dlty 3) as [-> | h3ne];
                [ destruct (bigF_three_head hy) as [Z ->];
                  cbn [ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((1, false) :: (0, true) :: (1, false) :: Z))) as [? ->];
                  exact (strong2_of_2_1_0s ((1, false) :: Z))
                | assert (hq2 : (1 + dlty) / 3 = S (S ((1 + dlty) / 3 - 2))) by dlia;
                  rewrite hq2 in hF2; cbn [ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists
                    ((1, false) :: (1, false) :: ones ((1 + dlty) / 3 - 2) ++ Ry))) as [? ->];
                  exact (strong2_of_2_1_1 (ones ((1 + dlty) / 3 - 2) ++ Ry)) ] ]
            end
          | pose proof (bigD1_ge2_of_ne_nil hy2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hy))); lia ]
        | pose proof (proj1 (f1 (ih s0 ltac:(lia)) h0f hN2W)) as hne3;
          destruct (Nat.eq_dec dlt0' 6) as [-> | hne6];
          [ destruct (proj1 (proj2 (proj2 (proj2 (f1 (ih s0 ltac:(lia)) h0f hN2W)))) eq_refl) as [U ->];
            cbn [ones app bumpR] in hF2;
            destruct (bigF_det hF2 (bigF_2s_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [? ->];
            exact (good1Safe_to_strong2 (good1Safe_of_1s_0s_1_1 ((1, false) :: U)))
          | assert (hq3 : (1 + dlt0') / 3 = S (S (S ((1 + dlt0') / 3 - 3)))) by dlia;
            rewrite hq3 in hF2; cbn [ones app bumpR] in hF2;
            exact (good1Safe_to_strong2 (proj2 (f2s_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN0)))) ] ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))); lia.
  - assert (dlt3 = 4) by lia; subst dlt3.
    pose proof (proj1 (proj2 hf11)) as hne3.
    pose proof (proj1 (proj2 (proj2 hf11))) as hne6.
    assert (hge9 : 9 <= dlt0) by dlia.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hf11)))) (or_introl (conj hrem hge9))) as hG2.
    destruct (Nat.eq_dec dlt0 9) as [-> | hne9].
    + cbn [ones app] in hF2.
      pose proof (proj1 (good2_f311 (ih s2 ltac:(lia)) hG2 hF2 hN1)); lia.
    + destruct (Nat.eq_dec dlt0 12) as [-> | hne12].
      * cbn [ones app] in hF2.
        pose proof (proj1 (good2_f3111 (ih s2 ltac:(lia)) hG2 hF2 hN1)); lia.
      * assert (hq4 : dlt0 / 3 - 1 = S (S (S (S (dlt0 / 3 - 5))))) by dlia.
        rewrite hq4 in hF2. cbn [ones app] in hF2.
        pose proof (proj1 (f3_1111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1))); lia.
Qed.

Lemma bigF_3_1_1_goodF2U_7 {m s : nat} (ih : InvLt m) (hs : s < m)
    {U R_fin : list Seg} (hU : GoodF2U U)
    (h : BigF s ((3, false) :: (1, false) :: (1, false) :: U) 7 R_fin) (hN : NoNonlast0F U) :
  Good2 R_fin.
Proof.
  destruct hU as [[W ->] | [[W ->] | [[W ->] | [W ->]]]].
  - exact (proj1 (proj2 (f3_111 (ih s hs) h (noNonlast0F_tail hN)))).
  - destruct (bigF_det h (bigF_3_1_1_1s_exists W)) as [? ->].
    exact (good2_of_2_0s (bumpR W)).
  - exact (proj1 (bigF_3_1_1_2_seven_strong ih hs h (noNonlast0F_tail hN))).
  - destruct (bigF_det h (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: W))) as [? ->].
    exact (good2_of_2_1_1 ((1, false) :: W)).
Qed.

Lemma bigF_3_2_12_strong {m s : nat} (ih : InvLt m) (hs : s < m)
    {W R_fin : list Seg} (h : BigF s ((3, false) :: (2, false) :: W) 12 R_fin)
    (hN : NoNonlast0F W) : Head0s11 R_fin \/ Strong2 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (nnf_2F hN) as hN2W.
  pose proof (bigF_nnf h1 hN2W) as hN1.
  destruct hcases as [[? [? [h0 _]]] |
    [[hrem2 [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [hrem0 [hge3 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 10) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt0 2) as [-> | hne2].
    + contradiction (bigF_2_ne2 (s := s1) ih ltac:(lia) h1 hN).
    + destruct (Nat.eq_dec dlt0 5) as [-> | hne5].
      * destruct (f_258 (ih s1 ltac:(lia)) h1 hN2W (or_intror (or_introl eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
        pose proof (proj1 (f2s_111 (ih s4 ltac:(lia)) hF4 hNU)); lia.
      * destruct (Nat.eq_dec dlt0 8) as [-> | hne8].
        -- destruct (f_258 (ih s1 ltac:(lia)) h1 hN2W (or_intror (or_intror eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
        -- destruct (Nat.eq_dec dlt0 11) as [-> | hne11].
           ++ destruct (f_11 (ih s1 ltac:(lia)) h1 hN2W) as [[U ->] | hS]; cbn [ones app] in hF2.
              ** destruct (bigF_det hF2 (bigF_3_1_1_1_0s_1_1_exists U)) as [h7 _]; lia.
              ** pose proof (proj1 (good2_f3111 (ih s2 ltac:(lia)) (proj1 hS) hF2 hN1)); lia.
           ++ assert (hq4 : dlt0 / 3 = S (S (S (S (dlt0 / 3 - 4))))) by dlia.
              rewrite hq4 in hF2. cbn [ones app] in hF2.
              pose proof (proj1 (f3_1111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1))); lia.
  - assert (dlt3 = 9) by lia; subst dlt3.
    destruct W as [| [dx bx] xs].
    + destruct bigF_2_nil_exists as [? hEx].
      destruct (bigF_det h1 hEx) as [h4 _]; lia.
    + destruct (bigF_ge2_zero_head h1) as [Z ->].
      cbn [bumpR] in hF2.
      pose proof (noNonlast0F_tail (noNonlast0F_tail hN1)) as hNZ.
      destruct (f2s_1 (ih s2 ltac:(lia)) hF2 hNZ) as [h' | [h' | [h' | h']]]; lia.
  - assert (dlt3 = 9) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt0 3) as [-> | hne3].
    + cbn [ones app] in hF2. exact (f3_9 (ih s2 ltac:(lia)) hF2 hN1).
    + destruct (Nat.eq_dec dlt0 6) as [-> | hne6].
      * cbn [ones app] in hF2. exact (f3_9 (ih s2 ltac:(lia)) hF2 (nnf_1F hN1)).
      * destruct (Nat.eq_dec dlt0 9) as [-> | hne9].
        -- cbn [ones app] in hF2.
           destruct (f3_11 (ih s2 ltac:(lia)) hF2 hN1) as [h0 | [h7 | [h10 _]]]; lia.
        -- assert (hq3 : dlt0 / 3 - 1 = S (S (S (dlt0 / 3 - 4)))) by dlia.
           rewrite hq3 in hF2. cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) as [h710 _]; lia.
Qed.

Lemma bigF_2_4_head {m s : nat} (ih : InvLt m) (hs : s < m)
    {Z R0 : list Seg} (h : BigF s ((2, false) :: Z) 4 R0) (hN : NoNonlast0F Z) :
  R0 = [(1, false)] \/
  (exists W, R0 = (2, false) :: (0, true) :: W /\
    (W = [(0, false)] \/ (exists U, W = (0, true) :: U) \/ (exists U, W = (1, false) :: U))) \/
  (exists W, R0 = (2, false) :: (1, false) :: W).
Proof.
  destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR hN)) as hN_b2.
  pose proof (bigF_nnf h1 hN_b2) as hN1.
  destruct hcases as [[? [? [h0 _]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[hrem2 [hge5 [s2 [hs2 [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [hadd hD2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]]]; try lia.
  - destruct (f_258 (ih s1 ltac:(lia)) h1 hN_b2 (or_introl eq_refl)) as [U ->].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 ltac:(lia)) hF2 hNU) as [[h4 _] | [[h10 _] | h13]]; lia.
  - contradiction (proj1 (f3_ne24 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
  - assert (dlt2 = 3) by lia; subst dlt2.
    destruct Z as [| [dx bx] xs].
    + destruct bigF_2_nil_exists as [? hEx].
      destruct (bigF_det h hEx) as [? ->]. left; reflexivity.
    + destruct dx as [| dx'].
      * destruct bx.
        -- cbn [bumpR] in h1.
           destruct (proj1 (proj2 (proj2 (f2s (ih s1 ltac:(lia)) h1 (noNonlast0F_tail hN)))) eq_refl) as [U [-> _]].
           destruct (bigD1_zeroT_inv hD2) as [? ->].
           right; right; exists U; reflexivity.
        -- destruct xs as [| y ys]; [| contradiction hN].
           destruct bigF_2_0_exists as [? hEx].
           destruct (bigF_det h hEx) as [h0 _]; lia.
      * cbn [bumpR] in h1.
        inverts h1 as hd1 hremd1 hd2; try lia.
        -- match type of hd1 with
           | BigD1 _ _ ?dltd1 ?Rd1 =>
             pose proof (bigD1_ge2_of_ne_nil hd1 ltac:(discriminate)) as hge2;
             destruct (bigD1_zeroT_inv hD2) as [? ->];
             destruct (Nat.eq_dec dltd1 4) as [-> | h4ne];
             [ pose proof (noNonlast0F_tail hN) as hNxs;
               inverts hd1 as h0f heqd; try lia;
               [ match type of h0f with BigF _ _ ?d0 _ => assert (d0 = 1) by lia; subst d0 end;
                 contradiction (bigF_ne_one h0f)
               | match type of h0f with BigF ?s0f _ ?d0 _ =>
                   assert (d0 = 2) by lia; subst d0;
                   destruct (f_258 (ih s0f ltac:(lia)) h0f (noNonlast0F_bumpR (noNonlast0F_bumpR hNxs))
                     (or_introl eq_refl)) as [U ->];
                   right; left; exists ((1, false) :: (1, false) :: U);
                   split; [reflexivity | right; right; eexists; reflexivity]
                 end
               | match type of h0f with BigF ?s0f _ ?d0 _ =>
                   assert (d0 = 2) by lia; subst d0;
                   destruct (f_258 (ih s0f ltac:(lia)) h0f (nnf_1F hNxs) (or_introl eq_refl)) as [U ->];
                   right; left; exists ((1, false) :: (1, false) :: U);
                   split; [reflexivity | right; right; eexists; reflexivity]
                 end
               | match type of h0f with BigD1 _ _ ?d0 _ => assert (d0 = 2) by lia; subst d0 end;
                 destruct (bigD1_two_head_nnf h0f hNxs) as [-> | [[U ->] | [U ->]]];
                 [ right; left; exists [(0, false)]; split; [reflexivity | left; reflexivity]
                 | right; left; exists ((0, true) :: U); split; [reflexivity | right; left; exists U; reflexivity]
                 | right; left; exists ((1, false) :: U); split; [reflexivity | right; right; exists U; reflexivity] ] ]
             | assert (hq2 : dltd1 / 3 = S (S (dltd1 / 3 - 2))) by dlia;
               rewrite hq2; right; right; exists (ones (dltd1 / 3 - 2) ++ Rd1); reflexivity ]
           end.
        -- pose proof (bigD1_ge2_of_ne_nil hd2 (append_nonempty_of_right _ _ (bigD1_out_ne_nil hd1))); lia.
  - assert (dlt3 = 1) by lia; subst dlt3; contradiction (bigF_ne_one hF2).
  - assert (dlt3 = 1) by lia; subst dlt3; contradiction (bigF_ne_one hF2).
Qed.

Lemma bigF_2_1_7_head {m s : nat} (ih : InvLt m) (hs : s < m)
    {W Rx : list Seg} (h : BigF s ((2, false) :: (1, false) :: W) 7 Rx) (hN : NoNonlast0F W) :
  Head0s111 Rx \/ Good1Safe Rx.
Proof.
  destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  cbn [bumpR] in h1.
  pose proof (bigF_nnf h1 (nnf_3F hN)) as hN1.
  destruct hcases as [[? [? [h0 _]]] |
    [[-> _] |
    [[hrem2 [hge5 [s2 [hs2 [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [hadd hD2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]]]; try lia.
  - contradiction (proj1 (f3_ne24 (ih s1 ltac:(lia)) h1 hN) eq_refl).
  - assert (dlt3 = 5) by lia; subst dlt3.
    left; exact (f3_5_0111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)).
  - destruct (bigF_3_zero_prefix h1) as [U ->].
    destruct (bigD1_zeroT_inv hD2) as [h3 _]; lia.
  - assert (dlt3 = 4) by lia; subst dlt3.
    assert (hGF : exists U, R1 = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U).
    { destruct W as [| [dx bx] xs].
      - destruct (f3_3_non0s (ih s1 ltac:(lia)) h1 I (fun _ hEq => ltac:(discriminate hEq))) as [U [-> hSU]].
        exists U; exact (conj eq_refl (safeU_to_goodF2U hSU)).
      - destruct (dec_seg_0s dx bx) as [[-> ->] | h0s].
        + destruct (bigF_3_0s_inv h1) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
          assert (dlt4 = 0) by lia; subst dlt4.
          exact (bigF_3_zero_goodF2U (s := s4) ih ltac:(lia) hF4 (noNonlast0F_tail hN)).
        + destruct (f3_3_non0s (ih s1 ltac:(lia)) h1 hN
            (fun Z hEq => ltac:(inversion hEq; subst; exact (h0s (conj eq_refl eq_refl))))) as [U [-> hSU]].
          exists U; exact (conj eq_refl (safeU_to_goodF2U hSU)). }
    destruct hGF as [U [-> hGFU]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 ltac:(lia)) hF2 hNU) as [[? hG1] | [[h10 _] | h13]]; try lia.
    right; exact (hG1 (goodF2U_to_goodZero111Head hGFU)).
  - contradiction (proj2 (f3_ne24 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
Qed.

Lemma validHead_decomp {rs : list Seg} (vh : ValidHead rs) (hN : NoNonlast0F rs) :
  rs = [(0, false)] \/ (exists Z, rs = (0, true) :: Z) \/ (exists Z, rs = (1, false) :: Z) \/
  (exists Z, rs = (1, true) :: Z) \/ (exists Z, rs = (2, false) :: Z).
Proof.
  destruct rs as [| [[| [| [| d3]]] []] xs]; try contradiction vh.
  - right; left; exists xs; reflexivity.
  - destruct xs as [| y ys]; [left; reflexivity | contradiction hN].
  - right; right; right; left; exists xs; reflexivity.
  - right; right; left; exists xs; reflexivity.
  - right; right; right; right; exists xs; reflexivity.
Qed.

Lemma bigF_3_1_12_of_validHead {m s : nat} (ih : InvLt m) (hs : s < m)
    {R1 R_fin : list Seg} (h : BigF s ((3, false) :: (1, false) :: R1) 12 R_fin)
    (hN1 : NoNonlast0F R1)
    (hHead : R1 = [(0, false)] \/ (exists Z, R1 = (0, true) :: Z) \/ (exists Z, R1 = (1, false) :: Z) \/
      (exists Z, R1 = (1, true) :: Z) \/ (exists Z, R1 = (2, false) :: Z)) :
  Head0s11 R_fin \/ Strong2 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R0 [h1 hcases]]]]].
  pose proof (nnf_1F hN1) as hN11.
  pose proof (bigF_nnf h1 hN11) as hN0.
  destruct hcases as [[? [? [h0 _]]] |
    [[hrem2 [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [hrem0 [hge3 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 10) by lia; subst dlt3.
    destruct (Nat.eq_dec dlt0 2) as [-> | hne2].
    + destruct (f_258 (ih s1 ltac:(lia)) h1 hN11 (or_introl eq_refl)) as [U ->].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN0))) as hNU.
      cbn [ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
      assert (dlt4 = 7) by lia; subst dlt4.
      destruct (bigF_1_inv h1) as [sa [hsa [dlta [Ra [ha hca]]]]].
      pose proof (bigF_nnf ha hN1) as hNa.
      destruct hca as [[? [h0 _]] |
        [[hrema [hgea [sb [hsb [dltb [haddb hFb]]]]]] |
        [[-> [? [? [? [haddb _]]]]] |
         [? [? [? [? [? [haddb _]]]]]]]]]; try lia.
      assert (dltb = 0) by lia; subst dltb.
      pose proof (noNonlast0F_ones_append (dlta / 3 - 1) hNa) as hNX.
      destruct (bigF_3_inv hFb) as [sc [hsc [dltc [Rc [hc hcc]]]]].
      pose proof (bigF_nnf hc hNX) as hNc.
      destruct hcc as [[hremc [hgec [? hEqU]]] | [[? [? [? [? [haddc _]]]]] |
                      [[? [? [? [? [haddc _]]]]] | [? [? [? [? [? [haddc _]]]]]]]]]; try lia.
      assert (hU : U = ones (dltc / 3 - 1) ++ Rc) by congruence; subst U; clear hEqU.
      destruct (Nat.eq_dec dltc 4) as [-> | hne4c].
      * cbn [Nat.div Nat.sub ones app] in hF4.
        destruct (f_4_head (ih sc ltac:(lia)) hc hNX) as [-> | [[W ->] | [W ->]]].
        -- destruct (bigF_det hF4 bigF_3_1_1_1_nil_exists) as [? ->].
           right; exact (strong2_of_2_0s (or_intror (or_introl eq_refl))).
        -- exfalso.
           destruct (Nat.eq_dec dlta 4) as [-> | hne4a].
           ++ cbn [Nat.div Nat.sub ones app] in hc.
              destruct hHead as [-> | [[Z ->] | [[Z ->] | [[Z ->] | [Z ->]]]]].
              ** inverts ha; lia.
              ** inverts ha; lia.
              ** exact (proj1 (proj2 (f1 (ih sa ltac:(lia)) ha (noNonlast0F_tail hN1))) eq_refl).
              ** inverts ha; lia.
              ** destruct (bigF_2_4_head (s := sa) ih ltac:(lia) ha (noNonlast0F_tail hN1)) as [-> | [[W' [-> _]] | [W' ->]]].
                 --- inverts hc as h0 hrem _; try lia; inverts h0; dlia.
                 --- destruct (bigF_2_4_head (s := sc) ih ltac:(lia) hc (noNonlast0F_tail hNa)) as [hE | [[? [hE _]] | [? hE]]]; discriminate hE.
                 --- destruct (bigF_2_4_head (s := sc) ih ltac:(lia) hc (noNonlast0F_tail hNa)) as [hE | [[? [hE _]] | [? hE]]]; discriminate hE.
           ++ assert (hq1 : 1 <= dlta / 3 - 1) by dlia.
              destruct (ones_pos_cons hq1 Ra) as [W' hW'].
              assert (hNW' : NoNonlast0F W') by (rewrite hW' in hNX; exact (noNonlast0F_tail hNX)).
              rewrite hW' in hc.
              exact (proj1 (proj2 (f1 (ih sc ltac:(lia)) hc hNW')) eq_refl).
        -- right; exact (bigF_3_1_1_2_seven_strong (s := s4) ih ltac:(lia) hF4 (noNonlast0F_tail hNc)).
      * destruct (Nat.eq_dec dltc 7) as [-> | hne7c].
        -- cbn [Nat.div Nat.sub ones app] in hF4.
           assert (hRc_good : Head0s111 Rc \/ Good1Safe Rc).
           { destruct (Nat.eq_dec dlta 4) as [-> | hne4a].
             - cbn [Nat.div Nat.sub ones app] in hc.
               destruct hHead as [-> | [[Z ->] | [[Z ->] | [[Z ->] | [Z ->]]]]].
               + inverts ha; lia.
               + inverts ha; lia.
               + contradiction (proj1 (proj2 (f1 (ih sa ltac:(lia)) ha (noNonlast0F_tail hN1))) eq_refl).
               + inverts ha; lia.
               + destruct (bigF_2_4_head (s := sa) ih ltac:(lia) ha (noNonlast0F_tail hN1)) as [-> | [[W [-> hW]] | [W ->]]].
                 * inverts hc as h0 hrem _; try lia; inverts h0; dlia.
                 * destruct hW as [-> | [[V ->] | [V ->]]].
                   -- destruct (bigF_2_inv hc) as [s2a [? [dlt2a [R2a [h2a hc2a]]]]].
                      cbn [bumpR] in h2a.
                      destruct (bigF_det h2a bigF_2s_0_exists) as [-> _].
                      destruct hc2a as [[? [? [h0 _]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]]; dlia.
                   -- destruct (bigF_2_inv hc) as [s2a [? [dlt2a [R2a [h2a hc2a]]]]].
                      cbn [bumpR] in h2a.
                      destruct (bigF_det h2a (bigF_2s_0s_full_exists V)) as [-> _].
                      destruct hc2a as [[? [? [h0 _]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]]; dlia.
                   -- destruct (bigF_2_inv hc) as [s2a [hs2a [dlt2a [R2a [h2a hc2a]]]]].
                      cbn [bumpR] in h2a.
                      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNa))) as hNV.
                      destruct (f2s_1 (ih s2a ltac:(lia)) h2a hNV) as [-> | [-> | [-> | ->]]].
                      ++ destruct hc2a as [[hrem _] | [[h2 _] | [[hrem _] | [[? [sd [? [dltd [haddd hDd]]]]] | [[h3 _] | [? [hge6 _]]]]]]]; try dlia.
                         destruct (proj1 (proj2 (proj2 (f2s (ih s2a ltac:(lia)) h2a (nnf_1F hNV)))) eq_refl) as [U2 [-> _]].
                         destruct (bigD1_zeroT_inv hDd) as [h3 _]; lia.
                      ++ destruct hc2a as [[? [? [h0 _]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]]; dlia.
                      ++ destruct hc2a as [[? [? [h0 _]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]]; dlia.
                      ++ destruct hc2a as [[? [? [h0 _]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]]; dlia.
                 * exact (bigF_2_1_7_head (s := sc) ih ltac:(lia) hc (noNonlast0F_tail (noNonlast0F_tail hNa))).
             - destruct (Nat.eq_dec dlta 7) as [-> | hne7a].
               + cbn [Nat.div Nat.sub ones app] in hc.
                 exact (proj1 (proj2 (proj2 (proj2 (proj2 (f1 (ih sc ltac:(lia)) hc hNa))))) eq_refl).
               + destruct (Nat.eq_dec dlta 10) as [-> | hne10a].
                 * cbn [Nat.div Nat.sub ones app] in hc.
                   right; exact (proj1 (proj2 (proj2 (proj2 (f11 (ih sc ltac:(lia)) hc hNa)))) eq_refl).
                 * assert (hq3 : dlta / 3 - 1 = S (S (S (dlta / 3 - 4)))) by dlia.
                   rewrite hq3 in hc. cbn [ones app] in hc.
                   destruct (f111 (ih sc ltac:(lia)) hc (noNonlast0F_ones_append _ hNa)) as [[h0 _] | [hm _]]; dlia. }
           destruct hRc_good as [[V ->] | hG1].
           ++ destruct (bigF_det hF4 (bigF_3_1_1_1_0s_1_1_exists ((1, false) :: V))) as [? ->].
              right; apply strong2_of_2_0s; right; right; right; left; eexists; reflexivity.
           ++ right; exact (proj2 (proj2 (good2_f3111 (ih s4 ltac:(lia)) (good1Safe_to_good2 hG1) hF4 hNc))
                (good1Safe_to_strong2 hG1)).
        -- assert (hq2 : dltc / 3 - 1 = S (S (dltc / 3 - 3))) by dlia.
           rewrite hq2 in hF4. cbn [ones app] in hF4.
           assert (hGZ : GoodZero111Head (ones (dltc / 3 - 3) ++ Rc)).
           { destruct (dltc / 3 - 3) as [| k] eqn:hq.
             - cbn [ones app].
               destruct (dec_head_0s Rc) as [[W hW] | hno].
               + right; exact (f_pos_0s (ih sc ltac:(lia)) hc hNX ltac:(dlia) hW).
               + left; exact hno.
             - left; intros ? hEq; discriminate hEq. }
           right; exact (proj2 (proj2 (f3_1111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_ones_append _ hNc))) hGZ).
    + destruct (Nat.eq_dec dlt0 5) as [-> | hne5].
      * destruct (f_258 (ih s1 ltac:(lia)) h1 hN11 (or_intror (or_introl eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN0))) as hNU.
        pose proof (proj1 (f2s_111 (ih s4 ltac:(lia)) hF4 hNU)); lia.
      * destruct (Nat.eq_dec dlt0 8) as [-> | hne8].
        -- destruct (f_258 (ih s1 ltac:(lia)) h1 hN11 (or_intror (or_intror eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
        -- destruct (Nat.eq_dec dlt0 11) as [-> | hne11].
           ++ destruct (f_11 (ih s1 ltac:(lia)) h1 hN11) as [[U ->] | hS]; cbn [ones app] in hF2.
              ** destruct (bigF_det hF2 (bigF_3_1_1_1_0s_1_1_exists U)) as [h7 _]; lia.
              ** pose proof (proj1 (good2_f3111 (ih s2 ltac:(lia)) (proj1 hS) hF2 hN0)); lia.
           ++ assert (hq4 : dlt0 / 3 = S (S (S (S (dlt0 / 3 - 4))))) by dlia.
              rewrite hq4 in hF2. cbn [ones app] in hF2.
              pose proof (proj1 (f3_1111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN0))); lia.
  - assert (dlt3 = 9) by lia; subst dlt3.
    destruct (bigF_oneF_zero_head h1) as [W ->].
    cbn [bumpR] in hF2.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (f2s (ih s2 ltac:(lia)) hF2 (noNonlast0F_tail hN0))))))) eq_refl).
  - assert (dlt3 = 9) by lia; subst dlt3.
    pose proof (proj1 (f1 (ih s1 ltac:(lia)) h1 hN1)) as hne3.
    destruct (Nat.eq_dec dlt0 6) as [-> | hne6].
    + cbn [ones app] in hF2. exact (f3_9 (ih s2 ltac:(lia)) hF2 (nnf_1F hN0)).
    + destruct (Nat.eq_dec dlt0 9) as [-> | hne9].
      * cbn [ones app] in hF2.
        destruct (f3_11 (ih s2 ltac:(lia)) hF2 hN0) as [h0 | [h7 | [h10 _]]]; lia.
      * assert (hq3 : dlt0 / 3 - 1 = S (S (S (dlt0 / 3 - 4)))) by dlia.
        rewrite hq3 in hF2. cbn [ones app] in hF2.
        destruct (f3_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN0)) as [h710 _]; lia.
Qed.

(* ========================================================================== *)
(* Group 3 Step Lemmas                                                        *)
(* ========================================================================== *)

Lemma step_f1 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((1, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  dlt <> 3 /\ dlt <> 4 /\
  (dlt = 5 -> Safe0s R_fin) /\
  (dlt = 6 -> Head0s11 R_fin) /\
  (dlt = 7 -> Head0s111 R_fin \/ Good1Safe R_fin) /\
  (dlt = 10 -> Head0s11 R_fin \/ Good2 R_fin) /\
  (dlt = 13 -> Head0s11 R_fin \/ Good2 R_fin) /\
  (dlt = 14 -> Head0s11 R_fin \/ Strong2 R_fin).
Proof.
  destruct (bigF_1_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [-> _]] |
    [[hrem1 [hge4 [s2 [hs2 [dlt3 [-> hF2]]]]]] |
    [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] |
     [hrem2 [hge5 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - split_and; intros; lia.
  - pose proof (noNonlast0F_ones_append (dlt1 / 3 - 1) hN1) as hN_in.
    pose proof (f3_ne24 (ih s2 hs2) hF2 hN_in) as [hne2 hne4].
    split; [intro; assert (dlt3 = 1) by lia; subst dlt3; exact (bigF_ne_one hF2) |].
    split; [lia |].
    split.
    + intro. assert (dlt3 = 3) by lia; subst dlt3.
      apply (f3_3_non0s (ih s2 hs2) hF2 hN_in).
      intros Z hZ.
      destruct (Nat.eq_dec dlt1 4) as [-> | h4ne].
      * cbn [Nat.div Nat.sub ones app] in hZ.
        exact (InvAt_f_4_ne0s (ih s1 hs1) h1 hN hZ).
      * assert (hq1 : 1 <= dlt1 / 3 - 1) by dlia.
        destruct (ones_pos_cons hq1 R1) as [W hW].
        rewrite hW in hZ. discriminate hZ.
    + split; [lia |].
      split.
      * intro. assert (dlt3 = 5) by lia; subst dlt3.
        left; exact (f3_5_0111 (ih s2 hs2) hF2 hN_in).
      * split.
        -- intro. assert (dlt3 = 8) by lia; subst dlt3.
           left; exact (f_258 (ih s2 hs2) hF2 (nnf_3F hN_in) (or_intror (or_intror eq_refl))).
        -- split.
           ++ intro. assert (dlt3 = 11) by lia; subst dlt3.
              destruct (f_11 (ih s2 hs2) hF2 (nnf_3F hN_in)) as [hH | hS]; [left; exact hH | right; exact (proj1 hS)].
           ++ intro. assert (dlt3 = 12) by lia; subst dlt3.
              destruct (Nat.eq_dec dlt1 4) as [-> | h4ne].
              ** cbn [Nat.div Nat.sub ones app] in hF2.
                 destruct (f_4_head (ih s1 hs1) h1 hN) as [-> | [[W ->] | [W ->]]].
                 --- destruct (bigF_det hF2 bigF_3_1_nil_exists) as [h7 _]; lia.
                 --- destruct (bigF_3_1s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
                     assert (dlt4 = 9) by lia; subst dlt4.
                     exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (f2s (ih s4 ltac:(lia)) hF4
                       (noNonlast0F_bumpR (noNonlast0F_tail hN1)))))))) eq_refl).
                 --- exact (bigF_3_2_12_strong ih hs2 hF2 (noNonlast0F_tail hN1)).
              ** destruct (Nat.eq_dec dlt1 7) as [-> | h7ne].
                 --- cbn [Nat.div Nat.sub ones app] in hF2.
                     exact (bigF_3_1_12_of_validHead ih hs2 hF2 hN1
                       (validHead_decomp (bigF_head_nnf _ _ _ _ h1 hN) hN1)).
                 --- destruct (Nat.eq_dec dlt1 10) as [-> | h10ne].
                     +++ cbn [Nat.div Nat.sub ones app] in hF2.
                         destruct (f3_11 (ih s2 hs2) hF2 hN1) as [h0 | [h7 | [h10 _]]]; lia.
                     +++ assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
                         rewrite hq3 in hF2. cbn [ones app] in hF2.
                         destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [h710 _]; lia.
  - destruct (f_25_goodF2U (ih s1 hs1) h1 hN (or_introl eq_refl)) as [U [-> hGFU]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 hs2) hF2 hNU) as [[-> hG1] | [[-> hS] | ->]].
    + split_and; try lia. intro. right; exact (hG1 (goodF2U_to_goodZero111Head hGFU)).
    + split_and; try lia. intro. right; exact (proj1 (hS hGFU)).
    + split_and; try lia.
  - pose proof (noNonlast0F_ones_append (dlt1 / 3 - 1) hN1) as hN_in.
    pose proof (f3_ne24 (ih s2 hs2) hF2 hN_in) as [hne2 hne4].
    split.
    + intro. assert (dlt3 = 0) by lia; subst dlt3.
      destruct (Nat.eq_dec dlt1 5) as [-> | hne5].
      * destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_introl eq_refl))) as [U ->].
        cbn [ones app] in hF2.
        destruct (bigF_3_0s_inv hF2) as [? [? [? [hadd _]]]]; lia.
      * destruct (Nat.eq_dec dlt1 8) as [-> | hne8].
        -- destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_intror eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_3_1_0s_inv hF2) as [? [? [? [hadd _]]]]; lia.
        -- destruct (Nat.eq_dec dlt1 11) as [-> | hne11].
           ++ destruct (f_11 (ih s1 hs1) h1 hN) as [[U ->] | hS]; cbn [ones app] in hF2.
              ** destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
              ** pose proof (proj1 (good2_f311 (ih s2 hs2) (proj1 hS) hF2 hN1)); lia.
           ++ assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
              rewrite hq3 in hF2. cbn [ones app] in hF2.
              destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [h710 _]; lia.
    + split; [intro; assert (dlt3 = 1) by lia; subst dlt3; exact (bigF_ne_one hF2) |].
      split; [lia |].
      split; [intro; assert (dlt3 = 3) by lia; subst dlt3; exact (f3_36 (ih s2 hs2) hF2 hN_in (or_introl eq_refl)) |].
      split; [lia |].
      split.
      * intro. assert (dlt3 = 7) by lia; subst dlt3.
        destruct (Nat.eq_dec dlt1 5) as [-> | hne5].
        -- destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_introl eq_refl))) as [U ->].
           cbn [ones app] in hF2.
           destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
           pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
           contradiction (proj2 (f3_ne24 (ih s4 ltac:(lia)) hF4 (nnf_1F (nnf_1F hNU))) ltac:(lia)).
        -- destruct (Nat.eq_dec dlt1 8) as [-> | hne8].
           ++ destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_intror eq_refl))) as [U ->].
              cbn [ones app] in hF2.
              destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
              pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
              right; exact (good1Safe_to_good2 (proj2 (f2s_111 (ih s4 ltac:(lia)) hF4 hNU))).
           ++ destruct (Nat.eq_dec dlt1 11) as [-> | hne11].
              ** destruct (f_11 (ih s1 hs1) h1 hN) as [[U ->] | hS]; cbn [ones app] in hF2.
                 --- destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [? ->].
                     right; exact (good2_of_2_1_1 ((1, false) :: U)).
                 --- right; exact (proj1 (proj2 (good2_f311 (ih s2 hs2) (proj1 hS) hF2 hN1))).
              ** assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
                 rewrite hq3 in hF2. cbn [ones app] in hF2.
                 right; exact (proj1 (proj2 (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)))).
      * split.
        -- intro. assert (dlt3 = 10) by lia; subst dlt3.
           destruct (Nat.eq_dec dlt1 5) as [-> | hne5].
           ++ destruct (f_25_goodF2U (ih s1 hs1) h1 hN (or_intror eq_refl)) as [U [-> hGFU]].
              cbn [ones app] in hF2.
              destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
              assert (dlt4 = 7) by lia; subst dlt4.
              pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
              right; exact (bigF_3_1_1_goodF2U_7 (s := s4) ih ltac:(lia) hGFU hF4 hNU).
           ++ destruct (Nat.eq_dec dlt1 8) as [-> | hne8].
              ** destruct (f_258 (ih s1 hs1) h1 hN (or_intror (or_intror eq_refl))) as [U ->].
                 cbn [ones app] in hF2.
                 destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [hadd4 hF4]]]].
                 pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
                 pose proof (proj1 (f2s_111 (ih s4 ltac:(lia)) hF4 hNU)); lia.
              ** destruct (Nat.eq_dec dlt1 11) as [-> | hne11].
                 --- destruct (f_11 (ih s1 hs1) h1 hN) as [[U ->] | hS]; cbn [ones app] in hF2.
                     +++ destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [h7 _]; lia.
                     +++ pose proof (proj1 (good2_f311 (ih s2 hs2) (proj1 hS) hF2 hN1)); lia.
                 --- assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
                     rewrite hq3 in hF2. cbn [ones app] in hF2.
                     right; exact (proj1 (proj2 (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)))).
        -- intro. assert (dlt3 = 11) by lia; subst dlt3.
           exact (f_11 (ih s2 hs2) hF2 (nnf_3F hN_in)).
Qed.

Lemma bigF_1_5_311_strong {m s1 s4 : nat} (ih : InvLt m) (hs1 : s1 < m) (hs4 : s4 < m)
    {Y U R_fin : list Seg} (hGF : GoodF2U Y)
    (h1 : BigF s1 ((1, false) :: Y) 5 ((0, true) :: (1, false) :: (1, false) :: U))
    (hF4 : BigF s4 ((3, false) :: (1, false) :: (1, false) :: U) 7 R_fin)
    (hN : NoNonlast0F Y) : Strong2 R_fin.
Proof.
  pose proof (bigF_nnf h1 (nnf_1F hN)) as hN_out.
  pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN_out))) as hNU.
  destruct (bigF_1_inv h1) as [sa [hsa [dlta [Ra [ha hca]]]]].
  pose proof (bigF_nnf ha hN) as hNa.
  destruct hca as [[? [h0 _]] |
    [[hrema [hgea [sb [hsb [dltb [haddb hFb]]]]]] |
    [[-> [sb [hsb [dltb [haddb hFb]]]]] |
     [hrema [hgea [sb [hsb [dltb [haddb hFb]]]]]]]]]; try lia.
  - assert (dltb = 3) by lia; subst dltb.
    pose proof (noNonlast0F_ones_append (dlta / 3 - 1) hNa) as hNX.
    destruct (bigF_3_inv hFb) as [sc [hsc [dltc [Rc [hc hcc]]]]].
    pose proof (bigF_nnf hc hNX) as hNc.
    destruct hcc as [[? [? [h0 _]]] |
      [[? [sd [hsd [dltd [haddd hFd]]]]] |
      [[-> [sd [hsd [dltd [haddd hFd]]]]] |
       [hremc [hge3c [sd [hsd [dltd [haddd hFd]]]]]]]]]; try lia.
    + assert (dltd = 1) by lia; subst dltd; contradiction (bigF_ne_one hFd).
    + assert (dltd = 0) by lia; subst dltd.
      assert (hRc1 : exists Zc, Rc = (0, true) :: (1, false) :: Zc).
      { destruct (Nat.eq_dec dlta 4) as [-> | h4ne].
        - cbn [Nat.div Nat.sub ones app] in hc.
          destruct hGF as [[W ->] | [[W ->] | [[W ->] | [W ->]]]].
          + contradiction (proj1 (proj2 (f1 (ih sa ltac:(lia)) ha (noNonlast0F_tail hN))) eq_refl).
          + inverts ha; lia.
          + destruct (bigF_2_4_head (s := sa) ih ltac:(lia) ha (noNonlast0F_tail hN)) as [-> | [[W' [-> _]] | [W' ->]]].
            * inverts hc as h0 hrem h2; try lia.
              -- inverts h0. cbn [ones app bumpR] in hFd.
                 destruct (bigF_det hFd bigF_2s_0_exists) as [h4 _]; lia.
              -- pose proof (bigD1_ge2_of_ne_nil h2 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0))); lia.
            * exact (bigF_ge2_zero_head hc).
            * exact (bigF_ge2_zero_head hc).
          + inverts ha; lia.
        - assert (hq1 : 1 <= dlta / 3 - 1) by dlia.
          destruct (ones_pos_cons hq1 Ra) as [W hW].
          assert (hNW : NoNonlast0F W) by (rewrite hW in hNX; exact (noNonlast0F_tail hNX)).
          rewrite hW in hc.
          inverts hc as hW0 hremW0 hW2; try lia.
          + match type of hW0 with
            | BigF _ _ ?dltW ?RW =>
              destruct (Nat.eq_dec dltW 0) as [-> | h0Wne];
              [ destruct (bigF_zero_head_3 hW0 hNW) as [-> | [[Z ->] | [Z ->]]];
                cbn [ones app bumpR] in hFd;
                [ destruct (bigF_det hFd bigF_2s_0_exists) as [h4 _]; lia
                | destruct (bigF_det hFd (bigF_2s_0s_full_exists Z)) as [h4 _]; lia
                | exists Z; reflexivity ]
              | assert (hqW : 1 <= (1 + dltW) / 3) by dlia;
                destruct (ones_pos_cons hqW RW) as [Z hZ];
                exists Z; cbn [app]; rewrite hZ; reflexivity ]
            end.
          + pose proof (bigD1_ge2_of_ne_nil hW2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hW0))); lia. }
      destruct hRc1 as [Zc ->].
      pose proof (noNonlast0F_tail (noNonlast0F_tail hNc)) as hNZc.
      cbn [bumpR] in hFd.
      destruct (bigF_2s_inv hFd) as [se [hse [dlte [Re [he hce]]]]].
      pose proof (bigF_nnf he (nnf_1F (nnf_1F hNZc))) as hNe.
      destruct hce as [[hreme [hgee [? hEq]]] | [[? [? [? [? [hadd _]]]]] |
                      [[? [? [? [? [? [hadd _]]]]]] | [[? [? [? [? [hadd _]]]]] |
                      [[? [? [? [? [hadd _]]]]] | [? [? [? [? [? [hadd _]]]]]]]]]]]; try lia.
      pose proof (f11 (ih se ltac:(lia)) he hNZc) as hf11e.
      pose proof (proj1 (proj2 (f1 (ih se ltac:(lia)) he (nnf_1F hNZc)))) as hne4.
      destruct (Nat.eq_dec dlte 7) as [-> | h7ne].
      * cbn [Nat.div ones app] in hEq. inversion hEq; subst U; clear hEq.
        pose proof (proj1 (proj2 (proj2 (proj2 hf11e))) eq_refl) as hG1.
        exact (proj2 (good2_f311 (ih s4 hs4) (good1Safe_to_good2 hG1) hF4 hNe)).
      * destruct (Nat.eq_dec dlte 10) as [-> | h10ne].
        -- cbn [Nat.div ones app] in hEq. inversion hEq; subst U; clear hEq.
           pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hf11e))))) eq_refl) as hS.
           exact (proj2 (proj2 (good2_f3111 (ih s4 hs4) (proj1 hS) hF4 hNe)) hS).
        -- assert (hq2 : dlte / 3 = S (S (S (S (dlte / 3 - 4))))) by dlia.
           rewrite hq2 in hEq. cbn [ones app] in hEq. inversion hEq; subst U; clear hEq.
           assert (hGZ : GoodZero111Head (ones (dlte / 3 - 4) ++ Re)).
           { destruct (dlte / 3 - 4) as [| k] eqn:hq.
             - cbn [ones app].
               destruct (dec_head_0s Re) as [[W hW] | hno].
               + right; exact (f_pos_0s (ih se ltac:(lia)) he (nnf_1F (nnf_1F hNZc)) ltac:(dlia) hW).
               + left; exact hno.
             - left; intros ? hEq2; discriminate hEq2. }
           exact (proj2 (proj2 (f3_1111 (ih s4 hs4) hF4 (noNonlast0F_ones_append _ hNe))) hGZ).
    + assert (dltd = 0) by lia; subst dltd.
      destruct (bigF_3_inv hFd) as [se [hse [dlte [Re [he hce]]]]].
      pose proof (noNonlast0F_ones_append (dltc / 3 - 1) hNc) as hNYe.
      pose proof (bigF_nnf he hNYe) as hNe.
      destruct hce as [[hreme [hgee [? hEq]]] | [[? [? [? [? [hadd _]]]]] |
                      [[? [? [? [? [hadd _]]]]] | [? [? [? [? [? [hadd _]]]]]]]]]; try lia.
      assert (hU : U = ones (dlte / 3 - 1) ++ Re) by congruence; subst U; clear hEq.
      destruct (Nat.eq_dec dlte 4) as [-> | h4ne].
      * cbn [Nat.div Nat.sub ones app] in hF4.
        destruct (f_4_head (ih se ltac:(lia)) he hNYe) as [-> | [[W ->] | [W ->]]].
        -- destruct (bigF_det hF4 bigF_3_1_1_1_nil_exists) as [? ->].
           exact (strong2_of_2_0s (or_intror (or_introl eq_refl))).
        -- exfalso.
           destruct (Nat.eq_dec dltc 3) as [-> | h3ne].
           ++ cbn [Nat.div Nat.sub ones app] in he.
              destruct (bigF_three_head hc) as [W' ->].
              inverts he; lia.
           ++ assert (hq1 : 1 <= dltc / 3 - 1) by dlia.
              destruct (ones_pos_cons hq1 Rc) as [W' hW'].
              assert (hNW' : NoNonlast0F W') by (rewrite hW' in hNYe; exact (noNonlast0F_tail hNYe)).
              rewrite hW' in he.
              exact (proj1 (proj2 (f1 (ih se ltac:(lia)) he hNW')) eq_refl).
        -- exact (bigF_3_1_1_2_seven_strong ih hs4 hF4 (noNonlast0F_tail hNe)).
      * destruct (Nat.eq_dec dlte 7) as [-> | h7ne].
        -- cbn [Nat.div Nat.sub ones app] in hF4.
           assert (hRe_good : Head0s111 Re \/ Good1Safe Re).
           { destruct (Nat.eq_dec dltc 3) as [-> | h3ne].
             - cbn [Nat.div Nat.sub ones app] in he.
               destruct (bigF_three_head hc) as [W ->].
               inverts he; lia.
             - destruct (Nat.eq_dec dltc 6) as [-> | h6ne].
               + cbn [Nat.div Nat.sub ones app] in he.
                 exact (proj1 (proj2 (proj2 (proj2 (proj2 (f1 (ih se ltac:(lia)) he hNc))))) eq_refl).
               + destruct (Nat.eq_dec dltc 9) as [-> | h9ne].
                 * cbn [Nat.div Nat.sub ones app] in he.
                   right; exact (proj1 (proj2 (proj2 (proj2 (f11 (ih se ltac:(lia)) he hNc)))) eq_refl).
                 * assert (hq3 : dltc / 3 - 1 = S (S (S (dltc / 3 - 4)))) by dlia.
                   rewrite hq3 in he. cbn [ones app] in he.
                   destruct (f111 (ih se ltac:(lia)) he (noNonlast0F_ones_append _ hNc)) as [[h0 _] | [hm _]]; dlia. }
           destruct hRe_good as [[V ->] | hG1].
           ++ destruct (bigF_det hF4 (bigF_3_1_1_1_0s_1_1_exists ((1, false) :: V))) as [? ->].
              apply strong2_of_2_0s; right; right; right; left; eexists; reflexivity.
           ++ exact (proj2 (proj2 (good2_f3111 (ih s4 hs4) (good1Safe_to_good2 hG1) hF4 hNe))
                (good1Safe_to_strong2 hG1)).
        -- assert (hq2 : dlte / 3 - 1 = S (S (dlte / 3 - 3))) by dlia.
           rewrite hq2 in hF4. cbn [ones app] in hF4.
           assert (hGZ : GoodZero111Head (ones (dlte / 3 - 3) ++ Re)).
           { destruct (dlte / 3 - 3) as [| k] eqn:hq.
             - cbn [ones app].
               destruct (dec_head_0s Re) as [[W hW] | hno].
               + right; exact (f_pos_0s (ih se ltac:(lia)) he hNYe ltac:(dlia) hW).
               + left; exact hno.
             - left; intros ? hEq2; discriminate hEq2. }
           exact (proj2 (proj2 (f3_1111 (ih s4 hs4) hF4 (noNonlast0F_ones_append _ hNe))) hGZ).
  - destruct (f_258 (ih sa ltac:(lia)) ha hN (or_introl eq_refl)) as [U1 ->].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNa))) as hNU1.
    cbn [bumpR] in hFb.
    destruct (f2s_11 (ih sb ltac:(lia)) hFb hNU1) as [[h4 _] | [[h10 _] | h13]]; lia.
  - contradiction (proj1 (f3_ne24 (ih sb ltac:(lia)) hFb (noNonlast0F_ones_append _ hNa)) ltac:(lia)).
Qed.

Lemma step_f11 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((1, false) :: (1, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  dlt mod 3 <> 2 /\ dlt <> 3 /\ dlt <> 6 /\
  (dlt = 7 -> Good1Safe R_fin) /\
  (((dlt mod 3 = 0 /\ 9 <= dlt) \/ dlt = 10) -> Good2 R_fin) /\
  (dlt = 13 -> GoodF2U Y -> Strong2 R_fin) /\
  (dlt = 10 -> Strong2 R_fin).
Proof.
  destruct (bigF_1_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (nnf_1F hN) as hN1Y.
  pose proof (bigF_nnf h1 hN1Y) as hN1.
  pose proof (f1 (ih s1 hs1) h1 hN) as hf1.
  destruct hcases as [[? [-> _]] |
    [[hrem1 [hge4 [s2 [hs2 [dlt3 [-> hF2]]]]]] |
    [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] |
     [hrem2 [hge5 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - split_and; try (intros [[? ?] | ?]; dlia); try dlia.
  - pose proof (proj1 (proj2 hf1)) as hne4.
    destruct (Nat.eq_dec dlt1 7) as [-> | h7ne].
    + destruct (proj1 (proj2 (proj2 (proj2 (proj2 hf1)))) eq_refl) as [[U ->] | hG1]; cbn [Nat.div Nat.sub ones app] in hF2.
      * destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
        destruct (f2s_111 (ih s4 ltac:(lia)) hF4 hNU) as [-> hG1'].
        split_and; try (intros [[? ?] | ?]; dlia); try dlia. intro. exact (good1Safe_to_good2 hG1').
      * destruct (good2_f31 (ih s2 hs2) (good1Safe_to_good2 hG1) hF2 hN1) as [h710 hSf].
        pose proof (hSf (good1Safe_to_strong2 hG1)) as hS.
        destruct h710 as [-> | [-> _]]; (split_and; try (intros [[? ?] | ?]; dlia); try dlia; intro; exact (proj1 hS)).
    + destruct (Nat.eq_dec dlt1 10) as [-> | h10ne].
      * destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 hf1))))) eq_refl) as [[U ->] | hG2];
          cbn [Nat.div Nat.sub ones app] in hF2.
        -- destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->].
           split_and; try (intros [[? ?] | ?]; dlia); try dlia. intro. exact (good2_of_2_1_1 ((1, false) :: U)).
        -- destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS'].
           split_and; try (intros [[? ?] | ?]; dlia); try dlia. intro. exact (proj1 hS').
      * assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
        rewrite hq3 in hF2. cbn [ones app] in hF2.
        destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] [hG2' _]];
          (split_and; try (intros [[? ?] | ?]; dlia); try dlia; intro; exact hG2').
  - destruct (f_25_goodF2U (ih s1 hs1) h1 hN1Y (or_introl eq_refl)) as [U [-> hGFU]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 hs2) hF2 hNU) as [[-> hG1] | [[-> hS] | ->]].
    + split_and; try (intros [[? ?] | ?]; dlia); try dlia. intro. exact (hG1 (goodF2U_to_goodZero111Head hGFU)).
    + split_and; try (intros [[? ?] | ?]; dlia); try dlia. intros ? ?. exact (hS hGFU).
    + split_and; try (intros [[? ?] | ?]; dlia); try dlia.
  - destruct (Nat.eq_dec dlt1 5) as [-> | h5ne].
    + destruct (proj1 (proj2 (proj2 hf1)) eq_refl) as [U [-> hSU]].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
      assert (hdlt4 : dlt4 = 7 \/ dlt4 = 10).
      { destruct hSU as [[Z ->] | [[Z [-> _]] | [[Z [-> _]] | [[Z ->] | [hG1 _]]]]].
        - left; exact (proj1 (f3_1111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail hNU)))).
        - left; exact (proj1 (f3_1111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail hNU)))).
        - exact (proj1 (f3_111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail hNU))).
        - left; exact (proj1 (bigF_det hF4 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: (1, false) :: Z)))).
        - left; exact (proj1 (good2_f311 (ih s4 ltac:(lia)) (good1_to_good2 hG1) hF4 hNU)). }
      destruct hdlt4 as [-> | ->].
      * split_and; try (intros [[? ?] | ?]; dlia); try dlia.
        intros ? hGF. exact (bigF_1_5_311_strong (s4 := s4) ih hs1 ltac:(lia) hGF h1 hF4 hN).
      * split_and; try (intros [[? ?] | ?]; dlia); try dlia.
    + destruct (Nat.eq_dec dlt1 8) as [-> | h8ne].
      * destruct (f_258 (ih s1 hs1) h1 hN1Y (or_intror (or_intror eq_refl))) as [U ->].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
        cbn [Nat.div Nat.sub ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
        destruct (f2s_111 (ih s4 ltac:(lia)) hF4 hNU) as [-> hG1'].
        split_and; try (intros [[? ?] | ?]; dlia); try dlia.
        -- intro; exact (good1Safe_to_good2 hG1').
        -- intro; exact (good1Safe_to_strong2 hG1').
      * destruct (Nat.eq_dec dlt1 11) as [-> | h11ne].
        -- destruct (f_11 (ih s1 hs1) h1 hN1Y) as [[U ->] | hS]; cbn [Nat.div Nat.sub ones app] in hF2.
           ++ destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->].
              split_and; try (intros [[? ?] | ?]; dlia); try dlia.
              ** intro; exact (good2_of_2_1_1 ((1, false) :: U)).
              ** intro; exact (strong2_of_2_1_1 ((1, false) :: U)).
           ++ destruct (good2_f311 (ih s2 hs2) (proj1 hS) hF2 hN1) as [-> hS'].
              split_and; try (intros [[? ?] | ?]; dlia); try dlia.
              ** intro; exact (proj1 hS').
              ** intro; exact hS'.
        -- destruct (Nat.eq_dec dlt1 14) as [-> | h14ne].
           ++ destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hf1)))))) eq_refl) as [[U ->] | hS];
                cbn [Nat.div Nat.sub ones app] in hF2.
              ** destruct (bigF_det hF2 (bigF_3_1_1_1_0s_1_1_exists U)) as [-> ->].
                 split_and; try (intros [[? ?] | ?]; dlia); try dlia.
                 --- intro; exact (good2_of_2_0s ((1, false) :: (1, false) :: (1, false) :: U)).
                 --- intro; apply strong2_of_2_0s; right; right; right; left; eexists; reflexivity.
              ** destruct (good2_f3111 (ih s2 hs2) (proj1 hS) hF2 hN1) as [-> [hG2' hSf]].
                 split_and; try (intros [[? ?] | ?]; dlia); try dlia.
                 --- intro; exact hG2'.
                 --- intro; exact (hSf hS).
           ++ assert (hq4 : dlt1 / 3 - 1 = S (S (S (S (dlt1 / 3 - 5))))) by dlia.
              rewrite hq4 in hF2. cbn [ones app] in hF2.
              assert (hGZ : GoodZero111Head (ones (dlt1 / 3 - 5) ++ R1)).
              { destruct (dlt1 / 3 - 5) as [| k] eqn:hq.
                - cbn [ones app].
                  destruct (dec_head_0s R1) as [[W hW] | hno].
                  + right; exact (f_pos_0s (ih s1 hs1) h1 hN1Y ltac:(dlia) hW).
                  + left; exact hno.
                - left; intros ? hEq; discriminate hEq. }
              destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [hG2' hSf]].
              split_and; try (intros [[? ?] | ?]; dlia); try dlia.
              ** intro; exact hG2'.
              ** intro; exact (hSf hGZ).
Qed.

Lemma bigF_3_7_goodF2U {m s : nat} (ih : InvLt m) (hs : s < m)
    {X R0 : list Seg} (h : BigF s ((3, false) :: X) 7 R0) (hN : NoNonlast0F X) :
  GoodF2U R0.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [? [h0 _]]] |
    [[? [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 5) by lia; subst dlt3.
    right; right; right.
    exact (head0s111_to_head0s11 (f3_5_0111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1))).
  - assert (dlt3 = 4) by lia; subst dlt3.
    destruct (f_4_head (ih s2 ltac:(lia)) hF2 (noNonlast0F_bumpR (noNonlast0F_bumpR hN1)))
      as [-> | [[W ->] | [W ->]]].
    + left; exists ([] : list Seg); reflexivity.
    + right; left; exists W; reflexivity.
    + right; right; left; exists W; reflexivity.
  - contradiction (proj2 (f3_ne24 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
Qed.

Lemma bigF_1_9_goodF2U {m s : nat} (ih : InvLt m) (hs : s < m)
    {Y R0 : list Seg} (h : BigF s ((1, false) :: Y) 9 R0) (hN : NoNonlast0F Y) :
  GoodF2U R0.
Proof.
  destruct (bigF_1_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  destruct hcases as [[? [h0 _]] |
    [[? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 7) by lia; subst dlt3.
    exact (bigF_3_7_goodF2U (s := s2) ih ltac:(lia) hF2 (noNonlast0F_ones_append _ hN1)).
  - destruct (f_258 (ih s1 ltac:(lia)) h1 hN (or_introl eq_refl)) as [U ->].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 ltac:(lia)) hF2 hNU) as [[h4 _] | [[h10 _] | h13]]; lia.
  - assert (dlt3 = 6) by lia; subst dlt3.
    right; right; right.
    exact (f3_36 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1) (or_intror eq_refl)).
Qed.

Lemma step_f111 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  (dlt = 0 /\ Zero111 R_fin /\ (GoodZero111Head Y -> TightZero111 R_fin)) \/
  (dlt mod 3 = 0 /\ 9 <= dlt /\ Good2 R_fin /\
    (dlt = 9 -> GoodF2U Y -> Strong2 R_fin) /\ (dlt = 12 -> Strong2 R_fin)).
Proof.
  destruct (bigF_1_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (nnf_1F (nnf_1F hN)) as hN11.
  pose proof (bigF_nnf h1 hN11) as hN1.
  pose proof (f11 (ih s1 hs1) h1 hN) as hf11.
  destruct hcases as [[hrem0 [-> ->]] |
    [[hrem1 [hge4 [s2 [hs2 [dlt3 [-> hF2]]]]]] |
    [[-> _] |
     [hrem2 _]]]].
  - destruct (Nat.eq_dec dlt1 0) as [-> | h0ne].
    + left; split; [reflexivity |]; cbn [Nat.div ones app].
      inverts h1 as h0f hrem0f h02; try lia.
      * match type of h0f with
        | BigF ?s0 _ ?dlt0 ?R0 =>
          pose proof (f1 (ih s0 ltac:(lia)) h0f hN) as hf1;
          pose proof (proj1 hf1) as hne3_0;
          destruct (Nat.eq_dec dlt0 0) as [-> | h0zne];
          [ cbn [Nat.div ones app];
            inverts h0f as hy hremy hy2; try lia;
            [ match type of hy with
              | BigF ?sy _ ?dlty ?Ry =>
                destruct (Nat.eq_dec dlty 0) as [-> | hyzne];
                [ destruct (bigF_zero_head_3 hy hN) as [-> | [[Z ->] | [Z ->]]];
                  cbn [Nat.div ones app];
                  [ split; [left; reflexivity |
                      intro; split; [left; reflexivity | intros ? hEq; discriminate hEq]]
                  | split; [right; left; exists Z; reflexivity |
                      intro; split; [right; left; exists Z; reflexivity | intros ? hEq; discriminate hEq]]
                  | split; [right; right; left; exists Z; reflexivity |
                      intro hGZ; split; [right; right; left; exists Z; reflexivity |]];
                    intros Z' hEq; inversion hEq; subst Z'; clear hEq;
                    destruct (bigF_zero_oneF_head hy hN) as [[? ->] | ->];
                    [ left; reflexivity
                    | destruct hGZ as [hne0 | [W hW]];
                      [ contradiction (hne0 Z eq_refl)
                      | inversion hW; subst Z; right; right; exists W; reflexivity ] ] ]
                | assert (hqy : 1 <= (1 + dlty) / 3) by dlia;
                  destruct (ones_pos_cons hqy Ry) as [Z hZ];
                  rewrite hZ;
                  split; [right; right; left; exists Z; reflexivity |];
                  intro; split; [right; right; left; exists Z; reflexivity |];
                  intros Z' hEq; inversion hEq; subst Z'; clear hEq;
                  destruct (Nat.eq_dec dlty 3) as [-> | h3yne];
                  [ cbn [Nat.div ones app] in hZ; inversion hZ; subst Z; clear hZ;
                    destruct (bigF_three_head hy) as [W ->];
                    right; left; exists ((1, false) :: W); reflexivity
                  | assert (hq2 : (1 + dlty) / 3 = S (S ((1 + dlty) / 3 - 2))) by dlia;
                    rewrite hq2 in hZ; cbn [ones app] in hZ; inversion hZ; subst Z; clear hZ;
                    right; right; eexists; reflexivity ] ]
              end
            | pose proof (bigD1_ge2_of_ne_nil hy2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hy))); lia ]
          | destruct (Nat.eq_dec dlt0 6) as [-> | h6ne];
            [ destruct (proj1 (proj2 (proj2 (proj2 hf1))) eq_refl) as [U ->];
              cbn [Nat.div ones app];
              split; [right; right; right; left; exists U; reflexivity |
                intro; split; [right; right; right; left; exists U; reflexivity | intros ? hEq; discriminate hEq]]
            | assert (hq3 : (1 + dlt0) / 3 = S (S (S ((1 + dlt0) / 3 - 3)))) by dlia;
              rewrite hq3; cbn [ones app];
              assert (hGF0 : GoodF2U (ones ((1 + dlt0) / 3 - 3) ++ R0)) by
                (destruct (Nat.eq_dec dlt0 9) as [-> | h9ne];
                 [ cbn [Nat.div Nat.sub ones app]; exact (bigF_1_9_goodF2U (s := s0) ih ltac:(lia) h0f hN)
                 | assert (hq1 : 1 <= (1 + dlt0) / 3 - 3) by dlia;
                   destruct (ones_pos_cons hq1 R0) as [W hW]; left; exists W; exact hW ]);
              split; [right; right; right; right; left; eexists; exact (conj eq_refl hGF0) |
                intro; split; [right; right; right; right; left; eexists; exact (conj eq_refl hGF0) |
                  intros ? hEq; discriminate hEq]] ] ]
        end.
      * pose proof (bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))); lia.
    + pose proof (proj1 (proj2 hf11)) as hne3.
      pose proof (proj1 (proj2 (proj2 hf11))) as hne6.
      assert (hge9 : 9 <= dlt1) by dlia.
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hf11)))) (or_introl (conj hrem0 hge9))) as hG2.
      assert (hq3 : dlt1 / 3 = S (S (S (dlt1 / 3 - 3)))) by dlia.
      rewrite hq3; cbn [ones app].
      pose proof (goodTail_ones_append (dlt1 / 3 - 3) (or_introl hG2)) as hT.
      left; split; [reflexivity |].
      split; [right; right; right; right; right; eexists; exact (conj eq_refl hT) |].
      intro; split; [right; right; right; right; right; eexists; exact (conj eq_refl hT) | intros ? hEq; discriminate hEq].
  - destruct (Nat.eq_dec dlt1 7) as [-> | h7ne].
    + pose proof (proj1 (proj2 (proj2 (proj2 hf11))) eq_refl) as hG1.
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (good2_f31 (ih s2 hs2) (good1Safe_to_good2 hG1) hF2 hN1) as [h710 hSf].
      pose proof (hSf (good1Safe_to_strong2 hG1)) as hS.
      destruct h710 as [-> | [-> _]].
      * right; split; [reflexivity | split; [lia | split; [exact (proj1 hS) | split; [intros ? ?; exact hS | intro; lia]]]].
      * right; split; [reflexivity | split; [lia | split; [exact (proj1 hS) | split; [intro; lia | intro; exact hS]]]].
    + destruct (Nat.eq_dec dlt1 10) as [-> | h10ne].
      * pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hf11)))) (or_intror eq_refl)) as hG2.
        cbn [Nat.div Nat.sub ones app] in hF2.
        destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS'].
        right; split; [reflexivity | split; [lia | split; [exact (proj1 hS') | split; [intros ? ?; exact hS' | intro; lia]]]].
      * destruct (Nat.eq_dec dlt1 13) as [-> | h13ne].
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (f3_111 (ih s2 hs2) hF2 hN1) as [[-> | ->] [hG2' hS10]].
           ++ right; split; [reflexivity | split; [lia | split; [exact hG2' | split; [| intro; lia]]]].
              intros ? hGF.
              pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 hf11))))) eq_refl hGF) as hS1.
              exact (proj2 (proj2 (good2_f3111 (ih s2 hs2) (proj1 hS1) hF2 hN1)) hS1).
           ++ right; split; [reflexivity | split; [lia | split; [exact hG2' | split; [intro; lia | intro; exact (hS10 eq_refl)]]]].
        -- pose proof (proj1 (proj2 (f1 (ih s1 hs1) h1 (nnf_1F hN)))) as hne4.
           assert (hq4 : dlt1 / 3 - 1 = S (S (S (S (dlt1 / 3 - 5))))) by dlia.
           rewrite hq4 in hF2. cbn [ones app] in hF2.
           assert (hGZ : GoodZero111Head (ones (dlt1 / 3 - 5) ++ R1)).
           { destruct (dlt1 / 3 - 5) as [| k] eqn:hq.
             - cbn [ones app].
               destruct (dec_head_0s R1) as [[W hW] | hno].
               + right; exact (f_pos_0s (ih s1 hs1) h1 hN11 ltac:(dlia) hW).
               + left; exact hno.
             - left; intros ? hEq; discriminate hEq. }
           destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [hG2' hSf]].
           right; split; [reflexivity | split; [lia | split; [exact hG2' | split; [intros ? ?; exact (hSf hGZ) | intro; lia]]]].
  - contradiction (proj1 hf11 eq_refl).
  - contradiction (proj1 hf11 hrem2).
Qed.

(* ========================================================================== *)
(* Group 4 Step Lemmas                                                        *)
(* ========================================================================== *)

Lemma bigD1_of_tightZero111 {s dlt2 : nat} {R1 R_fin : list Seg}
    (hTZ : TightZero111 R1) (hD : BigD1 s R1 dlt2 R_fin) :
  dlt2 = 3 /\ Good1Safe R_fin.
Proof.
  destruct (proj1 hTZ) as [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> hGF]] | [Z [-> hT]]]]]]];
    destruct (bigD1_zeroT_inv hD) as [-> ->]; cbn [bumpR].
  - exact (conj eq_refl good1Safe_of_1s_0s_0).
  - exact (conj eq_refl (good1Safe_of_1s_0s_0s Z)).
  - destruct (proj2 hTZ Z eq_refl) as [-> | [[W ->] | [W ->]]].
    + exact (conj eq_refl good1Safe_of_1s_0s_1_nil).
    + exact (conj eq_refl (good1Safe_of_1s_0s_1_0s W)).
    + exact (conj eq_refl (good1Safe_of_1s_0s_1_1 W)).
  - exact (conj eq_refl (good1Safe_of_1s_1_1_0s_1_1 Z)).
  - exact (conj eq_refl (good1Safe_of_1s_1_1_1 hGF)).
  - exact (conj eq_refl (good1Safe_of_2_1_1 hT)).
Qed.

Lemma step_f2s {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((2, true) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  dlt <> 2 /\ dlt <> 5 /\
  (dlt = 0 -> Safe0s R_fin) /\
  (dlt = 3 -> Head0s11 R_fin) /\
  (dlt = 6 -> Head0s11 R_fin \/ Good1Safe R_fin) /\
  (dlt = 9 -> Head0s11 R_fin \/ Strong2 R_fin) /\
  (dlt = 12 -> Head0s11 R_fin \/ Good2 R_fin).
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (nnf_1F hN) as hN1Y.
  pose proof (bigF_nnf h1 hN1Y) as hN1.
  pose proof (f1 (ih s1 hs1) h1 hN) as hf1.
  destruct hcases as [[hrem1 [hge4 [-> ->]]] |
    [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] |
    [[hrem2 [hge5 [s2 [hs2 [dlt3 [-> hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [-> hD2]]]]] |
    [[-> _] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]]]].
  - pose proof (proj1 (proj2 hf1)) as hne4.
    split_and; try lia.
    intro.
    destruct (Nat.eq_dec dlt1 7) as [-> | h7ne].
    + cbn [Nat.div ones app].
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 hf1)))) eq_refl) as [hH | hG1].
      * exists R1; split; [reflexivity | right; right; right; left; exact hH].
      * exists R1; split; [reflexivity | right; right; right; right; exact hG1].
    + destruct (Nat.eq_dec dlt1 10) as [-> | h10ne].
      * cbn [Nat.div ones app].
        assert (hGH : Good2 R1 \/ Head0s11 R1) by
          (destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 hf1))))) eq_refl) as [hH | hG2]; auto).
        exists ((1, false) :: R1); split; [reflexivity | right; right; left; exists R1; exact (conj eq_refl hGH)].
      * destruct (Nat.eq_dec dlt1 13) as [-> | h13ne].
        -- cbn [Nat.div ones app].
           assert (hGH : Good2 R1 \/ Head0s11 R1) by
             (destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hf1)))))) eq_refl) as [hH | hG2]; auto).
           exists ((1, false) :: (1, false) :: R1);
             split; [reflexivity | right; left; exists R1; exact (conj eq_refl hGH)].
        -- assert (hq5 : dlt1 / 3 = S (S (S (S (S (dlt1 / 3 - 5)))))) by dlia.
           rewrite hq5; cbn [ones app].
           eexists; split; [reflexivity | left; eexists; reflexivity].
  - destruct (f_25_goodF2U (ih s1 hs1) h1 hN1Y (or_introl eq_refl)) as [U [-> hGFU]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 hs2) hF2 hNU) as [[-> hG1] | [[-> hS] | ->]].
    + split_and; try lia. intro; right; exact (hG1 (goodF2U_to_goodZero111Head hGFU)).
    + split_and; try lia. intro; right; exact (proj1 (hS hGFU)).
    + split_and; try lia.
  - destruct (Nat.eq_dec dlt1 5) as [-> | h5ne].
    + destruct (proj1 (proj2 (proj2 hf1)) eq_refl) as [U [-> hSU]].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
      destruct hSU as [[Z ->] | [[Z [-> _]] | [[Z [-> _]] | [[Z ->] | [hG1 _]]]]].
      * destruct (f3_1111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail hNU))) as [-> [hG2' _]].
        split_and; try lia. intro; right; exact hG2'.
      * destruct (f3_1111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail hNU))) as [-> [hG2' _]].
        split_and; try lia. intro; right; exact hG2'.
      * destruct (f3_111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail hNU)) as [[-> | ->] [hG2' _]].
        -- split_and; try lia. intro; right; exact hG2'.
        -- split_and; try lia.
      * destruct (bigF_det hF4 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: (1, false) :: Z))) as [-> ->].
        split_and; try lia. intro; right; exact (good2_of_2_1_1 ((1, false) :: (1, false) :: Z)).
      * destruct (good2_f311 (ih s4 ltac:(lia)) (good1_to_good2 hG1) hF4 hNU) as [-> hS'].
        split_and; try lia. intro; right; exact (proj1 hS').
    + destruct (Nat.eq_dec dlt1 8) as [-> | h8ne].
      * destruct (f_258 (ih s1 hs1) h1 hN1Y (or_intror (or_intror eq_refl))) as [U ->].
        pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
        cbn [Nat.div Nat.sub ones app] in hF2.
        destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
        destruct (f2s_111 (ih s4 ltac:(lia)) hF4 hNU) as [-> hG1'].
        split_and; try lia. intro; right; exact (good1Safe_to_strong2 hG1').
      * destruct (Nat.eq_dec dlt1 11) as [-> | h11ne].
        -- destruct (f_11 (ih s1 hs1) h1 hN1Y) as [[U ->] | hS]; cbn [Nat.div Nat.sub ones app] in hF2.
           ++ destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->].
              split_and; try lia. intro; right; exact (strong2_of_2_1_1 ((1, false) :: U)).
           ++ destruct (good2_f311 (ih s2 hs2) (proj1 hS) hF2 hN1) as [-> hS'].
              split_and; try lia. intro; right; exact hS'.
        -- destruct (Nat.eq_dec dlt1 14) as [-> | h14ne].
           ++ destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hf1)))))) eq_refl) as [[U ->] | hS];
                cbn [Nat.div Nat.sub ones app] in hF2.
              ** destruct (bigF_det hF2 (bigF_3_1_1_1_0s_1_1_exists U)) as [-> ->].
                 split_and; try lia.
                 intro; right; apply strong2_of_2_0s; right; right; right; left; eexists; reflexivity.
              ** destruct (good2_f3111 (ih s2 hs2) (proj1 hS) hF2 hN1) as [-> [? hSf]].
                 split_and; try lia. intro; right; exact (hSf hS).
           ++ assert (hq4 : dlt1 / 3 - 1 = S (S (S (S (dlt1 / 3 - 5))))) by dlia.
              rewrite hq4 in hF2. cbn [ones app] in hF2.
              assert (hGZ : GoodZero111Head (ones (dlt1 / 3 - 5) ++ R1)).
              { destruct (dlt1 / 3 - 5) as [| k] eqn:hq.
                - cbn [ones app].
                  destruct (dec_head_0s R1) as [[W hW] | hno].
                  + right; exact (f_pos_0s (ih s1 hs1) h1 hN1Y ltac:(dlia) hW).
                  + left; exact hno.
                - left; intros ? hEq; discriminate hEq. }
              destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [? hSf]].
              split_and; try lia. intro; right; exact (hSf hGZ).
  - destruct (bigF_oneF_zero_head h1) as [W ->].
    destruct (bigD1_zeroT_inv hD2) as [-> _].
    split_and; try lia.
  - contradiction (proj1 hf1 eq_refl).
  - destruct (Nat.eq_dec dlt1 6) as [-> | h6ne].
    + destruct (proj1 (proj2 (proj2 (proj2 hf1))) eq_refl) as [U ->].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
      destruct (f3_11 (ih s4 ltac:(lia)) hF4 hNU) as [-> | [-> | [-> _]]].
      * split_and; try lia. intro; left; exact (bigF_3_zero_prefix hF4).
      * split_and; try lia.
      * split_and; try lia.
    + destruct (Nat.eq_dec dlt1 9) as [-> | h9ne].
      * cbn [Nat.div Nat.sub ones app] in hF2.
        pose proof (nnf_1F hN1) as hN_1R1.
        split; [lia |].
        split; [intro; exact (proj1 (f3_ne24 (ih s2 hs2) hF2 hN_1R1) ltac:(lia)) |].
        split; [lia |].
        split; [intro; assert (dlt3 = 0) by lia; subst dlt3; exact (bigF_3_zero_prefix hF2) |].
        split; [intro; assert (dlt3 = 3) by lia; subst dlt3; left; exact (f3_36 (ih s2 hs2) hF2 hN_1R1 (or_introl eq_refl)) |].
        split; [intro; assert (dlt3 = 6) by lia; subst dlt3; contradiction (f3_1_ne6 (ih s2 hs2) hF2 hN1) |].
        intro; assert (dlt3 = 9) by lia; subst dlt3.
        destruct (f3_9 (ih s2 hs2) hF2 hN_1R1) as [hH | hS]; [left; exact hH | right; exact (proj1 hS)].
      * destruct (Nat.eq_dec dlt1 12) as [-> | h12ne].
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (f3_11 (ih s2 hs2) hF2 hN1) as [-> | [-> | [-> _]]].
           ++ split_and; try lia. intro; exact (bigF_3_zero_prefix hF2).
           ++ split_and; try lia.
           ++ split_and; try lia.
        -- assert (hq3 : dlt1 / 3 - 2 = S (S (S (dlt1 / 3 - 5)))) by dlia.
           rewrite hq3 in hF2. cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] _];
             (split_and; try lia).
Qed.

Lemma step_f2s_1 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((2, true) :: (1, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  dlt = 0 \/ dlt = 4 \/ dlt = 10 \/ dlt = 13.
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F (nnf_1F hN))) as hN1.
  pose proof (f11 (ih s1 hs1) h1 hN) as hf11.
  destruct hcases as [[? [? [-> _]]] |
    [[-> _] |
    [[hrem2 _] |
    [[-> [s2 [hs2 [dlt2 [-> hD2]]]]] |
    [[-> _] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]]]].
  - left; reflexivity.
  - contradiction (proj1 hf11 eq_refl).
  - contradiction (proj1 hf11 hrem2).
  - destruct (bigF_oneF_zero_head h1) as [W ->].
    destruct (bigD1_zeroT_inv hD2) as [-> _].
    right; left; reflexivity.
  - contradiction (proj1 (proj2 hf11) eq_refl).
  - destruct (Nat.eq_dec dlt1 6) as [h6 | h6ne]; [contradiction (proj1 (proj2 (proj2 hf11)) h6) |].
    destruct (Nat.eq_dec dlt1 9) as [-> | h9ne].
    + assert (hG2 : Good2 R1) by (apply (proj1 (proj2 (proj2 (proj2 (proj2 hf11))))); left; split; [reflexivity | lia]).
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (proj1 (good2_f31 (ih s2 hs2) hG2 hF2 hN1)) as [-> | [-> _]]; auto.
    + destruct (Nat.eq_dec dlt1 12) as [-> | h12ne].
      * assert (hG2 : Good2 R1) by (apply (proj1 (proj2 (proj2 (proj2 (proj2 hf11))))); left; split; [reflexivity | lia]).
        cbn [Nat.div Nat.sub ones app] in hF2.
        destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> _]; auto.
      * assert (hq3 : dlt1 / 3 - 2 = S (S (S (dlt1 / 3 - 5)))) by dlia.
        rewrite hq3 in hF2. cbn [ones app] in hF2.
        destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] _]; auto.
Qed.

Lemma step_f2s_11 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((2, true) :: (1, false) :: (1, false) :: Y) dlt R_fin) (hN : NoNonlast0F Y) :
  (dlt = 4 /\ (GoodZero111Head Y -> Good1Safe R_fin)) \/
  (dlt = 10 /\ (GoodF2U Y -> Strong2 R_fin)) \/
  dlt = 13.
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F (nnf_1F (nnf_1F hN)))) as hN1.
  pose proof (f111 (ih s1 hs1) h1 hN) as hf111.
  destruct hcases as [[hrem1 _] |
    [[-> _] |
    [[hrem2 _] |
    [[-> [s2 [hs2 [dlt2 [-> hD2]]]]] |
    [[-> _] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]]]].
  - destruct hf111 as [[h0 _] | [hm _]]; dlia.
  - destruct hf111 as [[h0 _] | [hm _]]; dlia.
  - destruct hf111 as [[h0 _] | [hm _]]; dlia.
  - destruct hf111 as [[? [hZ hTZ]] | [? [hge _]]]; [| lia].
    assert (h0s : exists W, R1 = (0, true) :: W).
    { destruct hZ as [-> | [[? ->] | [[? ->] | [[? ->] | [[? [-> _]] | [? [-> _]]]]]]];
        eexists; reflexivity. }
    destruct h0s as [W ->].
    destruct (bigD1_zeroT_inv hD2) as [-> ->].
    left; split; [reflexivity |].
    intro hGZ. exact (proj2 (bigD1_of_tightZero111 (hTZ hGZ) (BD_zeroT W))).
  - destruct hf111 as [[h0 _] | [? [hge _]]]; lia.
  - destruct hf111 as [[h0 _] | [? [hge9 [hG2 [hS9 hS12]]]]]; [lia |].
    destruct (Nat.eq_dec dlt1 9) as [-> | h9ne].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (good2_f31 (ih s2 hs2) hG2 hF2 hN1) as [[-> | [-> _]] hSf].
      * right; left; split; [reflexivity | intro hGF; exact (hSf (hS9 eq_refl hGF))].
      * right; right; reflexivity.
    + destruct (Nat.eq_dec dlt1 12) as [-> | h12ne].
      * cbn [Nat.div Nat.sub ones app] in hF2.
        destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS'].
        right; left; split; [reflexivity | intro; exact hS'].
      * destruct (Nat.eq_dec dlt1 15) as [-> | h15ne].
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (good2_f3111 (ih s2 hs2) hG2 hF2 hN1) as [-> [? hSf]].
           right; left; split; [reflexivity | intro].
           assert (hS15 : Strong2 R1).
           { destruct (bigF_1_inv h1) as [sa [hsa [dlta [Ra [ha hca]]]]].
             destruct hca as [[? [h0 _]] | [[? [? [sb [hsb [dltb [haddb hFb]]]]]] | [[-> _] | [hrem2 _]]]]; try lia.
             - assert (dltb = 13) by lia; subst dltb.
               pose proof (bigF_nnf ha (nnf_1F (nnf_1F hN))) as hNa.
               pose proof (f11 (ih sa ltac:(lia)) ha hN) as hf11a.
               destruct (Nat.eq_dec dlta 7) as [-> | h7ne].
               + pose proof (proj1 (proj2 (proj2 (proj2 hf11a))) eq_refl) as hG1a.
                 cbn [Nat.div Nat.sub ones app] in hFb.
                 destruct (proj1 (good2_f31 (ih sb ltac:(lia)) (good1Safe_to_good2 hG1a) hFb hNa)) as [h7 | [h10 _]]; lia.
               + destruct (Nat.eq_dec dlta 10) as [-> | h10ne].
                 * pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hf11a)))) (or_intror eq_refl)) as hG2a.
                   cbn [Nat.div Nat.sub ones app] in hFb.
                   pose proof (proj1 (good2_f311 (ih sb ltac:(lia)) hG2a hFb hNa)); lia.
                 * pose proof (proj1 (proj2 (f1 (ih sa ltac:(lia)) ha (nnf_1F hN)))) as hne4.
                   assert (hq3 : dlta / 3 - 1 = S (S (S (dlta / 3 - 4)))) by dlia.
                   rewrite hq3 in hFb. cbn [ones app] in hFb.
                   destruct (f3_111 (ih sb ltac:(lia)) hFb (noNonlast0F_ones_append _ hNa)) as [h710 _]; lia.
             - contradiction (proj1 (f11 (ih sa ltac:(lia)) ha hN) eq_refl).
             - contradiction (proj1 (f11 (ih sa ltac:(lia)) ha hN) hrem2). }
           exact (hSf hS15).
        -- assert (hq4 : dlt1 / 3 - 2 = S (S (S (S (dlt1 / 3 - 6))))) by dlia.
           rewrite hq4 in hF2. cbn [ones app] in hF2.
           assert (hGZ : GoodZero111Head (ones (dlt1 / 3 - 6) ++ R1)).
           { destruct (dlt1 / 3 - 6) as [| k].
             - cbn [ones app]. left; exact (good2_ne_zeroT hG2).
             - left; intros ? hEq; discriminate hEq. }
           destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [? hSf]].
           right; left; split; [reflexivity | intro; exact (hSf hGZ)].
Qed.

Lemma step_f2s_111 {m : nat} (ih : InvLt m)
    {Y : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((2, true) :: (1, false) :: (1, false) :: (1, false) :: Y) dlt R_fin)
    (hN : NoNonlast0F Y) :
  dlt = 4 /\ Good1Safe R_fin.
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  assert (h1_zero : dlt1 = 0 /\ TightZero111 R1).
  { inverts h1 as h0 hrem0 h02; try lia.
    - match type of h0 with
      | BigF ?s0 _ ?dlt0 ?R0 =>
        destruct (f111 (ih s0 ltac:(lia)) h0 hN) as [[-> [hZ _]] | [hm [hge9 [hG2 _]]]];
        [ split; [reflexivity |];
          destruct hZ as [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z [-> hT]]]]]]];
          cbn [Nat.div ones app];
          [ split; [right; left; exists [(0, false)]; reflexivity | intros ? hEq; discriminate hEq]
          | split; [right; left; exists ((0, true) :: Z); reflexivity | intros ? hEq; discriminate hEq]
          | split; [right; left; exists ((1, false) :: Z); reflexivity | intros ? hEq; discriminate hEq]
          | split; [right; right; left; eexists; reflexivity |
              intros Z' hEq; inversion hEq; subst Z'; right; right; eexists; reflexivity]
          | split; [right; right; left; eexists; reflexivity |
              intros Z' hEq; inversion hEq; subst Z'; right; right; eexists; reflexivity]
          | split; [right; right; right; right; left; exists Z; exact (conj eq_refl (goodTail_to_goodF2U hT)) |
              intros ? hEq; discriminate hEq] ]
        | split; [reflexivity |];
          assert (hq3 : (1 + dlt0) / 3 = S (S (S ((1 + dlt0) / 3 - 3)))) by dlia;
          rewrite hq3; cbn [ones app];
          pose proof (goodTail_ones_append ((1 + dlt0) / 3 - 3) (or_introl hG2)) as hT;
          split; [right; right; right; right; right; eexists; exact (conj eq_refl hT) |
            intros ? hEq; discriminate hEq] ]
      end.
    - match type of h0 with
      | BigF ?s0 _ _ _ =>
        destruct (f111 (ih s0 ltac:(lia)) h0 hN) as [[h0e _] | [hm _]]; dlia
      end.
    - match type of h0 with
      | BigF ?s0 _ _ _ =>
        destruct (f111 (ih s0 ltac:(lia)) h0 hN) as [[h0e _] | [hm _]]; dlia
      end. }
  destruct h1_zero as [-> hTZ].
  destruct hcases as [[hrem _] | [[h2 _] | [[hrem _] | [[? [s2 [hs2 [dlt2 [-> hD2]]]]] | [[h3 _] | [? [hge _]]]]]]]; try dlia.
  destruct (bigD1_of_tightZero111 hTZ hD2) as [-> hG1].
  exact (conj eq_refl hG1).
Qed.

(* ========================================================================== *)
(* Group 5 Helpers and Concrete Boundary Witnesses                            *)
(* ========================================================================== *)

Lemma good2_head_cases {G : list Seg} (hG : Good2 G) :
  (exists Y, G = (1, true) :: Y) \/ (exists Y, G = (2, false) :: Y).
Proof.
  destruct hG as [? h1g | | | | ? | | ? | | | ? | ? | ? | ? | ? | ? | ? | ? ? | ? ?];
    try (right; eexists; reflexivity).
  destruct h1g as [-> | [[? ->] | [-> | [-> | [[? ->] | [[? ->] | [[? ->] | [[? [-> _]] | [? ->]]]]]]]]];
    try (left; eexists; reflexivity).
  right; eexists; reflexivity.
Qed.

Lemma good2_good1_or_ge2 {G : list Seg} (hG : Good2 G) :
  Good1 G \/ (exists Y, G = (2, false) :: Y).
Proof.
  destruct hG as [? h1g | | | | ? | | ? | | | ? | ? | ? | ? | ? | ? | ? | ? ? | ? ?];
    try (right; eexists; reflexivity).
  left; exact h1g.
Qed.

Lemma bigF_2_3_goodF2U {m s : nat} (ih : InvLt m)
    {Y R_fin : list Seg} (h : BigF s ((2, false) :: Y) 3 R_fin)
    (hs : s < m) (hN : NoNonlast0F Y) :
  exists U, R_fin = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U.
Proof.
  destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR hN)) as hN_b2.
  pose proof (bigF_nnf h1 hN_b2) as hN1.
  destruct hcases as [[? [? [h0 _]]] |
    [[-> [? [? [dlt3 [hadd hF2]]]]] |
    [[? [? [? [? [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [hadd hD2]]]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]]]; try lia.
  - assert (dlt3 = 1) by lia; subst dlt3. contradiction (bigF_ne_one hF2).
  - assert (dlt3 = 1) by lia; subst dlt3. contradiction (bigF_ne_one hF2).
  - assert (dlt2 = 2) by lia; subst dlt2.
    destruct Y as [| [dx bx] xs].
    + destruct bigF_2_nil_exists as [? hEx].
      destruct (bigF_det h hEx) as [h4 _]; lia.
    + destruct (bigF_ge2_zero_head h1) as [Z ->].
      inverts hD2; lia.
  - assert (dlt3 = 0) by lia; subst dlt3.
    destruct (bigF_three_head h1) as [Z ->].
    cbn [bumpR] in hF2.
    destruct (proj1 (proj2 (proj2 (f2s (ih s2 ltac:(lia)) hF2 (noNonlast0F_tail hN1)))) eq_refl) as [U [-> hSU]].
    exists U. exact (conj eq_refl (safeU_to_goodF2U hSU)).
  - assert (dlt3 = 0) by lia; subst dlt3.
    exact (bigF_3_zero_goodF2U (s := s2) ih ltac:(lia) hF2 (noNonlast0F_ones_append _ hN1)).
Qed.

Lemma bigF_2_3_head0s11 {m s : nat} (ih : InvLt m)
    {Y R_fin : list Seg} (h : BigF s ((2, false) :: Y) 3 R_fin)
    (hs : s < m) (hN : NoNonlast0F Y) :
  Head0s11 R_fin.
Proof.
  destruct (bigF_2_3_goodF2U ih h hs hN) as [U [-> _]].
  exists U; reflexivity.
Qed.

Lemma bigF_2s_3_goodF2U {m s : nat} (ih : InvLt m)
    {Z R1 : list Seg} (h : BigF s ((2, true) :: Z) 3 R1)
    (hs : s < m) (hN : NoNonlast0F Z) :
  exists U, R1 = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U.
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [Ra [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F hN)) as hN1.
  pose proof (f1 (ih s1 ltac:(lia)) h1 hN) as hf1.
  destruct hcases as [[? [? [h0 _]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [hadd hD2]]]]] |
    [[h3 _] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]]]; try lia.
  - assert (dlt3 = 1) by lia; subst dlt3. contradiction (bigF_ne_one hF2).
  - assert (dlt3 = 1) by lia; subst dlt3. contradiction (bigF_ne_one hF2).
  - destruct (bigF_oneF_zero_head h1) as [W ->].
    inverts hD2; lia.
  - assert (dlt3 = 0) by lia; subst dlt3.
    exact (bigF_3_zero_goodF2U (s := s2) ih ltac:(lia) hF2 (noNonlast0F_ones_append _ hN1)).
Qed.

Lemma bigF_3_1_1_7_good2_of_gz {m s : nat} (ih : InvLt m)
    {X R_fin : list Seg} (hGZ : GoodZero111Head X)
    (h : BigF s ((3, false) :: (1, false) :: (1, false) :: X) 7 R_fin)
    (hs : s < m) (hN : NoNonlast0F X) :
  Good2 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (nnf_1F (nnf_1F hN)) as hN11.
  pose proof (bigF_nnf h1 hN11) as hN1.
  pose proof (f11 (ih s1 ltac:(lia)) h1 hN) as hf11.
  destruct hcases as [[? [? [h0 _]]] |
    [[hrem2 _] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
     [hrem0 [hge3 [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]; try lia.
  - assert (dlt3 = 4) by lia; subst dlt3.
    inverts h1 as h0f hrem0f h02; try lia.
    + match type of h0f with
      | BigF ?s0 _ ?dlt0' ?R0 =>
        pose proof (bigF_nnf h0f (nnf_1F hN)) as hN0;
        destruct (Nat.eq_dec dlt0' 0) as [-> | h0z];
        [ cbn [Nat.div ones app] in hF2;
          inverts h0f as hx hremx hx2; try lia;
          [ match type of hx with
            | BigF ?sx _ ?dltx ?Rx =>
              destruct (Nat.eq_dec dltx 0) as [-> | hxz];
              [ destruct (bigF_zero_head_3 hx hN) as [-> | [[Z ->] | [Z ->]]];
                [ cbn [Nat.div ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists [(0, false)])) as [? ->];
                  exact G2_c_2_0
                | cbn [Nat.div ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: Z))) as [? ->];
                  exact (good2_of_2_0s Z)
                | cbn [Nat.div ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((1, false) :: Z))) as [? ->];
                  destruct (bigF_zero_oneF_head hx hN) as [[? ->] | ->];
                  [ exact G2_c_2_1
                  | destruct hGZ as [hne0 | [W hW]];
                    [ contradiction (hne0 Z eq_refl)
                    | inversion hW; subst; exact (good2_of_2_1_1 W) ] ] ]
              | destruct (Nat.eq_dec dltx 3) as [-> | h3x];
                [ destruct (bigF_three_head hx) as [W ->];
                  cbn [Nat.div ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((1, false) :: (0, true) :: (1, false) :: W))) as [? ->];
                  exact (good2_of_2_1_0s ((1, false) :: W))
                | assert (hq2 : (1 + dltx) / 3 = S (S ((1 + dltx) / 3 - 2))) by dlia;
                  rewrite hq2 in hF2; cbn [ones app bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists
                    ((1, false) :: (1, false) :: ones ((1 + dltx) / 3 - 2) ++ Rx))) as [? ->];
                  exact (good2_of_2_1_1 (ones ((1 + dltx) / 3 - 2) ++ Rx)) ] ]
            end
          | pose proof (bigD1_ge2_of_ne_nil hx2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hx))); lia ]
        | pose proof (proj1 (f1 (ih s0 ltac:(lia)) h0f hN)) as hne3;
          destruct (Nat.eq_dec dlt0' 6) as [-> | h6];
          [ destruct (proj1 (proj2 (proj2 (proj2 (f1 (ih s0 ltac:(lia)) h0f hN)))) eq_refl) as [U ->];
            cbn [Nat.div ones app bumpR] in hF2;
            destruct (bigF_det hF2 (bigF_2s_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [? ->];
            exact (good1Safe_to_good2 (good1Safe_of_1s_0s_1_1 ((1, false) :: U)))
          | assert (hq3 : (1 + dlt0') / 3 = S (S (S ((1 + dlt0') / 3 - 3)))) by dlia;
            rewrite hq3 in hF2; cbn [ones app bumpR] in hF2;
            exact (good1Safe_to_good2 (proj2 (f2s_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN0)))) ] ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil h02 (append_nonempty_of_right _ _ (bigF_out_ne_nil h0f))); lia.
  - assert (dlt3 = 4) by lia; subst dlt3.
    pose proof (proj1 (proj2 hf11)) as hne3.
    pose proof (proj1 (proj2 (proj2 hf11))) as hne6.
    assert (hge9 : 9 <= dlt0) by dlia.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 hf11)))) (or_introl (conj hrem0 hge9))) as hG2.
    destruct (Nat.eq_dec dlt0 9) as [-> | h9].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      pose proof (proj1 (good2_f311 (ih s2 ltac:(lia)) hG2 hF2 hN1)); lia.
    + destruct (Nat.eq_dec dlt0 12) as [-> | h12].
      * cbn [Nat.div Nat.sub ones app] in hF2.
        pose proof (proj1 (good2_f3111 (ih s2 ltac:(lia)) hG2 hF2 hN1)); lia.
      * assert (hq4 : dlt0 / 3 - 1 = S (S (S (S (dlt0 / 3 - 5))))) by dlia.
        rewrite hq4 in hF2. cbn [ones app] in hF2.
        pose proof (proj1 (f3_1111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1))); lia.
Qed.

Lemma bigF_2s_good2 {m s : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF s ((2, true) :: G) dlt R_fin)
    (hs : s < m) (hN : NoNonlast0F G) :
  (dlt = 4 /\ (Good2 R_fin \/ exists W, R_fin = (1, true) :: W)) \/ dlt = 10 \/ dlt = 13.
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F hN)) as hN1.
  pose proof (good2_f1 (ih s1 ltac:(lia)) hG h1 hN) as hf1.
  destruct hcases as [[hrem1 _] |
    [[-> _] |
    [[hrem2 _] |
    [[-> [s2 [hs2 [dlt2 [-> hD2]]]]] |
    [[-> _] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]]]].
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - inverts h1 as hg hremg hg2; try lia.
    + match type of hg with
      | BigF ?sg _ ?dltg ?Rg =>
        destruct (bigD1_zeroT_inv hD2) as [-> ->];
        destruct (Nat.eq_dec dltg 0) as [-> | h0g];
        [ assert (hRg0s : exists W, Rg = (0, true) :: W) by
            (destruct (good2_head_cases hG) as [[Y ->] | [Y ->]];
             [ inverts hg; eexists; reflexivity
             | destruct (bigF_ge2_zero_head hg) as [Z hZ]; exists ((1, false) :: Z); exact hZ ]);
          destruct hRg0s as [W ->];
          cbn [Nat.div ones app bumpR];
          left; split; [reflexivity | right; exists W; reflexivity]
        | destruct (Nat.eq_dec dltg 3) as [-> | h3g];
          [ destruct (bigF_three_head hg) as [W ->];
            cbn [Nat.div ones app bumpR];
            left; split; [reflexivity | left; exact (good2_of_2_0s ((1, false) :: W))]
          | destruct (Nat.eq_dec dltg 6) as [-> | h6g];
            [ destruct (proj1 (proj2 (proj2 (good2_f (ih sg ltac:(lia)) hG hg hN))) eq_refl) as [U ->];
              cbn [Nat.div ones app bumpR];
              left; split; [reflexivity | left; exact (good2_of_2_1_0s ((1, false) :: (1, false) :: U))]
            | assert (hq3 : (1 + dltg) / 3 = S (S (S ((1 + dltg) / 3 - 3)))) by dlia;
              rewrite hq3; cbn [ones app bumpR];
              left; split; [reflexivity | left; exact (good2_of_2_1_1 (ones ((1 + dltg) / 3 - 3) ++ Rg))] ] ] ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))); lia.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - destruct hf1 as [h0 | [[-> hG2] | [[-> hS2] | [? hge15]]]]; [lia | | |].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (proj1 (good2_f31 (ih s2 ltac:(lia)) hG2 hF2 hN1)) as [-> | [-> _]]; auto.
    + cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (good2_f311 (ih s2 ltac:(lia)) (proj1 hS2) hF2 hN1) as [-> _]; auto.
    + assert (hq3 : dlt1 / 3 - 2 = S (S (S (dlt1 / 3 - 5)))) by dlia.
      rewrite hq3 in hF2. cbn [ones app] in hF2.
      destruct (f3_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] _]; auto.
Qed.

Lemma bigF_3_good1Safe {m s : nat} (ih : InvLt m)
    {rs : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG1 : Good1Safe rs) (h : BigF s ((3, false) :: rs) dlt R_fin)
    (hs : s < m) (hN : NoNonlast0F rs) :
  (dlt = 7 /\ (Good2 R_fin \/ exists W, R_fin = (1, true) :: W)) \/ (dlt mod 3 = 1 /\ 13 <= dlt).
Proof.
  destruct (proj1 hG1) as [-> | [[Z ->] | [-> | [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> hGF]] | [Z ->]]]]]]]]].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    cbn [bumpR] in hF4.
    assert (hEx : BigF 2 [(2, true); (1, true); (0, false)] 4 [(1, true); (1, false)])
      by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT [(0, false)]) eq_refl) eq_refl (BD_zeroT [(0, true); (1, false)])).
    destruct (bigF_det hF4 hEx) as [-> ->].
    left; split; [reflexivity | right; exists [(1, false)]; reflexivity].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    cbn [bumpR] in hF4.
    assert (hEx : BigF 2 ((2, true) :: (1, true) :: (0, true) :: Z) 4 ((1, true) :: (1, true) :: Z))
      by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT ((0, true) :: Z)) eq_refl) eq_refl (BD_zeroT ((0, true) :: (1, true) :: Z))).
    destruct (bigF_det hF4 hEx) as [-> ->].
    left; split; [reflexivity | right; exists ((1, true) :: Z); reflexivity].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    cbn [bumpR] in hF4.
    assert (hEx : BigF 2 [(2, true); (1, true); (1, false)] 4 [(1, true); (2, false)])
      by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT [(1, false)]) eq_refl) eq_refl (BD_zeroT [(0, true); (2, false)])).
    destruct (bigF_det hF4 hEx) as [-> ->].
    left; split; [reflexivity | right; exists [(2, false)]; reflexivity].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    cbn [bumpR] in hF4.
    assert (hEx : BigF 2 [(2, true); (1, true); (1, false); (0, false)] 4 [(1, true); (2, false); (0, false)])
      by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT [(1, false); (0, false)]) eq_refl) eq_refl
        (BD_zeroT [(0, true); (2, false); (0, false)])).
    destruct (bigF_det hF4 hEx) as [-> ->].
    left; split; [reflexivity | right; exists [(2, false); (0, false)]; reflexivity].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    cbn [bumpR] in hF4.
    assert (hEx : BigF 2 ((2, true) :: (1, true) :: (1, false) :: (0, true) :: Z) 4
      ((1, true) :: (2, false) :: (0, true) :: Z))
      by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT ((1, false) :: (0, true) :: Z)) eq_refl) eq_refl
        (BD_zeroT ((0, true) :: (2, false) :: (0, true) :: Z))).
    destruct (bigF_det hF4 hEx) as [-> ->].
    left; split; [reflexivity | right; exists ((2, false) :: (0, true) :: Z); reflexivity].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    cbn [bumpR] in hF4.
    assert (hEx : BigF 2 ((2, true) :: (1, true) :: (1, false) :: (1, false) :: Z) 4
      ((1, true) :: (2, false) :: (1, false) :: Z))
      by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT ((1, false) :: (1, false) :: Z)) eq_refl) eq_refl
        (BD_zeroT ((0, true) :: (2, false) :: (1, false) :: Z))).
    destruct (bigF_det hF4 hEx) as [-> ->].
    left; split; [reflexivity | right; exists ((2, false) :: (1, false) :: Z); reflexivity].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    pose proof (noNonlast0F_bumpR (noNonlast0F_tail hN)) as hNb.
    cbn [bumpR] in hF4, hNb.
    destruct (bigF_2s_good2 ih (good2_of_2_1_0s ((1, false) :: (1, false) :: Z)) hF4 ltac:(lia) hNb)
      as [[-> hO] | [-> | ->]].
    + left; exact (conj eq_refl hO).
    + right; split; [reflexivity | lia].
    + right; split; [reflexivity | lia].
  - destruct (bigF_3_1s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    pose proof (noNonlast0F_bumpR (noNonlast0F_tail hN)) as hNb.
    cbn [bumpR] in hF4, hNb.
    destruct (bigF_2s_good2 ih (good2_of_2_1_1 Z) hF4 ltac:(lia) hNb)
      as [[-> hO] | [-> | ->]].
    + left; exact (conj eq_refl hO).
    + right; split; [reflexivity | lia].
    + right; split; [reflexivity | lia].
  - pose proof (proj2 hG1 Z eq_refl) as hT.
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hNZ.
    destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
    destruct (bigF_2_inv h1) as [sa [hsa [dlta [Ra [ha hca]]]]].
    cbn [bumpR] in ha.
    pose proof (bigF_nnf ha (nnf_3F (nnf_1F hNZ))) as hNa.
    assert (hdlta : dlta = 7 \/ dlta = 10).
    { destruct hT as [hG | [[U ->] | [[W [-> hW]] | [W ->]]]].
      - destruct (proj1 (good2_f31 (ih sa ltac:(lia)) hG ha hNZ)) as [-> | [-> _]]; auto.
      - destruct (bigF_3_1_0s_inv ha) as [s4 [hs4 [dlt4 [-> hF4]]]].
        destruct (f2s_111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNZ)))) as [-> _].
        left; reflexivity.
      - destruct hW as [hG | [U ->]].
        + left; exact (proj1 (good2_f311 (ih sa ltac:(lia)) hG ha (noNonlast0F_tail hNZ))).
        + destruct (bigF_det ha (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> _].
          left; reflexivity.
      - exact (proj1 (f3_111 (ih sa ltac:(lia)) ha (noNonlast0F_tail (noNonlast0F_tail hNZ)))). }
    assert (hdlt0 : dlt0 = 0 /\
      ((dlta = 7 /\ R1 = (0, true) :: (1, false) :: (1, false) :: Ra) \/
       (dlta = 10 /\ R1 = (0, true) :: (1, false) :: (1, false) :: (1, false) :: Ra))).
    { destruct hca as [[? [? [-> ->]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]].
      - destruct hdlta as [-> | ->]; split; [reflexivity | | reflexivity |];
          [left | right]; exact (conj eq_refl eq_refl).
      - destruct hdlta as [-> | ->]; dlia.
      - destruct hdlta as [-> | ->]; dlia.
      - destruct hdlta as [-> | ->]; dlia.
      - destruct hdlta as [-> | ->]; dlia.
      - destruct hdlta as [-> | ->]; dlia. }
    destruct hdlt0 as [-> hR1].
    destruct hcases as [[hrem _] | [[hrem _] | [[? [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [hge _]]]]]; try dlia.
    destruct hR1 as [[-> ->] | [-> ->]].
    + cbn [bumpR] in hF2.
      assert (hGZ : GoodZero111Head Ra).
      { destruct (dec_head_0s Ra) as [[W hW] | hno0s].
        - right; exact (f_pos_0s (ih sa ltac:(lia)) ha (nnf_3F (nnf_1F hNZ)) ltac:(lia) hW).
        - left; exact hno0s. }
      destruct (f2s_11 (ih s2 ltac:(lia)) hF2 hNa) as [[-> hG1f] | [[-> _] | ->]].
      * left; split; [reflexivity | left; exact (good1Safe_to_good2 (hG1f hGZ))].
      * right; split; [reflexivity | lia].
      * right; split; [reflexivity | lia].
    + cbn [bumpR] in hF2.
      destruct (f2s_111 (ih s2 ltac:(lia)) hF2 hNa) as [-> hG1f].
      left; split; [reflexivity | left; exact (good1Safe_to_good2 hG1f)].
Qed.

Lemma bigF_3_safeU {m s : nat} (ih : InvLt m)
    {U : list Seg} {dlt : nat} {R_fin : list Seg}
    (hSU : SafeU U) (h : BigF s ((3, false) :: U) dlt R_fin)
    (hs : s < m) (hN : NoNonlast0F U) :
  dlt mod 3 = 1 /\ 7 <= dlt.
Proof.
  destruct hSU as [[Z ->] | [[Z [-> hZ]] | [[Z [-> hZ]] | [[Z ->] | hG1]]]].
  - destruct (f3_111 (ih s hs) h (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))) as [[-> | ->] _];
      (split; [reflexivity | lia]).
  - destruct hZ as [hG | [W ->]].
    + destruct (good2_f311 (ih s hs) hG h (noNonlast0F_tail (noNonlast0F_tail hN))) as [-> _];
        (split; [reflexivity | lia]).
    + destruct (bigF_det h (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: W))) as [-> _];
        (split; [reflexivity | lia]).
  - destruct hZ as [hG | [W ->]].
    + destruct (proj1 (good2_f31 (ih s hs) hG h (noNonlast0F_tail hN))) as [-> | [-> _]];
        (split; [reflexivity | lia]).
    + destruct (bigF_3_1_0s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
      destruct (f2s_111 (ih s4 ltac:(lia)) hF4
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))) as [-> _];
        (split; [reflexivity | lia]).
  - destruct (bigF_3_0s_inv h) as [s4 [hs4 [dlt4 [-> hF4]]]].
    destruct (f3_111 (ih s4 ltac:(lia)) hF4
      (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))) as [[-> | ->] _];
      (split; [reflexivity | lia]).
  - destruct (bigF_3_good1Safe ih hG1 h hs hN) as [[-> _] | [hm hge]];
      [split; [reflexivity | lia] | split; [exact hm | lia]].
Qed.

Lemma bigF_3_2_1_of_3_mod1_ge7 {m s : nat} (ih : InvLt m)
    {U : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF s ((3, false) :: (2, false) :: (1, false) :: U) dlt R_fin)
    (hs : s < m) (hN : NoNonlast0F U)
    (h3U : forall sa dlta Ra, sa < s -> BigF sa ((3, false) :: U) dlta Ra -> dlta mod 3 = 1 /\ 7 <= dlta) :
  (dlt = 7 /\ Good2 R_fin) \/ (dlt mod 3 = 1 /\ 13 <= dlt).
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  destruct (bigF_2_inv h1) as [sa [hsa [dlta [Ra [ha hca]]]]].
  cbn [bumpR] in ha.
  pose proof (bigF_nnf ha (nnf_3F hN)) as hNa.
  destruct (h3U sa dlta Ra ltac:(lia) ha) as [hrema hge7a].
  assert (hdlt0 : dlt0 = 0 /\ R1 = (0, true) :: ones (dlta / 3) ++ Ra).
  { destruct hca as [[? [? [-> ->]]] | [[h2 _] | [[hrem _] | [[h0 _] | [[h3 _] | [hrem _]]]]]]; try dlia.
    exact (conj eq_refl eq_refl). }
  destruct hdlt0 as [-> ->].
  destruct hcases as [[hrem _] | [[hrem _] | [[? [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [hge _]]]]]; try dlia.
  destruct (Nat.eq_dec dlta 7) as [-> | h7a].
  - cbn [Nat.div ones app bumpR] in hF2.
    assert (hGZ : GoodZero111Head Ra).
    { destruct (dec_head_0s Ra) as [[W hW] | hno0s].
      - right; exact (f_pos_0s (ih sa ltac:(lia)) ha (nnf_3F hN) ltac:(lia) hW).
      - left; exact hno0s. }
    destruct (f2s_11 (ih s2 ltac:(lia)) hF2 hNa) as [[-> hG1] | [[-> _] | ->]].
    + left; exact (conj eq_refl (good1Safe_to_good2 (hG1 hGZ))).
    + right; split; [reflexivity | lia].
    + right; split; [reflexivity | lia].
  - assert (hq3 : dlta / 3 = S (S (S (dlta / 3 - 3)))) by dlia.
    rewrite hq3 in hF2. cbn [ones app bumpR] in hF2.
    destruct (f2s_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hNa)) as [-> hG1].
    left; exact (conj eq_refl (good1Safe_to_good2 hG1)).
Qed.

Lemma bigF_3_good4Out {m s : nat} (ih : InvLt m)
    {Z : list Seg} {dlt : nat} {R_fin : list Seg}
    (hZ : Good4Out Z) (h : BigF s ((3, false) :: Z) dlt R_fin)
    (hs : s < m) (hN : NoNonlast0F Z) :
  (dlt = 7 /\ Good2 R_fin) \/ (dlt mod 3 = 1 /\ 13 <= dlt).
Proof.
  revert s dlt R_fin h hs hN.
  induction hZ as [| W | U hSU | Z' hZ' ihZ]; intros s dlt R_fin h hs hN.
  - eapply (bigF_3_2_1_of_3_mod1_ge7 ih h hs I).
    intros sa dlta Ra hlt ha.
    destruct (bigF_det ha bigF_3_1_nil_exists) as [-> _].
    split; [reflexivity | lia].
  - eapply (bigF_3_2_1_of_3_mod1_ge7 ih h hs (noNonlast0F_tail (noNonlast0F_tail hN))).
    intros sa dlta Ra hlt ha.
    destruct (bigF_det ha (bigF_3_1_1_1s_exists W)) as [-> _].
    split; [reflexivity | lia].
  - pose proof (noNonlast0F_tail (noNonlast0F_tail hN)) as hNU.
    eapply (bigF_3_2_1_of_3_mod1_ge7 ih h hs hNU).
    intros sa dlta Ra hlt ha.
    exact (bigF_3_safeU ih hSU ha ltac:(lia) hNU).
  - pose proof (noNonlast0F_tail (noNonlast0F_tail hN)) as hNZ'.
    eapply (bigF_3_2_1_of_3_mod1_ge7 ih h hs hNZ').
    intros sa dlta Ra hlt ha.
    destruct (ihZ sa dlta Ra ha ltac:(lia) hNZ') as [[-> _] | [hm hge]];
      [split; [reflexivity | lia] | split; [exact hm | lia]].
Qed.

Lemma bigF_2s_4_good2_of_strongHead {m s : nat} (ih : InvLt m)
    {U R_2s : list Seg} (hU : GoodStrongHead U)
    (h : BigF s ((2, true) :: U) 4 R_2s)
    (hs : s < m) (hN : NoNonlast0F U) :
  Good2 ((2, false) :: (1, false) :: R_2s).
Proof.
  destruct (bigF_2s_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 (nnf_1F hN)) as hN1.
  pose proof (f1 (ih s1 ltac:(lia)) h1 hN) as hf1.
  destruct hcases as [[? [? [h0 _]]] |
    [[-> [s2 [hs2 [dlt3 [hadd hF2]]]]] |
    [[? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [hadd hD2]]]]] |
    [[h3 _] |
     [? [? [s2 [hs2 [dlt3 [hadd hF2]]]]]]]]]]]; try lia.
  - destruct (f_258 (ih s1 ltac:(lia)) h1 (nnf_1F hN) (or_introl eq_refl)) as [U' ->].
    cbn [bumpR] in hF2.
    destruct (f2s_11 (ih s2 ltac:(lia)) hF2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))))
      as [[h4 _] | [[h10 _] | h13]]; lia.
  - contradiction (proj1 (f3_ne24 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) ltac:(lia)).
  - inverts h1 as hu hremu hu2; try lia.
    + match type of hu with
      | BigF ?su _ ?dltu ?Ru =>
        assert (dlt2 = 3) by lia; subst dlt2;
        destruct (bigD1_zeroT_inv hD2) as [_ ->];
        destruct (Nat.eq_dec dltu 0) as [-> | h0u];
        [ destruct (bigF_zero_head_3 hu hN) as [-> | [[Z ->] | [Z ->]]];
          [ cbn [Nat.div ones app bumpR]; exact (G2_c_2_1_1 ([] : list Seg))
          | cbn [Nat.div ones app bumpR]; exact (G2_c_2_1_1s Z)
          | destruct (bigF_zero_oneF_head hu hN) as [[? ->] | ->];
            [ cbn [Nat.div ones app bumpR]; exact G2_c_2_1_2
            | destruct hU as [hE | [hE | [[W [hE hW]] | [[? hE] | [[? hE] | hG]]]]]; try discriminate hE;
              [ inversion hE; subst; clear hE;
                destruct hW as [-> | hG2];
                [ cbn [Nat.div ones app bumpR]; exact G2_c_2_1_2
                | cbn [Nat.div ones app bumpR]; exact (G2_step_21 hG2) ]
              | contradiction (good2_ne_zeroT hG Z eq_refl) ] ] ]
        | destruct (Nat.eq_dec dltu 3) as [-> | h3u];
          [ destruct (bigF_three_head hu) as [Z ->];
            cbn [Nat.div ones app bumpR];
            exact (G2_step_21 (G2_c_2_0s ((1, false) :: Z)))
          | destruct (Nat.eq_dec dltu 6) as [-> | h6u];
            [ assert (hRu : Good2 Ru \/ Head0s11 Ru) by
                (destruct hU as [-> | [-> | [[W [-> _]] | [[W ->] | [[W ->] | hG]]]]];
                 [ inverts hu; lia
                 | inverts hu; lia
                 | inverts hu; lia
                 | right; exact (proj1 (proj2 (proj2 (proj2 (f1 (ih su ltac:(lia)) hu (noNonlast0F_tail hN))))) eq_refl)
                 | inverts hu; lia
                 | right; exact (proj1 (proj2 (proj2 (good2_f (ih su ltac:(lia)) hG hu hN))) eq_refl) ]);
              destruct hRu as [hG2 | [V ->]];
              [ cbn [Nat.div ones app bumpR]; exact (G2_step_21 (G2_step_21 hG2))
              | cbn [Nat.div ones app bumpR]; exact (G2_step_21 (G2_c_2_1_0s ((1, false) :: (1, false) :: V))) ]
            | assert (hq3 : (1 + dltu) / 3 = S (S (S ((1 + dltu) / 3 - 3)))) by dlia;
              rewrite hq3; cbn [ones app bumpR];
              exact (G2_step_21 (G2_c_2_1_1 (ones ((1 + dltu) / 3 - 3) ++ Ru))) ] ] ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil hu2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hu))); lia.
  - assert (dlt3 = 1) by lia; subst dlt3. contradiction (bigF_ne_one hF2).
Qed.

Lemma bigF_4_ne4 {m s : nat} (ih : InvLt m)
    {Y R_fin : list Seg} (h : BigF s ((4, false) :: Y) 4 R_fin)
    (hs : s < m) (hN : NoNonlast0F Y) : False.
Proof.
  inverts h as h1 hrem h2 heq; try lia.
  - pose proof (bigD1_nnf h1 hN) as hN1.
    match type of h1 with
    | BigD1 _ _ ?dlt1 _ =>
      destruct (dlt1 / 3) as [| q'] eqn:hq;
      [ assert (dlt1 = 2) by dlia; subst dlt1;
        cbn [ones app] in h2;
        inverts h2 as hF heq2;
        match type of hF with BigF ?s3 _ ?dlt3 _ =>
          assert (dlt3 = 2) by lia; subst dlt3;
          destruct (bigD1_two_head_nnf h1 hN) as [-> | [[Z ->] | [Z ->]]];
          [ cbn [bumpR] in hF;
            destruct (bigF_det hF bigF_2s_0_exists) as [h4 _]; lia
          | cbn [bumpR] in hF;
            destruct (bigF_det hF (bigF_2s_0s_full_exists Z)) as [h4 _]; lia
          | cbn [bumpR] in hF;
            destruct (f2s_1 (ih s3 ltac:(lia)) hF (noNonlast0F_tail (noNonlast0F_tail hN1))) as [h0 | [h4 | [h10 | h13]]]; lia ]
        end
      | cbn [ones app] in h2;
        inverts h2 as hF heq2;
        match type of hF with BigF ?s3 _ ?dlt3 _ =>
          assert (dlt3 = 2) by lia; subst dlt3;
          cbn [bumpR] in hF;
          exact (proj1 (f3_ne24 (ih s3 ltac:(lia)) hF (noNonlast0F_ones_append q' hN1)) eq_refl)
        end ]
    end.
  - pose proof (bigD1_ge2_of_ne_nil h1 ltac:(discriminate)) as hge2.
    match type of h1 with
    | BigD1 _ _ ?dlt1 _ =>
      assert (hq : dlt1 / 3 = S (dlt1 / 3 - 1)) by dlia;
      rewrite hq in h2; cbn [ones app] in h2;
      inverts h2 as hF heq2;
      match type of hF with BigF _ _ ?dlt3 _ => assert (dlt3 = 1) by lia; subst dlt3 end;
      exact (bigF_ne_one hF)
    end.
Qed.

Lemma bigF_2_1_nil_exists :
  exists s, BigF s [(2, false); (1, false)] 0 [(0, true); (1, false); (1, false); (1, false)].
Proof.
  destruct bigF_3_nil_exists as [s3 h3].
  eexists. exact (BF_twoF_rem1 (Y := [(1, false)]) h3 eq_refl).
Qed.

Lemma bigF_3_2_nil_exists :
  exists s, BigF s [(3, false); (2, false)] 0 [(0, true); (1, false); (1, false); (1, false)].
Proof.
  destruct bigF_2_nil_exists as [s2 h2].
  eexists. exact (BF_ge3_rem1 (d := 0) (b := false) (Y := [(2, false)]) (BD_zeroF h2) eq_refl).
Qed.

Lemma bigF_2_1_2_exists :
  exists s, BigF s [(2, false); (1, false); (2, false)] 4 [(2, false); (1, false); (1, false)].
Proof.
  destruct bigF_3_2_nil_exists as [s32 h32].
  eexists.
  exact (BF_twoF_rem0 (Y := [(1, false); (2, false)]) h32 eq_refl
    (BD_zeroT [(1, false); (1, false); (1, false)])).
Qed.

Lemma bigF_4_nil_exists :
  exists s, BigF s [(4, false)] 6 [(2, false)].
Proof.
  assert (h1 : BigD1 2 [(1, false)] 2 [(0, true); (0, false)])
    by exact (BD_oneF (Y := ([] : list Seg)) (BF_oneF_rem1 BF_nil eq_refl)).
  eexists.
  exact (BF_ge3_rem2 (d := 1) (b := false) (Y := ([] : list Seg)) h1 eq_refl
    (BD_oneF (Y := [(0, true); (0, false)]) bigF_2s_0_exists)).
Qed.

Lemma bigF_2_1s_1_exists :
  exists s R, BigF s [(2, false); (1, true); (1, false)] 13 R.
Proof.
  destruct bigF_4_nil_exists as [s4 h4].
  pose proof (BF_ge3_rem0 (d := 0) (b := true) (Y := [(1, false)]) (BD_zeroT [(1, false)]) eq_refl
    (BD_oneF (Y := [(2, false)]) h4)) as h3s1.
  destruct bigF_2_nil_exists as [s2 h2].
  pose proof (BF_oneF_rem2 h2 eq_refl (BD_oneF (Y := [(1, false); (1, false)]) bigF_3_1_nil_exists)) as h12.
  pose proof (BF_oneF_rem1 h12 eq_refl) as h112.
  pose proof (BF_oneF_rem1 h112 eq_refl) as h1112.
  pose proof (BF_oneF_rem1 h1112 eq_refl) as h11112.
  pose proof (BF_twoT_rem0 h11112 eq_refl
    (BD_zeroT [(0, true); (0, true); (1, false); (1, false); (1, false); (2, false)])) as h2s1112.
  pose proof (BF_ge3_rem0 (d := 0) (b := false) (Y := [(1, false); (1, false); (2, false)])
    (BD_zeroF h112) eq_refl
    (BD_oneF (Y := [(0, true); (1, false); (1, false); (1, false); (2, false)]) h2s1112)) as h3112.
  pose proof (BF_ge3_rem0 (d := 0) (b := false) (Y := [(1, false); (2, false)])
    (BD_zeroF h12) eq_refl
    (BD_oneF (Y := [(1, false); (1, false); (1, false); (2, false)]) h3112)) as h312.
  eexists. eexists.
  exact (BF_twoF_rem0 (Y := [(1, true); (1, false)]) h3s1 eq_refl
    (BD_oneF (Y := [(1, false); (1, false); (2, false)]) h312)).
Qed.

Lemma bigF_2_1s_1_0_exists :
  exists s, BigF s [(2, false); (1, true); (1, false); (0, false)] 0
    [(0, true); (1, false); (1, false); (1, false); (1, false); (2, false)].
Proof.
  destruct bigF_2_nil_exists as [s2 h2].
  pose proof (BF_ge3_rem0 (d := 1) (b := false) (Y := [(0, false)])
    (BD_oneF (Y := [(0, false)]) h2) eq_refl
    (BD_oneF (Y := [(1, false); (1, false)]) bigF_3_1_nil_exists)) as h40.
  pose proof (BF_ge3_rem0 (d := 0) (b := true) (Y := [(1, false); (0, false)])
    (BD_zeroT [(1, false); (0, false)]) eq_refl
    (BD_oneF (Y := [(2, false); (0, false)]) h40)) as h3s10.
  eexists.
  exact (BF_twoF_rem1 (Y := [(1, true); (1, false); (0, false)]) h3s10 eq_refl).
Qed.

Lemma good2_f_dispatch_high {m s s1 dlt dlt1 : nat} {Y R1 R_fin : list Seg}
    (ih : InvLt m) (hs : s <= m) (hs1 : s1 < s)
    (h1 : BigF s1 (bumpR (bumpR Y)) dlt1 R1) (hN_b2 : NoNonlast0F (bumpR (bumpR Y)))
    (hcases : FrontAfter s dlt1 R1 dlt R_fin)
    (hne2 : dlt1 <> 2)
    (h5 : dlt1 = 5 -> dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
      (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
      (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)))
    (h0 : dlt1 = 0 -> forall s2 dlt2, s2 < s -> dlt = dlt2 + 1 -> BigD1 s2 R1 dlt2 R_fin ->
      dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
      (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
      (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)))
    (h3 : dlt1 = 3 -> forall s2 dlt3, s2 < s -> dlt = dlt3 + 3 -> BigF s2 (bumpR (bumpR R1)) dlt3 R_fin ->
      dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
      (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
      (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)))
    (h6 : dlt1 = 6 -> forall s2 dlt3, s2 < s -> dlt = dlt3 + 3 -> BigF s2 ((3, false) :: R1) dlt3 R_fin ->
      dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
      (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
      (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)))
    (h9 : dlt1 = 9 -> forall s2 dlt3, s2 < s -> dlt = dlt3 + 3 -> BigF s2 ((3, false) :: (1, false) :: R1) dlt3 R_fin ->
      dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
      (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
      (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W))) :
  dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
  (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
  (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)).
Proof.
  pose proof (bigF_nnf h1 hN_b2) as hN1.
  destruct hcases as [[? [? [-> _]]] |
    [[h2 _] |
    [[hrem2 [hge5 [s2 [hs2 [dlt3 [-> hF2]]]]]] |
    [[-> [s2 [hs2 [dlt2 [-> hD2]]]]] |
    [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] |
     [hrem0 [hge6 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]]]]; try contradiction.
  - split_and; dlia.
  - destruct (Nat.eq_dec dlt1 5) as [h5e | h5ne]; [exact (h5 h5e) |].
    destruct (Nat.eq_dec dlt1 8) as [-> | h8ne].
    + destruct (f_258 (ih s1 ltac:(lia)) h1 hN_b2 (or_intror (or_intror eq_refl))) as [U ->].
      pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
      destruct (f2s_111 (ih s4 ltac:(lia)) hF4 hNU) as [-> _].
      split_and; dlia.
    + destruct (Nat.eq_dec dlt1 11) as [-> | h11ne].
      * destruct (f_11 (ih s1 ltac:(lia)) h1 hN_b2) as [[U ->] | hS].
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> _].
           split_and; dlia.
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (good2_f311 (ih s2 ltac:(lia)) (proj1 hS) hF2 hN1) as [-> _].
           split_and; dlia.
      * assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
        rewrite hq3 in hF2. cbn [ones app] in hF2.
        destruct (f3_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] _];
          split_and; dlia.
  - exact (h0 eq_refl s2 dlt2 hs2 eq_refl hD2).
  - exact (h3 eq_refl s2 dlt3 hs2 eq_refl hF2).
  - destruct (Nat.eq_dec dlt1 6) as [-> | h6ne].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      exact (h6 eq_refl s2 dlt3 hs2 eq_refl hF2).
    + destruct (Nat.eq_dec dlt1 9) as [-> | h9ne].
      * cbn [Nat.div Nat.sub ones app] in hF2.
        exact (h9 eq_refl s2 dlt3 hs2 eq_refl hF2).
      * destruct (Nat.eq_dec dlt1 12) as [-> | h12ne].
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (f3_11 (ih s2 ltac:(lia)) hF2 hN1) as [-> | [-> | [-> _]]].
           ++ split_and; dlia.
           ++ assert (hGZ : GoodZero111Head R1).
              { destruct (dec_head_0s R1) as [[W hW] | hno0s].
                - right; exact (f_pos_0s (ih s1 ltac:(lia)) h1 hN_b2 ltac:(lia) hW).
                - left; exact hno0s. }
              split_and; try dlia.
              intro; left; exact (bigF_3_1_1_7_good2_of_gz ih hGZ hF2 ltac:(lia) hN1).
           ++ split_and; dlia.
        -- assert (hq3 : dlt1 / 3 - 2 = S (S (S (dlt1 / 3 - 5)))) by dlia.
           rewrite hq3 in hF2. cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 ltac:(lia)) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] [hG2' _]].
           ++ split_and; try dlia. intro; left; exact hG2'.
           ++ split_and; dlia.
Qed.

Lemma good2_f_from_3_0s11 {m s2 dlt3 : nat} {U R_fin : list Seg}
    (ih : InvLt m) (hGZ : GoodZero111Head U)
    (hF2 : BigF s2 (bumpR (bumpR ((0, true) :: (1, false) :: (1, false) :: U))) dlt3 R_fin)
    (hs2 : s2 < m) (hNU : NoNonlast0F U) :
  (dlt3 + 3) mod 3 <> 2 /\ (dlt3 + 3 = 4 -> Good4Out R_fin) /\ (dlt3 + 3 = 6 -> Head0s11 R_fin) /\
  (dlt3 + 3 = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
  (dlt3 + 3 = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)).
Proof.
  cbn [bumpR] in hF2.
  destruct (f2s_11 (ih s2 hs2) hF2 hNU) as [[-> hG1] | [[-> _] | ->]].
  - split_and; try dlia. intro; left; exact (good1Safe_to_strong2 (hG1 hGZ)).
  - split_and; dlia.
  - split_and; dlia.
Qed.

Lemma good2_f_from_6_0s11 {m s2 dlt3 : nat} {U R_fin : list Seg}
    (ih : InvLt m)
    (hF2 : BigF s2 ((3, false) :: (0, true) :: (1, false) :: (1, false) :: U) dlt3 R_fin)
    (hs2 : s2 < m) (hNU : NoNonlast0F U) :
  (dlt3 + 3) mod 3 <> 2 /\ (dlt3 + 3 = 4 -> Good4Out R_fin) /\ (dlt3 + 3 = 6 -> Head0s11 R_fin) /\
  (dlt3 + 3 = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
  (dlt3 + 3 = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)).
Proof.
  destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
  destruct (f3_11 (ih s4 ltac:(lia)) hF4 hNU) as [-> | [-> | [-> _]]].
  - split_and; try dlia. intro; exact (bigF_3_zero_prefix hF4).
  - split_and; dlia.
  - split_and; dlia.
Qed.

Lemma good2_f_from_9_hs {m s2 dlt3 : nat} {R1 R_fin : list Seg}
    (ih : InvLt m) (hR1 : Head0s11 R1 \/ Strong2 R1)
    (hF2 : BigF s2 ((3, false) :: (1, false) :: R1) dlt3 R_fin)
    (hs2 : s2 < m) (hN1 : NoNonlast0F R1) :
  (dlt3 + 3) mod 3 <> 2 /\ (dlt3 + 3 = 4 -> Good4Out R_fin) /\ (dlt3 + 3 = 6 -> Head0s11 R_fin) /\
  (dlt3 + 3 = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
  (dlt3 + 3 = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)).
Proof.
  destruct hR1 as [[U ->] | hS].
  - destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
    destruct (f2s_111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))))
      as [-> hG1].
    split_and; try dlia. intro; left; exact (good1Safe_to_good2 hG1).
  - destruct (good2_f31 (ih s2 hs2) (proj1 hS) hF2 hN1) as [h710 hSf].
    pose proof (hSf hS) as hS'.
    destruct h710 as [-> | [-> _]].
    + split_and; try dlia. intro; left; exact (proj1 hS').
    + split_and; dlia.
Qed.

(* ========================================================================== *)
(* Group 5 Master Step Theorem: step_good2_f                                  *)
(* ========================================================================== *)

Lemma good2_f_case_2_1_1 {m : nat} (ih : InvLt m)
    {Z : list Seg} {dlt : nat} {R_fin : list Seg}
    (h : BigF m ((2, false) :: (1, false) :: (1, false) :: Z) dlt R_fin)
    (hN : NoNonlast0F ((2, false) :: (1, false) :: (1, false) :: Z)) :
  dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
  (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
  (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)).
Proof.
  destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hNZ.
  pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
  pose proof (bigF_nnf h1 hN_b2) as hN1.
  pose proof h1 as h1'. cbn [bumpR] in h1'.
  eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases).
  - exact (proj1 (f3_ne24 (ih s1 hs1) h1' (nnf_1F hNZ))).
  - intro h5; subst dlt1.
    destruct hcases as [[? _] | [[? _] | [[? [? [s2 [hs2 [dlt3 [-> hF2]]]]]] |
      [[? _] | [[? _] | [? _]]]]]]; try dlia.
    destruct (f3_5_0111 (ih s1 hs1) h1' (nnf_1F hNZ)) as [U ->].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))) as hNU.
    cbn [Nat.div Nat.sub ones app] in hF2.
    destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
    destruct (f3_111 (ih s4 ltac:(lia)) hF4 hNU) as [[-> | ->] _];
      split_and; dlia.
  - intros h0 s2 dlt2 hs2 -> hD2; subst dlt1.
    destruct (bigF_3_inv h1') as [sa [hsa [dlta [Ra [ha hca]]]]].
    destruct hca as [[hrema [hgea [? ->]]] | [[? [? [? [? [hadd0 _]]]]] |
      [[? [? [? [? [hadd0 _]]]]] | [? [? [? [? [? [hadd0 _]]]]]]]]]; try lia.
    destruct (bigD1_zeroT_inv hD2) as [-> ->].
    pose proof (f1 (ih sa ltac:(lia)) ha hNZ) as hf1a.
    pose proof (proj1 (proj2 hf1a)) as hne4.
    assert (hSU : SafeU (ones (dlta / 3 - 1) ++ Ra)).
    { destruct (Nat.eq_dec dlta 7) as [-> | h7a].
      - cbn [Nat.div Nat.sub ones app].
        destruct (proj1 (proj2 (proj2 (proj2 (proj2 hf1a)))) eq_refl) as [hH | hG1a].
        + right; right; left; exists Ra; exact (conj eq_refl (or_intror (head0s111_to_head0s11 hH))).
        + right; right; left; exists Ra; exact (conj eq_refl (or_introl (good1Safe_to_good2 hG1a))).
      - destruct (Nat.eq_dec dlta 10) as [-> | h10a].
        + cbn [Nat.div Nat.sub ones app].
          destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 hf1a))))) eq_refl) as [hH | hG2a].
          * right; left; exists Ra; exact (conj eq_refl (or_intror hH)).
          * right; left; exists Ra; exact (conj eq_refl (or_introl hG2a)).
        + assert (hq3 : dlta / 3 - 1 = S (S (S (dlta / 3 - 4)))) by dlia.
          rewrite hq3; cbn [ones app].
          left; exists (ones (dlta / 3 - 4) ++ Ra); reflexivity. }
    cbn [bumpR]; split_and; try dlia.
    intro; exact (G4_of_safeU hSU).
  - intros h3 s2 dlt3 hs2 -> hF2; subst dlt1.
    destruct (f3_3_non0s (ih s1 hs1) h1' (nnf_1F hNZ) (fun _ hEq => ltac:(discriminate hEq))) as [U [-> hSU]].
    exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2 hs2
      (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
  - intros h6 ? ? ? ? ?; subst dlt1.
    contradiction (f3_1_ne6 (ih s1 hs1) h1' hNZ).
  - intros h9 s2 dlt3 hs2 -> hF2; subst dlt1.
    exact (good2_f_from_9_hs ih (f3_9 (ih s1 hs1) h1' (nnf_1F hNZ)) hF2 hs2 hN1).
Qed.

(* The two suffixes needed after a leading 4 have the same call interface. *)
Definition TightHead (R : list Seg) :=
  exists U, R = (0, true) :: (1, false) :: (1, false) :: U /\ GoodZero111Head U.

Record FourSeed (d : nat) (R : list Seg) : Prop := {
  seed_ne2 : d <> 2;
  seed_0 : d = 0 -> TightHead R;
  seed_3 : d = 3 -> Head0s11 R;
  seed_5 : d = 5 -> Head0s111 R;
  seed_6 : d = 6 -> Head0s11 R \/ Good1Safe R;
  seed_9 : d = 9 -> Head0s11 R \/ Strong2 R
}.

Lemma four_seed_2s {m k d U R} (ih : InvLt m) (hk : k < m)
    (h : BigF k ((2, true) :: U) d R) (hn : NoNonlast0F U) : FourSeed d R.
Proof.
  destruct (f2s (ih k hk) h hn) as [h2 [h5 [h0 [h3 [h6 [h9 _]]]]]].
  constructor; try assumption; [| contradiction].
  intro hd. destruct (h0 hd) as [V [-> hv]].
  exists V; split; [reflexivity |].
  exact (goodF2U_to_goodZero111Head (safeU_to_goodF2U hv)).
Qed.

Lemma four_seed_3 {m k d U R} (ih : InvLt m) (hk : k < m)
    (h : BigF k ((3, false) :: U) d R) (hn : NoNonlast0F U) : FourSeed d R.
Proof.
  constructor; [exact (proj1 (f3_ne24 (ih k hk) h hn)) | ..]; intro hd.
  - subst d. destruct (bigF_3_zero_goodF2U ih hk h hn) as [V [-> hv]].
    exists V; split; [reflexivity | exact (goodF2U_to_goodZero111Head hv)].
  - exact (f3_36 (ih k hk) h hn (or_introl hd)).
  - subst d. exact (f3_5_0111 (ih k hk) h hn).
  - left; exact (f3_36 (ih k hk) h hn (or_intror hd)).
  - subst d. exact (f3_9 (ih k hk) h hn).
Qed.

Inductive FourReturn (R : list Seg) : nat -> Prop :=
  | F4_zero : TightHead R -> FourReturn R 0
  | F4_three : Head0s11 R -> FourReturn R 3
  | F4_five : Head0s11 R -> FourReturn R 5
  | F4_six : Head0s11 R \/ Good1Safe R -> FourReturn R 6
  | F4_other d : d = 8 \/ d mod 3 = 1 \/ 9 <= d -> FourReturn R d.

Lemma four_return {m k W d R} (ih : InvLt m) (hk : k < m)
    (h : BigF k ((4, false) :: W) d R) (hn : NoNonlast0F W)
    (seed : forall j e T, j < k -> BigF j (bumpR (bumpR W)) e T -> FourSeed e T) :
  FourReturn R d.
Proof.
  inverts h as h1 hrem h2.
  - destruct (bigD1_oneF_inv h1) as [j [hj [e [-> hf]]]].
    destruct (seed j e _ ltac:(lia) hf) as [hne2 _ _ h5 _ _].
    apply F4_zero.
    destruct (Nat.eq_dec e 5) as [-> | hne5].
    + destruct (h5 eq_refl) as [V ->]. cbn [Nat.div ones app].
      eexists; split; [reflexivity | right; eexists; reflexivity].
    + assert (hq : (e + 2) / 3 = S (S (S ((e + 2) / 3 - 3)))) by dlia.
      rewrite hq. cbn [ones app].
      eexists; split; [reflexivity | left; intros ? heq; discriminate heq].
  - destruct (bigD1_oneF_inv h1) as [j [hj [e [-> hf]]]].
    destruct (seed j e _ ltac:(lia) hf) as [_ h0 h3 _ h6 h9].
    pose proof (bigF_nnf hf (noNonlast0F_bumpR (noNonlast0F_bumpR hn))) as hnt.
    destruct (bigD1_oneF_inv h2) as [p [hp [f [-> hg]]]].
    destruct (Nat.eq_dec e 0) as [-> | hne0].
    + destruct (h0 eq_refl) as [V [-> hv]].
      cbn [Nat.div ones app bumpR] in hg.
      destruct (f2s_11 (ih p ltac:(lia)) hg
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hnt)))) as [[-> h4] | [[-> _] | ->]];
        try (apply F4_other; right; right; lia).
      apply F4_six. right; exact (h4 hv).
    + destruct (Nat.eq_dec e 3) as [-> | hne3].
      * destruct (h3 eq_refl) as [V ->]. cbn [Nat.div ones app bumpR] in hg.
        destruct (bigF_3_0s_inv hg) as [q [hq [g [-> hh]]]].
        destruct (f3_11 (ih q ltac:(lia)) hh
          (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hnt)))) as [-> | [-> | [-> _]]];
          try (apply F4_other; right; right; lia).
        apply F4_five. exact (bigF_3_zero_prefix hh).
      * destruct (Nat.eq_dec e 6) as [-> | hne6].
        -- cbn [Nat.div ones app bumpR] in hg. destruct (h6 eq_refl) as [[V ->] | hv].
           ++ destruct (bigF_3_1_0s_inv hg) as [q [hq [g [-> hh]]]].
              destruct (f2s_111 (ih q ltac:(lia)) hh
                (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hnt)))) as [-> _].
              apply F4_other; right; right; lia.
           ++ destruct (proj1 (good2_f31 (ih p ltac:(lia)) (good1Safe_to_good2 hv) hg hnt)) as [-> | [-> _]];
                apply F4_other; right; right; lia.
        -- destruct (Nat.eq_dec e 9) as [-> | hne9].
           ++ cbn [Nat.div ones app bumpR] in hg. destruct (h9 eq_refl) as [[V ->] | hv].
              ** destruct (bigF_det hg (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: V))) as [-> _].
                 apply F4_other; right; right; lia.
              ** destruct (good2_f311 (ih p ltac:(lia)) (proj1 hv) hg hnt) as [-> _].
                 apply F4_other; right; right; lia.
           ++ assert (hq : (e + 2) / 3 = S (S (S (S ((e + 2) / 3 - 4))))) by dlia.
              rewrite hq in hg. cbn [ones app bumpR] in hg.
              destruct (f3_111 (ih p ltac:(lia)) hg (noNonlast0F_ones_append _ hnt)) as [[-> | ->] _];
                apply F4_other; right; right; lia.
  - destruct (bigD1_oneF_inv h1) as [j [hj [e [-> hf]]]].
    pose proof (bigF_nnf hf (noNonlast0F_bumpR (noNonlast0F_bumpR hn))) as hnt.
    pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ hf)) as hne1.
    assert (hq : (e + 2) / 3 = S (S ((e + 2) / 3 - 2))) by dlia.
    rewrite hq in h2.
    destruct (bigD1_1_1_inv h2) as [p [hp [f [-> hg]]]].
    pose proof (noNonlast0F_ones_append ((e + 2) / 3 - 2) hnt) as hn'.
    pose proof (f3_ne24 (ih p ltac:(lia)) hg hn') as hne24.
    destruct (Nat.eq_dec f 0) as [-> | hne0].
    + apply F4_three. exact (bigF_3_zero_prefix hg).
    + destruct (Nat.eq_dec f 3) as [-> | hne3].
      * apply F4_six. left; exact (f3_36 (ih p ltac:(lia)) hg hn' (or_introl eq_refl)).
      * destruct (Nat.eq_dec f 5) as [-> | hne5].
        -- apply F4_other; left; lia.
        -- destruct (Nat.eq_dec f 1) as [-> | hne1']; [contradiction (bigF_ne_one hg) |].
           destruct (Nat.eq_dec (f mod 3) 1);
             apply F4_other; right; [left | right]; dlia.
Qed.

Lemma good2_f_via_four {m W dlt R} (ih : InvLt m)
    (h : BigF m ((2, false) :: (1, true) :: (1, false) :: W) dlt R)
    (hn : NoNonlast0F W)
    (seed : forall j e T, j < m -> BigF j (bumpR (bumpR W)) e T -> FourSeed e T) :
  dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R) /\ (dlt = 6 -> Head0s11 R) /\
  (dlt = 7 -> Strong2 R \/ Head0s11 R) /\
  (dlt = 10 -> Good2 R \/ Head0s11 R \/ (exists U, R = (1, true) :: U)).
Proof.
  destruct (bigF_2_inv h) as [s [hs [d [T [hF hcases]]]]].
  assert (hn' : NoNonlast0F (bumpR (bumpR ((1, true) :: (1, false) :: W)))).
  { cbn [bumpR]. apply nnf_Sd, nnf_1F, hn. }
  pose proof (bigF_nnf hF hn') as hnT.
  pose proof hF as hF'. cbn [bumpR] in hF'.
  destruct (bigF_3s_inv hF') as [k [hk [e [he hg]]]].
  cbn [bumpR] in hg.
  pose proof (four_return (k := k) ih ltac:(lia) hg hn (fun j f V hj => seed j f V ltac:(lia))) as hret.
  eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs hF hn' hcases ltac:(lia)
    (fun h5 => ltac:(destruct hret as [| | | | ? [? | [? | ?]]]; dlia))
    (fun h0 => ltac:(lia))).
  - intros h3 j f hj -> hh.
    destruct hret as [[U [-> hG]] | | | | ? [? | [? | ?]]]; try dlia.
    exact (good2_f_from_3_0s11 ih hG hh hj (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hnT)))).
  - intros h6 j f hj -> hh.
    destruct hret as [| [U ->] | | | ? [? | [? | ?]]]; try dlia.
    exact (good2_f_from_6_0s11 ih hh hj (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hnT)))).
  - intros h9 j f hj -> hh.
    destruct hret as [| | | hshape | ? [? | [? | ?]]]; try dlia.
    destruct hshape as [hH | hG].
    + exact (good2_f_from_9_hs ih (or_introl hH) hh hj hnT).
    + exact (good2_f_from_9_hs ih (or_intror (good1Safe_to_strong2 hG)) hh hj hnT).
Qed.

Lemma step_good2_f {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF m G dlt R_fin) (hN : NoNonlast0F G) :
  dlt mod 3 <> 2 /\ (dlt = 4 -> Good4Out R_fin) /\ (dlt = 6 -> Head0s11 R_fin) /\
  (dlt = 7 -> Strong2 R_fin \/ Head0s11 R_fin) /\
  (dlt = 10 -> Good2 R_fin \/ Head0s11 R_fin \/ (exists W, R_fin = (1, true) :: W)).
Proof.
  destruct hG as [? h1g | | | | Z | | Z | | | Z | Z | Z | Z | Z | Z | Z | Z hGF | G' hG'].
  - (* G2_of_good1 *)
    destruct h1g as [-> | [[Z ->] | [-> | [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z ->]]]]]]]]].
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + inverts h; split_and; dlia.
    + exact (good2_f_case_2_1_1 ih h hN).
  - (* G2_c_2_0 *)
    destruct bigF_2_0_exists as [? hEx].
    destruct (bigF_det h hEx) as [-> _].
    split_and; dlia.
  - (* G2_c_2_1 *)
    destruct bigF_2_1_nil_exists as [? hEx].
    destruct (bigF_det h hEx) as [-> _].
    split_and; dlia.
  - (* G2_c_2_1_2 *)
    destruct bigF_2_1_2_exists as [? hEx].
    destruct (bigF_det h hEx) as [-> ->].
    split_and; try dlia. intro; exact G4_two_one_one.
  - (* G2_c_2_0s *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail hN)) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    pose proof (f2s (ih s1 hs1) h1' hNZ) as hf2s.
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases
      (proj1 hf2s) (fun h5 => False_ind _ (proj1 (proj2 hf2s) h5))).
    + intros h0 s2 dlt2 hs2 -> hD2; subst dlt1.
      destruct (proj1 (proj2 (proj2 hf2s)) eq_refl) as [U [-> hSU]].
      destruct (bigD1_zeroT_inv hD2) as [-> ->].
      cbn [bumpR]; split_and; try dlia. intro; exact (G4_of_safeU hSU).
    + intros h3 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct (bigF_2s_3_goodF2U ih h1' hs1 hNZ) as [U [-> hGFU]].
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head hGFU) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h6 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 hf2s)))) eq_refl) as [[U ->] | hG1].
      * exact (good2_f_from_6_0s11 ih hF2 hs2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
      * destruct (bigF_3_good1Safe ih hG1 hF2 hs2 hN1) as [[-> hO] | [hm hge]].
        -- destruct hO as [hG2 | [W ->]].
           ++ split_and; try dlia. intro; left; exact hG2.
           ++ split_and; try dlia. intro; right; right; exists W; reflexivity.
        -- split_and; dlia.
    + intros h9 s2 dlt3 hs2 -> hF2; subst dlt1.
      exact (good2_f_from_9_hs ih (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 hf2s))))) eq_refl) hF2 hs2 hN1).
  - (* G2_c_2_1s_0 *)
    destruct bigF_2_1s_0_exists as [? hEx].
    destruct (bigF_det h hEx) as [-> _].
    split_and; dlia.
  - (* G2_c_2_1s_0s *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    destruct (bigF_3s_inv h1') as [sa [hsa [dlta [hadd1 ha]]]].
    cbn [bumpR] in ha.
    destruct (bigF_3s_inv ha) as [sb [hsb [dltb [hadda hb]]]].
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases ltac:(lia) ltac:(lia)
      (fun h0 => ltac:(lia)) (fun h3 => ltac:(lia))).
    + intros h6 s2 dlt3 hs2 -> hF2; subst dlt1.
      assert (dltb = 0) by lia; subst dltb.
      destruct Z as [| [dx bx] xs].
      * destruct bigF_2_nil_exists as [? hEx].
        cbn [bumpR] in hb.
        destruct (bigF_det hb hEx) as [h4 _]; lia.
      * cbn [bumpR] in hb.
        destruct (bigF_ge3_zero_prefix hb) as [[U ->] | [U ->]].
        -- exact (good2_f_from_6_0s11 ih hF2 hs2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
        -- destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
           destruct (bigF_3_1_0s_inv hF4) as [s5 [hs5 [dlt5 [-> hF5]]]].
           pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))) as hNU.
           destruct (f2s_1 (ih s5 ltac:(lia)) hF5 hNU) as [-> | [-> | [-> | ->]]];
             split_and; dlia.
    + intros h9 s2 dlt3 hs2 -> hF2; subst dlt1.
      assert (dltb = 3) by lia; subst dltb.
      destruct (bigF_three_head hb) as [U ->].
      pose proof (noNonlast0F_tail (noNonlast0F_tail hN1)) as hNU.
      destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
      destruct (f2s_11 (ih s4 ltac:(lia)) hF4 hNU) as [[-> hG1] | [[-> _] | ->]].
      * split_and; try dlia.
        intro.
        destruct (dec_head_0s U) as [[W ->] | hno0s].
        -- destruct (bigF_det hF4 (bigF_2s_1_1_0s_exists W)) as [? ->].
           right; right; exists ((0, true) :: (1, false) :: W); reflexivity.
        -- left; exact (good1Safe_to_good2 (hG1 (or_introl hno0s))).
      * split_and; dlia.
      * split_and; dlia.
  - (* G2_c_2_1s_1 *)
    destruct bigF_2_1s_1_exists as [? [? hEx]].
    destruct (bigF_det h hEx) as [-> _].
    split_and; dlia.
  - (* G2_c_2_1s_1_0 *)
    destruct bigF_2_1s_1_0_exists as [? hEx].
    destruct (bigF_det h hEx) as [-> _].
    split_and; dlia.
  - (* G2_c_2_1s_1_0s *)
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hW.
    apply (good2_f_via_four ih h hW).
    intros j e T hj hT. exact (four_seed_2s ih hj hT (noNonlast0F_tail hW)).
  - (* G2_c_2_1s_1_1 *)
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hW.
    apply (good2_f_via_four ih h hW).
    intros j e T hj hT. exact (four_seed_3 ih hj hT (noNonlast0F_tail hW)).
  - (* G2_c_2_1_0s *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    destruct (bigF_3_0s_inv h1') as [sa [hsa [dlta [hadd1 ha]]]].
    pose proof (f3_ne24 (ih sa ltac:(lia)) ha hNZ) as hne24.
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases ltac:(lia) (fun h5 => ltac:(lia)) (fun h0 => ltac:(lia))).
    + intros h3 s2 dlt3 hs2 -> hF2.
      assert (dlta = 0) by lia; subst dlta.
      destruct (bigF_3_zero_goodF2U (s := sa) ih ltac:(lia) ha hNZ) as [U [-> hGFU]].
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head hGFU) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h6 s2 dlt3 hs2 -> hF2.
      assert (dlta = 3) by lia; subst dlta.
      destruct (f3_36 (ih sa ltac:(lia)) ha hNZ (or_introl eq_refl)) as [U ->].
      exact (good2_f_from_6_0s11 ih hF2 hs2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h9 s2 dlt3 hs2 -> hF2.
      assert (dlta = 6) by lia; subst dlta.
      exact (good2_f_from_9_hs ih (or_introl (f3_36 (ih sa ltac:(lia)) ha hNZ (or_intror eq_refl))) hF2 hs2 hN1).
  - (* G2_c_2_1_1 *)
    exact (good2_f_case_2_1_1 ih h hN).
  - (* G2_c_2_1_1s *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    destruct (bigF_3_1s_inv h1') as [sa [hsa [dlta [hadd1 ha]]]].
    pose proof (noNonlast0F_bumpR hNZ) as hNbZ.
    pose proof (f2s (ih sa ltac:(lia)) ha hNbZ) as hf2s.
    pose proof (proj1 hf2s) as hne2a.
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases ltac:(lia) (fun h5 => ltac:(lia)) (fun h0 => ltac:(lia))).
    + intros h3 s2 dlt3 hs2 -> hF2.
      assert (dlta = 0) by lia; subst dlta.
      destruct (proj1 (proj2 (proj2 hf2s)) eq_refl) as [U [-> hSU]].
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h6 s2 dlt3 hs2 -> hF2.
      assert (dlta = 3) by lia; subst dlta.
      destruct (proj1 (proj2 (proj2 (proj2 hf2s))) eq_refl) as [U ->].
      exact (good2_f_from_6_0s11 ih hF2 hs2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h9 s2 dlt3 hs2 -> hF2.
      assert (dlta = 6) by lia; subst dlta.
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 hf2s)))) eq_refl) as [hH | hG1].
      * exact (good2_f_from_9_hs ih (or_introl hH) hF2 hs2 hN1).
      * exact (good2_f_from_9_hs ih (or_intror (good1Safe_to_strong2 hG1)) hF2 hs2 hN1).
  - (* G2_c_2_2_0s_1_1 *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN))))) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    assert (h4_out :
      (dlt1 = 3 /\ exists U, R1 = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U) \/ dlt1 mod 3 = 1).
    { inverts h1' as hd1 hremd1 hd2.
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        destruct (f2s_11 (ih sb ltac:(lia)) hb hNZ) as [[h4 _] | [[h10 _] | h13]]; dlia.
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        destruct (f2s_11 (ih sb ltac:(lia)) hb hNZ) as [[h4 _] | [[h10 _] | h13]]; dlia.
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        pose proof (bigF_nnf hb (nnf_2T (nnf_1F (nnf_1F hNZ)))) as hNb.
        destruct (f2s_11 (ih sb ltac:(lia)) hb hNZ) as [[-> _] | [[-> _] | ->]].
        + cbn [Nat.div ones app] in hd2.
          destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
          destruct (bigF_2s_inv hb) as [se [hse [dlte [Re [he hce]]]]].
          pose proof (f111 (ih se ltac:(lia)) he hNZ) as hf111e.
          assert (hRd1 :
            (exists W, Rd1 = (1, true) :: (0, true) :: W) \/
            (exists W, Rd1 = (1, true) :: (1, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: W) \/
            (exists W, Rd1 = (1, true) :: (1, false) :: (1, false) :: (1, false) :: W /\ GoodF2U W) \/
            (exists W, Rd1 = (2, false) :: (1, false) :: (1, false) :: W /\ GoodTail W)).
          { destruct hce as [[hrem _] | [[-> _] | [[hrem _] |
              [[-> [sf [hsf [dltf [haddf hDf]]]]] | [[-> _] | [? [hge6 [sf [? [dltf [haddf hFf]]]]]]]]]]].
            - destruct hf111e as [[h0 _] | [hm ?]]; dlia.
            - destruct hf111e as [[h0 _] | [hm ?]]; dlia.
            - destruct hf111e as [[h0 _] | [hm ?]]; dlia.
            - destruct hf111e as [[? [hZ111 _]] | [? [hge9 _]]]; [| lia].
              destruct hZ111 as [-> | [[W ->] | [[W ->] | [[W ->] | [[W [-> hGF]] | [W [-> hT]]]]]]];
                destruct (bigD1_zeroT_inv hDf) as [_ ->].
              + left; exists [(0, false)]; reflexivity.
              + left; exists ((0, true) :: W); reflexivity.
              + left; exists ((1, false) :: W); reflexivity.
              + right; left; exists W; reflexivity.
              + right; right; left; exists W; exact (conj eq_refl hGF).
              + right; right; right; exists W; exact (conj eq_refl hT).
            - destruct hf111e as [[h0 _] | [? [hge9 _]]]; lia.
            - assert (dltf = 1) by lia; subst dltf; contradiction (bigF_ne_one hFf). }
          destruct hRd1 as [[W ->] | [[W ->] | [[W [-> hGF]] | [W [-> hT]]]]].
          * destruct (bigF_3_1s_inv hF) as [sf [hsf [dltf [-> hFf]]]].
            cbn [bumpR] in hFf.
            assert (hEx : BigF 2 ((2, true) :: (1, true) :: W) 4 ((1, true) :: bumpR W))
              by exact (BF_twoT_rem0 (BF_oneF_rem1 (BF_oneT W) eq_refl) eq_refl (BD_zeroT ((0, true) :: bumpR W))).
            destruct (bigF_det hFf hEx) as [-> _].
            right; reflexivity.
          * destruct (bigF_3_good1Safe ih (good1Safe_of_1s_1_1_0s_1_1 W) hF ltac:(lia) hNb) as [[-> _] | [hm ?]];
              right; dlia.
          * destruct (bigF_3_good1Safe ih (good1Safe_of_1s_1_1_1 hGF) hF ltac:(lia) hNb) as [[-> _] | [hm ?]];
              right; dlia.
          * destruct (bigF_3_good1Safe ih (good1Safe_of_2_1_1 hT) hF ltac:(lia) hNb) as [[-> _] | [hm ?]];
              right; dlia.
        + cbn [Nat.div ones app] in hd2.
          destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
          destruct (f3_11 (ih sc ltac:(lia)) hF hNb) as [-> | [-> | [-> _]]].
          * left; split; [reflexivity | exact (bigF_3_zero_goodF2U (s := sc) ih ltac:(lia) hF (nnf_1F (nnf_1F hNb)))].
          * right; reflexivity.
          * right; reflexivity.
        + cbn [Nat.div ones app] in hd2.
          destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
          destruct (f3_111 (ih sc ltac:(lia)) hF hNb) as [[-> | ->] _]; right; reflexivity. }
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases).
    + intro; destruct h4_out as [[h3 _] | hm]; dlia.
    + intro; destruct h4_out as [[h3 _] | hm]; dlia.
    + intro; destruct h4_out as [[h3 _] | hm]; dlia.
    + intros h3 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct h4_out as [[? [U [-> hGFU]]] | hm]; [| dlia].
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head hGFU) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intro; destruct h4_out as [[h3 _] | hm]; dlia.
    + intro; destruct h4_out as [[h3 _] | hm]; dlia.
  - (* G2_c_2_2_1_0s_1_1 *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail
      (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))))) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    assert (h4_out :
      (dlt1 = 3 /\ exists U, R1 = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U) \/
      dlt1 mod 3 = 1 \/ dlt1 = 12 \/ dlt1 = 15).
    { inverts h1' as hd1 hremd1 hd2.
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        destruct (bigF_3_0s_inv hb) as [sc [hsc [dltc [-> hc]]]].
        destruct (f3_11 (ih sc ltac:(lia)) hc hNZ) as [-> | [-> | [-> _]]]; dlia.
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        destruct (bigF_3_0s_inv hb) as [sc [hsc [dltc [-> hc]]]].
        destruct (f3_11 (ih sc ltac:(lia)) hc hNZ) as [-> | [-> | [-> _]]]; try dlia.
        cbn [Nat.div ones app] in hd2.
        destruct (bigD1_1_1_inv hd2) as [sd [hsd [dltd [-> hFd]]]].
        destruct (bigF_3_inv hc) as [se [hse [dlte [Re [he hce]]]]].
        pose proof (bigF_nnf he (nnf_1F (nnf_1F hNZ))) as hNe.
        destruct hce as [[hreme [hgee [? ->]]] | [[? [? [? [? [hadd0 _]]]]] |
          [[? [? [? [? [hadd0 _]]]]] | [? [? [? [? [? [hadd0 _]]]]]]]]]; try lia.
        pose proof (proj1 (proj2 (f1 (ih se ltac:(lia)) he (nnf_1F hNZ)))) as hne4.
        assert (hq1 : 1 <= dlte / 3 - 1) by dlia.
        destruct (ones_pos_cons hq1 Re) as [W hW].
        rewrite hW in hFd.
        destruct (bigF_3_0s_inv hFd) as [sf [hsf [dltf [-> hFf]]]].
        assert (hNW : NoNonlast0F W)
          by (pose proof (noNonlast0F_ones_append (dlte / 3 - 1) hNe) as htmp;
              rewrite hW in htmp; exact (noNonlast0F_tail htmp)).
        destruct (f3_111 (ih sf ltac:(lia)) hFf hNW) as [[-> | ->] _];
          [right; right; left; reflexivity | right; right; right; reflexivity].
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        pose proof (bigF_nnf hb (nnf_3F (nnf_0T (nnf_1F (nnf_1F hNZ))))) as hNb.
        destruct (bigF_3_0s_inv hb) as [sc [hsc [dltc [-> hc]]]].
        destruct (f3_11 (ih sc ltac:(lia)) hc hNZ) as [-> | [-> | [-> _]]]; [dlia | |].
        + cbn [Nat.div ones app] in hd2.
          destruct (bigD1_1_1_inv hd2) as [sd [hsd [dltd [-> hFd]]]].
          destruct (f3_11 (ih sd ltac:(lia)) hFd hNb) as [-> | [-> | [-> _]]].
          * left; split; [reflexivity | exact (bigF_3_zero_goodF2U (s := sd) ih ltac:(lia) hFd (nnf_1F (nnf_1F hNb)))].
          * right; left; reflexivity.
          * right; left; reflexivity.
        + cbn [Nat.div ones app] in hd2.
          destruct (bigD1_1_1_inv hd2) as [sd [hsd [dltd [-> hFd]]]].
          destruct (f3_111 (ih sd ltac:(lia)) hFd hNb) as [[-> | ->] _]; right; left; reflexivity. }
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases).
    + intro; destruct h4_out as [[h3 _] | [hm | [h12 | h15]]]; dlia.
    + intro; destruct h4_out as [[h3 _] | [hm | [h12 | h15]]]; dlia.
    + intro; destruct h4_out as [[h3 _] | [hm | [h12 | h15]]]; dlia.
    + intros h3 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct h4_out as [[? [U [-> hGFU]]] | [hm | [h12 | h15]]]; try dlia.
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head hGFU) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intro; destruct h4_out as [[h3 _] | [hm | [h12 | h15]]]; dlia.
    + intro; destruct h4_out as [[h3 _] | [hm | [h12 | h15]]]; dlia.
  - (* G2_c_2_2_1_1_gf *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN)))) as hNZ.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    assert (h4_out :
      (dlt1 = 0 /\ Safe0s R1) \/
      (dlt1 = 3 /\ exists U, R1 = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U) \/
      (dlt1 = 5 /\ Head0s111 R1) \/
      (dlt1 = 6 /\ (Head0s11 R1 \/ Good1Safe R1)) \/
      (dlt1 = 9 /\ Strong2 R1) \/
      dlt1 = 8 \/ dlt1 mod 3 = 1 \/ 11 <= dlt1).
    { pose proof (nnf_1F hNZ) as hN1Z.
      inverts h1' as hd1 hremd1 hd2.
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        pose proof (nnf_3F hN1Z) as hN31Z.
        pose proof (f3_ne24 (ih sb ltac:(lia)) hb hN1Z) as hne24.
        destruct (Nat.eq_dec dltb 5) as [-> | h5b].
        + destruct (f3_5_0111 (ih sb ltac:(lia)) hb hN1Z) as [U ->].
          cbn [Nat.div ones app].
          left; split; [reflexivity | exists ((0, true) :: (1, false) :: (1, false) :: (1, false) :: U);
            split; [reflexivity | right; right; right; left; exists U; reflexivity]].
        + destruct (Nat.eq_dec dltb 8) as [-> | h8b].
          * destruct (f_258 (ih sb ltac:(lia)) hb hN31Z (or_intror (or_intror eq_refl))) as [U ->].
            cbn [Nat.div ones app].
            left; split; [reflexivity | exists ((1, false) :: (0, true) :: (1, false) :: (1, false) :: U);
              split; [reflexivity | right; right; left; eexists; split; [reflexivity | right; exists U; reflexivity]]].
          * destruct (Nat.eq_dec dltb 11) as [-> | h11b].
            -- cbn [Nat.div ones app].
               destruct (f_11 (ih sb ltac:(lia)) hb hN31Z) as [hH | hS].
               ++ left; split; [reflexivity | exists ((1, false) :: (1, false) :: Rd1);
                    split; [reflexivity | right; left; exists Rd1; exact (conj eq_refl (or_intror hH))]].
               ++ left; split; [reflexivity | exists ((1, false) :: (1, false) :: Rd1);
                    split; [reflexivity | right; left; exists Rd1; exact (conj eq_refl (or_introl (proj1 hS)))]].
            -- assert (hq5 : (dltb + 2) / 3 = S (S (S (S (S ((dltb + 2) / 3 - 5)))))) by dlia.
               rewrite hq5; cbn [ones app].
               left; split; [reflexivity | exists ((1, false) :: (1, false) :: (1, false) :: ones ((dltb + 2) / 3 - 5) ++ Rd1);
                 split; [reflexivity | left; exists (ones ((dltb + 2) / 3 - 5) ++ Rd1); reflexivity]].
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        pose proof (nnf_3F hN1Z) as hN31Z.
        pose proof (bigF_nnf hb hN31Z) as hNb.
        destruct (Nat.eq_dec dltb 0) as [-> | h0b].
        + cbn [Nat.div ones app] in hd2.
          destruct (bigF_3_inv hb) as [se [hse [dlte [Re [he hce]]]]].
          pose proof (bigF_nnf he hN1Z) as hNe.
          destruct hce as [[hreme [hgee [? ->]]] | [[? [? [? [? [hadd0 _]]]]] |
            [[? [? [? [? [hadd0 _]]]]] | [? [? [? [? [? [hadd0 _]]]]]]]]]; try lia.
          pose proof (proj1 (proj2 (f1 (ih se ltac:(lia)) he hNZ))) as hne4.
          assert (hq1 : 1 <= dlte / 3 - 1) by dlia.
          destruct (ones_pos_cons hq1 Re) as [W hW].
          rewrite hW in hd2.
          destruct (bigD1_oneF_inv hd2) as [sc [hsc [dltc [-> hF]]]].
          cbn [bumpR] in hF.
          assert (hNW : NoNonlast0F W)
            by (pose proof (noNonlast0F_ones_append (dlte / 3 - 1) hNe) as htmp;
                rewrite hW in htmp; exact (noNonlast0F_tail htmp)).
          destruct (f2s_111 (ih sc ltac:(lia)) hF hNW) as [-> hG1].
          right; right; right; left; exact (conj eq_refl (or_intror hG1)).
        + destruct (Nat.eq_dec dltb 3) as [-> | h3b].
          * destruct (f3_36 (ih sb ltac:(lia)) hb hN1Z (or_introl eq_refl)) as [U ->].
            pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb))) as hNU.
            cbn [Nat.div ones app] in hd2.
            destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
            destruct (bigF_3_0s_inv hF) as [s4 [hs4 [dlt4 [-> hF4]]]].
            destruct (f3_11 (ih s4 ltac:(lia)) hF4 hNU) as [-> | [-> | [-> _]]];
              [| right; right; right; right; right; right; right; lia
               | right; right; right; right; right; right; right; lia].
            destruct (bigF_3_inv hF4) as [se [hse [dlte [Re [he hce]]]]].
            destruct hce as [[hreme [hgee [? ->]]] | [[? [? [? [? [hadd0 _]]]]] |
              [[? [? [? [? [hadd0 _]]]]] | [? [? [? [? [? [hadd0 _]]]]]]]]]; try lia.
            pose proof (proj1 (proj2 (f1 (ih se ltac:(lia)) he (nnf_1F hNU)))) as hne4.
            assert (hq1 : 1 <= dlte / 3 - 1) by dlia.
            destruct (ones_pos_cons hq1 Re) as [W hW].
            rewrite hW.
            right; right; left; split; [reflexivity | exists W; reflexivity].
          * destruct (Nat.eq_dec dltb 6) as [-> | h6b]; [contradiction (f3_1_ne6 (ih sb ltac:(lia)) hb hNZ) |].
            destruct (Nat.eq_dec dltb 9) as [-> | h9b].
            -- cbn [Nat.div ones app] in hd2.
               destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
               destruct (f3_9 (ih sb ltac:(lia)) hb hN1Z) as [[U ->] | hS].
               ++ destruct (bigF_det hF (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->].
                  right; right; right; right; left; exact (conj eq_refl (strong2_of_2_1_1 ((1, false) :: U))).
               ++ destruct (good2_f311 (ih sc ltac:(lia)) (proj1 hS) hF hNb) as [-> hS'].
                  right; right; right; right; left; exact (conj eq_refl hS').
            -- destruct (Nat.eq_dec dltb 12) as [-> | h12b].
               ++ assert (hHead : Z = [(0, false)] \/ (exists W, Z = (0, true) :: W) \/
                    (exists W, Z = (1, false) :: W) \/ (exists W, Z = (1, true) :: W) \/
                    (exists W, Z = (2, false) :: W)).
                  { destruct hGF as [[W ->] | [[W ->] | [[W ->] | [W ->]]]].
                    - right; right; left; exists W; reflexivity.
                    - right; right; right; left; exists W; reflexivity.
                    - right; right; right; right; exists W; reflexivity.
                    - right; left; exists ((1, false) :: (1, false) :: W); reflexivity. }
                  cbn [Nat.div ones app] in hd2.
                  destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
                  destruct (bigF_3_1_12_of_validHead (s := sb) ih ltac:(lia) hb hNZ hHead) as [[U ->] | hS].
                  ** destruct (bigF_det hF (bigF_3_1_1_1_0s_1_1_exists U)) as [-> ->].
                     right; right; right; right; left; split; [reflexivity |].
                     apply strong2_of_2_0s; right; right; right; left; exists ((1, false) :: (1, false) :: U); reflexivity.
                  ** destruct (good2_f3111 (ih sc ltac:(lia)) (proj1 hS) hF hNb) as [-> [? hSf]].
                     right; right; right; right; left; exact (conj eq_refl (hSf hS)).
               ++ assert (hq6 : S ((dltb + 2) / 3) = S (S (S (S (S (S ((dltb + 2) / 3 - 5))))))) by dlia.
                  rewrite hq6 in hd2.
                  destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
                  cbn [ones app] in hF.
                  assert (hGZ : GoodZero111Head (ones ((dltb + 2) / 3 - 5) ++ Rd1)).
                  { destruct ((dltb + 2) / 3 - 5) as [| k] eqn:hq.
                    - cbn [ones app].
                      destruct (dec_head_0s Rd1) as [[W hW] | hno0s].
                      + right; exact (f_pos_0s (ih sb ltac:(lia)) hb hN31Z ltac:(dlia) hW).
                      + left; exact hno0s.
                    - left; intros ? hEq; discriminate hEq. }
                  destruct (f3_1111 (ih sc ltac:(lia)) hF (noNonlast0F_ones_append _ hNb)) as [-> [? hSf]].
                  right; right; right; right; left; exact (conj eq_refl (hSf hGZ)).
      - match type of hd1 with BigD1 _ _ _ ?R => rename R into Rd1 end; destruct (bigD1_oneF_inv hd1) as [sb [hsb [dltb [-> hb]]]].
        cbn [bumpR] in hb.
        pose proof (nnf_3F hN1Z) as hN31Z.
        pose proof (bigF_nnf hb hN31Z) as hNb.
        pose proof (f3_ne24 (ih sb ltac:(lia)) hb hN1Z) as hne24.
        pose proof (proj1 (proj1 (bigFD_bounds _) _ _ _ hb)) as hne1b.
        destruct (Nat.eq_dec dltb 7) as [-> | h7b].
        + cbn [Nat.div ones app] in hd2.
          destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
          pose proof (f3_ne24 (ih sc ltac:(lia)) hF (nnf_1F hNb)) as hne24c.
          destruct (Nat.eq_dec dltc 0) as [-> | h0c].
          * right; left; split; [reflexivity | exact (bigF_3_zero_goodF2U (s := sc) ih ltac:(lia) hF (nnf_1F hNb))].
          * destruct (Nat.eq_dec dltc 3) as [-> | h3c].
            -- right; right; right; left; split; [reflexivity | left; exact (f3_36 (ih sc ltac:(lia)) hF (nnf_1F hNb) (or_introl eq_refl))].
            -- destruct (Nat.eq_dec dltc 6) as [-> | h6c]; [contradiction (f3_1_ne6 (ih sc ltac:(lia)) hF hNb) |].
               destruct (Nat.eq_dec dltc 5) as [-> | h5c]; [right; right; right; right; right; left; reflexivity |].
               destruct (Nat.eq_dec dltc 1) as [-> | h1c]; [contradiction (bigF_ne_one hF) |].
               destruct (Nat.eq_dec (dltc mod 3) 1) as [hm1 | hm1].
               ++ right; right; right; right; right; right; left; dlia.
               ++ right; right; right; right; right; right; right; dlia.
        + destruct (Nat.eq_dec dltb 10) as [-> | h10b].
          * cbn [Nat.div ones app] in hd2.
            destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
            destruct (f3_11 (ih sc ltac:(lia)) hF hNb) as [-> | [-> | [-> _]]].
            -- right; left; split; [reflexivity | exact (bigF_3_zero_goodF2U (s := sc) ih ltac:(lia) hF (nnf_1F (nnf_1F hNb)))].
            -- right; right; right; right; right; right; left; reflexivity.
            -- right; right; right; right; right; right; left; reflexivity.
          * assert (hq5 : (dltb + 2) / 3 = S (S (S (S (S ((dltb + 2) / 3 - 5)))))) by dlia.
            rewrite hq5 in hd2.
            destruct (bigD1_1_1_inv hd2) as [sc [hsc [dltc [-> hF]]]].
            cbn [ones app] in hF.
            destruct (f3_111 (ih sc ltac:(lia)) hF (noNonlast0F_ones_append _ hNb)) as [[-> | ->] _];
              right; right; right; right; right; right; left; reflexivity. }
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases).
    + intro; destruct h4_out as [[? _] | [[? _] | [[? _] | [[? _] | [[? _] | [? | [? | ?]]]]]]]; dlia.
    + intro h5; subst dlt1.
      destruct h4_out as [[? _] | [[? _] | [[? [W ->]] | [[? _] | [[? _] | [? | [? | ?]]]]]]]; try dlia.
      destruct hcases as [[? _] | [[? _] | [[? [? [s2 [hs2 [dlt3 [-> hF2]]]]]] |
        [[? _] | [[? _] | [? _]]]]]]; try dlia.
      cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (bigF_3_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
      destruct (f3_111 (ih s4 ltac:(lia)) hF4
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))))) as [[-> | ->] _];
        split_and; dlia.
    + intros h0 s2 dlt2 hs2 -> hD2; subst dlt1.
      destruct h4_out as [[? [U [-> hSU]]] | [[? _] | [[? _] | [[? _] | [[? _] | [? | [? | ?]]]]]]]; try dlia.
      destruct (bigD1_zeroT_inv hD2) as [-> ->].
      cbn [bumpR]; split_and; try dlia. intro; exact (G4_of_safeU hSU).
    + intros h3 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct h4_out as [[? _] | [[? [U [-> hGFU]]] | [[? _] | [[? _] | [[? _] | [? | [? | ?]]]]]]]; try dlia.
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head hGFU) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h6 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct h4_out as [[? _] | [[? _] | [[? _] | [[? [[U ->] | hG1]] | [[? _] | [? | [? | ?]]]]]]]; try dlia.
      * exact (good2_f_from_6_0s11 ih hF2 hs2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
      * destruct (bigF_3_good1Safe ih hG1 hF2 hs2 hN1) as [[-> hO'] | [hm2 hge]].
        -- destruct hO' as [hG2 | [W ->]].
           ++ split_and; try dlia. intro; left; exact hG2.
           ++ split_and; try dlia. intro; right; right; exists W; reflexivity.
        -- split_and; dlia.
    + intros h9 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct h4_out as [[? _] | [[? _] | [[? _] | [[? _] | [[? hS] | [? | [? | ?]]]]]]]; try dlia.
      exact (good2_f_from_9_hs ih (or_intror hS) hF2 hs2 hN1).
  - (* G2_step_21 *)
    destruct (bigF_2_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
    pose proof (noNonlast0F_tail (noNonlast0F_tail hN)) as hNG'.
    pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR (noNonlast0F_tail hN))) as hN_b2.
    pose proof (bigF_nnf h1 hN_b2) as hN1.
    pose proof h1 as h1'; cbn [bumpR] in h1'.
    destruct (bigF_3_inv h1') as [sa [hsa [dlta [Ra [ha hca]]]]].
    pose proof (bigF_nnf ha hNG') as hNa.
    pose proof (good2_f (ih sa ltac:(lia)) hG' ha hNG') as hfg.
    eapply (good2_f_dispatch_high ih (Nat.le_refl m) hs1 h1 hN_b2 hcases
      (proj1 (f3_ne24 (ih s1 hs1) h1' hNG'))).
    + intro h5.
      destruct hca as [[? [? [h0 _]]] | [[hrem2 _] |
        [[-> [sb [hsb [dltb [haddb hFb]]]]] | [hrem0 [hge3 [sb [hsb [dltb [haddb hFb]]]]]]]]]; try lia.
      * assert (dltb = 2) by lia; subst dltb.
        exfalso.
        destruct (good2_head_cases hG') as [[Y ->] | [Y ->]].
        -- inverts ha; cbn [bumpR] in hFb.
           exact (proj1 (f2s (ih sb ltac:(lia)) hFb (noNonlast0F_bumpR (noNonlast0F_tail hNG'))) eq_refl).
        -- destruct (bigF_ge2_zero_head ha) as [Z ->]; cbn [bumpR] in hFb.
           destruct (f2s_1 (ih sb ltac:(lia)) hFb (noNonlast0F_tail (noNonlast0F_tail hNa)))
             as [? | [? | [? | ?]]]; lia.
      * contradiction (proj1 (f3_ne24 (ih sb ltac:(lia)) hFb (noNonlast0F_ones_append _ hNa)) ltac:(lia)).
    + intros h0 s2 dlt2 hs2 -> hD2; subst dlt1.
      destruct hca as [[hrema [hgea [? ->]]] | [[hrem2 _] |
        [[? [? [? [? [hadd0 _]]]]] | [? [? [? [? [? [hadd0 _]]]]]]]]]; try lia.
      destruct (bigD1_zeroT_inv hD2) as [-> ->].
      destruct (Nat.eq_dec dlta 4) as [-> | h4a].
      * cbn [Nat.div Nat.sub ones app bumpR]; split_and; try dlia.
        intro; exact (G4_step_21 (proj1 (proj2 hfg) eq_refl)).
      * destruct (Nat.eq_dec dlta 7) as [-> | h7a].
        -- assert (hSU : SafeU ((1, false) :: Ra)).
           { destruct (proj1 (proj2 (proj2 (proj2 hfg))) eq_refl) as [hS | hH].
             - right; right; left; exists Ra; exact (conj eq_refl (or_introl (proj1 hS))).
             - right; right; left; exists Ra; exact (conj eq_refl (or_intror hH)). }
           cbn [Nat.div Nat.sub ones app bumpR]; split_and; try dlia.
           intro; exact (G4_of_safeU hSU).
        -- destruct (Nat.eq_dec dlta 10) as [-> | h10a].
           ++ cbn [Nat.div Nat.sub ones app bumpR].
              destruct (proj2 (proj2 (proj2 (proj2 hfg))) eq_refl) as [hG2 | [hH | [W ->]]].
              ** split_and; try dlia.
                 intro; apply G4_of_safeU; right; left; exists Ra; exact (conj eq_refl (or_introl hG2)).
              ** split_and; try dlia.
                 intro; apply G4_of_safeU; right; left; exists Ra; exact (conj eq_refl (or_intror hH)).
              ** split_and; try dlia. intro; exact (G4_of_1_1_1s W).
           ++ assert (hq3 : dlta / 3 - 1 = S (S (S (dlta / 3 - 4)))) by dlia.
              rewrite hq3; cbn [ones app bumpR].
              split_and; try dlia.
              intro; apply G4_of_safeU; left; exists (ones (dlta / 3 - 4) ++ Ra); reflexivity.
    + intros h3 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct (f3_3_non0s (ih s1 hs1) h1' hNG' (good2_ne_zeroT hG')) as [U [-> hSU]].
      exact (good2_f_from_3_0s11 ih (goodF2U_to_goodZero111Head (safeU_to_goodF2U hSU)) hF2 hs2
        (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h6 s2 dlt3 hs2 -> hF2; subst dlt1.
      destruct (f3_36 (ih s1 hs1) h1' hNG' (or_intror eq_refl)) as [U ->].
      exact (good2_f_from_6_0s11 ih hF2 hs2 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1)))).
    + intros h9 s2 dlt3 hs2 -> hF2; subst dlt1.
      exact (good2_f_from_9_hs ih (f3_9 (ih s1 hs1) h1' hNG') hF2 hs2 hN1).
Qed.

(* ========================================================================== *)
(* Remaining Group 5 Step Lemmas, invAt_all, StrongWall, and nonhalt          *)
(* ========================================================================== *)

Lemma step_good2_f1 {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF m ((1, false) :: G) dlt R_fin) (hN : NoNonlast0F G) :
  dlt = 0 \/ (dlt = 9 /\ Good2 R_fin) \/ (dlt = 12 /\ Strong2 R_fin) \/ (dlt mod 3 = 0 /\ 15 <= dlt).
Proof.
  destruct (bigF_1_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (bigF_nnf h1 hN) as hN1.
  pose proof (good2_f (ih s1 hs1) hG h1 hN) as hfg.
  destruct hcases as [[? [-> _]] |
    [[hrem1 [hge4 [s2 [hs2 [dlt3 [-> hF2]]]]]] |
    [[-> _] |
     [hrem2 _]]]].
  - left; reflexivity.
  - destruct (Nat.eq_dec dlt1 4) as [-> | h4ne].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (bigF_3_good4Out ih (proj1 (proj2 hfg) eq_refl) hF2 hs2 hN1) as [[-> hG2] | [hm hge13]].
      * right; left; exact (conj eq_refl hG2).
      * right; right; right; dlia.
    + destruct (Nat.eq_dec dlt1 7) as [-> | h7ne].
      * cbn [Nat.div Nat.sub ones app] in hF2.
        destruct (proj1 (proj2 (proj2 (proj2 hfg))) eq_refl) as [hS | [U ->]].
        -- destruct (good2_f31 (ih s2 hs2) (proj1 hS) hF2 hN1) as [h710 hSf].
           pose proof (hSf hS) as hS'.
           destruct h710 as [-> | [-> _]].
           ++ right; left; exact (conj eq_refl (proj1 hS')).
           ++ right; right; left; exact (conj eq_refl hS').
        -- destruct (bigF_3_1_0s_inv hF2) as [s4 [hs4 [dlt4 [-> hF4]]]].
           destruct (f2s_111 (ih s4 ltac:(lia)) hF4 (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hN1))))
             as [-> hG1].
           right; left; exact (conj eq_refl (good1Safe_to_good2 hG1)).
      * destruct (Nat.eq_dec dlt1 10) as [-> | h10ne].
        -- cbn [Nat.div Nat.sub ones app] in hF2.
           destruct (proj2 (proj2 (proj2 (proj2 hfg))) eq_refl) as [hG2 | [[U ->] | [W ->]]].
           ++ destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS'].
              right; left; exact (conj eq_refl (proj1 hS')).
           ++ destruct (bigF_det hF2 (bigF_3_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->].
              right; left; exact (conj eq_refl (good2_of_2_1_1 ((1, false) :: U))).
           ++ destruct (bigF_det hF2 (bigF_3_1_1_1s_exists W)) as [-> ->].
              right; left; exact (conj eq_refl (good2_of_2_0s (bumpR W))).
        -- assert (hq3 : dlt1 / 3 - 1 = S (S (S (dlt1 / 3 - 4)))) by dlia.
           rewrite hq3 in hF2; cbn [ones app] in hF2.
           destruct (f3_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [[-> | ->] [hG2' hS10]].
           ++ right; left; exact (conj eq_refl hG2').
           ++ right; right; left; exact (conj eq_refl (hS10 eq_refl)).
  - contradiction (proj1 hfg eq_refl).
  - contradiction (proj1 hfg hrem2).
Qed.

Lemma step_good2_f11 {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF m ((1, false) :: (1, false) :: G) dlt R_fin) (hN : NoNonlast0F G) :
  dlt = 0.
Proof.
  destruct (bigF_1_inv h) as [s1 [hs1 [dlt1 [R1 [h1 hcases]]]]].
  pose proof (good2_f1 (ih s1 hs1) hG h1 hN) as hf1.
  destruct hcases as [[? [-> _]] | [[hrem1 _] | [[-> _] | [hrem2 _]]]].
  - reflexivity.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
Qed.

(* Only the second segment matters when a zero return follows a leading 2. *)
Definition Good2Tail Y :=
  match Y with
  | (0,false)::X => X = []
  | (0,true)::_ | (1,_)::_ | (2,false)::_ => True
  | _ => False
  end.

Lemma good2_tail_shape Y : Good2 ((2,false)::Y) -> Good2Tail Y.
Proof.
  intro h. inverts h as h1; try (exact I || reflexivity).
  destruct h1 as [h | [[W h] | [h | [h | [[W h] | [[W h] | [[W h] | [[W [h _]] | [W h]]]]]]]]];
    try discriminate. inversion h. exact I.
Qed.

Lemma bump_good1_zero G Y : Good1 G -> G = (1,true)::Y ->
  Strong2 ((2,false)::bumpR Y).
Proof.
  intros h he. destruct h as [-> | [[W ->] | [-> | [-> | [[W ->] | [[W ->] | [[W ->] | [[W [-> hv]] | [W ->]]]]]]]]];
    try discriminate; inversion he; subst; cbn [bumpR];
    eauto using strong2_of_2_1s_0, strong2_of_2_1s_0s, strong2_of_2_1s_1, strong2_of_2_1s_1_0,
      strong2_of_2_1s_1_0s, strong2_of_2_1s_1_1, strong2_of_2_2_1_0s_1_1, strong2_of_2_2_1_1_gf.
Qed.

Lemma bigF_two_zero_result {s Y R} : BigF s ((2,false)::Y) 0 R ->
  exists t n Z, t < s /\ BigF t (bumpR (bumpR Y)) n Z /\
    4 <= n /\ n mod 3 = 1 /\ R = (0,true)::ones (n/3) ++ Z.
Proof.
  intro hf. destruct (bigF_2_inv hf) as [t [ht [n [Z [h cases]]]]].
  destruct cases as [[hm [hle [_ ->]]] | [[? [? [? [? [ha _]]]]] |
    [[? [? [? [? [? [ha _]]]]]] | [[? [? [? [? [ha _]]]]] |
    [[? [? [? [? [ha _]]]]] | [? [? [? [? [? [ha _]]]]]]]]]]]; try lia.
  exists t, n, Z. auto.
Qed.

Lemma good2_inner_four {m t Y Z} (ih : InvLt m) :
  t < m -> Strong2 ((2,false)::Y) -> NoNonlast0F Y -> BigF t (bumpR (bumpR Y)) 4 Z ->
  Strong2 ((2,false)::(1,false)::Z).
Proof.
  intros ht hstrong hn hf. pose proof (good2_tail_shape _ (proj1 hstrong)) as hshape.
  destruct Y as [|[[|[|[|d]]] c] Y]; try contradiction hshape; destruct c; try contradiction hshape.
  - cbn [bumpR] in hf.
    pose proof (bigF_2s_4_good2_of_strongHead ih (proj2 hstrong Y eq_refl) hf ht (noNonlast0F_tail hn)) as hG.
    split; [exact hG | intros U h; discriminate h].
  - change (Y = []) in hshape. subst Y.
    destruct bigF_2_nil_exists as [t' hf'].
    destruct (bigF_det hf hf') as [_ ->].
    exact (strong2_of_2_1_1 []).
  - cbn [bumpR] in hf.
    destruct (bigF_3s_inv hf) as [u [hu [i [e h]]]].
    assert (i=1) by lia. subst i. contradiction (bigF_ne_one h).
  - exact (False_ind _ (proj2 (f3_ne24 (ih _ ht) hf (noNonlast0F_tail hn)) eq_refl)).
  - exact (False_ind _ (bigF_4_ne4 ih hf ht (noNonlast0F_tail hn))).
Qed.

Lemma good2_zero_suffix {m s G R} (ih : InvLt m) :
  Good2 G -> BigF s G 0 R -> s < m -> NoNonlast0F G ->
  exists U, R = (0,true)::U /\ (Strong2 G -> Strong2 ((2,false)::U)).
Proof.
  intros hg hf hs hn.
  destruct (good2_head_cases hg) as [[Y ->] | [Y ->]].
  - inverts hf. exists (bumpR Y). split; [reflexivity | intros _].
    destruct (good2_good1_or_ge2 hg) as [h | [X h]]; [| discriminate h].
    exact (bump_good1_zero _ _ h eq_refl).
  - destruct (bigF_two_zero_result hf) as [t [n [Z [ht [h [hle [hm ->]]]]]]].
    exists (ones (n/3) ++ Z). split; [reflexivity | intros hstrong].
    destruct (Nat.eq_dec n 4) as [-> | hne].
    + exact (good2_inner_four (t := t) ih ltac:(lia) hstrong (noNonlast0F_tail hn) h).
    + assert (hq : n/3 = S (S (n/3-2))) by dlia.
      rewrite hq. exact (strong2_of_2_1_1 (ones (n/3-2) ++ Z)).
Qed.
Lemma step_good2_f31 {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF m ((3, false) :: (1, false) :: G) dlt R_fin) (hN : NoNonlast0F G) :
  (dlt = 7 \/ (dlt = 10 /\ Good2 R_fin)) /\ (Strong2 G -> Strong2 R_fin).
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (nnf_1F hN) as hN1G.
  pose proof (bigF_nnf h1 hN1G) as hN1.
  pose proof (good2_f1 (ih s1 hs1) hG h1 hN) as hf1.
  destruct hcases as [[hrem1 _] |
    [[hrem2 _] |
    [[-> [s2 [hs2 [dlt3 [-> hF2]]]]] |
     [hrem0 [hge3 [s2 [hs2 [dlt3 [-> hF2]]]]]]]]].
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - destruct hf1 as [h0 | [[h9 _] | [[h12 _] | [hm ?]]]]; dlia.
  - inverts h1 as hg hremg hg2; try lia.
    + match type of hg with
      | BigF ?sg _ ?dltg ?Rg =>
        pose proof (bigF_nnf hg hN) as hNg;
        destruct (Nat.eq_dec dltg 0) as [-> | h0g];
        [ cbn [Nat.div ones app] in hF2;
          destruct (good2_zero_suffix (s := sg) ih hG hg ltac:(lia) hN) as [U [-> hstrong]];
          cbn [bumpR] in hF2;
          destruct (bigF_det hF2 (bigF_2s_0s_full_exists U)) as [-> ->];
          split; [left; reflexivity | exact hstrong]
        | destruct (Nat.eq_dec dltg 3) as [-> | h3g];
          [ assert (hRg : exists U, Rg = (0, true) :: (1, false) :: (1, false) :: U /\ GoodF2U U) by
              (destruct (good2_head_cases hG) as [[Y ->] | [Y ->]];
               [ inverts hg; lia
               | exact (bigF_2_3_goodF2U ih hg ltac:(lia) (noNonlast0F_tail hN)) ]);
            destruct hRg as [U [-> hGFU]];
            cbn [Nat.div ones app bumpR] in hF2;
            destruct (bigF_det hF2 (bigF_2s_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->];
            split; [left; reflexivity | intro; exact (good1Safe_to_strong2 (good1Safe_of_1s_1_1_1 hGFU))]
          | destruct (Nat.eq_dec dltg 6) as [-> | h6g];
            [ destruct (proj1 (proj2 (proj2 (good2_f (ih sg ltac:(lia)) hG hg hN))) eq_refl) as [U ->];
              cbn [Nat.div ones app bumpR] in hF2;
              destruct (bigF_det hF2 (bigF_2s_1_1_0s_exists ((1, false) :: (1, false) :: U))) as [-> ->];
              split; [left; reflexivity | intro; exact (good1Safe_to_strong2 (good1Safe_of_1s_0s_1_1 ((1, false) :: U)))]
            | assert (hq3 : (1 + dltg) / 3 = S (S (S ((1 + dltg) / 3 - 3)))) by dlia;
              rewrite hq3 in hF2; cbn [ones app bumpR] in hF2;
              destruct (f2s_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hNg)) as [-> hG1];
              split; [left; reflexivity | intro; exact (good1Safe_to_strong2 hG1)] ] ] ]
      end.
    + pose proof (bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))); lia.
  - destruct hf1 as [h0 | [[-> hG2] | [[-> hS2] | [? hge15]]]]; [lia | | |].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (good2_f311 (ih s2 hs2) hG2 hF2 hN1) as [-> hS'].
      split; [right; exact (conj eq_refl (proj1 hS')) | intro; exact hS'].
    + cbn [Nat.div Nat.sub ones app] in hF2.
      destruct (good2_f3111 (ih s2 hs2) (proj1 hS2) hF2 hN1) as [-> [hG' hSf]].
      pose proof (hSf hS2) as hS'.
      split; [right; exact (conj eq_refl hG') | intro; exact hS'].
    + assert (hq4 : dlt0 / 3 - 1 = S (S (S (S (dlt0 / 3 - 5))))) by dlia.
      rewrite hq4 in hF2; cbn [ones app] in hF2.
      assert (hGZ : GoodZero111Head (ones (dlt0 / 3 - 5) ++ R1)).
      { destruct (dlt0 / 3 - 5) as [| k] eqn:hq.
        - cbn [ones app].
          destruct (dec_head_0s R1) as [[W hW] | hno0s].
          + right; exact (f_pos_0s (ih s1 hs1) h1 hN1G ltac:(lia) hW).
          + left; exact hno0s.
        - left; intros ? hEq; discriminate hEq. }
      destruct (f3_1111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1)) as [-> [hG' hSf]].
      split; [right; exact (conj eq_refl hG') | intro; exact (hSf hGZ)].
Qed.

Lemma step_good2_f311 {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF m ((3, false) :: (1, false) :: (1, false) :: G) dlt R_fin) (hN : NoNonlast0F G) :
  dlt = 7 /\ Strong2 R_fin.
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  pose proof (good2_f11 (ih s1 hs1) hG h1 hN) as h0; subst dlt0.
  destruct hcases as [[hrem _] | [[hrem _] | [[? [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [hge _]]]]]; try dlia.
  inverts h1 as h1f hrem1f h12; try lia.
  - match type of h1f with
    | BigF ?s1f _ ?dlt1f ?R1f =>
      pose proof (bigF_nnf h1f (nnf_1F hN)) as hN1f;
      destruct (good2_f1 (ih s1f ltac:(lia)) hG h1f hN) as [-> | [[-> _] | [[-> _] | [? hge15]]]];
      [ cbn [Nat.div ones app] in hF2;
        inverts h1f as hg hremg hg2; try lia;
        [ match type of hg with
          | BigF ?sg _ ?dltg ?Rg =>
            destruct (Nat.eq_dec dltg 0) as [-> | h0g];
            [ cbn [Nat.div ones app] in hF2;
              destruct (good2_good1_or_ge2 hG) as [h1g | [Y ->]];
              [ destruct h1g as [-> | [[Z ->] | [-> | [-> | [[Z ->] | [[Z ->] | [[Z ->] | [[Z [-> _]] | [Z ->]]]]]]]]];
                [ inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists [(0, true); (1, true); (0, false)])) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; left; exists [(0, false)]; reflexivity]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, true) :: (0, true) :: Z))) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; left; exists ((0, true) :: Z); reflexivity]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists [(0, true); (1, true); (1, false)])) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; left; exists [(1, false)]; reflexivity]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists [(0, true); (1, true); (1, false); (0, false)])) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; left; exists [(1, false); (0, false)]; reflexivity]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, true) :: (1, false) :: (0, true) :: Z))) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; left; exists ((1, false) :: (0, true) :: Z); reflexivity]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, true) :: (1, false) :: (1, false) :: Z))) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; left; exists ((1, false) :: (1, false) :: Z); reflexivity]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists
                    ((0, true) :: (2, false) :: (1, false) :: (0, true) :: (1, false) :: (1, false) :: Z))) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; right;
                    exact (good2_of_2_1_0s ((1, false) :: (1, false) :: Z))]
                | inverts hg; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists
                    ((0, true) :: (2, false) :: (1, false) :: (1, false) :: Z))) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; right; right; exact (good2_of_2_1_1 Z)]
                | destruct (bigF_ge2_zero_head hg) as [Z' ->]; cbn [bumpR] in hF2;
                  destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, false) :: Z'))) as [-> ->];
                  split; [reflexivity | apply strong2_of_2_0s; right; right; right; left; exists Z'; reflexivity] ]
              | destruct (bigF_ge2_zero_head hg) as [Z' ->]; cbn [bumpR] in hF2;
                destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, false) :: Z'))) as [-> ->];
                split; [reflexivity | apply strong2_of_2_0s; right; right; right; left; exists Z'; reflexivity] ]
            | destruct (Nat.eq_dec dltg 3) as [-> | h3g];
              [ assert (hRg : Head0s11 Rg) by
                  (destruct (good2_head_cases hG) as [[Y ->] | [Y ->]];
                   [ inverts hg; lia
                   | exact (bigF_2_3_head0s11 ih hg ltac:(lia) (noNonlast0F_tail hN)) ]);
                destruct hRg as [U ->]; cbn [Nat.div ones app bumpR] in hF2;
                destruct (bigF_det hF2 (bigF_2s_0s_full_exists
                  ((1, false) :: (0, true) :: (1, false) :: (1, false) :: U))) as [-> ->];
                exact (conj eq_refl (strong2_of_2_1_0s ((1, false) :: (1, false) :: U)))
              | assert (hq2 : (1 + dltg) / 3 = S (S ((1 + dltg) / 3 - 2))) by dlia;
                rewrite hq2 in hF2; cbn [ones app bumpR] in hF2;
                destruct (bigF_det hF2 (bigF_2s_0s_full_exists
                  ((1, false) :: (1, false) :: ones ((1 + dltg) / 3 - 2) ++ Rg))) as [-> ->];
                exact (conj eq_refl (strong2_of_2_1_1 (ones ((1 + dltg) / 3 - 2) ++ Rg))) ] ]
          end
        | pose proof (bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))); lia ]
      | cbn [Nat.div ones app bumpR] in hF2;
        destruct (f2s_111 (ih s2 hs2) hF2 hN1f) as [-> hG1];
        exact (conj eq_refl (good1Safe_to_strong2 hG1))
      | cbn [Nat.div ones app bumpR] in hF2;
        destruct (f2s_111 (ih s2 hs2) hF2 (nnf_1F hN1f)) as [-> hG1];
        exact (conj eq_refl (good1Safe_to_strong2 hG1))
      | assert (hq3 : (1 + dlt1f) / 3 = S (S (S ((1 + dlt1f) / 3 - 3)))) by dlia;
        rewrite hq3 in hF2; cbn [ones app bumpR] in hF2;
        destruct (f2s_111 (ih s2 hs2) hF2 (noNonlast0F_ones_append _ hN1f)) as [-> hG1];
        exact (conj eq_refl (good1Safe_to_strong2 hG1)) ]
    end.
  - pose proof (bigD1_ge2_of_ne_nil h12 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1f))); lia.
Qed.

Lemma step_good2_f3111 {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good2 G) (h : BigF m ((3, false) :: (1, false) :: (1, false) :: (1, false) :: G) dlt R_fin)
    (hN : NoNonlast0F G) :
  dlt = 7 /\ Good2 R_fin /\ (Strong2 G -> Strong2 R_fin).
Proof.
  destruct (bigF_3_inv h) as [s1 [hs1 [dlt0 [R1 [h1 hcases]]]]].
  assert (h1_zero : dlt0 = 0 /\ exists s11, s11 < s1 /\ exists R11,
    R1 = (0, true) :: R11 /\ BigF s11 ((1, false) :: (1, false) :: G) 0 R11).
  { inverts h1 as h11 hrem11 h12.
    - match type of h11 with BigF ?s11 _ ?d11 ?R11 =>
        pose proof (good2_f11 (ih s11 ltac:(lia)) hG h11 hN) as ->;
        cbn [Nat.div ones app];
        split; [reflexivity | exists s11; split; [lia | exists R11; exact (conj eq_refl h11)]]
      end.
    - match type of h11 with BigF ?s11 _ ?d11 _ =>
        pose proof (good2_f11 (ih s11 ltac:(lia)) hG h11 hN); dlia
      end.
    - match type of h11 with BigF ?s11 _ ?d11 _ =>
        pose proof (good2_f11 (ih s11 ltac:(lia)) hG h11 hN); dlia
      end. }
  destruct h1_zero as [-> [s11 [hs11 [R11 [-> h11]]]]].
  destruct hcases as [[hrem _] | [[hrem _] | [[? [s2 [hs2 [dlt3 [-> hF2]]]]] | [? [hge _]]]]]; try dlia.
  inverts h11 as h1f hrem1f h12; try lia.
  - match type of h1f with
    | BigF ?s1f _ ?dlt1f ?R1f =>
      destruct (good2_f1 (ih s1f ltac:(lia)) hG h1f hN) as [-> | [[-> _] | [[-> _] | [? hge15]]]];
      [ cbn [Nat.div ones app] in hF2;
        inverts h1f as hg hremg hg2; try lia;
        [ match type of hg with
          | BigF ?sg _ ?dltg ?Rg =>
            destruct (Nat.eq_dec dltg 0) as [-> | h0g];
            [ destruct (good2_zero_suffix (s := sg) ih hG hg ltac:(lia) hN) as [U [-> hstrong]];
              cbn [Nat.div ones app bumpR] in hF2;
              destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0,true)::(0,true)::U))) as [-> ->];
              split; [reflexivity | split; [apply good2_of_2_0s |]];
              intro hS; apply strong2_of_2_0s; right; right; left;
              exists U; split; [reflexivity | right; exact (proj1 (hstrong hS))]
            | assert (hq1 : 1 <= (1 + dltg) / 3) by dlia;
              destruct (ones_pos_cons hq1 Rg) as [W hW];
              rewrite hW in hF2; cbn [bumpR] in hF2;
              destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((0, true) :: (1, false) :: W))) as [-> ->];
              split; [reflexivity | split; [exact (good2_of_2_0s ((1, false) :: W)) |
                intro; apply strong2_of_2_0s; right; right; right; left; exists W; reflexivity]] ]
          end
        | pose proof (bigD1_ge2_of_ne_nil hg2 (append_nonempty_of_right _ _ (bigF_out_ne_nil hg))); lia ]
      | cbn [Nat.div ones app bumpR] in hF2;
        destruct (bigF_det hF2 (bigF_2s_0s_full_exists ((1, false) :: (1, false) :: (1, false) :: R1f))) as [-> ->];
        split; [reflexivity | split; [exact (good2_of_2_1_1 ((1, false) :: R1f)) |
          intro; exact (strong2_of_2_1_1 ((1, false) :: R1f))]]
      | cbn [Nat.div ones app bumpR] in hF2;
        destruct (bigF_det hF2 (bigF_2s_0s_full_exists
          ((1, false) :: (1, false) :: (1, false) :: (1, false) :: R1f))) as [-> ->];
        split; [reflexivity | split; [exact (good2_of_2_1_1 ((1, false) :: (1, false) :: R1f)) |
          intro; exact (strong2_of_2_1_1 ((1, false) :: (1, false) :: R1f))]]
      | assert (hq3 : (1 + dlt1f) / 3 = S (S (S ((1 + dlt1f) / 3 - 3)))) by dlia;
        rewrite hq3 in hF2; cbn [ones app bumpR] in hF2;
        destruct (bigF_det hF2 (bigF_2s_0s_full_exists
          ((1, false) :: (1, false) :: (1, false) :: ones ((1 + dlt1f) / 3 - 3) ++ R1f))) as [-> ->];
        split; [reflexivity | split;
          [ exact (good2_of_2_1_1 ((1, false) :: ones ((1 + dlt1f) / 3 - 3) ++ R1f))
          | intro; exact (strong2_of_2_1_1 ((1, false) :: ones ((1 + dlt1f) / 3 - 3) ++ R1f)) ]] ]
    end.
  - pose proof (bigD1_ge2_of_ne_nil h12 (append_nonempty_of_right _ _ (bigF_out_ne_nil h1f))); lia.
Qed.

Lemma step_good1_f3121 {m : nat} (ih : InvLt m)
    {G : list Seg} {dlt : nat} {R_fin : list Seg}
    (hG : Good1 G) (h : BigF m ((3, false) :: (1, false) :: (2, false) :: (1, false) :: G) dlt R_fin)
    (hN : NoNonlast0F G) :
  (dlt = 7 \/ dlt = 10) /\ Good2 R_fin.
Proof.
  pose proof (G2_step_21 (G2_of_good1 hG)) as h21.
  pose proof (strong2_of_step_21 (G2_of_good1 hG)) as hS21.
  pose proof (nnf_2F (nnf_1F hN)) as hN21.
  destruct (step_good2_f31 ih h21 h hN21) as [h710 hSf].
  pose proof (hSf hS21) as hS'.
  destruct h710 as [-> | [-> _]].
  - exact (conj (or_introl eq_refl) (proj1 hS')).
  - exact (conj (or_intror eq_refl) (proj1 hS')).
Qed.

(* ========================================================================== *)
(* Master Strong Induction Closure: invAt_all                                 *)
(* ========================================================================== *)

Lemma invAt_all (m : nat) : InvAt m.
Proof.
  induction m as [m ih] using strong_induction.
  exact {|
    f_258 := fun _ _ _ h hN hdlt => step_f_258 ih h hN hdlt;
    f_25_goodF2U := fun _ _ _ h hN hdlt => step_f_25_goodF2U ih h hN hdlt;
    f_pos_0s := fun _ _ _ _ h hN hpos h0s => step_f_pos_0s ih h hN hpos h0s;
    f_4_head := fun _ _ h hN => step_f_4_head ih h hN;
    f_11 := fun _ _ h hN => step_f_11 ih h hN;
    f3_ne24 := fun _ _ _ h hN => step_f3_ne24 ih h hN;
    f3_36 := fun _ _ _ h hN hdlt => step_f3_36 ih h hN hdlt;
    f3_3_non0s := fun _ _ h hN hne => step_f3_3_non0s ih h hN hne;
    f3_5_0111 := fun _ _ h hN => step_f3_5_0111 ih h hN;
    f3_9 := fun _ _ h hN => step_f3_9 ih h hN;
    f3_1_ne6 := fun _ _ h hN => step_f3_1_ne6 ih h hN;
    f3_11 := fun _ _ _ h hN => step_f3_11 ih h hN;
    f3_111 := fun _ _ _ h hN => step_f3_111 ih h hN;
    f3_1111 := fun _ _ _ h hN => step_f3_1111 ih h hN;
    f1 := fun _ _ _ h hN => step_f1 ih h hN;
    f11 := fun _ _ _ h hN => step_f11 ih h hN;
    f111 := fun _ _ _ h hN => step_f111 ih h hN;
    f2s := fun _ _ _ h hN => step_f2s ih h hN;
    f2s_1 := fun _ _ _ h hN => step_f2s_1 ih h hN;
    f2s_11 := fun _ _ _ h hN => step_f2s_11 ih h hN;
    f2s_111 := fun _ _ _ h hN => step_f2s_111 ih h hN;
    good2_f := fun _ _ _ hG h hN => step_good2_f ih hG h hN;
    good2_f1 := fun _ _ _ hG h hN => step_good2_f1 ih hG h hN;
    good2_f11 := fun _ _ _ hG h hN => step_good2_f11 ih hG h hN;
    good2_f31 := fun _ _ _ hG h hN => step_good2_f31 ih hG h hN;
    good2_f311 := fun _ _ _ hG h hN => step_good2_f311 ih hG h hN;
    good2_f3111 := fun _ _ _ hG h hN => step_good2_f3111 ih hG h hN;
    good1_f3121 := fun _ _ _ hG h hN => step_good1_f3121 ih hG h hN
  |}.
Qed.

(* ========================================================================== *)
(* StrongWall Closure and Final Non-Halting Theorem                           *)
(* ========================================================================== *)

Definition StrongWall (rs : list Seg) : Prop :=
  exists tail, rs = (0, true) :: tail /\ NoNonlast0F tail /\
    ((exists G, bumpR (bumpR tail) = (3, false) :: (1, false) :: G /\ Strong2 G) \/
     (exists G, bumpR (bumpR tail) = (3, false) :: (1, false) :: (1, false) :: G /\ Good2 G)).

Lemma strongWall_step (rs : list Seg) (hW : StrongWall rs) :
  exists tail, rs = (0, true) :: tail /\
    forall s dlt R_fin, BigF s (bumpR (bumpR tail)) dlt R_fin ->
      dlt mod 3 = 1 /\ StrongWall ((0, true) :: ones (dlt / 3) ++ R_fin).
Proof.
  destruct hW as [tail [-> [hN hC]]].
  exists tail. split; [reflexivity |].
  intros s dlt R_fin hF.
  pose proof (noNonlast0F_bumpR (noNonlast0F_bumpR hN)) as hNb2.
  pose proof (bigF_nnf hF hNb2) as hNf.
  destruct hC as [[G [hEq hS]] | [G [hEq hG]]].
  - rewrite hEq in hF, hNb2.
    pose proof (noNonlast0F_tail (noNonlast0F_tail hNb2)) as hNG.
    destruct (good2_f31 (invAt_all s) (proj1 hS) hF hNG) as [h710 hSf].
    pose proof (hSf hS) as hS'.
    destruct h710 as [-> | [-> _]].
    + cbn [Nat.div ones app].
      split; [reflexivity |].
      exists ((1, false) :: (1, false) :: R_fin).
      split; [reflexivity | split; [exact (nnf_1F (nnf_1F hNf)) |]].
      left; exists R_fin; exact (conj eq_refl hS').
    + cbn [Nat.div ones app].
      split; [reflexivity |].
      exists ((1, false) :: (1, false) :: (1, false) :: R_fin).
      split; [reflexivity | split; [exact (nnf_1F (nnf_1F (nnf_1F hNf))) |]].
      right; exists R_fin; exact (conj eq_refl (proj1 hS')).
  - rewrite hEq in hF, hNb2.
    pose proof (noNonlast0F_tail (noNonlast0F_tail (noNonlast0F_tail hNb2))) as hNG.
    destruct (good2_f311 (invAt_all s) hG hF hNG) as [-> hS'].
    cbn [Nat.div ones app].
    split; [reflexivity |].
    exists ((1, false) :: (1, false) :: R_fin).
    split; [reflexivity | split; [exact (nnf_1F (nnf_1F hNf)) |]].
    left; exists R_fin; exact (conj eq_refl hS').
Qed.

Lemma strongWall_no_halt (rs : list Seg) (hW : StrongWall rs) :
  forall n, run581 n (mkCfg581 BL0 [1; 3; 2] rs) <> None.
Proof.
  intro n.
  exact (wall_no_halt_of_bigF_inv StrongWall strongWall_step n rs hW).
Qed.

End CounterWall.
Import CounterWall.

Module TM115.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE").
Arguments tm _ : simpl never.
Local Definition interpret := evalCfg581 F B D.

Lemma local_step c c' (h : step581 c = Some c') :
  interpret c -[ tm ]->+ interpret c'.
Proof. unfold interpret. prove_step581 c h. Qed.

Lemma init_reaches_start_local :
  c0 -[ tm ]->+ interpret (mkCfg581 BL0 [1; 0] [(0, false)]).
Proof.
  unfold c0, tape0, interpret, evalCfg581.
  cbn [cfg_mode cfg_L cfg_R encLeft581 encRight581 rep1].
  run_steps.
Qed.

Definition wallR0_local : list Seg :=
  [(0, true); (1, false); (1, false); (2, false);
   (1, false); (1, false); (1, false); (1, false); (2, false);
   (1, false); (1, false); (1, false); (1, false); (2, false);
   (0, true); (1, true); (1, false); (1, false); (1, false); (2, false)].

Lemma start_reaches_wall_local :
  run581 803 (mkCfg581 BL0 [1; 0] [(0, false)]) =
    Some (mkCfg581 BL0 [1; 3; 2] wallR0_local).
Proof.
  vm_compute. reflexivity.
Qed.

Lemma init_reaches_wall_local :
  c0 -[ tm ]->+ interpret (mkCfg581 BL0 [1; 3; 2] wallR0_local).
Proof.
  eapply progress_evstep_trans.
  - exact init_reaches_start_local.
  - exact (run581_evstep tm interpret local_step 803 _ _ start_reaches_wall_local).
Qed.

Lemma wallR0_is_strongWall : StrongWall wallR0_local.
Proof.
  unfold wallR0_local, StrongWall.
  eexists. split; [reflexivity |].
  split; [cbn; exact I |].
  left. eexists. split; [reflexivity |].
  exact (strong2_of_2_1_1 _).
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  exact (nonhalt_of_run581_no_halt tm interpret local_step _
    init_reaches_wall_local (strongWall_no_halt _ wallR0_is_strongWall)).
Qed.

End TM115.

Module TM118.

Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC0RF_1LE0LD_1RC0LB_---1RA_1LB1RA").
Arguments tm _ : simpl never.
Local Definition interpret := evalCfg581 B C A.

Lemma local_step c c' (h : step581 c = Some c') :
  interpret c -[ tm ]->+ interpret c'.
Proof. unfold interpret. prove_step581 c h. Qed.

Lemma init_reaches_start_local :
  c0 -[ tm ]->+ interpret (mkCfg581 BL0 [0] [(1, false); (0, false)]).
Proof.
  unfold c0, tape0, interpret, evalCfg581.
  cbn [cfg_mode cfg_L cfg_R encLeft581 encRight581 rep1].
  run_steps.
Qed.

Definition wallR0_local : list Seg :=
  [(0, true); (1, false); (1, false); (2, false);
   (1, false); (2, false); (1, false); (1, false); (2, false);
   (0, true); (0, true); (1, false); (1, true); (2, false);
   (1, false); (1, false); (2, false)].

Lemma start_reaches_wall_local :
  run581 760 (mkCfg581 BL0 [0] [(1, false); (0, false)]) =
    Some (mkCfg581 BL0 [1; 3; 2] wallR0_local).
Proof.
  vm_compute. reflexivity.
Qed.

Lemma init_reaches_wall_local :
  c0 -[ tm ]->+ interpret (mkCfg581 BL0 [1; 3; 2] wallR0_local).
Proof.
  eapply progress_evstep_trans.
  - exact init_reaches_start_local.
  - exact (run581_evstep tm interpret local_step 760 _ _ start_reaches_wall_local).
Qed.

Lemma wallR0_is_strongWall : StrongWall wallR0_local.
Proof.
  unfold wallR0_local, StrongWall.
  eexists. split; [reflexivity |].
  split; [cbn; exact I |].
  left. eexists. split; [reflexivity |].
  exact (strong2_of_step_21 (good2_of_2_1_1 _)).
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  exact (nonhalt_of_run581_no_halt tm interpret local_step _
    init_reaches_wall_local (strongWall_no_halt _ wallR0_is_strongWall)).
Qed.

End TM118.

Module SixMode.

Local Notation "'0inf'" := (@const Sym S0).
Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Inductive Mode484 : Type :=
  | mC0
  | mAL
  | mE1
  | mBR
  | mDR
  | mD0.

Record State484 : Type := mkState484 {
  s_mode : Mode484;
  s_L : list (nat * bool);
  s_R : list (nat * bool)
}.

Definition bump (xs : list (nat * bool)) : list (nat * bool) :=
  match xs with
  | [] => [(0, false)]
  | (a, sep) :: rest => (S a, sep) :: rest
  end.

Definition stepAtomic (s : State484) : option State484 :=
  match s_mode s with
  | mC0 => Some (mkState484 mAL (s_L s) (bump (s_R s)))
  | mAL =>
    match s_L s with
    | [] => Some (mkState484 mBR [(0, false)] (s_R s))
    | (0, false) :: Ls => Some (mkState484 mE1 Ls (s_R s))
    | (0, true) :: _ => None
    | (1, false) :: Ls =>
      match s_R s with
      | [] => Some (mkState484 mC0 Ls [])
      | r0 :: Rs => Some (mkState484 mAL Ls ((0, true) :: r0 :: Rs))
      end
    | (1, true) :: Ls => Some (mkState484 mBR (bump Ls) ((0, true) :: s_R s))
    | (2, false) :: Ls => Some (mkState484 mBR (bump Ls) ((1, false) :: s_R s))
    | (2, true) :: Ls => Some (mkState484 mBR ((0, false) :: Ls) ((1, false) :: s_R s))
    | (S (S (S a)), sep) :: Ls => Some (mkState484 mC0 ((a, sep) :: Ls) ((0, false) :: s_R s))
    end
  | mE1 =>
    match s_L s with
    | [] => None
    | l0 :: Ls => Some (mkState484 mBR (l0 :: Ls) (bump (bump (s_R s))))
    end
  | mBR =>
    match s_R s with
    | [] =>
      match s_L s with
      | [] => Some (mkState484 mC0 [] [(0, false)])
      | (0, false) :: Ls => Some (mkState484 mD0 ((0, true) :: Ls) [])
      | (0, true) :: Ls => Some (mkState484 mBR ((0, false) :: Ls) [(0, true); (0, false)])
      | (S a, sep) :: Ls => Some (mkState484 mD0 ((0, false) :: (a, sep) :: Ls) [])
      end
    | (0, false) :: Rs => Some (mkState484 mD0 (bump (s_L s)) Rs)
    | (0, true) :: Rs => Some (mkState484 mC0 (bump (bump (s_L s))) Rs)
    | (S d, c) :: Rs => Some (mkState484 mDR (bump (s_L s)) ((d, c) :: Rs))
    end
  | mDR =>
    match s_R s with
    | [] => Some (mkState484 mC0 (bump (s_L s)) [])
    | (0, false) :: Rs =>
      match s_L s with
      | [] => Some (mkState484 mBR [] (bump Rs))
      | l0 :: Ls => Some (mkState484 mDR ((0, false) :: l0 :: Ls) Rs)
      end
    | (0, true) :: Rs =>
      match s_L s with
      | [] => Some (mkState484 mBR [] ((0, false) :: Rs))
      | l0 :: Ls => Some (mkState484 mD0 ((0, false) :: l0 :: Ls) Rs)
      end
    | (S d, c) :: Rs => Some (mkState484 mBR (bump (s_L s)) ((d, c) :: Rs))
    end
  | mD0 =>
    match s_R s with
    | [] => Some (mkState484 mC0 (bump (s_L s)) [])
    | (0, false) :: Rs => Some (mkState484 mC0 (bump (s_L s)) (bump Rs))
    | (0, true) :: Rs => Some (mkState484 mC0 (bump (s_L s)) ((0, false) :: Rs))
    | (1, false) :: Rs => Some (mkState484 mD0 ((0, false) :: bump (s_L s)) Rs)
    | (1, true) :: Rs => Some (mkState484 mC0 ((1, false) :: bump (s_L s)) Rs)
    | (S (S d), c) :: Rs => Some (mkState484 mDR ((0, false) :: bump (s_L s)) ((d, c) :: Rs))
    end
  end.

Definition isDoor (s : State484) : bool :=
  match s_mode s, s_L s with
  | mAL, (0, true) :: _ => true
  | mE1, [] => true
  | _, _ => false
  end.

Definition stepTot (s : State484) : State484 :=
  match stepAtomic s with
  | None => s
  | Some s' => s'
  end.

Fixpoint runTot (n : nat) (s : State484) : State484 :=
  match n with
  | 0 => s
  | S n' => runTot n' (stepTot s)
  end.

Lemma stepAtomic_eq_none_iff (s : State484) :
  stepAtomic s = None <-> isDoor s = true.
Proof.
  destruct s as [mode L R]; destruct mode; cbn [stepAtomic isDoor s_mode s_L s_R].
  - split; discriminate.
  - destruct L as [| [[| [| [| a]]] [|]] Ls];
      try destruct R; split; (reflexivity || discriminate).
  - destruct L; split; (reflexivity || discriminate).
  - destruct R as [| [[| d] [|]] Rs];
      try destruct L as [| [[| a] [|]] Ls];
      split; discriminate.
  - destruct R as [| [[| d] [|]] Rs];
      try destruct L; split; discriminate.
  - destruct R as [| [[| [| d]] [|]] Rs]; split; discriminate.
Qed.

Lemma stepAtomic_some_of_not_door {s : State484} (h : isDoor s = false) :
  stepAtomic s = Some (stepTot s).
Proof.
  unfold stepTot.
  destruct (stepAtomic s) as [s' |] eqn:hs.
  - reflexivity.
  - apply stepAtomic_eq_none_iff in hs.
    rewrite hs in h. discriminate h.
Qed.

Lemma runTot_add (a b : nat) (s : State484) :
  runTot (a + b) s = runTot b (runTot a s).
Proof.
  revert s.
  induction a as [| a' ih]; intro s; [reflexivity |].
  cbn [Nat.add runTot].
  exact (ih (stepTot s)).
Qed.

Fixpoint pushOnes (n : nat) (t : side) : side :=
  match n with
  | 0 => t
  | S n' => S1 >> pushOnes n' t
  end.

Definition pushSep (sep : bool) (t : side) : side :=
  if sep then S0 >> S0 >> t else S0 >> t.

Fixpoint encStack (xs : list (nat * bool)) : side :=
  match xs with
  | [] => 0inf
  | (a, sep) :: rest => S1 >> pushOnes a (pushSep sep (encStack rest))
  end.

Lemma encStack_bump (xs : list (nat * bool)) :
  encStack (bump xs) = S1 >> encStack xs.
Proof.
  destruct xs as [| [a sep] rest]; cbn [bump encStack pushOnes pushSep].
  - rewrite zero_cons_default581. reflexivity.
  - reflexivity.
Qed.

Tactic Notation "prove_stepAtomic" hyp(s) hyp(h) constr(enc) :=
  (destruct s as [mode L R];
  destruct mode;
  [ idtac
  | destruct L as [| [[| [| [| a3]]] sep] Ls];
    [ idtac | destruct sep | destruct sep; [idtac | destruct R as [| [d c] Rs]] |
      destruct sep | destruct sep ]
  | destruct L as [| [a sep] Ls]
  | destruct R as [| [[| d1] c] Rs];
    [ destruct L as [| [[| a1] sep] Ls]; [idtac | destruct sep | destruct sep]
    | destruct c | destruct c ]
  | destruct R as [| [[| d1] c] Rs];
    [ idtac | destruct c; destruct L as [| [a sep] Ls] | destruct c ]
  | destruct R as [| [[| [| d2]] c] Rs];
    [ idtac | destruct c | destruct c | destruct c ] ];
  cbn [stepAtomic s_mode s_L s_R] in h; try discriminate h;
  inversion h; subst; clear h;
  unfold enc; cbn [s_mode s_L s_R encStack pushOnes pushSep];
  repeat rewrite encStack_bump;
  run_steps).

Section OrbitSoundness.

Context (tm : TM) (enc : State484 -> Q * tape)
  (step_sound : forall s s', stepAtomic s = Some s' -> enc s -[ tm ]->+ enc s').

Lemma safe_of_orbit_safe (k : nat) :
  forall s, (forall n, isDoor (runTot n s) = false) -> Safe tm k (enc s).
Proof.
  induction k as [k ih] using strong_induction.
  intros s hsafe.
  pose proof (stepAtomic_some_of_not_door (hsafe 0)) as hs.
  eapply (Safe_of_stepPlus tm); [exact (step_sound s (stepTot s) hs) |].
  intros k' hk'.
  apply ih; [exact hk' |].
  intro n.
  exact (hsafe (S n)).
Qed.

Lemma nonhalt_of_orbit_safe
    (start : State484) (enc_start : c0 = enc start)
    (hsafe : forall n, isDoor (runTot n start) = false) :
  ~ halts tm c0.
Proof.
  intros [k Hhalt].
  rewrite enc_start in Hhalt.
  exact (safe_of_orbit_safe k start hsafe k (Nat.le_refl k) Hhalt).
Qed.

End OrbitSoundness.

Fixpoint safePrefix (k : nat) (s : State484) : bool :=
  match k with
  | 0 => true
  | S k' => negb (isDoor s) && safePrefix k' (stepTot s)
  end.

Lemma safePrefix_sound (k : nat) :
  forall s, safePrefix k s = true -> forall j, j < k -> isDoor (runTot j s) = false.
Proof.
  induction k as [| k' ih]; intros s hs j hj; [lia |].
  cbn [safePrefix] in hs.
  apply andb_true_iff in hs. destruct hs as [hnd hrest].
  apply negb_true_iff in hnd.
  destruct j as [| j'].
  - exact hnd.
  - cbn [runTot].
    apply ih; [exact hrest | lia].
Qed.

Fixpoint rep1Seg (n : nat) (R : list (nat * bool)) : list (nat * bool) :=
  match n with
  | 0 => R
  | S n' => (1, false) :: rep1Seg n' R
  end.

Definition bump2 (R : list (nat * bool)) : list (nat * bool) :=
  bump (bump R).

Lemma rep1Seg_cons_one (q : nat) (R : list (nat * bool)) :
  rep1Seg q ((1, false) :: R) = (1, false) :: rep1Seg q R.
Proof.
  induction q as [| q' ih]; [reflexivity |].
  cbn [rep1Seg]. rewrite ih. reflexivity.
Qed.

Definition SafeSteps (k : nat) (s : State484) : Prop :=
  forall j : nat, j < k -> isDoor (runTot j s) = false.

Lemma safeSteps_zero (s : State484) : SafeSteps 0 s.
Proof.
  intros j hj. lia.
Qed.

Lemma safeSteps_step {k : nat} {s : State484}
    (hd : isDoor s = false) (hnext : SafeSteps k (stepTot s)) :
  SafeSteps (S k) s.
Proof.
  intros [| j'] hj.
  - exact hd.
  - cbn [runTot]. apply hnext. lia.
Qed.

Ltac solve_safe_steps :=
  repeat (apply safeSteps_zero || (apply safeSteps_step; [reflexivity |])).

Lemma safeSteps_trans {a b : nat} {s : State484}
    (ha : SafeSteps a s) (hb : SafeSteps b (runTot a s)) :
  SafeSteps (a + b) s.
Proof.
  intros j hj.
  destruct (Nat.lt_ge_cases j a) as [hlt | hge].
  - exact (ha j hlt).
  - replace j with (a + (j - a)) by lia.
    rewrite runTot_add.
    apply hb. lia.
Qed.

Lemma mAL_drain_3q (q r : nat) (Ls R : list (nat * bool)) :
  SafeSteps (2 * q) (mkState484 mAL ((3 * q + r, false) :: Ls) R) /\
  runTot (2 * q) (mkState484 mAL ((3 * q + r, false) :: Ls) R) =
    mkState484 mAL ((r, false) :: Ls) (rep1Seg q R).
Proof.
  revert R.
  induction q as [| q' ih]; intro R.
  - cbn [Nat.mul Nat.add rep1Seg].
    exact (conj (safeSteps_zero _) eq_refl).
  - replace (3 * S q' + r) with (S (S (S (3 * q' + r)))) by lia.
    replace (2 * S q') with (2 + 2 * q') by lia.
    destruct (ih ((1, false) :: R)) as [hs hr].
    assert (hpre2 : SafeSteps 2 (mkState484 mAL ((S (S (S (3 * q' + r))), false) :: Ls) R))
      by solve_safe_steps.
    assert (hrun2 : runTot 2 (mkState484 mAL ((S (S (S (3 * q' + r))), false) :: Ls) R) =
        mkState484 mAL ((3 * q' + r, false) :: Ls) ((1, false) :: R))
      by reflexivity.
    split.
    + apply safeSteps_trans; [exact hpre2 |].
      rewrite hrun2. exact hs.
    + rewrite runTot_add, hrun2, hr, rep1Seg_cons_one. reflexivity.
Qed.

Lemma bump_eq_bumpR (R : list Seg) : bump R = bumpR R.
Proof.
  destruct R as [| [d b] xs]; reflexivity.
Qed.

Lemma bump2_eq_bumpR2 (R : list Seg) : bump2 R = bumpR (bumpR R).
Proof.
  unfold bump2. rewrite !bump_eq_bumpR. reflexivity.
Qed.

Lemma rep1Seg_eq_ones_append (q : nat) (R : list Seg) :
  rep1Seg q R = ones q ++ R.
Proof.
  induction q as [| k ih]; [reflexivity |].
  cbn [rep1Seg ones app]. rewrite ih. reflexivity.
Qed.

(* It is enough to account for calls on a trace that reaches a door.
   Calls that never return need not have a BigF/BigD1 derivation. *)
Definition Bad (k : nat) (s : State484) := isDoor (runTot k s) = true.
Definition Transfer k st (P : State484 -> Prop) :=
  Bad k st -> exists j, j < k /\ exists out, P out /\ Bad j out.

Lemma transfer_map k st P Q : Transfer k st P ->
  (forall out, P out -> Q out) -> Transfer k st Q.
Proof.
  intros h hPQ hb. destruct (h hb) as [j [hj [out [hp hbad]]]].
  exists j. split; [exact hj |]. exists out. auto.
Qed.


Lemma transfer_bind k st P Q : Transfer k st P ->
  (forall j out, j < k -> P out -> Transfer j out Q) -> Transfer k st Q.
Proof.
  intros h hPQ hb. destruct (h hb) as [j [hj [out [hp hbad]]]].
  destruct (hPQ j out hj hp hbad) as [i [hi hs]].
  exists i. split; [lia | exact hs].
Qed.

Lemma bad_skip k n st out : SafeSteps n st -> runTot n st = out ->
  Bad k st -> Bad (k - n) out.
Proof.
  intros hs hr hb.
  assert (hn : n <= k).
  { destruct (Nat.lt_ge_cases k n) as [h | h]; [| exact h].
    specialize (hs k h). unfold Bad in hb. congruence. }
  unfold Bad in *. now rewrite <- hr, <- runTot_add, Nat.add_comm, Nat.sub_add.
Qed.

Lemma transfer_skip k n st out P : SafeSteps n st -> runTot n st = out ->
  Transfer (k - n) out P -> Transfer k st P.
Proof.
  intros hs hr ht hb. destruct (ht (bad_skip k n st out hs hr hb)) as [j [hj h]].
  exists j. split; [lia | exact h].
Qed.

Lemma transfer_stop k n st out P : 0 < n ->
  SafeSteps n st -> runTot n st = out -> P out -> Transfer k st P.
Proof.
  intros hn hs hr hp hb. pose proof (bad_skip k n st out hs hr hb) as he.
  assert (hnk : n <= k).
  { destruct (Nat.lt_ge_cases k n) as [h | h]; [| exact h].
    specialize (hs k h). unfold Bad in hb. congruence. }
  exists (k-n). split; [lia |]. exists out. auto.
Qed.

Definition Fret (a : nat) (Ls R : list Seg) (out : State484) : Prop :=
  exists s i Z, BigF s R i Z /\ out = mkState484 mAL ((a + i, false) :: Ls) Z.

Definition Dret (a : nat) (Ls R : list Seg) (out : State484) : Prop :=
  exists s i Z, BigD1 s R (S i) Z /\ out = mkState484 mAL ((a + i, false) :: Ls) Z.

Definition Dispatch (v : nat) (R : list Seg) (i : nat) (Z : list Seg) : Prop :=
  match v mod 3 with
  | 0 => exists s d, BigD1 s (ones (v / 3) ++ R) d Z /\ i = d + 1
  | 1 => i = 0 /\ Z = (0, true) :: ones (v / 3) ++ R
  | _ => exists s, BigD1 s (ones (S (v / 3)) ++ R) i Z
  end.

Definition Pret (v b : nat) (Ls R : list Seg) (out : State484) : Prop :=
  exists i Z, Dispatch v R i Z /\ out = mkState484 mAL ((b + i, false) :: Ls) Z.

Definition Call0 k a Ls R :=
  Transfer k (mkState484 mD0 ((a, false) :: Ls) R) (Fret (S a) Ls R).
Definition CallB k a Ls d c R :=
  Transfer k (mkState484 mBR ((a, false) :: Ls) ((d, c) :: R)) (Dret a Ls ((d, c) :: R)).
Definition CallR k b Ls R :=
  Transfer k (mkState484 mDR ((0, false) :: (b, false) :: Ls) R) (Fret b Ls (bump2 R)).
Definition CallP k v b Ls Z :=
  Z <> [] -> Transfer k (mkState484 mAL ((v, false) :: (b, false) :: Ls) Z) (Pret v b Ls Z).

Ltac take_steps count :=
  eapply transfer_skip with (n := count);
  [ solve_safe_steps | reflexivity | ].
Ltac return_steps count :=
  eapply transfer_stop with (n := count);
  [ lia | solve_safe_steps | reflexivity | ].
Ltac ret_eq :=
  cbn [runTot stepTot stepAtomic s_mode s_L s_R bump];
  solve [repeat (first [solve [lia] | f_equal])].

(* Dispatch is the only place a quotient occurs.  Constructors of BigF then
   just consume its three possible exit descriptions. *)
Ltac use_dispatch h :=
  unfold Dispatch in h;
  let E := fresh "E" in
  match type of h with context [ ?v mod 3 ] =>
    destruct (v mod 3) as [| [| r]] eqn:E
  end;
  [ destruct h as [? [? [h ->]]]
  | destruct h as [-> ->]
  | destruct h as [? h] ].

Lemma dispatch_one {s R i Z j Y} :
  BigF s R i Z -> Dispatch (1 + i) Z j Y -> exists t, BigF t ((1, false) :: R) j Y.
Proof.
  intros hf hp. use_dispatch hp; eexists.
  - exact (BF_oneF_rem0 hf E hp).
  - exact (BF_oneF_rem1 hf E).
  - replace (S (S r)) with 2 in E by (pose proof (Nat.mod_upper_bound (1+i) 3 ltac:(lia)); lia).
    exact (BF_oneF_rem2 hf E hp).
Qed.

Lemma dispatch_twoF {s R i Z j Y} :
  BigF s (bump2 R) i Z -> Dispatch i Z j Y -> exists t, BigF t ((2, false) :: R) j Y.
Proof.
  rewrite bump2_eq_bumpR2. intros hf hp. use_dispatch hp; eexists.
  - exact (BF_twoF_rem0 hf E hp).
  - exact (BF_twoF_rem1 hf E).
  - replace (S (S r)) with 2 in E by (pose proof (Nat.mod_upper_bound i 3 ltac:(lia)); lia).
    exact (BF_twoF_rem2 hf E hp).
Qed.

Lemma dispatch_twoT {s R i Z j Y} :
  BigF s ((1, false) :: R) i Z -> Dispatch i Z j Y -> exists t, BigF t ((2, true) :: R) j Y.
Proof.
  intros hf hp. use_dispatch hp; eexists.
  - exact (BF_twoT_rem0 hf E hp).
  - exact (BF_twoT_rem1 hf E).
  - replace (S (S r)) with 2 in E by (pose proof (Nat.mod_upper_bound i 3 ltac:(lia)); lia).
    exact (BF_twoT_rem2 hf E hp).
Qed.

Lemma dispatch_ge3 {s d c R i Z j Y} :
  BigD1 s ((d, c) :: R) i Z -> Dispatch i Z j Y ->
  exists t, BigF t ((S (S (S d)), c) :: R) j Y.
Proof.
  intros hf hp. use_dispatch hp; eexists.
  - exact (BF_ge3_rem0 hf E hp).
  - exact (BF_ge3_rem1 hf E).
  - replace (S (S r)) with 2 in E by (pose proof (Nat.mod_upper_bound i 3 ltac:(lia)); lia).
    exact (BF_ge3_rem2 hf E hp).
Qed.

Lemma bigD1_out_nonempty s R d Z : BigD1 s R d Z -> Z <> [].
Proof.
  intro h. induction h; try discriminate; eauto using bigF_out_ne_nil, bumpR_nonempty.
Qed.

(* Repeatedly use the remaining bad trace as the measure for subcalls. *)
Lemma calls_return k :
  (forall a Ls R, Call0 k a Ls R) /\
  (forall a Ls d c R, CallB k a Ls d c R) /\
  (forall b Ls R, CallR k b Ls R) /\
  (forall v b Ls Z, CallP k v b Ls Z).
Proof.
  induction k as [k IH] using strong_induction.
  destruct k as [| prev].
  { clear IH. split; [| split; [| split]].
    - intros a Ls R hb. discriminate hb.
    - intros a Ls d c R hb. discriminate hb.
    - intros b Ls R hb. discriminate hb.
    - intros [|v] b Ls Z _ hb; discriminate hb. }
  remember (S prev) as k eqn:hk in *.
  assert (I0 : forall j, j < k -> forall a Ls R, Call0 j a Ls R)
    by (intros j hj; exact (proj1 (IH j hj))).
  assert (IB : forall j, j < k -> forall a Ls d c R, CallB j a Ls d c R)
    by (intros j hj; exact (proj1 (proj2 (IH j hj)))).
  assert (IR : forall j, j < k -> forall b Ls R, CallR j b Ls R)
    by (intros j hj; exact (proj1 (proj2 (proj2 (IH j hj))))).
  assert (IP : forall j, j < k -> forall v b Ls Z, CallP j v b Ls Z)
    by (intros j hj; exact (proj2 (proj2 (proj2 (IH j hj))))).
  clear IH.
  split; [| split; [| split]].
  - intros a Ls [| [[| [| d]] c] R]; unfold Call0.
    + return_steps 2. exists 0, 0, [(0,false)]. split; [exact BF_nil | ret_eq].
    + destruct c.
      * return_steps 2. exists 0, 0, ((1,false)::R). split; [apply BF_zeroT | ret_eq].
      * return_steps 2. exists 0, 0, (bump2 R).
        split; [rewrite bump2_eq_bumpR2; apply BF_zeroF | ret_eq].
    + destruct c.
      * destruct R as [|[d c] R]; return_steps 3.
        all: eexists 0, 0, _; split; [apply BF_oneT | ret_eq].
      * take_steps 1.
        eapply transfer_bind; [apply I0; lia |].
        intros j out hj [s [i [Z [hf ->]]]].
        eapply transfer_map; [apply IP; [lia | exact (bigF_out_ne_nil hf)] |].
        intros out [d [Y [hp ->]]]. destruct (dispatch_one hf hp) as [t h].
        exists t, d, Y. auto.
    + take_steps 1. apply IR. lia.
  - intros a Ls [| [| d]] c R; unfold CallB.
    + destruct c.
      * return_steps 2. exists 0, 2, (bump R).
        split; [rewrite bump_eq_bumpR; apply BD_zeroT | ret_eq].
      * take_steps 1. eapply transfer_map; [apply I0; lia |].
        intros out [s [i [Z [hf ->]]]].
        exists (s+1), (S (S i)), Z. split.
        -- replace (S (S (S i))) with (i+3) by lia. exact (BD_zeroF hf).
        -- ret_eq.
    + destruct c.
      * take_steps 2.
        eapply transfer_bind; [apply I0; lia |].
        intros j out hj [s [i [Z [hf ->]]]].
        eapply transfer_map; [apply IP; [lia | exact (bigF_out_ne_nil hf)] |].
        intros out [j' [Y [hp ->]]]. destruct (dispatch_one hf hp) as [t h].
        exists (t+1), (S j'), Y. split.
        -- replace (S (S j')) with (j'+2) by lia. exact (BD_oneT h).
        -- ret_eq.
      * take_steps 2. eapply transfer_map; [apply IR; lia |].
        intros out [s [i [Z [hf ->]]]].
        exists (s+1), (S i), Z. split.
        -- rewrite bump2_eq_bumpR2 in hf. replace (S (S i)) with (i+2) by lia.
           exact (BD_oneF hf).
        -- ret_eq.
    + take_steps 2. eapply transfer_map; [apply IB; lia |].
      intros out [s [i [Z [hd ->]]]].
      exists (s+1), (S (S i)), Z. split.
      * replace (S (S (S i))) with (S i+2) by lia. exact (BD_ge2 hd).
      * ret_eq.
  - intros b Ls [| [[| d] c] R]; unfold CallR.
    + return_steps 3. exists 1, 0, [(0,true); (0,false)]. split.
      * exact (BF_oneF_rem1 BF_nil eq_refl).
      * ret_eq.
    + destruct c.
      * take_steps 1.
        eapply transfer_bind; [apply I0; lia |].
        intros j out hj [s [i [Z [hf ->]]]].
        eapply transfer_bind; [apply IP; [lia | exact (bigF_out_ne_nil hf)] |].
        intros j' out hj' [i' [Z' [hp ->]]].
        destruct (dispatch_one hf hp) as [t h].
        eapply transfer_map; [apply IP; [lia | exact (bigF_out_ne_nil h)] |].
        intros out [d [Y [hp' ->]]].
        destruct (dispatch_twoT h hp') as [t' h'].
        exists t', d, Y. auto.
      * take_steps 1.
        eapply transfer_bind; [apply IR; lia |].
        intros j out hj [s [i [Z [hf ->]]]].
        eapply transfer_map; [apply IP; [lia | exact (bigF_out_ne_nil hf)] |].
        intros out [d [Y [hp ->]]]. destruct (dispatch_twoF hf hp) as [t h].
        exists t, d, Y. auto.
    + take_steps 1.
      eapply transfer_bind; [apply IB; lia |].
      intros j out hj [s [i [Z [hd ->]]]].
      eapply transfer_map.
      * apply IP; [lia | exact (bigD1_out_nonempty _ _ _ _ hd)].
      * intros out [j' [Y [hp ->]]]. destruct (dispatch_ge3 hd hp) as [t h].
        exists t, j', Y. auto.
  - intros v b Ls R hR. unfold CallP.
    pose proof (Nat.div_mod v 3 ltac:(lia)) as he.
    pose proof (Nat.mod_upper_bound v 3 ltac:(lia)) as hh.
    remember (v / 3) as q eqn:hq; remember (v mod 3) as r eqn:hr.
    (* Drain the left register in one stride; all cases share it. *)
    destruct (mAL_drain_3q q r ((b,false)::Ls) R) as [hs ht].
    rewrite <- he in hs, ht.
    eapply transfer_skip; [exact hs | exact ht |].
    rewrite rep1Seg_eq_ones_append.
    assert (hT : ones q ++ R <> []) by (apply append_nonempty_of_right; exact hR).
    destruct r as [| [| r]].
    + remember (ones q ++ R) as T eqn:hT'. destruct T as [|[d c] T]; [contradiction |].
      take_steps 4.
      eapply transfer_map; [apply IB; lia |].
      intros out [s [i [Z [hd ->]]]]. exists (S i + 1), Z.
      split.
      * unfold Dispatch. rewrite <- hr, <- hq, <- hT'. eauto.
      * ret_eq.
    + remember (ones q ++ R) as T eqn:hT'. destruct T as [|x T]; [contradiction |].
      return_steps 1. exists 0, ((0,true)::x::T).
      unfold Dispatch. now rewrite <- hr, <- hq, <- hT', Nat.add_0_r.
    + assert (r=0) by lia. subst r.
      take_steps 1. eapply transfer_map; [apply IB; lia |].
      intros out [s [i [Z [hd ->]]]]. exists (S i), Z.
      split.
      * unfold Dispatch. rewrite <- hr, <- hq. exists s. exact hd.
      * ret_eq.
Qed.

Definition atWall xs := mkState484 mAL [(2,false)] ((1,false)::xs).

Lemma wall_return k xs :
  Transfer k (atWall xs) (Fret 1 [] ((3,false)::xs)).
Proof.
  unfold atWall. take_steps 3.
  exact (proj1 (proj2 (proj2 (calls_return _))) 1 [] ((1,false)::xs)).
Qed.

Lemma strongWall_front R :
  StrongWall R -> exists xs, R = (0,true)::(1,false)::xs.
Proof.
  intros [tail [-> [_ [[G [h _]] | [G [h _]]]]]];
    destruct tail as [|[d c] xs]; cbn [bumpR] in h; try discriminate;
    inversion h; subst; eauto.
Qed.

Lemma wall_no_door k xs :
  StrongWall ((0,true)::(1,false)::xs) -> ~ Bad k (atWall xs).
Proof.
  revert xs. induction k as [k IH] using strong_induction. intros xs hW hb.
  destruct (wall_return k xs hb) as [j [hj [out [[s [i [Z [hf ->]]]] hbad]]]].
  destruct (strongWall_step _ hW) as [tail [he hw]]. inversion he; subst tail; clear he.
  destruct (hw _ _ _ hf) as [hmod hWall].
  pose proof (Nat.div_mod i 3 ltac:(lia)) as he.
  assert (hv : 1 + i = 3 * (i / 3) + 2) by lia.
  rewrite hv in hbad.
  destruct (mAL_drain_3q (i / 3) 2 [] Z) as [hpre hrun].
  pose proof (bad_skip _ _ _ _ hpre hrun hbad) as hshort.
  rewrite rep1Seg_eq_ones_append in hshort.
  destruct (strongWall_front _ hWall) as [xs' hh].
  assert (hr : ones (i/3) ++ Z = (1,false)::xs') by congruence.
  rewrite hr in hWall, hshort.
  apply (IH (j - 2 * (i/3)) ltac:(lia) xs' hWall hshort).
Qed.

Lemma wall_entry_safe_return start fuel xs :
  runTot fuel start = atWall xs -> safePrefix fuel start = true ->
  StrongWall ((0,true)::(1,false)::xs) ->
  forall k, isDoor (runTot k start) = false.
Proof.
  intros hr hs hW k.
  destruct (isDoor (runTot k start)) eqn:hb; [| reflexivity].
  exfalso. exact (wall_no_door _ _ hW
    (bad_skip k fuel start (atWall xs) (safePrefix_sound fuel start hs) hr hb)).
Qed.

End SixMode.
Import SixMode.
Local Notation "'0inf'" := (@const Sym S0).

Module TM116.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC0LA_1LA0RE_1LB1LA_1RF0RB_---0LB").
Arguments tm _ : simpl never.

Definition start : State484 := mkState484 mBR [] [].

Definition interpret (s : State484) : Q * tape :=
  let l := encStack (s_R s) in
  let r := encStack (s_L s) in
  match s_mode s with
  | mC0 => (B, (l, S0, r))
  | mAL => l {{C}}> r
  | mE1 => (E, (S0 >> l, S0, r))
  | mBR => l <{{A}} r
  | mDR => l <{{D}} r
  | mD0 => (D, (l, S0, r))
  end.

Lemma enc_start : c0 = interpret start.
Proof.
  reflexivity.
Qed.

Lemma local_step s s' (h : stepAtomic s = Some s') :
  interpret s -[ tm ]->+ interpret s'.
Proof. prove_stepAtomic s h interpret. Qed.

Definition suffix : list Seg :=
  [(1, false); (1, false); (2, false); (0, true); (2, false); (1, false); (1, false); (2, false)].

Theorem nonhalt : ~halts tm c0.
Proof.
  apply (nonhalt_of_orbit_safe tm interpret local_step start enc_start).
  apply (wall_entry_safe_return start 315 suffix); [vm_compute; reflexivity | vm_compute; reflexivity |].
  unfold StrongWall. eexists. split; [reflexivity |]. split; [exact I |].
  right. eexists. split; [reflexivity | apply good2_of_2_0s].
Qed.

End TM116.

Module TM117.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC0RE_1RA1LD_1LA1LC_1RF0RA_---0LA").
Arguments tm _ : simpl never.

Definition start : State484 := mkState484 mC0 [] [].

Definition interpret (s : State484) : Q * tape :=
  let l := encStack (s_R s) in
  let r := encStack (s_L s) in
  match s_mode s with
  | mC0 => (A, (l, S0, r))
  | mAL => l {{B}}> r
  | mE1 => (E, (S0 >> l, S0, r))
  | mBR => l <{{C}} r
  | mDR => l <{{D}} r
  | mD0 => (D, (l, S0, r))
  end.

Lemma enc_start : c0 = interpret start.
Proof.
  reflexivity.
Qed.

Lemma local_step s s' (h : stepAtomic s = Some s') :
  interpret s -[ tm ]->+ interpret s'.
Proof. prove_stepAtomic s h interpret. Qed.

Definition suffix : list Seg :=
  [(1, false); (2, false); (1, false); (1, false); (1, false); (1, false); (2, false); (1, false); (1, false); (1, false); (1, false); (2, false); (0, true); (1, true); (1, false); (1, false); (1, false); (2, false)].

Theorem nonhalt : ~halts tm c0.
Proof.
  apply (nonhalt_of_orbit_safe tm interpret local_step start enc_start).
  apply (wall_entry_safe_return start 794 suffix); [vm_compute; reflexivity | vm_compute; reflexivity |].
  unfold StrongWall. eexists. split; [reflexivity |]. split; [exact I |].
  left. eexists. split; [reflexivity | apply strong2_of_2_1_1].
Qed.

End TM117.

Module TM119.

Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC").
Arguments tm _ : simpl never.

Definition start : State484 := mkState484 mAL [] [].

Definition interpret (s : State484) : Q * tape :=
  let l := encStack (s_L s) in
  let r := encStack (s_R s) in
  match s_mode s with
  | mC0 => (C, (l, S0, r))
  | mAL => l <{{A}} r
  | mE1 => (E, (l, S0, S0 >> r))
  | mBR => l {{B}}> r
  | mDR => l {{D}}> r
  | mD0 => (D, (l, S0, r))
  end.

Lemma enc_start : c0 = interpret start.
Proof.
  reflexivity.
Qed.

Lemma local_step s s' (h : stepAtomic s = Some s') :
  interpret s -[ tm ]->+ interpret s'.
Proof. prove_stepAtomic s h interpret. Qed.

Definition suffix : list Seg :=
  [(1, false); (2, false); (1, false); (1, false); (2, false)].

Theorem nonhalt : ~halts tm c0.
Proof.
  apply (nonhalt_of_orbit_safe tm interpret local_step start enc_start).
  apply (wall_entry_safe_return start 173 suffix); [vm_compute; reflexivity | vm_compute; reflexivity |].
  unfold StrongWall. eexists. split; [reflexivity |]. split; [exact I |].
  left. eexists. split; [reflexivity | apply strong2_of_2_1_1].
Qed.

End TM119.
