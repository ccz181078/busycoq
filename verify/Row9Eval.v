From Coq Require Import List Arith Lia Wf_nat Wellfounded Lexicographic_Product.
Import ListNotations.

(** The exact, strict row-9 evaluator on finite words. *)
Definition word := list nat.
Definition result := option word.
Definition bind (r : result) (h : word -> result) : result :=
  match r with None => None | Some W => h W end.
Definition first_plus (k : nat) (W : word) : word :=
  match W with [] => [] | a :: U => (a+k) :: U end.
Definition lift_plus (k : nat) (r : result) : result :=
  option_map (first_plus k) r.
Definition lift_prefix (U : word) (r : result) : result :=
  option_map (app U) r.

Inductive Eval : word -> result -> Prop :=
| Eval_nil : Eval [] (Some [1])
| Eval_one U r : Eval U r -> Eval (1::U) (lift_plus 4 r)
| Eval_two U r : Eval U r -> Eval (2::U) (lift_prefix [2] r)
| Eval_three_halt U : Eval U None -> Eval (3::U) None
| Eval_three U V r : Eval U (Some V) -> Eval V r ->
    Eval (3::U) (lift_prefix [3] r)
| Eval_large g U : Eval (S(S(S(S g)))::U) (Some (1::g::U))
| Eval_zero : Eval [0] (Some [2;2])
| Eval_zero_zero U : Eval (0::0::U) None
| Eval_zero_one U r : Eval U r ->
    Eval (0::1::U) (lift_prefix [2] (lift_plus 2 r))
| Eval_zero_two U r : Eval U r ->
    Eval (0::2::U) (lift_prefix [2;0] r)
| Eval_zero_large g U r : Eval (g::U) r ->
    Eval (0::S(S(S g))::U) (lift_prefix [2] (lift_plus 1 r)).

Definition label_weight (a : nat) : nat := (a+3) mod 4.
Fixpoint Pplus (W : word) : nat :=
  match W with [] => 0 | a::U => label_weight a + Pplus U end.
Definition positive_head (W : word) : Prop :=
  exists a U, W = a::U /\ 0 < a /\ a mod 4 <> 0.

Lemma label_weight_period a : label_weight (a+4) = label_weight a.
Proof.
  unfold label_weight. replace (a+4+3) with ((a+3)+1*4) by lia.
  now rewrite Nat.mod_add.
Qed.
Lemma label_weight_bound a : label_weight a < 4.
Proof. apply Nat.mod_upper_bound; lia. Qed.
Lemma label_weight_shift a k : label_weight (a+k) <= label_weight a + k.
Proof.
  unfold label_weight. replace (a+k+3) with ((a+3)+k) by lia.
  rewrite <- Nat.add_mod_idemp_l by lia. apply Nat.mod_le; lia.
Qed.
Lemma label_weight_back_three a : label_weight a <= label_weight (a+3) + 1.
Proof.
  pose proof (label_weight_shift (a+3) 1).
  replace (a+3+1) with (a+4) in H by lia.
  now rewrite label_weight_period in H.
Qed.
Lemma Pplus_first_plus_four W : Pplus (first_plus 4 W) = Pplus W.
Proof. destruct W; simpl; auto. now rewrite label_weight_period. Qed.
Lemma Pplus_first_plus_bound W k :
  Pplus (first_plus k W) <= Pplus W + k.
Proof.
  destruct W; simpl; try lia. pose proof (label_weight_shift n k); lia.
Qed.
Lemma positive_head_plus_four W : positive_head W -> positive_head (first_plus 4 W).
Proof.
  intros (a & U & -> & Ha & Hmod). exists (a+4), U.
  change ((a+4)::U = (a+4)::U /\ 0<a+4 /\ (a+4) mod 4 <> 0).
  repeat split; try lia.
  replace (a+4) with (a+1*4) by lia. now rewrite Nat.mod_add.
Qed.

Theorem Eval_deterministic W r : Eval W r -> forall s, Eval W s -> r=s.
Proof.
  intros E. induction E; intros s E'; inversion E'; subst; try reflexivity.
  all: try solve [do 2 f_equal; eauto].
  - specialize (IHE _ H0). discriminate.
  - specialize (IHE1 _ H0). discriminate.
  - specialize (IHE1 _ H0). inversion IHE1; subst. f_equal. eauto.
Qed.

Theorem Eval_success_properties W r (E : Eval W r) :
  forall V, r = Some V -> positive_head V /\ Pplus V <= Pplus W.
Proof.
  induction E; intros X HX.
  - inversion HX; subst. split; [exists 1, []; simpl; repeat split; lia | simpl; lia].
  - destruct r as [V|]; try discriminate. inversion HX; subst X.
    specialize (IHE V eq_refl). destruct IHE as [Hpos HP].
    split; [now apply positive_head_plus_four |].
    rewrite Pplus_first_plus_four. simpl. exact HP.
  - destruct r as [V|]; try discriminate. inversion HX; subst X.
    specialize (IHE V eq_refl). destruct IHE as [Hpos HP].
    split; [exists 2, V; simpl; repeat split; lia | simpl; lia].
  - discriminate.
  - destruct r as [V'|]; try discriminate. inversion HX; subst X.
    specialize (IHE1 V eq_refl). specialize (IHE2 V' eq_refl).
    destruct IHE1 as [_ HP1]; destruct IHE2 as [_ HP2].
    split; [exists 3, V'; simpl; repeat split; lia | simpl; lia].
  - inversion HX; subst X. split; [exists 1, (g::U); simpl; repeat split; lia |].
    simpl. replace (S(S(S(S g)))) with (g+4) by lia.
    rewrite label_weight_period. simpl. lia.
  - inversion HX; subst X. split; [exists 2, [2]; simpl; repeat split; lia | simpl; lia].
  - discriminate.
  - destruct r as [V|]; try discriminate. inversion HX; subst X.
    specialize (IHE V eq_refl). destruct IHE as [_ HP].
    split; [exists 2, (first_plus 2 V); simpl; repeat split; lia |].
    simpl. pose proof (Pplus_first_plus_bound V 2); lia.
  - destruct r as [V|]; try discriminate. inversion HX; subst X.
    specialize (IHE V eq_refl). destruct IHE as [_ HP].
    split; [exists 2, (0::V); simpl; repeat split; lia | simpl; lia].
  - destruct r as [V|]; try discriminate. inversion HX; subst X.
    specialize (IHE V eq_refl). destruct IHE as [_ HP].
    split; [exists 2, (first_plus 1 V); simpl; repeat split; lia |].
    cbn [Pplus] in *. change (1 + Pplus (first_plus 1 V) <= 3 + label_weight (S(S(S g))) + Pplus U).
    pose proof (Pplus_first_plus_bound V 1).
    pose proof (label_weight_back_three g).
    replace (S(S(S g))) with (g+3) by lia. lia.
Qed.
Corollary Eval_positive_head W V : Eval W (Some V) -> positive_head V.
Proof. intros E. exact (proj1 (Eval_success_properties _ _ E _ eq_refl)). Qed.
Corollary Eval_success_nonempty W V : Eval W (Some V) -> V <> [].
Proof.
  intros E. destruct (Eval_positive_head _ _ E) as (a & U & -> & _).
  discriminate.
Qed.
Corollary Eval_Pplus W V : Eval W (Some V) -> Pplus V <= Pplus W.
Proof. intros E. exact (proj2 (Eval_success_properties _ _ E _ eq_refl)). Qed.

(** Lexicographic descent in the nonnegative potential and word length. *)
Definition word_lt (U W : word) : Prop :=
  Pplus U < Pplus W \/ (Pplus U = Pplus W /\ length U < length W).
Lemma word_lt_wf : well_founded word_lt.
Proof.
  assert (Hacc : forall p n W, Pplus W=p -> length W=n -> Acc word_lt W).
  { intro p. induction p using lt_wf_ind.
    intro n. induction n using lt_wf_ind.
    intros W HP HL. constructor. intros U [HU | [HU Hlen]].
    - apply (H (Pplus U) ltac:(lia) (length U) U); reflexivity.
    - apply (H0 (length U) ltac:(lia) U); lia. }
  intro W. exact (Hacc (Pplus W) (length W) W eq_refl eq_refl).
Qed.

Definition Eval_total : forall W, {r : result | Eval W r}.
Proof.
  apply (well_founded_induction_type word_lt_wf).
  intros W IH. destruct W as [|a U].
  - exists (Some [1]). apply Eval_nil.
  - destruct a as [|[|[|[|g]]]].
    + destruct U as [|b U].
      * exists (Some [2;2]). apply Eval_zero.
      * destruct b as [|[|[|g]]].
        -- exists None. apply Eval_zero_zero.
        -- assert (D : word_lt U (0::1::U)).
           { left. simpl. lia. }
           destruct (IH U D) as [r E].
           exists (lift_prefix [2] (lift_plus 2 r)). now apply Eval_zero_one.
        -- assert (D : word_lt U (0::2::U)).
           { left. simpl. lia. }
           destruct (IH U D) as [r E].
           exists (lift_prefix [2;0] r). now apply Eval_zero_two.
        -- assert (D : word_lt (g::U) (0::S(S(S g))::U)).
           { left. cbn [Pplus]. change (label_weight g + Pplus U < 3 + (label_weight (S(S(S g))) + Pplus U)).
             replace (S(S(S g))) with (g+3) by lia.
             pose proof (label_weight_back_three g). lia. }
           destruct (IH (g::U) D) as [r E].
           exists (lift_prefix [2] (lift_plus 1 r)). now apply Eval_zero_large.
    + assert (D : word_lt U (1::U)).
      { right. simpl. split; lia. }
      destruct (IH U D) as [r E]. exists (lift_plus 4 r). now apply Eval_one.
    + assert (D : word_lt U (2::U)).
      { left. simpl. lia. }
      destruct (IH U D) as [r E]. exists (lift_prefix [2] r). now apply Eval_two.
    + assert (D : word_lt U (3::U)).
      { left. simpl. lia. }
      destruct (IH U D) as [[V|] E].
      * assert (D' : word_lt V (3::U)).
        { left. simpl. pose proof (Eval_Pplus _ _ E). lia. }
        destruct (IH V D') as [r E']. exists (lift_prefix [3] r).
        eapply Eval_three; eauto.
      * exists None. now apply Eval_three_halt.
    + exists (Some (1::g::U)). apply Eval_large.
Defined.

Definition f (W : word) : result := proj1_sig (Eval_total W).
Theorem f_spec W : Eval W (f W).
Proof. exact (proj2_sig (Eval_total W)). Qed.
Theorem Eval_iff_f W r : Eval W r <-> f W = r.
Proof.
  split.
  - intro E. eapply Eval_deterministic; [apply f_spec | exact E].
  - intro E. rewrite <- E. apply f_spec.
Qed.

Theorem f_nil : f [] = Some [1].
Proof. apply Eval_iff_f. apply Eval_nil. Qed.
Theorem f_one U : f (1::U) = lift_plus 4 (f U).
Proof. apply Eval_iff_f. apply Eval_one. apply f_spec. Qed.
Theorem f_two U : f (2::U) = lift_prefix [2] (f U).
Proof. apply Eval_iff_f. apply Eval_two. apply f_spec. Qed.
Theorem f_three U : f (3::U) = lift_prefix [3] (bind (f U) f).
Proof.
  apply Eval_iff_f. pose proof (f_spec U) as E.
  destruct (f U) as [V|]; cbn [bind lift_prefix option_map].
  - eapply Eval_three; [exact E | apply f_spec].
  - now apply Eval_three_halt.
Qed.
Theorem f_large g U : f ((g+4)::U) = Some (1::g::U).
Proof. apply Eval_iff_f. replace (g+4) with (S(S(S(S g)))) by lia. apply Eval_large. Qed.
Theorem f_zero : f [0] = Some [2;2].
Proof. apply Eval_iff_f. apply Eval_zero. Qed.
Theorem f_zero_zero U : f (0::0::U) = None.
Proof. apply Eval_iff_f. apply Eval_zero_zero. Qed.
Theorem f_zero_one U : f (0::1::U) = lift_prefix [2] (lift_plus 2 (f U)).
Proof. apply Eval_iff_f. apply Eval_zero_one. apply f_spec. Qed.
Theorem f_zero_two U : f (0::2::U) = lift_prefix [2;0] (f U).
Proof. apply Eval_iff_f. apply Eval_zero_two. apply f_spec. Qed.
Theorem f_zero_large g U : f (0::(g+3)::U) = lift_prefix [2] (lift_plus 1 (f (g::U))).
Proof.
  apply Eval_iff_f. replace (g+3) with (S(S(S g))) by lia.
  apply Eval_zero_large. apply f_spec.
Qed.
Corollary f_success_nonempty W V : f W = Some V -> V <> [].
Proof. intros H. apply (Eval_success_nonempty W). now apply Eval_iff_f. Qed.
Corollary f_positive_head W V : f W = Some V -> positive_head V.
Proof. intros H. apply (Eval_positive_head W). now apply Eval_iff_f. Qed.
Corollary f_Pplus W V : f W = Some V -> Pplus V <= Pplus W.
Proof. intros H. apply Eval_Pplus. now apply Eval_iff_f. Qed.

Lemma Eval_zero_head U V : Eval (0::U) (Some V) -> exists T, V = 2::T.
Proof.
  intro E. inversion E; subst; try discriminate.
  - exists [2]. reflexivity.
  - destruct r; inversion H0; subst. eexists. reflexivity.
  - destruct r; inversion H0; subst. eexists. reflexivity.
  - destruct r; inversion H0; subst. eexists. reflexivity.
Qed.
Corollary f_zero_head U V : f (0::U) = Some V -> exists T, V = 2::T.
Proof. intro H. apply (Eval_zero_head U V). now apply Eval_iff_f. Qed.
