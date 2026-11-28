(** The rule map of 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE from the raw machine, with exact step counts.
    The corpus has this map only from the wiki; there is no Lean certificate for it. *)
From BusyCoq Require Import Individual62.
Require Import Lia String PeanoNat.
Open Scope list.
Open Scope string.

Definition tm := Eval compute in (TM_from_str "1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE").
Notation "c -->> n / c'" := (c -[ tm ]->> n / c') (at level 40, n at next level).

Lemma ms_refl c c': c = c' -> c -->> 0 / c'.
Proof. intros ->. constructor. Qed.
Lemma ms_app n m c c' c'': c -->> n / c' -> c' -->> m / c'' -> c -->> (n + m) / c''.
Proof. intros H1 H2. eapply multistep_trans; eauto. Qed.
Lemma ms_eq n N c c': c -->> n / c' -> n = N -> c -->> N / c'.
Proof. intros H <-. exact H. Qed.

Lemma p01 (x:Stream Sym) k: [0;1]^^k *> 0 >> 1 >> x = 0 >> 1 >> [0;1]^^k *> x.
Proof. apply lpow_shift2. Qed.
Lemma p10 (x:Stream Sym) k: [1;0]^^k *> 1 >> 0 >> x = 1 >> 0 >> [1;0]^^k *> x.
Proof. apply lpow_shift2. Qed.
Lemma p11 (x:Stream Sym) k: [1;1]^^k *> 1 >> 1 >> x = 1 >> 1 >> [1;1]^^k *> x.
Proof. apply lpow_shift2. Qed.
Lemma rot01 k (x:Stream Sym): [0;1]^^k *> 0 >> x = 0 >> [1;0]^^k *> x.
Proof. apply (lpow_rotate [1] 0 x k). Qed.
Lemma rot10 k (x:Stream Sym): [1;0]^^k *> 1 >> x = 1 >> [0;1]^^k *> x.
Proof. apply (lpow_rotate [0] 1 x k). Qed.
Lemma ones1 (x:Stream Sym) k: [1]^^k *> 1 >> x = 1 >> [1]^^k *> x.
Proof. apply lpow_shift1. Qed.
Lemma ones2 (x:Stream Sym) k: [1]^^(2*k) *> x = [1;1]^^k *> x.
Proof.
  induction k. { reflexivity. }
  replace (2 * S k) with (S (S (2*k))) by lia. cbn [lpow app Str_app]. rewrite IHk. reflexivity.
Qed.

Ltac cstep := eapply multistep_S; [prove_step | simpl_tape].
Ltac costs := eapply ms_eq.

(** Left streams list the cell next to the head first. *)
Definition Lf a b : side := [0;1]^^b *> [1]^^a *> const 0.

(** The sweeps. *)
Lemma SC k l r: ([0;1]^^k *> l) <{{C}} r -->> (2*k) / l <{{C}} [0;1]^^k *> r.
Proof.
  revert r. induction k; intros r. { apply ms_refl; reflexivity. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p01. apply IHk. } lia.
Qed.
Lemma SB k l r: l {{B}}> [0;1]^^k *> r -->> (2*k) / [1;0]^^k *> l {{B}}> r.
Proof.
  revert l. induction k; intros l. { apply ms_refl; reflexivity. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p10. apply IHk. } lia.
Qed.
Lemma SA k l r: l {{A}}> [0;1]^^k *> 0 >> r -->> (4*k) / [1;1]^^k *> l {{A}}> 0 >> r.
Proof.
  revert l. induction k; intros l. { apply ms_refl; reflexivity. }
  costs.
  { rewrite (rot01 (S k)). cbn [lpow app Str_app]. do 4 cstep.
    pose proof (IHk (1>>1>>l)) as H. rewrite rot01 in H. cbn [hd tl] in H. rewrite p11 in H. exact H. }
  lia.
Qed.
Lemma SE k l r: ([1;1]^^k *> l) <{{E}} r -->> (2*k) / l <{{E}} [1;0]^^k *> r.
Proof.
  revert r. induction k; intros r. { apply ms_refl; reflexivity. }
  costs. { cbn [lpow app Str_app]. cstep. cstep. rewrite <- p10. apply IHk. } lia.
Qed.

(** A(a+1,b,c+3) -> A(a,b+2,c) *)
Lemma R_drain a b r:
  Lf (S a) b {{C}}> 1 >> 1 >> 1 >> r -->> (4*b+9) / Lf a (S (S b)) {{C}}> r.
Proof.
  unfold Lf. costs.
  { do 5 cstep.
    eapply ms_app. { apply (SC b). }
    cbn [lpow app Str_app]. cstep.
    eapply ms_app. { apply (SB b). }
    do 3 cstep.
    rewrite rot10. apply ms_refl. reflexivity. }
  lia.
Qed.

(** 1^(a+1) (10)^(b+2) C> 0 r  ->  1^a (10)^(b+2) C> 0 1 r *)
Lemma R_inner a b r:
  Lf (S a) (S (S b)) {{C}}> 0 >> r -->> (4*b+9) / Lf a (S (S b)) {{C}}> 0 >> 1 >> r.
Proof.
  unfold Lf. costs.
  { cbn [lpow app Str_app]. do 5 cstep.
    eapply ms_app. { apply (SC b). }
    cbn [lpow app Str_app]. cstep.
    eapply ms_app. { apply (SB b). }
    do 3 cstep.
    rewrite rot10. apply ms_refl. reflexivity. }
  lia.
Qed.

Lemma R_inner_all a b r:
  Lf a (S (S b)) {{C}}> 0 >> r -->> (a*(4*b+9)) / Lf 0 (S (S b)) {{C}}> 0 >> [1]^^a *> r.
Proof.
  revert r. induction a; intros r. { apply ms_refl. reflexivity. }
  costs.
  { eapply ms_app. { apply R_inner. }
    eapply ms_app. { apply IHa. }
    rewrite ones1. apply ms_refl. reflexivity. }
  lia.
Qed.

Lemma ones_odd k x: [1;1]^^k *> 1 >> x = [1]^^(2*k+1) *> x.
Proof. rewrite <- ones2. replace (2*k+1) with (S (2*k)) by lia. cbn [lpow app Str_app]. apply ones1. Qed.
Lemma Lf1 k: Lf (2*k+1) 1 = 0 >> 1 >> [1;1]^^k *> 1 >> const 0.
Proof. unfold Lf. rewrite ones_odd. reflexivity. Qed.

(** C on the blank left end *)
Lemma R_end k r:
  const 0 <{{C}} [0;1]^^k *> 0 >> 0 >> 1 >> r -->> (4*k+9) / Lf (2*k+3) 1 {{C}}> 1 >> r.
Proof.
  replace (2*k+3) with (2*(S k)+1) by lia. rewrite Lf1. costs.
  { do 3 cstep.
    eapply ms_app. { apply (SA (S k) (1 >> const 0) (0 >> 1 >> r)). }
    do 2 cstep. apply ms_refl. reflexivity. }
  lia.
Qed.

(** A(a,b+2,0), tail 0 r  ->  A(2b+5,1,a+1) *)
Lemma R_c0 a b r:
  Lf a (S (S b)) {{C}}> 0 >> r -->> (a*(4*b+9)+(6*b+18)) / Lf (2*b+5) 1 {{C}}> 1 >> [1]^^a *> r.
Proof.
  costs.
  { eapply ms_app. { apply R_inner_all. }
    change (Lf 0 (S (S b))) with (0 >> 1 >> 0 >> 1 >> [0;1]^^b *> const 0).
    do 5 cstep.
    eapply ms_app. { apply (SC b). }
    rewrite p01.
    eapply ms_app. { apply (R_end (S b)). }
    replace (2*(S b)+3) with (2*b+5) by lia. apply ms_refl. reflexivity. }
  nia.
Qed.

(** A(a,b+1,1), tail 0 r  ->  A(2b+5,1,a+1) *)
Lemma R_c1 a b r:
  Lf a (S b) {{C}}> 1 >> 0 >> 0 >> r -->> (2+(a*(4*b+9)+(6*b+18))) / Lf (2*b+5) 1 {{C}}> 1 >> [1]^^a *> r.
Proof.
  eapply ms_app with (n:=2). 2:{ apply R_c0. }
  change (Lf a (S (S b))) with (0 >> 1 >> Lf a (S b)).
  do 2 cstep. apply ms_refl. reflexivity.
Qed.

(** A(a+1,b+1,2) with tail 0 0 r -> 1^a (10)^(b+3) C> 0 1 r, then the c=0 rule *)
Lemma R_c2_step a b r:
  Lf (S a) (S b) {{C}}> 1 >> 1 >> 0 >> 0 >> 0 >> r -->> (4*b+19) / Lf a (S (S (S b))) {{C}}> 0 >> 1 >> r.
Proof.
  change (Lf (S a) (S b)) with (0 >> 1 >> [0;1]^^b *> 1 >> [1]^^a *> const 0).
  change (Lf a (S (S (S b)))) with (0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1]^^b *> [1]^^a *> const 0).
  costs.
  { do 13 cstep.
    eapply ms_app. { apply (SC b). }
    cbn [hd tl]. cstep.
    eapply ms_app. { apply (SB b). }
    do 5 cstep.
    rewrite rot10. apply ms_refl. reflexivity. }
  lia.
Qed.
Lemma R_c2_zero b r:
  Lf 0 (S b) {{C}}> 1 >> 1 >> 0 >> 0 >> 0 >> r -->> (6*b+30) / Lf (2*b+7) 1 {{C}}> 1 >> r.
Proof.
  change (Lf 0 (S b)) with (0 >> 1 >> [0;1]^^b *> const 0).
  costs.
  { do 13 cstep.
    eapply ms_app. { apply (SC b). }
    rewrite !p01.
    eapply ms_app. { apply (R_end (S (S b))). }
    replace (2*(S (S b))+3) with (2*b+7) by lia. apply ms_refl. reflexivity. }
  lia.
Qed.

(** A(0,b,c+5) -> A(2b+4,2,c) *)
Lemma R_reset b r:
  Lf 0 b {{C}}> 1 >> 1 >> 1 >> 1 >> 1 >> r -->> (6*b+25) / Lf (2*b+4) 2 {{C}}> r.
Proof.
  change (Lf 0 b) with ([0;1]^^b *> const 0).
  replace (Lf (2*b+4) 2) with (0 >> 1 >> 0 >> [1;1]^^(S (S b)) *> 1 >> const 0).
  2:{ unfold Lf. rewrite ones_odd. replace (2*S (S b)+1) with (S (2*b+4)) by lia. reflexivity. }
  costs.
  { do 5 cstep.
    eapply ms_app. { apply (SC b). }
    rewrite p01.
    do 3 cstep.
    eapply ms_app. { apply (SA (S (S b)) (1 >> const 0) (1 >> 1 >> r)). }
    do 9 cstep. apply ms_refl. reflexivity. }
  lia.
Qed.

Lemma p1c (x:Stream Sym) t: [1;1]^^t *> 1 >> x = 1 >> [1;1]^^t *> x.
Proof. induction t. { reflexivity. } cbn [lpow app Str_app]. rewrite IHt. reflexivity. Qed.

Definition halts_from c := exists n ch, c -->> n / ch /\ halted tm ch.

(** A(0,b,3) halts. *)
Lemma R_halt3 b r: halts_from (Lf 0 b {{C}}> 1 >> 1 >> 1 >> 0 >> 0 >> r).
Proof.
  change (Lf 0 b) with ([0;1]^^b *> const 0).
  do 2 eexists. split.
  { eapply ms_app. { do 5 cstep. apply (SC b). }
    rewrite p01.
    eapply ms_app. { do 3 cstep. apply (SA (S (S b)) (1 >> const 0) (0 >> 0 >> r)). }
    cbn [lpow app Str_app]. do 4 cstep. rewrite p1c.
    eapply ms_app. { apply (SE (S (S (S b))) (const 0)). }
    cstep. constructor. }
  reflexivity.
Qed.

(** A(0,b,4) halts. *)
Lemma R_halt4 b r: halts_from (Lf 0 b {{C}}> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 0 >> r).
Proof.
  change (Lf 0 b) with ([0;1]^^b *> const 0).
  do 2 eexists. split.
  { eapply ms_app. { do 5 cstep. apply (SC b). }
    rewrite p01.
    eapply ms_app. { do 3 cstep. apply (SA (S (S b)) (1 >> const 0) (1 >> 0 >> 0 >> 0 >> r)). }
    cbn [lpow app Str_app]. do 8 cstep. rewrite p1c.
    eapply ms_app. { apply (SE (S (S (S (S b)))) (const 0)). }
    cstep. constructor. }
  reflexivity.
Qed.

(** The high-level map. A(a,b,c) = 0^inf 1^a (10)^b C> 1^c 0^inf. *)
Definition A a b c : Q * tape := Lf a b {{C}}> [1]^^c *> const 0.
Definition reach x y := exists n, x -->> n / y.

Lemma padd (w:list Sym) (x:Stream Sym) a b: w^^a *> w^^b *> x = w^^(a+b) *> x.
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma c0u: const 0 = 0 >> const 0.
Proof. apply const_unfold. Qed.

Lemma drain k a b r: exists n, Lf (k+a) b {{C}}> [1]^^(3*k) *> r -->> n / Lf a (2*k+b) {{C}}> r.
Proof.
  revert b. induction k; intros b. { exists O. apply ms_refl. reflexivity. }
  destruct (IHk (S (S b))) as [n Hn].
  replace (3 * S k) with (S (S (S (3*k)))) by lia.
  replace (2 * S k + b) with (2*k + S (S b)) by lia.
  eexists. eapply ms_app. { apply (R_drain (k+a) b ([1]^^(3*k) *> r)). } exact Hn.
Qed.

Lemma reach_trans x y z: reach x y -> reach y z -> reach x z.
Proof. intros [n H1] [m H2]. exists (n+m). eapply ms_app; eauto. Qed.

(** rr=0, 1, 2 after draining. *)
Lemma tail_rule a b rr: rr < 3 -> b >= 1 -> (b >= 2 \/ rr >= 1 \/ a = O) ->
  reach (A a b rr) (A (2*b+2*rr+1) 1 (a+1)).
Proof.
  intros Hr Hb Hc. unfold A.
  replace (a+1) with (S a) by lia.
  destruct rr as [|[|[|rr]]]; [|  | | lia].
  - destruct b as [|[|b]]; [lia| |].
    + destruct Hc as [Hc|[Hc|Hc]]; [lia|lia|subst a].
      unfold reach, Lf. eexists. cbn [lpow app Str_app].
      repeat (try solve [apply ms_refl; reflexivity]; cstep).
    + replace (2*S (S b)+2*O+1) with (2*b+5) by lia.
      pose proof (R_c0 a b (const 0)) as H. rewrite <- c0u in H. eexists. exact H.
  - destruct b as [|b]; [lia|].
    replace (2*S b+2*(S O)+1) with (2*b+5) by lia.
    pose proof (R_c1 a b (const 0)) as H. rewrite <- !c0u in H. eexists. exact H.
  - destruct b as [|b]; [lia|].
    destruct a as [|a].
    + replace (2*S b+2*(S (S O))+1) with (2*b+7) by lia.
      pose proof (R_c2_zero b (const 0)) as H. rewrite <- !c0u in H. eexists. exact H.
    + replace (2*S b+2*(S (S O))+1) with (2*(S b)+5) by lia.
      pose proof (R_c2_step a b (const 0)) as H. rewrite <- !c0u in H.
      pose proof (R_c0 a (S b) (1 >> const 0)) as H2. rewrite ones1 in H2.
      eexists. eapply ms_app; [exact H | exact H2].
Qed.

Definition d3 c := Nat.div c 3.
Definition m3 c := Nat.modulo c 3.
Lemma dm3 c: c = 3*d3 c + m3 c /\ m3 c < 3.
Proof. unfold d3, m3. split; [apply Nat.div_mod; lia | apply Nat.mod_upper_bound; lia]. Qed.
Global Opaque d3 m3.

Definition step273 (s: nat*nat*nat) : option (nat*nat*nat) :=
  match s with (a,b,c) =>
    if Nat.ltb c (3*a+3) then Some ((4*(d3 c)+2*b+2*(m3 c)+1)%nat, 1%nat, (a-d3 c+1)%nat)
    else if Nat.ltb c (3*a+5) then None
    else Some ((4*a+2*b+4)%nat, 2%nat, (c-3*a-5)%nat)
  end.

Definition inv (s: nat*nat*nat) := match s with (a,b,c) => b = 2%nat \/ (b = 1%nat /\ (c >= 1 \/ a = O)) end.
Definition cfg (s: nat*nat*nat) := match s with (a,b,c) => A a b c end.

Lemma inv_step s s': inv s -> step273 s = Some s' -> inv s'.
Proof.
  destruct s as [[a b] c]. destruct s' as [[a' b'] c']. cbn [step273 inv]. intros _ H.
  destruct (Nat.ltb c (3*a+3)) eqn:E1.
  - inversion H; subst. right. split; [reflexivity | left; lia].
  - destruct (Nat.ltb c (3*a+5)); inversion H; subst. left; reflexivity.
Qed.

Lemma lo_rule k a0 b rr: rr < 3 -> b >= 1 -> (2*k+b >= 2 \/ rr >= 1 \/ a0 = O) ->
  reach (A (k+a0) b (3*k+rr)) (A (4*k+2*b+2*rr+1) 1 (a0+1)).
Proof.
  intros Hr Hb Hc.
  eapply reach_trans with (y:=A a0 (2*k+b) rr).
  { destruct (drain k a0 b ([1]^^rr *> const 0)) as [n Hn]. exists n. unfold A.
    rewrite <- padd. exact Hn. }
  replace (4*k+2*b+2*rr+1) with (2*(2*k+b)+2*rr+1) by lia.
  apply tail_rule; lia.
Qed.

Lemma hi_rule a b d: reach (A a b (3*a+(5+d))) (A (4*a+2*b+4) 2 d).
Proof.
  destruct (drain a 0 b ([1]^^5 *> [1]^^d *> const 0)) as [n Hn].
  replace (a+O) with a in Hn by lia.
  replace (4*a+2*b+4) with (2*(2*a+b)+4) by lia.
  eexists. eapply ms_app.
  { unfold A. rewrite <- !padd. exact Hn. }
  exact (R_reset (2*a+b) ([1]^^d *> const 0)).
Qed.

Lemma step_some s s': inv s -> step273 s = Some s' -> reach (cfg s) (cfg s').
Proof.
  destruct s as [[a b] c]. destruct s' as [[a' b'] c']. cbn [step273 inv cfg]. intros Hi H.
  destruct (Nat.ltb c (3*a+3)) eqn:E1.
  - apply Nat.ltb_lt in E1. injection H; intros Hc' Hb' Ha'; clear H.
    destruct (dm3 c) as [Hc Hr]. revert Hc Hr Hc' Ha'.
    generalize (d3 c) (m3 c). intros k rr Hc Hr Hc' Ha'.
    assert (Hk: k <= a) by lia.
    destruct (Nat.le_exists_sub k a Hk) as [a0 [Ha _]].
    assert (Ea: a' = 4*k+2*b+2*rr+1) by lia.
    assert (Ec: c' = a0+1) by lia.
    clear Ha' Hc'. subst a' b' c' c a.
    replace (a0+k) with (k+a0) by lia.
    apply lo_rule; lia.
  - apply Nat.ltb_ge in E1.
    destruct (Nat.ltb c (3*a+5)) eqn:E2; [discriminate|].
    apply Nat.ltb_ge in E2.
    injection H; intros Hc' Hb' Ha'; clear H.
    destruct (Nat.le_exists_sub (3*a+5) c E2) as [d [Hd _]].
    assert (Ea: a' = 4*a+2*b+4) by lia.
    assert (Ec: c' = d) by lia.
    replace c with (3*a+(5+d)) by lia.
    clear Ha' Hc'. subst a' b' c'.
    apply hi_rule.
Qed.

Lemma halts_trans x y: reach x y -> halts_from y -> halts_from x.
Proof. intros [n H1] [m [ch [H2 H3]]]. exists (n+m), ch. split; [eapply ms_app; eauto | exact H3]. Qed.

Lemma step_none s: step273 s = None -> halts_from (cfg s).
Proof.
  destruct s as [[a b] c]. cbn [step273 cfg]. intros H.
  destruct (Nat.ltb c (3*a+3)) eqn:E1; [discriminate|].
  destruct (Nat.ltb c (3*a+5)) eqn:E2; [|discriminate].
  apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2.
  assert (Hc: c = 3*a+3 \/ c = 3*a+4) by lia.
  destruct Hc as [->| ->].
  - eapply halts_trans.
    2:{ apply (R_halt3 (2*a+b) (const 0)). }
    destruct (drain a 0 b ([1]^^3 *> const 0)) as [n Hn].
    exists n. unfold A. rewrite <- padd. replace (a+O) with a in Hn by lia.
    cbn [lpow app Str_app] in Hn. rewrite <- !c0u. exact Hn.
  - eapply halts_trans.
    2:{ apply (R_halt4 (2*a+b) (const 0)). }
    destruct (drain a 0 b ([1]^^4 *> const 0)) as [n Hn].
    exists n. unfold A. rewrite <- padd. replace (a+O) with a in Hn by lia.
    cbn [lpow app Str_app] in Hn. rewrite <- !c0u. exact Hn.
Qed.

Lemma start: reach c0 (A 0 1 0).
Proof.
  unfold reach, A, Lf, c0, tape0. eexists. cbn [lpow app Str_app].
  repeat (try solve [apply ms_refl; reflexivity]; cstep).
Qed.

Fixpoint iter (n:nat) (s: nat*nat*nat) : option (nat*nat*nat) :=
  match n with
  | O => Some s
  | S m => match step273 s with Some s' => iter m s' | None => None end
  end.

(** If the map halts within N steps from A(0,1,0), the machine halts from the blank tape. *)
Theorem halts_of_orbit N: iter N (O,1%nat,O) = None -> halts tm c0.
Proof.
  intros H.
  assert (G: forall n s, inv s -> iter n s = None -> halts_from (cfg s)).
  { induction n; intros s Hi Ht; cbn in Ht; [discriminate|].
    destruct (step273 s) as [s'|] eqn:E.
    - eapply halts_trans. { eapply step_some; eauto. } apply IHn; [eapply inv_step; eauto | exact Ht].
    - apply step_none. exact E. }
  assert (X: halts_from c0).
  { eapply halts_trans. { apply start. } apply (G N (O,1%nat,O)); [| exact H]. cbn [inv]. right. split; [reflexivity|right; reflexivity]. }
  destruct X as [n [ch [H1 H2]]]. exists n, ch. split; assumption.
Qed.

Print Assumptions halts_of_orbit.
